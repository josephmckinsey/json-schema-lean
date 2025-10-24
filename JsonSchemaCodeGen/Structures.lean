import JsonSchema.Schema
import JsonSchemaCodeGen.Config
import JsonSchemaCodeGen.InlineTypes
import Lean

namespace JsonSchemaCodeGen

open Lean JsonSchema

/-- Check if a field name is in the required array -/
def isFieldRequired (fieldName : String) (required : Option (Array String)) : Bool :=
  required.any (·.contains fieldName)

/-- Generate a type name for a nested field (prepend parent name to avoid conflicts) -/
def generateFieldTypeName (parentTypeName : String) (fieldName : String) (config : Config) : String :=
  config.sanitizeName (parentTypeName ++ capitalize fieldName)

/-- Get the type definition for a field, trying parseInline first, then schemaToTypeDef.
    Returns the full TypeDefinition to preserve FromJson/ToJson instances and doc comments.
    The prec parameter is passed to parseInline for proper parenthesization. -/
partial def getFieldType (schema : JsonSchema.Schema) (parentTypeName : String) (fieldName : String)
    (prec : Nat) (schemaToTypeDef : JsonSchema.Schema → String → SchemaGen TypeDefinition)
    : SchemaGen TypeDefinition :=
  -- Try to parse inline first (for simple types)
  parseInline schema prec <|> (do
    -- Complex type, needs a named definition
    let typeName := generateFieldTypeName parentTypeName fieldName (← getConfig)
    let typeDef ← schemaToTypeDef schema typeName
    -- Return a TypeDefinition that references this named type
    return {
      typeDecl := .text typeName
      dependencies := [typeDef]
    }
  )

/-- Wrap a type in Option for optional fields, preserving FromJson/ToJson and doc comments -/
def makeOptionalFieldType (schema : JsonSchema.Schema) (parentTypeName : String) (fieldName : String)
    (schemaToTypeDef : JsonSchema.Schema → String → SchemaGen TypeDefinition)
    : SchemaGen TypeDefinition := do
  let innerTypeDef ← getFieldType schema parentTypeName fieldName max_prec schemaToTypeDef

  -- If the inner type has custom FromJson/ToJson, wrap them with Option instances
  let fromJsonImpl := innerTypeDef.fromJsonImpl.map fun innerFromJson =>
    "Option.some" ++ .line ++ "<$>" ++ .line ++ Std.Format.paren innerFromJson

  let toJsonImpl := innerTypeDef.toJsonImpl.map fun innerToJson =>
    Std.Format.text "@Option.toJson" ++ Std.Format.line ++ "_" ++
      Std.Format.line ++ "⟨fun x => " ++ innerToJson ++ "⟩" ++
      Std.Format.line ++ Std.Format.text "x"

  return {
    typeDecl := "Option " ++ innerTypeDef.typeDecl
    fromJsonImpl := fromJsonImpl
    toJsonImpl := toJsonImpl
    dependencies := innerTypeDef.dependencies
    extraDocComment := innerTypeDef.extraDocComment
  }

/-- Build a single field declaration with optional doc comment.
    Merges the schema's description with any extra documentation from the field's type. -/
def mkFieldDecl (fieldName : String) (typeFormat : Std.Format) (schema : JsonSchema.Schema)
    (extraDocComment : Option Std.Format) (config : Config) : Std.Format :=
  let sanitizedName := config.sanitizeName fieldName

  -- Combine schema description with extra doc comment from inlined type
  let combined := combineDocStrings schema.getDocString extraDocComment
  let docComment := if combined.isEmpty then .nil else mkDocComment combined ++ "\n"

  docComment ++ sanitizedName ++ " : " ++ typeFormat

/-- Build FromJson instance for a structure.
    For each field, we parse it from the JSON object and use fromJson?.
    If a field has a custom FromJson implementation, it will be used automatically
    by the type system when we call fromJson? on that field's value. -/
def mkStructFromJson (typeName : String) (fieldInfos : List (String × String × TypeDefinition)) : Format := Id.run do
  -- Generate parsing code for each field
  let mut fieldBindsList : List Format := []
  for (origName, sanitizedName, typeDef) in fieldInfos do
    -- Get the JSON value for this field
    let getField := "j.getObjValD \"" ++ origName ++ "\""

    -- Parse the field value
    -- If the field has a custom fromJson, we need to use it
    let parseExpr := match typeDef.fromJsonImpl with
      | some customParser =>
        -- Custom parser expects 'j' to be bound to the field value
        "(let j := " ++ getField ++ "; " ++ customParser.pretty ++ ")"
      | none =>
        -- Use standard fromJson?
        "fromJson? (" ++ getField ++ ")"

    fieldBindsList := ("let " ++ sanitizedName ++ " ← " ++ parseExpr) :: fieldBindsList

  let fieldBinds := fieldBindsList.reverse

  -- Build the final structure construction
  let ctorCall := "{ " ++ String.intercalate ", " (fieldInfos.map (fun (_, sanitizedName, _) => sanitizedName)) ++ " }"

  let parseCode : Format := Std.Format.joinSep fieldBinds "\n" ++ "\n.ok " ++ ctorCall

  return Std.Format.group (Std.Format.nestD (
    "instance : FromJson " ++ typeName ++ " where\n" ++
    Std.Format.nestD ("fromJson? j := do\n" ++
      parseCode
    )
  ))

/-- Build ToJson instance for a structure.
    For each field, we serialize it using toJson and build a JSON object. -/
def mkStructToJson (typeName : String) (fieldInfos : List (String × String × TypeDefinition)) : Format := Id.run do
  -- Generate serialization for each field
  let fieldSerializers := fieldInfos.map fun (origName, sanitizedName, typeDef) =>
    let toJsonExpr := match typeDef.toJsonImpl with
      | some customToJson =>
        -- Custom toJson that expects 'x' to be bound to the field value
        let binding := "let x := s." ++ sanitizedName ++ "; "
        "(\"" ++ origName ++ "\", " ++ binding ++ customToJson.pretty ++ ")"
      | none =>
        -- Use standard toJson
        "(\"" ++ origName ++ "\", toJson s." ++ sanitizedName ++ ")"
    toJsonExpr

  let objCode : Format := "Json.mkObj [" ++ Std.Format.joinSep fieldSerializers ", " ++ "]"

  return Std.Format.group (Std.Format.nestD (
    "instance : ToJson " ++ typeName ++ " where\n" ++
    Std.Format.nestD ("toJson s := " ++ objCode)
  ))

/-- Convert an object schema to a structure definition

    This will handle:
    - properties → struct fields
    - required vs optional fields
    - nested objects (via schemaToTypeDef)
    - doc comments from descriptions
-/
partial def objectToStructure (obj : JsonSchema.SchemaObject) (typeName : String)
    (schemaToTypeDef : JsonSchema.Schema → String → SchemaGen TypeDefinition)
    : SchemaGen TypeDefinition := do
  let config ← getConfig
  -- Check that we have properties
  let properties := obj.properties.getD #[]
  if properties.isEmpty then
    throw "Object has no properties, cannot generate structure"

  -- Process each field once, collecting all info needed
  let mut allDependencies : List TypeDefinition := []
  let mut fieldDecls : List Std.Format := []
  let mut fieldInfosList : List (String × String × TypeDefinition) := []

  for (fieldName, fieldSchema) in properties do
    let required := isFieldRequired fieldName obj.required
    let fieldTypeDef ← if required then
      getFieldType fieldSchema typeName fieldName 0 schemaToTypeDef
    else
      makeOptionalFieldType fieldSchema typeName fieldName schemaToTypeDef

    -- Collect dependencies
    allDependencies := allDependencies ++ fieldTypeDef.dependencies

    -- Build field declaration
    let fieldDecl := mkFieldDecl fieldName fieldTypeDef.typeDecl
      fieldSchema fieldTypeDef.extraDocComment config
    fieldDecls := fieldDecl :: fieldDecls

    -- Collect field info for instances
    let sanitizedName := config.sanitizeName fieldName
    fieldInfosList := (fieldName, sanitizedName, fieldTypeDef) :: fieldInfosList

  -- Build the structure format
  let structDoc := match obj.description with
    | some desc => f!"/-- {desc} -/\n"
    | none => .nil

  let fields := Std.Format.joinSep fieldDecls.reverse "\n"
  let structDecl := structDoc ++ .group (.nestD  ("structure " ++ typeName ++ " where\n" ++ fields))

  -- Build FromJson and ToJson instances
  let fieldInfos := fieldInfosList.reverse
  let fromJsonImpl := mkStructFromJson typeName fieldInfos
  let toJsonImpl := mkStructToJson typeName fieldInfos

  return {
    typeDecl := structDecl
    fromJsonImpl := fromJsonImpl
    toJsonImpl := toJsonImpl
    dependencies := allDependencies
  }

end JsonSchemaCodeGen
