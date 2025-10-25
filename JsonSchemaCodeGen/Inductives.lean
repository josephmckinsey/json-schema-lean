import JsonSchema.Schema
import JsonSchemaCodeGen.Config
import JsonSchemaCodeGen.InlineTypes
import JsonSchemaCodeGen.Structures
import Lean

namespace JsonSchemaCodeGen

open Lean JsonSchema

/-- Generate a constructor name from a JSON value for an enum.

- Strings become the sanitized string value
- Objects use their first key (sanitized) with "_" appended to other keys
- Other types get generic names
-/
def jsonToConstructorName (j : Json) (config : Config) : String :=
  match j with
  | .str s => config.sanitizeName s
  | .obj kvPairs =>
    -- For objects, concatenate all keys separated by underscores
    let keys := kvPairs.toArray.map (fun (k, _) => config.sanitizeName k)
    String.intercalate "_" keys.toList
  | .num n => s!"num_{n.toString.replace "." "_" |>.replace "-" "neg_"}"
  | .bool true => "true"
  | .bool false => "false"
  | .null => "null"
  | .arr _ => "arr"


inductive Test' where | A | B

/-- Convert an enum schema to an inductive type with custom FromJson/ToJson.

This handles:
- enum values → constructors (no payloads)
- Name generation from values
- FromJson/ToJson instances that validate exact matches
-/
def enumToInductive (enum : Array Json) (typeName : String)
    (config : Config := {}) : Except String TypeDefinition := do
  -- Generate constructor names from enum values
  let constructors := enum.map (fun j => jsonToConstructorName j config)

  -- Build the inductive type declaration
  let constructorLines := constructors.map (fun c => "| " ++ c)
  let typeDecl := .group (.nestD (
    "inductive " ++ typeName ++ " where" ++
    Std.Format.prefixJoin .line constructorLines.toList
  ))

  -- Build FromJson instance
  -- Pattern: match all values with their corresponding constructors
  let fromJsonCases := (enum.zip constructors).map fun (jsonVal, ctorName) =>
    let jsonReprFmt := jsonRepr jsonVal 0  -- Use the jsonRepr from Types.lean
    "| " ++ jsonReprFmt ++ " => .ok ." ++ ctorName
  let fromJsonImpl := Std.Format.group (Std.Format.nestD (
    "instance : FromJson " ++ typeName ++ " where\n" ++
    Std.Format.nestD ("fromJson? j := match j with\n" ++
      Std.Format.joinSep fromJsonCases.toList "\n" ++ "\n" ++
      "| _ => .error s!\"Invalid enum value: {j}\""
    )
  ))

  -- Build ToJson instance
  let toJsonCases := constructors.map fun ctorName =>
    let matchingJson := enum.find? (fun j => jsonToConstructorName j config == ctorName)
    match matchingJson with
    | some j => "| ." ++ ctorName ++ " => " ++ jsonRepr j 0
    | none => "| ." ++ ctorName ++ " => Json.null"  -- Shouldn't happen
  let toJsonImpl := Std.Format.group (Std.Format.nestD (
    "instance : ToJson " ++ typeName ++ " where\n" ++
    Std.Format.nestD ("toJson x := match x with\n" ++
      Std.Format.joinSep toJsonCases.toList "\n"
    )
  ))

  .ok {
    typeDecl := typeDecl
    fromJsonImpl := fromJsonImpl
    toJsonImpl := toJsonImpl
  }

/-- Field information for a constructor argument -/
structure FieldInfo where
  origName : String              -- Original JSON field name
  sanitizedName : String         -- Sanitized Lean identifier
  typeDef : TypeDefinition       -- Type information with custom FromJson/ToJson

/-- Build constructor arguments for an object-based variant.
    Returns field declarations like "(x : Int) (tail : List)" along with field information -/
partial def mkConstructorArgs (obj : JsonSchema.SchemaObject) (typeName : String)
    (schemaToTypeDef : JsonSchema.Schema → String → SchemaGen TypeDefinition)
    : SchemaGen (Format × List TypeDefinition × Array FieldInfo) := do
  let properties := obj.properties.getD #[]
  if properties.isEmpty then
    throw "Constructor variant has no properties"

  let mut allDependencies : List TypeDefinition := []
  let mut argDecls : List Format := []
  let mut fieldInfosList : List FieldInfo := []

  for (fieldName, fieldSchema) in properties do
    let required := obj.required.any (·.contains fieldName)
    -- We call the baseURI pdate within getFieldType
    let fieldTypeDef ← if required then
      getFieldType fieldSchema typeName fieldName max_prec schemaToTypeDef
    else
      makeOptionalFieldType fieldSchema typeName fieldName schemaToTypeDef
    allDependencies := allDependencies ++ fieldTypeDef.dependencies
    let sanitizedName := (←getConfig).sanitizeName fieldName
    argDecls := ("(" ++ sanitizedName ++ " : " ++ fieldTypeDef.typeDecl ++ ")") :: argDecls
    fieldInfosList := { origName := fieldName, sanitizedName := sanitizedName, typeDef := fieldTypeDef } :: fieldInfosList

  let fieldInfos := fieldInfosList.reverse.toArray
  return (Std.Format.joinSep argDecls.reverse " ", allDependencies, fieldInfos)

/-- Info about a variant constructor -/
structure VariantInfo where
  ctorName : String
  ctorDecl : Format
  /-- Field information for object-based variants (none for simple types) -/
  fieldInfos : Option (Array FieldInfo) := none
  dependencies : List TypeDefinition
  /-- Custom FromJson implementation from parseInline (if any) -/
  fromJsonTerm : Option Format := none
  /-- Custom ToJson implementation from parseInline (if any) -/
  toJsonTerm : Option Format := none
  /-- Doc comment for this variant (from schema description) -/
  docComment : Option Format := none

/-- Convert a oneOf variant to a constructor declaration with metadata.
    Returns variant info including whether it's a simple type or object. -/
partial def variantToConstructor (variant : JsonSchema.Schema) (ctorName : String) (typeName : String)
    (schemaToTypeDef : JsonSchema.Schema → String → SchemaGen TypeDefinition)
    : SchemaGen VariantInfo :=
  -- Simple inline type: | case0 (val : String)
  (do
    let typeDef ← parseInline variant max_prec
    let ctorDecl := "| " ++ ctorName ++ " (val : " ++ typeDef.typeDecl ++ ")"
    -- Extract doc comment from variant schema
    let docComment := variant.getDocString
    return {
      ctorName,
      ctorDecl,
      fieldInfos := none,
      dependencies := [],
      fromJsonTerm := typeDef.fromJsonImpl,
      toJsonTerm := typeDef.toJsonImpl,
      docComment := if docComment.isEmpty then none else some docComment
    }) <|>
  match variant with
  | .Object obj => do
    if obj.type.contains .ObjectType && obj.properties.isSome then
      -- Multi-field constructor: | cons (head : Int) (tail : List)
      -- Use typeName + ctorName as parent to avoid naming conflicts between variants
      let (args, deps, fieldInfos) ← mkConstructorArgs obj (typeName ++ ctorName) schemaToTypeDef
      let ctorDecl := "| " ++ ctorName ++ " " ++ args

      -- Combine variant description with field extraDocComments
      let variantDoc := variant.getDocString
      let fieldExtraDocs := fieldInfos.toList.filterMap (·.typeDef.extraDocComment)
      let allDocs := if variantDoc.isEmpty then fieldExtraDocs else variantDoc :: fieldExtraDocs
      let combinedDoc := if allDocs.isEmpty then .nil else Std.Format.joinSep allDocs "\n\n"

      return {
        ctorName,
        ctorDecl,
        fieldInfos := some fieldInfos,
        dependencies := deps,
        docComment := if combinedDoc.isEmpty then none else some combinedDoc
      }
    else
      -- Complex type that can't be inlined: generate as named type dependency
      -- This handles enums, nested oneOf/anyOf, and other complex schemas
      let variantTypeName := typeName ++ ctorName.capitalize
      let typeDef ← schemaToTypeDef variant variantTypeName
      let ctorDecl := "| " ++ ctorName ++ " (val : " ++ variantTypeName ++ ")"
      let docComment := variant.getDocString
      return {
        ctorName,
        ctorDecl,
        fieldInfos := none,
        dependencies := [typeDef],
        docComment := if docComment.isEmpty then none else some docComment
      }
  | _ => throwWithContext s!"Could not construct argument for variant {ctorName} {variant} of {typeName}
  This error should be unreachable"

/-- Build FromJson instance for a oneOf inductive type -/
def mkOneOfFromJson (variantInfos : Array VariantInfo) (typeName : String) : Format := Id.run do
  let mut fromJsonCases : List Format := []
  for info in variantInfos do
    let ctorName := info.ctorName
    match info.fieldInfos with
    | none =>
      -- Simple type: use custom parser if available, otherwise use fromJson?
      let caseFormat : Format := match info.fromJsonTerm with
        | some customParser => "." ++ ctorName ++ " <$> (" ++ customParser ++ ")"
        | none => "." ++ ctorName ++ " <$> fromJson? j"
      fromJsonCases := fromJsonCases ++ [caseFormat]
    | some fieldInfos =>
      -- Object type: parse each field with custom parsers if available
      let fieldBinds := fieldInfos.toList.zipIdx.map fun (fieldInfo, idx) =>
        let getField := "j.getObjValD \"" ++ fieldInfo.origName ++ "\""
        let parseExpr := match fieldInfo.typeDef.fromJsonImpl with
          | some customParser =>
            -- Custom parser expects 'j' to be bound to the field value
            "(let j := " ++ getField ++ "; " ++ customParser.pretty ++ ")"
          | none =>
            -- Use standard fromJson?
            "fromJson? (" ++ getField ++ ")"
        s!"let f{idx} ← " ++ parseExpr
      let ctorCall := "." ++ ctorName ++ " " ++ String.intercalate " " (List.range fieldInfos.size |>.map fun i => s!"f{i}")
      let parseCode : Format := Std.Format.joinSep fieldBinds.reverse "\n" ++ "\n.ok " ++ ctorCall
      fromJsonCases := fromJsonCases ++ ["(do\n" ++ Std.Format.nestD parseCode ++ ")"]

  return Std.Format.group (Std.Format.nestD (
    "instance : FromJson " ++ typeName ++ " where\n" ++
    Std.Format.nestD ("fromJson? j :=\n" ++
      Std.Format.nestD (Std.Format.joinSep fromJsonCases " <|>\n")
    )
  ))

/-- Build ToJson instance for a oneOf inductive type -/
def mkOneOfToJson (variantInfos : Array VariantInfo) (typeName : String) : Format := Id.run do
  let mut toJsonCases : List Format := []
  for info in variantInfos do
    let ctorName := info.ctorName
    match info.fieldInfos with
    | none =>
      -- Simple type: use custom serializer if available, otherwise use toJson
      let caseFormat : Format := match info.toJsonTerm with
      -- Custom toJson that takes the value and returns Json
      | some customToJson => "| ." ++ ctorName ++ " x => " ++ customToJson
      | none => "| ." ++ ctorName ++ " val => toJson val"
      toJsonCases := toJsonCases ++ [caseFormat]
    | some fieldInfos =>
      -- Object type: serialize as object with field names, using custom serializers if available
      let fieldList : List Format := fieldInfos.toList.map fun fieldInfo =>
        let toJsonExpr := match fieldInfo.typeDef.toJsonImpl with
          | some customToJson =>
            -- Custom toJson that expects 'x' to be bound to the field value
            let binding := "let x := " ++ fieldInfo.sanitizedName ++ "; "
            "(\"" ++ fieldInfo.origName ++ "\", " ++ binding ++ customToJson.pretty ++ ")"
          | none =>
            -- Use standard toJson
            "(\"" ++ fieldInfo.origName ++ "\", toJson " ++ fieldInfo.sanitizedName ++ ")"
        toJsonExpr
      let objCode : Format := "Json.mkObj [" ++ Std.Format.joinSep fieldList ", " ++ "]"
      let pattern : Format := "." ++ ctorName ++ " " ++ String.intercalate " " (fieldInfos.toList.map (·.sanitizedName))
      let caseFormat : Format := "| " ++ pattern ++ " => " ++ objCode
      toJsonCases := toJsonCases ++ [caseFormat]

  return Std.Format.group (Std.Format.nestD (
    "instance : ToJson " ++ typeName ++ " where\n" ++
    Std.Format.nestD ("toJson x := match x with\n" ++
      Std.Format.joinSep toJsonCases "\n"
    )
  ))

/-- Convert a oneOf schema to an inductive type with constructor payloads.

This handles:
- oneOf variants → constructors with payloads
- Case naming (case0, case1, etc.)
- FromJson/ToJson instances that try each variant
-/
def oneOfToInductive (variants : Array JsonSchema.Schema) (typeName : String)
    (schemaToTypeDef : JsonSchema.Schema → String → SchemaGen TypeDefinition)
    : SchemaGen TypeDefinition := do
  -- For each variant, convert to constructor
  let mut variantInfos : Array VariantInfo := #[]
  let mut allDependencies : List TypeDefinition := []

  for i in [:variants.size] do
    let variant := variants[i]!
    let ctorName := s!"case{i}"
    let info ← variantToConstructor variant ctorName typeName schemaToTypeDef
    variantInfos := variantInfos.push info
    allDependencies := allDependencies ++ info.dependencies

  -- Build the inductive type declaration with doc comments
  let constructorDeclsWithDocs := variantInfos.toList.map fun info =>
    match info.docComment with
    | some doc => mkDocComment doc ++ Std.Format.line ++ info.ctorDecl
    | none => info.ctorDecl
  let typeDecl := .group (.nestD (
    "inductive " ++ typeName ++ " where" ++
    Std.Format.prefixJoin Std.Format.line constructorDeclsWithDocs
  ))

  -- Build FromJson and ToJson instances
  let fromJsonImpl := mkOneOfFromJson variantInfos typeName
  let toJsonImpl := mkOneOfToJson variantInfos typeName

  pure {
    typeDecl := typeDecl
    fromJsonImpl := fromJsonImpl
    toJsonImpl := toJsonImpl
    dependencies := allDependencies
  }

/-- Convert an anyOf schema to an inductive type.

For now, anyOf is treated the same as oneOf - we generate an inductive type
with constructors for each variant. In the future, we may want to handle
the semantic difference (anyOf allows multiple valid interpretations).
-/
def anyOfToInductive (variants : Array JsonSchema.Schema) (typeName : String)
    (schemaToTypeDef : JsonSchema.Schema → String → SchemaGen TypeDefinition)
    : SchemaGen TypeDefinition :=
  oneOfToInductive variants typeName schemaToTypeDef

end JsonSchemaCodeGen
