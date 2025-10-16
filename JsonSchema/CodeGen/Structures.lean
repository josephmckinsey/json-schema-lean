import JsonSchema.Schema
import JsonSchema.CodeGen.Config
import JsonSchema.CodeGen.Types
import Lean

namespace JsonSchema.CodeGen

open Lean

/-- Check if a field name is in the required array -/
def isFieldRequired (fieldName : String) (required : Option (Array String)) : Bool :=
  required.any (·.contains fieldName)

/-- Generate a type name for a nested field (prepend parent name to avoid conflicts) -/
def generateFieldTypeName (parentTypeName : String) (fieldName : String) (config : Config) : String :=
  config.sanitizeName (parentTypeName ++ capitalize fieldName)

/-- Get the type format for a field, trying parseInline first, then schemaToTypeDef.
    Returns (typeFormat, dependencies) where dependencies are nested type definitions.
    The prec parameter is passed to parseInline for proper parenthesization. -/
partial def getFieldType (schema : JsonSchema.Schema) (parentTypeName : String) (fieldName : String)
    (prec : Nat) (schemaToTypeDef : JsonSchema.Schema → String → Except String TypeDefinition)
    (config : Config) : Except String (Std.Format × List TypeDefinition) := do
  -- Try to parse inline first (for simple types)
  match parseInline schema prec with
  | .ok typeDef => return (typeDef.typeDecl, [])
  | .error _ =>
    -- Complex type, needs a named definition
    let typeName := generateFieldTypeName parentTypeName fieldName config
    let typeDef ← schemaToTypeDef schema typeName
    return (.text typeName, [typeDef])

/-- Wrap a type format in Option for optional fields -/
def makeOptionalFieldType (schema : JsonSchema.Schema) (parentTypeName : String) (fieldName : String)
    (schemaToTypeDef : JsonSchema.Schema → String → Except String TypeDefinition)
    (config : Config) : Except String (Std.Format × List TypeDefinition) := do
  let (typeFormat, deps) ← getFieldType schema parentTypeName fieldName max_prec schemaToTypeDef config
  return ("Option " ++ typeFormat, deps)

/-- Build a single field declaration with optional doc comment -/
def mkFieldDecl (fieldName : String) (typeFormat : Std.Format) (schema : JsonSchema.Schema)
    (config : Config) : Std.Format :=
  let sanitizedName := config.sanitizeName fieldName
  let docComment := schema.getDoc
  docComment ++ sanitizedName ++ " : " ++ typeFormat

/-- Convert an object schema to a structure definition

    This will handle:
    - properties → struct fields
    - required vs optional fields
    - nested objects (via schemaToTypeDef)
    - doc comments from descriptions
-/
partial def objectToStructure (obj : JsonSchema.SchemaObject) (typeName : String)
    (schemaToTypeDef : JsonSchema.Schema → String → Except String TypeDefinition)
    (config : Config := {}) : Except String TypeDefinition := do
  -- Check that we have properties
  let properties := obj.properties.getD #[]
  if properties.isEmpty then
    throw "Object has no properties, cannot generate structure"

  -- Process each field
  let mut allDependencies : List TypeDefinition := []
  let mut fieldDecls : List Std.Format := []

  for (fieldName, fieldSchema) in properties do
    let required := isFieldRequired fieldName obj.required
    let (fieldType, deps) ← if required then
      getFieldType fieldSchema typeName fieldName 0 schemaToTypeDef config
    else
      makeOptionalFieldType fieldSchema typeName fieldName schemaToTypeDef config
    allDependencies := allDependencies ++ deps
    let fieldDecl := mkFieldDecl fieldName fieldType fieldSchema config
    fieldDecls := fieldDecl :: fieldDecls

  -- Build the structure format
  let structDoc := match obj.description with
    | some desc => f!"/-- {desc} -/\n"
    | none => .nil

  let fields := Std.Format.joinSep fieldDecls.reverse "\n"
  let structDecl := structDoc ++ .group (.nestD  ("structure " ++ typeName ++ " where\n" ++ fields))

  return {
    typeDecl := structDecl
    dependencies := allDependencies
  }

end JsonSchema.CodeGen
