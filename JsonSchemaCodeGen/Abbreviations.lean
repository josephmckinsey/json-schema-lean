import JsonSchema.Schema
import JsonSchemaCodeGen.Config
import JsonSchemaCodeGen.References
import JsonSchemaCodeGen.InlineTypes
import Lean

namespace JsonSchemaCodeGen

open Lean JsonSchema

def mkAbbrevTypeDefinition (s : JsonSchema.Schema) (name : String) (form : TypeDefinition) : TypeDefinition :=
  let combined := combineDocStrings s.getDocString form.extraDocComment
  let docComment := if combined.isEmpty then .nil else mkDocComment combined ++ .line
  {
    typeDecl := docComment ++ (
      Std.Format.group <|
        .nest 2 (
          f!"abbrev {name} :=" ++ .line ++ form.typeDecl
          ))
    fromJsonImpl := form.fromJsonImpl <&> fun fromJsonImpl =>
      .nestD ("instance : FromJson {name} where\n" ++
        .group (.nestD "fromJson? j :=" ++ .line ++ fromJsonImpl)
      )
    toJsonImpl := form.fromJsonImpl <&> fun fromJsonImpl =>
      .nestD ("instance : ToJson {name} where\n" ++
        .group (.nestD "toJson x :=" ++ .line ++ fromJsonImpl)
      )
    dependencies := form.dependencies
  }

def getItemArray (s : JsonSchema.Schema) : SchemaGen ItemsSchema :=
  match s with
  | .Boolean _ => .error "Could not parse array from bool"
  | .Object o => withNewID s do
    if o.type != #[.ArrayType] then
      .error s!"Could not parse array from type {o.type}"
    match o.items with
    | .some itemschema => pure itemschema
    | _ => .error "Could not find item schema"

/-- Try to parse a homogeneous array where the item type is inlineable.

    This handles: {"type": "array", "items": simpleSchema} → Array Type
    Only succeeds if the item schema can be parsed inline.
-/
def parseArrayAbbrev (s : JsonSchema.Schema) (name : String)
    (recurse : JsonSchema.Schema → String → SchemaGen TypeDefinition)
    : SchemaGen TypeDefinition := getItemArray s >>= fun itemschema => do
  let singleschema ← match itemschema with
  | (.Single singleschema) => pure singleschema
  | _ => .error "Cannot parse array from multi-itemschema"

  let itemTypeDef ← recurse singleschema (name ++ "Items")

  let typeDecl := "Array " ++ (name ++ "Items")

  -- Build FromJson instance if item has custom parser
  let fromJsonImpl := itemTypeDef.fromJsonImpl.map fun itemFromJson =>
    Std.Format.text "Array.fromJson?" ++ .line ++
      Std.Format.paren itemFromJson

  -- Build ToJson instance if item has custom serializer
  let toJsonImpl := itemTypeDef.toJsonImpl.map fun itemToJson =>
    Std.Format.text "@Array.toJson" ++ .line ++ "_" ++
      .line ++ "⟨fun x => " ++ itemToJson ++ "⟩" ++
      .line ++ Std.Format.text "x"

  pure <| mkAbbrevTypeDefinition s name {
    typeDecl := typeDecl
    fromJsonImpl := fromJsonImpl
    toJsonImpl := toJsonImpl
    dependencies := [itemTypeDef]
    extraDocComment := itemTypeDef.extraDocComment
  }

def parseInlineAbbrev (s : JsonSchema.Schema) (name : String) : SchemaGen TypeDefinition :=
  parseInline s <&> mkAbbrevTypeDefinition s name

end JsonSchemaCodeGen
