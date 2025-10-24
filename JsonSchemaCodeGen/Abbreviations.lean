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
      .nestD (f!"instance : FromJson {name} where\n" ++
        .group (.nestD "fromJson? j :=" ++ .line ++ fromJsonImpl)
      )
    toJsonImpl := form.toJsonImpl <&> fun toJsonImpl =>
      .nestD (f!"instance : ToJson {name} where\n" ++
        .group (.nestD "toJson x :=" ++ .line ++ toJsonImpl)
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

/-- Try to parse a tuple type (fixed-length array) as an abbreviation.

    This handles: {"type": "array", "items": [schema1, schema2, ...], "minItems": n, "maxItems": n}
    → abbrev Name := Type1 × Type2 × ...

    This tries to inline tuple items first (e.g., String, String ⊕ Int), and only creates
    named dependencies for complex types that can't be inlined.
-/
def parseTupleAbbrev (s : JsonSchema.Schema) (name : String)
    (recurse : JsonSchema.Schema → String → SchemaGen TypeDefinition)
    : SchemaGen TypeDefinition := getItemArray s >>= fun itemschema => do
  -- Extract tuple schemas
  let itemSchemas ← match itemschema with
  | (.Tuple schemas) => pure schemas
  | _ => .error "Cannot parse tuple from non-tuple item schema"

  -- Check for fixed-length tuple
  let len := itemSchemas.size
  if len < 2 then
    .error "Tuple must have at least 2 items"

  let obj ← match s with
  | .Object o => pure o
  | _ => .error "Expected object schema"

  match obj.minItems, obj.maxItems with
  | some min, some max =>
    if min != len || max != len then
      .error s!"minItems ({min}) and maxItems ({max}) must equal items length ({len})"
  | _, _ =>
    .error "Tuple requires both minItems and maxItems to be set"

  -- Try to parse each item as an inline type first, falling back to named types
  let mut itemTypeDefsAux : List TypeDefinition := []
  let mut allDependencies : List TypeDefinition := []
  let mut extraComments : List (Option Format) := []

  for (itemSchema, idx) in itemSchemas.toList.zipIdx do
    -- Try inline first (precedence 35 for × operator)
    try
      let inlineTypeDef ← parseInline itemSchema 35
      itemTypeDefsAux := inlineTypeDef :: itemTypeDefsAux
      allDependencies := inlineTypeDef.dependencies ++ allDependencies
      extraComments := inlineTypeDef.extraDocComment :: extraComments
    catch _ =>
      -- Fall back to named type
      let itemTypeDef ← recurse itemSchema s!"{name}Item{idx}"
      itemTypeDefsAux := { typeDecl := s!"{name}Item{idx}" } :: itemTypeDefsAux
      allDependencies := itemTypeDef :: allDependencies
      extraComments := itemTypeDef.extraDocComment :: extraComments

  let itemTypeDefs := itemTypeDefsAux.reverse
  let extraCommentsRev := extraComments.reverse

  -- Combine all extra doc comments
  let combinedExtra := extraCommentsRev.filterMap id
  let extraDocComment := if combinedExtra.isEmpty then none
    else some (Std.Format.joinSep combinedExtra ("\n\n"))

  -- Build the tuple type declaration from the type definitions
  let tupleType := Std.Format.joinSep (itemTypeDefs.map (·.typeDecl)) " × "

  -- Generate FromJson/ToJson instances using the full item type definitions
  let fromJsonImpl := getTupleFromJson itemTypeDefs
  let toJsonImpl := getTupleToJson itemTypeDefs

  pure <| mkAbbrevTypeDefinition s name {
    typeDecl := tupleType
    fromJsonImpl := fromJsonImpl
    toJsonImpl := toJsonImpl
    dependencies := allDependencies.reverse
    extraDocComment := extraDocComment
  }

def parseInlineAbbrev (s : JsonSchema.Schema) (name : String) : SchemaGen TypeDefinition :=
  parseInline s <&> mkAbbrevTypeDefinition s name

end JsonSchemaCodeGen
