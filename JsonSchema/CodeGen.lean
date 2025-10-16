import JsonSchema.Schema
import JsonSchema.Validation
import UriTesting.Helpers

import Lean

open Lean Elab Command Term Meta

/-
## Design Goals

### Overall Rules

- Anything that validates the JSON schema should parse correctly with FromJson
- Serialized ToJson should always pass validation
- There should be a bijective Json objects that pass and the type.

This will be a best-effort only.

### Weird Things

- weird names
- nested types that should be inlined or split apart
- weird types like an array with maxItems=minItems that should become a tuple

### Output Requirements

- You should be able to put things in different files.
- You need to normalize names so they don't suck.
- Eventually, we will want to deal with self-referencing types, and definitions should be topologically sorted.
- Descriptions turn into comments

## Implementation Strategy

Using Format-based approach
https://lean-lang.org/doc/reference/latest/Interacting-with-Lean/#Format

1. Build Format objects with proper comments and newlines
2. Render Format to string with .pretty

This avoids hygiene issues and makes it easy to add comments/formatting.
-/

namespace CodeGen

/-- Default name sanitization: replace invalid characters, handle keywords -/
def defaultSanitizeName (name : String) : String :=
  -- Replace < with "Of" and > with "" to get A<T> → AOfT
  let withOf := name.replace "<" "Of" |>.replace ">" ""
  let cleaned := withOf.toList.map fun c =>
    if c.isAlphanum then c
    else if c == '_' then c
    else '_'
  let result := String.mk cleaned
  -- Basic keyword avoidance (add more as needed)
  if ["def", "theorem", "structure", "inductive", "where", "match", "if", "then", "else"].contains result
  then result ++ "_"
  else if result.isEmpty || result.front.isDigit
  then "t_" ++ result  -- Prepend if starts with digit or empty
  else result

/-- Configuration for code generation -/
structure Config where
  /-- How to sanitize names to valid Lean identifiers -/
  sanitizeName : String → String := defaultSanitizeName
  /-- Indentation string -/
  indent : String := "  "

/-- Capitalize first letter -/
def capitalize (s : String) : String :=
  if s.isEmpty then s
  else s.take 1 |>.toUpper ++ s.drop 1

/-- Create a doc comment from a description -/
def mkDocComment (desc : String) : Format :=
  .text s!"/-- {desc} -/"

/-- Get the Lean type name for a single JsonType -/
def jsonTypeToLean : JsonSchema.JsonType → String
  | .StringType => "String"
  | .IntegerType => "Int"
  | .NumberType => "Float"
  | .BooleanType => "Bool"
  | .NullType => "Unit"
  | .ObjectType => "Json"  -- Generic fallback
  | .ArrayType => "Array Json"  -- Generic fallback
  | .AnyType => "Json"

/-- Extract type name from a schema (from title or ref) -/
def extractTypeName? (s : JsonSchema.Schema) : Option String :=
  match s with
  | .Boolean _ => none
  | .Object obj =>
    obj.title <|> (obj.ref >>= fun ref =>
      match ref with
      | .inr relRef =>
        -- Extract last component from #/definitions/TypeName
        let parts := relRef.fragment.getD "" |>.splitOn "/"
        parts.getLast?
      | .inl _ => none
    )

/-- Determine if a schema represents an optional type (has null in types) -/
def hasNullType (types : Array JsonSchema.JsonType) : Bool :=
  types.contains .NullType

/-- Get non-null types from type array -/
def nonNullTypes (types : Array JsonSchema.JsonType) : Array JsonSchema.JsonType :=
  types.filter (· != .NullType)




def getBoolType (b : Bool) : String :=
  if b then "Unit" else "Empty"

def isSimple (o : JsonSchema.SchemaObject) : Except String Unit := do
  if o.const.isSome then return -- constants are always simple
  if o.ref.isSome then return -- Refs are always simple
  if o.allOf.isSome then .error "allOf is not simple"
  if o.anyOf.isSome then .error "anyOf is not simple"
  if o.oneOf.isSome then .error "oneOf is not simple"
  if o.type.contains .ObjectType then .error "object type possible"
  -- These don't necessary make a type complex, but it
  -- probably should be a struct or inductive if these exist.
  if o.contains.isSome then .error "contains is not simple"
  if o.not.isSome then .error "not is not simple"
  if o.ifSchema.isSome then .error "if is not simple"
  if o.thenSchema.isSome then .error "then is not simple"
  if o.elseSchema.isSome then .error "else is not simple"
  if o.dependencies.isSome then .error "dependencies is not simple"
  -- These can't reay be inlined if they exist
  if o.enum.isSome then .error "enum is not simple"
  if o.pattern.isSome then .error "pattern is not simple"


partial def jsonRepr (j : Json) (_ : Nat) : Format :=
  let subRepr : Repr Json := ⟨jsonRepr⟩
  match j with
  | .arr x => Format.nest 2  <| .text "Lean.Json.arr <|" ++ .line ++
    (@repr _ (@Array.instRepr _ subRepr) x)
  | .obj kvPairs => Format.nest 2 <| .text "Lean.Json.obj <|" ++ .line ++
    (@repr _ (@Std.TreeMap.Raw.instRepr _ _ _ _ subRepr) kvPairs)
  | .str s => Format.nest 2 <| "Lean.Json.str <|" ++ .line ++ repr s
  | .num n => Format.nest 2 <| "Lean.Json.num <|" ++ .line ++ repr n
  | .null => "Lean.Json.null"
  | .bool b => Format.nest 2 <| "Lean.Json.bool " ++ repr b

local instance : Repr Json := ⟨jsonRepr⟩

#eval Json.mkObj [("what", .null)]

def parseConstant (o : JsonSchema.SchemaObject) :
    Except String (String × Format) := do
  match o.const with
  | some c => .ok ("Unit", repr c)
  | none => .error "Could not find constant"

def parseRef (o : JsonSchema.SchemaObject) : Except String String :=
  match o.ref with
  | some _ => .ok "NotImplemented"
  | none => .error "Could not find ref"

def parseAnyType (types : Array JsonSchema.JsonType) : Except String String :=
  if types.contains .AnyType then .ok "Json" else .error "Could not find any type"

def parseSimpleType (o : JsonSchema.SchemaObject) : Except String String :=
  parseAnyType o.type <|>
  match (o.type.mergeSort (le := fun x y => (compare x y).isLE)).toList with
  | [x] => .ok (jsonTypeToLean x)
  | [.NullType, x] => .ok ("Option " ++ jsonTypeToLean x)
  | [] => .error "Type list is empty"
  | .NullType::xs =>
    .ok ("Option (" ++ (String.intercalate " ⊕ " (xs.map jsonTypeToLean)))
  | xs => .ok (String.intercalate " ⊕ " (xs.map jsonTypeToLean))

/-- Inline types such as String ⊕ Int do not need complicated definitions.
-/
def parseInline (s : JsonSchema.Schema) : Except String Format :=
  match s with
  | .Boolean b => pure (getBoolType b)
  | .Object o => do
  isSimple o
  parseRef o <|>
  (parseConstant o <&> Prod.fst) <|>
  parseSimpleType o

def parseInlineAbbrev (s : JsonSchema.Schema) (name : String) : Except String Format :=
  parseInline s <&> fun form =>
    .group <| .nest 2 (f!"abbrev {name} :=" ++ .line ++ form)


/-- Main schema to format conversion -/
def schemaToFormat (s : JsonSchema.Schema) (typeName : String)
    (config : Config := {}) : Except String Format := do
  -- We are going to ignore refs for now, which we will fill in
  -- by providing all the name ahead of time in the config,
  -- and then parsing in the correct order (+ mutual types)
  /- test -/
  let name := config.sanitizeName typeName
  parseInlineAbbrev s name

/-- Main function to convert a Schema to String (not Format, to simplify) -/
def schemaToString (s : JsonSchema.Schema) (typeName : String) : String :=
  match schemaToFormat s typeName with
  | .ok s => s.pretty
  | .error e => e

end CodeGen

-- Test the new Format-based code generation
section FormatTests

open CodeGen

def testPersonSchema : JsonSchema.Schema := .Object {
  type := #[.ObjectType]
  required := some #["name", "age"]
  properties := some #[
    ("name", .Object { type := #[.StringType] }),
    ("age", .Object { type := #[.IntegerType] }),
    ("email", .Object { type := #[.StringType] })
  ]
}

def testUnionSchema : JsonSchema.Schema := JsonSchema.Schema.Object {
  oneOf := some #[
    JsonSchema.Schema.Object { type := #[.StringType] },
    JsonSchema.Schema.Object { type := #[.IntegerType] }
  ]
}

def testAnyOfSchema : JsonSchema.Schema := JsonSchema.Schema.Object {
  anyOf := some #[
    JsonSchema.Schema.Object { type := #[.StringType] },
    JsonSchema.Schema.Object { type := #[.IntegerType] }
  ]
}

def testNullableSchema : JsonSchema.Schema := JsonSchema.Schema.Object {
  type := #[.StringType, .NullType]
}

def testNestedUnionSchema : JsonSchema.Schema := .Object {
  type := #[.ObjectType]
  description := some "Could be worse"
  required := some #["name", "age"]
  properties := some #[
    ("name", .Object { type := #[.StringType], description := some "Could be better"}),
    ("age", testAnyOfSchema),
  ]
}

def testNestedUnionString := r#"/-- Could be worse -/
structure NestedUnion where
  /-- Could be better -/
  name : String
  age : String ⊕ Int"#

def testEnum : JsonSchema.Schema := .Object {
  enum := some #[Json.str "hello", Json.str "hi", Json.obj (.ofList [("oh_boy", Json.str "nope")])]
}

def testEnumString := r#"inductive TestEnum where
  | hello
  | hi
  | oh_boy_nope"#

def testRef : JsonSchema.Schema := .Object {
  ref := (LeanUri.parseReference "#/definitions/A<T>").toOption
  definitions := some (.ofList [
    ("A<T>", testEnum)
  ])
}
-- Use of name sanitizer for references. A<T> turns into AofT
def testRefString := r#"inductive AOfT where
  | hello
  | hi
  | oh_boy_nope

abbrev TestReference := AofT"#

namespace Test

open Testing

def testIt : TestM Unit := testFunction "basic tests" do
  testEq "Person" (schemaToString testPersonSchema "Person")
    r#"structure Person where
  name : String
  age : Int
  email : Option String"#
  testEq "StringOrInt" (schemaToString testUnionSchema "StringOrInt")
    r#"inductive StringOrInt where
  | case0 : String → StringOrInt
  | case1 : Int → StringOrInt"#
  testEq "NullableString" (schemaToString testNullableSchema "NullableString")
    r#"abbrev NullableString := Option String"#
  testEq "NestedUnion" (schemaToString testNestedUnionSchema "NestedUnion")
    testNestedUnionString
  testEq "Enum" (schemaToString testEnum "TestEnum") testEnumString
  testEq "Ref" (schemaToString testRef "TestReference") testRefString

#eval TestM.run do
  testIt
  printSummary

end Test

end FormatTests
