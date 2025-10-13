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

def schemaToFormat (s : JsonSchema.Schema) (typeName : String) : Format :=
  .nil

/-- Main function to convert a Schema to String (not Format, to simplify) -/
def schemaToString (s : JsonSchema.Schema) (typeName : String) : String :=
  (schemaToFormat s typeName).pretty

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

abbrev TestReference := A"#

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
