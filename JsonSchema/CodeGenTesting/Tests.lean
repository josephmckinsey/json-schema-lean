import JsonSchema.CodeGen
import UriTesting.Helpers

-- Test the new Format-based code generation
section FormatTests

open JsonSchema.CodeGen
open Lean

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

def testSimpleSum : JsonSchema.Schema := JsonSchema.Schema.Object {
  type := #[.StringType, .IntegerType, .NumberType]
}

def testNullableSum : JsonSchema.Schema := JsonSchema.Schema.Object {
  type := #[.StringType, .IntegerType, .NullType]
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

def simpleTest : TestM Unit := testFunction "abbreviation tests" do
  testEq "NullableString" (schemaToString testNullableSchema "NullableString")
    r#"abbrev NullableString := Option String"#
  testEq "SimpleSum" (schemaToString testSimpleSum "SimpleSum")
    r#"abbrev SimpleSum := String ⊕ Float ⊕ Int"#
  testEq "NullableSimpleSum" (schemaToString testNullableSum "NullableSimpleSum")
    r#"abbrev NullableSimpleSum := Option (String ⊕ Int)"#

def structureTests : TestM Unit := testFunction "structureTests" do
  testEq "Person" (schemaToString testPersonSchema "Person")
    r#"structure Person where
  name : String
  age : Int
  email : Option String"#

def inductiveTests : TestM Unit := testFunction "structureTests" do
  testEq "Enum" (schemaToString testEnum "TestEnum") testEnumString
  testEq "StringOrInt" (schemaToString testUnionSchema "StringOrInt")
    r#"inductive StringOrInt where
  | case0 : String → StringOrInt
  | case1 : Int → StringOrInt"#
  testEq "NestedUnion" (schemaToString testNestedUnionSchema "NestedUnion")
    testNestedUnionString

def otherTests : TestM Unit := testFunction "other tests" do
  testEq "Ref" (schemaToString testRef "TestReference") testRefString

#eval TestM.run do
  simpleTest
  printSummary

def hmm := Option (String ⊕ Int)

end Test

end FormatTests
