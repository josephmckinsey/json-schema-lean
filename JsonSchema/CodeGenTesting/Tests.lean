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

def testStructWithOptionalSum : JsonSchema.Schema := .Object {
  type := #[.ObjectType]
  required := some #["id"]
  properties := some #[
    ("id", .Object { type := #[.IntegerType] }),
    ("value", .Object { type := #[.StringType, .NumberType] })
  ]
}

def testNestedStructSchema : JsonSchema.Schema := .Object {
  type := #[.ObjectType]
  required := some #["name", "address"]
  properties := some #[
    ("name", .Object { type := #[.StringType] }),
    ("address", .Object {
      type := #[.ObjectType]
      required := some #["street", "city"]
      properties := some #[
        ("street", .Object { type := #[.StringType] }),
        ("city", .Object { type := #[.StringType] }),
        ("zipCode", .Object { type := #[.StringType] })
      ]
    })
  ]
}

def testAllOptionalFields : JsonSchema.Schema := .Object {
  type := #[.ObjectType]
  properties := some #[
    ("field1", .Object { type := #[.StringType] }),
    ("field2", .Object { type := #[.IntegerType] })
  ]
}

def structureTests : TestM Unit := testFunction "structureTests" do
  testEq "Person" (schemaToString testPersonSchema "Person")
    r#"structure Person where
  name : String
  age : Int
  email : Option String"#

  testEq "Struct with optional sum type" (schemaToString testStructWithOptionalSum "Record")
    r#"structure Record where
  id : Int
  value : Option (String ⊕ Float)"#

  testEq "Nested struct" (schemaToString testNestedStructSchema "Person")
    r#"structure PersonAddress where
  street : String
  city : String
  zipCode : Option String

structure Person where
  name : String
  address : PersonAddress"#

  testEq "All optional fields" (schemaToString testAllOptionalFields "OptionalData")
    r#"structure OptionalData where
  field1 : Option String
  field2 : Option Int"#

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

def constantTests : TestM Unit := testFunction "constant tests" do
  testEq "getConstantFromJsonTerm null"
    ((getConstantFromJsonTerm .null).pretty (width := 80))
    "if j == Json.null then\n  Except.ok ()\nelse\n  Except.error \"Could not match constant Json.null\""
  testEq "getConstantToJsonTerm null"
    ((getConstantToJsonTerm .null).pretty)
    "Json.null"

def depthTests : TestM Unit := testFunction "depth tests" do
  testEq "depthToInlInr"
    ((Std.Format.nestD (.group (depthToInlInr "hi" 2 1))).pretty)
    ".inr (hi)"

def fromJsonListSumTests : TestM Unit := testFunction "fromJson list sum tests" do
  testEq "getFromJsonListSum NumberType IntegerType"
    ((getFromJsonListSum [.NumberType, .IntegerType]).pretty)
    "(fun x => .inl x) <$> ((inferInstance : FromJson Float).fromJson? j) <|>\n(fun x => .inr (x)) <$> ((inferInstance : FromJson Int).fromJson? j)"

def parseSimpleTypeTests : TestM Unit := testFunction "parseSimpleType tests" do
  testEq "parseSimpleType with null, string, int"
    (((parseSimpleType { type := #[.NullType, .StringType, .IntegerType] }).toOption.get!.toJsonImpl.get!).pretty)
    "@Option.toJson\n_\n⟨fun x => match x with\n| .inl x => toJson x\n| .inr (x) => toJson x⟩\nx"

def descriptionTests : TestM Unit := testFunction "description tests" do
  let simpleSchemaWithDesc : JsonSchema.Schema := .Object {
    type := #[.StringType]
    description := some "A simple string type"
  }
  testEq "Simple type with description"
    (schemaToString simpleSchemaWithDesc "MyString")
    "/-- A simple string type -/\nabbrev MyString := String"

#eval TestM.run do
  simpleTest
  structureTests
  constantTests
  depthTests
  fromJsonListSumTests
  parseSimpleTypeTests
  descriptionTests
  printSummary

def hmm := Option (String ⊕ Int)

end Test

end FormatTests
