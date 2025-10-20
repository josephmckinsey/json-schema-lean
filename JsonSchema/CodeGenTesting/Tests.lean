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

def testNestedUnionString := r#"inductive NestedUnionAge where | case0 (val : String) | case1 (val : Int)

/-- Could be worse -/
structure NestedUnion where
  /-- Could be better -/
  name : String
  age : NestedUnionAge"#

def testEnum : JsonSchema.Schema := .Object {
  enum := some #[Json.str "hello", Json.str "hi", Json.obj (.ofList [("oh_boy", Json.str "nope")])]
}

def testEnumString := "inductive TestEnum where | hello | hi | oh_boy"

def testRef : JsonSchema.Schema := .Object {
  ref := (LeanUri.parseReference "#/definitions/A<T>").toOption
  definitions := some (.ofList [
    ("A<T>", testEnum)
  ])
}
-- Use of name sanitizer for references. A<T> turns into AofT
def testRefString := "inductive AOfT where | hello | hi | oh_boy\n\nabbrev TestReference := AofT"

namespace Test

open Testing

def simpleTest : TestM Unit := testFunction "abbreviation tests" do
  testEq "NullableString" (schemaToString testNullableSchema "NullableString")
    r#"abbrev NullableString := Option String"#
  testEq "SimpleSum" (schemaToString testSimpleSum "SimpleSum")
    r#"abbrev SimpleSum := String ⊕ Float ⊕ Int"#
  testEq "NullableSimpleSum" (schemaToString testNullableSum "NullableSimpleSum")
    r#"abbrev NullableSimpleSum := Option (String ⊕ Int)"#

  -- Test inlined anyOf (should create an abbreviation, not an inductive)
  testEq "Inlined anyOf" (schemaToString testAnyOfSchema "StringOrInt")
    r#"abbrev StringOrInt := String ⊕ Int"#

  -- Test inlined oneOf (should create an abbreviation, not an inductive)
  testEq "Inlined oneOf" (schemaToString testUnionSchema "StringOrInt")
    r#"abbrev StringOrInt := String ⊕ Int"#

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

  -- Test structure with inlined anyOf field (should inline as String ⊕ Int, not generate separate type)
  let testStructWithInlinedAnyOf : JsonSchema.Schema := .Object {
    type := #[.ObjectType]
    required := some #["cornerRadius"]
    properties := some #[
      ("cornerRadius", .Object {
        anyOf := some #[
          .Object { type := #[.NumberType] },
          .Object { type := #[.StringType] }
        ]
      })
    ]
  }
  testEq "Struct with inlined anyOf field" (schemaToString testStructWithInlinedAnyOf "Layout")
    r#"structure Layout where
  cornerRadius : Float ⊕ String"#

def inductiveTests : TestM Unit := testFunction "inductiveTests" do
  testEq "Enum" (schemaToString testEnum "TestEnum") testEnumString
  -- oneOf/anyOf now inline as abbreviations when all variants are simple
  testEq "StringOrInt" (schemaToString testUnionSchema "StringOrInt")
    "abbrev StringOrInt := String ⊕ Int"
  -- Nested anyOf field now inlines
  testEq "NestedUnion" (schemaToString testNestedUnionSchema "NestedUnion")
    r#"/-- Could be worse -/
structure NestedUnion where
  /-- Could be better -/
  name : String
  age : String ⊕ Int"#

  -- Tests from Inductives.lean
  let testEnumSimple : Array Json := #[.str "hello", .str "hi"]
  testEq "Simple enum type decl"
    ((enumToInductive testEnumSimple "TestEnum").toOption.get!.typeDecl.pretty)
    "inductive TestEnum where | hello | hi"

  let testEnumWithObject : Array Json :=
    #[.str "hello", .str "hi", .mkObj [("oh_boy", Json.str "nope")]]
  testEq "Enum with object - compact"
    ((enumToInductive testEnumWithObject "TestEnum").toOption.get!.typeDecl.pretty)
    "inductive TestEnum where | hello | hi | oh_boy"

  testEq "Enum with object - expanded"
    ((enumToInductive testEnumWithObject "TestEnum").toOption.get!.typeDecl.pretty (width := 0))
    "inductive TestEnum where\n  | hello\n  | hi\n  | oh_boy"

  let testOneOfSimple : Array JsonSchema.Schema := #[
    .Object { type := #[.StringType] },
    .Object { type := #[.IntegerType] }
  ]
  testEq "Simple oneOf type decl"
    ((oneOfToInductive testOneOfSimple "StringOrInt" (fun _ _ => .error "uh oh")).toOption.get!.typeDecl.pretty)
    "inductive StringOrInt where | case0 (val : String) | case1 (val : Int)"

  testEq "Enum FromJson instance"
    ((enumToInductive testEnumSimple "TestEnum").toOption.get!.fromJsonImpl.get!.pretty)
    r#"instance : FromJson TestEnum where
  fromJson? j := match j with
    | Json.str "hello" => .ok .hello
    | Json.str "hi" => .ok .hi
    | _ => .error s!"Invalid enum value: {j}""#

  testEq "Enum ToJson instance"
    ((enumToInductive testEnumSimple "TestEnum").toOption.get!.toJsonImpl.get!.pretty)
    r#"instance : ToJson TestEnum where
  toJson x := match x with
    | .hello => Json.str "hello"
    | .hi => Json.str "hi""#

def oneOfFromJsonToJsonTests : TestM Unit := testFunction "oneOf FromJson/ToJson tests" do
  -- Test FromJson instance generation for oneOf with simple types
  testEq "oneOf FromJson instance"
    ((oneOfToInductive
      #[.Object { type := #[.StringType] }, .Object { type := #[.IntegerType] }]
      "StringOrInt"
      (fun _ _ => Except.error "uh oh")
      {}).toOption.get!.fromJsonImpl.get!.pretty)
    r#"instance : FromJson StringOrInt where
  fromJson? j :=
    .case0 <$> fromJson? j <|>
      .case1 <$> fromJson? j"#

  -- Test ToJson instance generation for oneOf with simple types
  testEq "oneOf ToJson instance"
    ((oneOfToInductive
      #[.Object { type := #[.StringType] }, .Object { type := #[.IntegerType] }]
      "StringOrInt"
      (fun _ _ => Except.error "uh oh")
      {}).toOption.get!.toJsonImpl.get!.pretty)
    r#"instance : ToJson StringOrInt where
  toJson x := match x with
    | .case0 val => toJson val
    | .case1 val => toJson val"#

  -- Test oneOf with a sum type variant (String ⊕ Int)
  -- Bool has no custom impl, but String ⊕ Int does
  testEq "oneOf with sum type variant - FromJson"
    ((oneOfToInductive
      #[.Object { type := #[.BooleanType] },
        .Object { type := #[.StringType, .IntegerType] }]
      "BoolOrStringOrInt"
      (fun _ _ => Except.error "uh oh")
      {}).toOption.get!.fromJsonImpl.get!.pretty)
    r#"instance : FromJson BoolOrStringOrInt where
  fromJson? j :=
    .case0 <$> fromJson? j <|>
      .case1 <$> ((fun x => .inl x) <$> ((inferInstance : FromJson String).fromJson? j) <|>
      (fun x => .inr (x)) <$> ((inferInstance : FromJson Int).fromJson? j))"#

  testEq "oneOf with sum type variant - ToJson"
    ((oneOfToInductive
      #[.Object { type := #[.BooleanType] },
        .Object { type := #[.StringType, .IntegerType] }]
      "BoolOrStringOrInt"
      (fun _ _ => Except.error "uh oh")
      {}).toOption.get!.toJsonImpl.get!.pretty)
    r#"instance : ToJson BoolOrStringOrInt where
  toJson x := match x with
    | .case0 val => toJson val
    | .case1 x => match x with
    | .inl x => toJson x
    | .inr (x) => toJson x"#

def oneOfVariantTests : TestM Unit := testFunction "oneOf variant doc comments and custom parsers" do
  -- Test oneOf with variant descriptions
  let testOneOfWithDesc : Array JsonSchema.Schema := #[
    .Object { type := #[.StringType], description := some "A string variant" },
    .Object { type := #[.IntegerType], description := some "An integer variant" }
  ]
  let result := (oneOfToInductive testOneOfWithDesc "MyUnion" (fun _ _ => .error "uh oh") {}).toOption.get!

  testEq "oneOf with variant descriptions - type decl"
    (result.typeDecl.pretty (width := 0))
    r#"inductive MyUnion where
  /-- A string variant -/
  | case0 (val : String)
  /-- An integer variant -/
  | case1 (val : Int)"#

  -- Test oneOf with object variants containing sum type fields
  let dummyResolver : JsonSchema.Schema → String → Except String TypeDefinition := fun _ _ => .error "not used"
  let testOneOfWithSumFields : Array JsonSchema.Schema := #[
    .Object {
      type := #[.ObjectType]
      description := some "A person record"
      required := some #["name", "age"]
      properties := some #[
        ("name", .Object { type := #[.StringType] }),
        ("age", .Object { type := #[.IntegerType, .StringType] })  -- sum type field
      ]
    },
    .Object {
      type := #[.ObjectType]
      description := some "A simple record"
      required := some #["value"]
      properties := some #[
        ("value", .Object { type := #[.NumberType, .StringType] })  -- sum type field
      ]
    }
  ]

  let result2 := (oneOfToInductive testOneOfWithSumFields "Record" dummyResolver {}).toOption.get!

  -- Check that constructor has doc comments
  testEq "oneOf object variants with descriptions"
    (result2.typeDecl.pretty.containsSubstr "/-- A person record -/")
    true
  testEq "oneOf object variants with descriptions 2"
    (result2.typeDecl.pretty.containsSubstr "/-- A simple record -/")
    true

  -- Check that FromJson uses custom parsers for sum type fields
  let fromJsonStr := result2.fromJsonImpl.get!.pretty
  testEq "oneOf object with sum field uses custom FromJson"
    (fromJsonStr.containsSubstr "let j := j.getD \"age\" .null; (fun x => .inl x) <$>")
    true
  testEq "oneOf object with sum field uses custom FromJson 2"
    (fromJsonStr.containsSubstr "(inferInstance : FromJson String).fromJson? j")
    true

  -- Check that ToJson uses custom serializers for sum type fields
  let toJsonStr := result2.toJsonImpl.get!.pretty
  testEq "oneOf object with sum field uses custom ToJson"
    (toJsonStr.containsSubstr "let x := age; match x with")
    true

  -- Test that field extraDocComments are propagated to variant docstrings
  let testOneOfWithFieldExtraDocs : Array JsonSchema.Schema := #[
    .Object {
      type := #[.ObjectType]
      description := some "Variant with docs"
      required := some #["id"]
      properties := some #[
        ("id", .Object {
          anyOf := some #[
            .Object { type := #[.IntegerType], description := some "Numeric ID" },
            .Object { type := #[.StringType], description := some "String UUID" }
          ]
        })
      ]
    }
  ]
  let result3 := (oneOfToInductive testOneOfWithFieldExtraDocs "MyVariant" dummyResolver {}).toOption.get!
  let docStr := result3.typeDecl.pretty

  -- Check that variant description is included
  testEq "oneOf variant with field extraDocComment - variant desc"
    (docStr.containsSubstr "Variant with docs")
    true

  -- Check that field anyOf descriptions are combined into variant docstring
  testEq "oneOf variant with field extraDocComment - field desc 1"
    (docStr.containsSubstr "Numeric ID")
    true

  testEq "oneOf variant with field extraDocComment - field desc 2"
    (docStr.containsSubstr "String UUID")
    true

def structInstanceTests : TestM Unit := testFunction "structure FromJson/ToJson tests" do
  -- Test simple structure with generateInstances
  testEq "Simple struct with instances"
    (schemaToString testPersonSchema "Person" { generateInstances := true })
    r#"structure Person where
  name : String
  age : Int
  email : Option String

instance : FromJson Person where
  fromJson? j := do
    name ← fromJson? (j.getD "name" .null)
    age ← fromJson? (j.getD "age" .null)
    email ← fromJson? (j.getD "email" .null)
    .ok { name, age, email }

instance : ToJson Person where
  toJson s := Json.mkObj [("name", toJson s.name), ("age", toJson s.age), ("email", toJson s.email)]"#

  -- Test structure with optional sum type field
  testEq "Struct with optional sum type and instances"
    (schemaToString testStructWithOptionalSum "Record" { generateInstances := true })
    r#"structure Record where
  id : Int
  value : Option (String ⊕ Float)

instance : FromJson Record where
  fromJson? j := do
    id ← fromJson? (j.getD "id" .null)
    value ← let j := j.getD "value" .null; Option.fromJson?
    ((fun x => .inl x) <$> ((inferInstance : FromJson String).fromJson? j) <|>
     (fun x => .inr (x)) <$> ((inferInstance : FromJson Float).fromJson? j))
    .ok { id, value }

instance : ToJson Record where
  toJson s := Json.mkObj [("id", toJson s.id), ("value", let x := s.value; @Option.toJson
    _
    ⟨fun x => match x with
    | .inl x => toJson x
    | .inr (x) => toJson x⟩
    x)]"#

  -- Test that nested structures generate instances for both types
  let nestedResult := schemaToString testNestedStructSchema "Person" { generateInstances := true }
  -- Should contain both PersonAddress and Person instances
  testEq "Nested struct has PersonAddress FromJson"
    (nestedResult.containsSubstr "instance : FromJson PersonAddress where")
    true
  testEq "Nested struct has PersonAddress ToJson"
    (nestedResult.containsSubstr "instance : ToJson PersonAddress where")
    true
  testEq "Nested struct has Person FromJson"
    (nestedResult.containsSubstr "instance : FromJson Person where")
    true
  testEq "Nested struct has Person ToJson"
    (nestedResult.containsSubstr "instance : ToJson Person where")
    true

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

-- Test that generated code actually compiles and works
-- This inductive type was generated from oneOf schema
inductive TestStringOrInt where
  | case0 (val : String)
  | case1 (val : Int)

instance : FromJson TestStringOrInt where
  fromJson? j :=
    .case0 <$> fromJson? j <|>
      .case1 <$> fromJson? j

instance : ToJson TestStringOrInt where
  toJson x := match x with
    | .case0 val => toJson val
    | .case1 val => toJson val

def generatedCodeTests : TestM Unit := testFunction "generated code compilation tests" do
  -- Test that parsing works correctly
  let stringParse : Except String TestStringOrInt := fromJson? (Json.str "hello")
  let intParse : Except String TestStringOrInt := fromJson? (Json.num 42)

  testEq "Parse string to case0"
    (match stringParse with | .ok (.case0 s) => s | _ => "failed")
    "hello"

  testEq "Parse int to case1"
    (match intParse with | .ok (.case1 i) => i | _ => 0)
    42

  -- Test that serialization works correctly
  testEq "Serialize case0 to bare string"
    (toJson (TestStringOrInt.case0 "world"))
    (Json.str "world")

  testEq "Serialize case1 to bare number"
    (toJson (TestStringOrInt.case1 123))
    (Json.num 123)

#eval TestM.run do
  simpleTest
  structureTests
  structInstanceTests
  inductiveTests
  oneOfFromJsonToJsonTests
  oneOfVariantTests
  generatedCodeTests
  constantTests
  depthTests
  fromJsonListSumTests
  parseSimpleTypeTests
  descriptionTests
  printSummary

def hmm := Option (String ⊕ Int)

end Test

end FormatTests
