import JsonSchemaCodeGen
import JsonSchema.Resolving
import JsonSchemaCodeGenTesting.TestUtils
import UriTesting.Helpers

-- Test integrated code generation with references

section IntegrationTests

open JsonSchemaCodeGen
open JsonSchemaCodeGenTesting
open JsonSchema
open Lean

namespace Test

open Testing

-- Test 1: Simple schema with no references
def simpleIntegrationTest : TestM Unit := testFunction "Simple schema generation" do
  let schema : Schema := .Object {
    type := #[.StringType]
    title := some "UserName"
  }
  let resolver := Resolver.empty.addSchema schema (testURI "/user.json")

  match generateAllSchemas resolver with
  | .ok output =>
      test "Generated code contains type" (output.containsSubstr "UserName")
      test "Generated code contains String" (output.containsSubstr "String")
  | .error e =>
      test s!"Generation failed: {e}" false

-- Test 2: Schema with definitions (acyclic)
def definitionsIntegrationTest : TestM Unit := testFunction "Schema with definitions" do
  let schema : Schema := .Object {
    -- Root schema is just a definition container (no type)
    definitions := some (.ofList [
      ("Address", Schema.Object {
        type := #[.ObjectType]
        properties := some #[
          ("street", Schema.Object { type := #[.StringType] })
        ]
      }),
      ("Person", Schema.Object {
        type := #[.ObjectType]
        properties := some #[
          ("name", Schema.Object { type := #[.StringType] }),
          ("address", Schema.Object {
            ref := some (.inr {
              authority := none
              path := ""
              query := none
              fragment := some "/definitions/Address"
            })
          })
        ]
      })
    ])
  }
  let resolver := Resolver.empty.addSchema schema (testURI "/person.json")
  let config : Config := { generateInstances := true }

  match generateAllSchemas resolver config with
  | .ok output =>
      test "Generated code contains PersonAddress" (output.containsSubstr "PersonAddress")
      test "Generated code contains PersonPerson" (output.containsSubstr "PersonPerson")
      -- Address should come before Person (topological order)
      -- Use indexOf to find position in string
      match output.splitOn "PersonAddress", output.splitOn "PersonPerson" with
      | addrParts, personParts =>
          if addrParts.length > 1 && personParts.length > 1 then
            -- Both found; compare positions by checking first parts
            test "Address defined before Person" (addrParts.head!.length < personParts.head!.length)
          else
            test "Both types found in output" false
  | .error e =>
      test s!"Generation failed: {e}" false

-- Test 3: Circular reference (mutual block)
def circularRefTest : TestM Unit := testFunction "Circular references" do
  let schema : Schema := .Object {
    -- Root schema is just a definition container (no type)
    definitions := some (.ofList [
      ("Node", Schema.Object {
        type := #[.ObjectType]
        properties := some #[
          ("value", Schema.Object { type := #[.IntegerType] }),
          ("next", Schema.Object {
            ref := some (mkRef "#/definitions/Node")
          })
        ]
      })
    ])
  }
  let resolver := Resolver.empty.addSchema schema (testURI "/node.json")
  let config : Config := { generateInstances := true }

  match generateAllSchemas resolver config with
  | .ok output =>
      -- Self-referencing schema should still be standalone (SCC of size 1)
      test "Generated code contains NodeNode" (output.containsSubstr "NodeNode")
      test "Generated code contains structure" (output.containsSubstr "structure")
  | .error e =>
      test s!"Generation failed: {e}" false

-- Test 4: Two mutually recursive types
def mutualRecursionTest : TestM Unit := testFunction "Mutual recursion" do
  let schema : Schema := .Object {
    -- Root schema is just a definition container (no type)
    definitions := some (.ofList [
      ("A", Schema.Object {
        type := #[.ObjectType]
        properties := some #[
          ("b", Schema.Object {
            ref := some (mkRef "#/definitions/B")
          })
        ]
      }),
      ("B", Schema.Object {
        type := #[.ObjectType]
        properties := some #[
          ("a", Schema.Object {
            ref := some (mkRef "#/definitions/A")
          })
        ]
      })
    ])
  }
  let resolver := Resolver.empty.addSchema schema (testURI "/mutual.json")
  let config : Config := { generateInstances := true }

  match generateAllSchemas resolver config with
  | .ok output =>
      test "Generated code contains mutual" (output.containsSubstr "mutual")
      test "Generated code contains end" (output.containsSubstr "end")
      test "Generated code contains MutualA" (output.containsSubstr "MutualA")
      test "Generated code contains MutualB" (output.containsSubstr "MutualB")
  | .error e =>
      test s!"Generation failed: {e}" false

def allIntegrationTests : TestM Unit := group "Integration Tests" do
  simpleIntegrationTest
  definitionsIntegrationTest
  circularRefTest
  mutualRecursionTest

end Test
end IntegrationTests
