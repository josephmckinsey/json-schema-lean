import JsonSchema.CodeGen.References
import JsonSchema.Resolving
import UriTesting.Helpers

-- Test reference resolution and name generation
section ReferencesTests

open JsonSchema.CodeGen
open JsonSchema
open Lean

-- Helper to create a simple URI for testing
def testURI (path : String) : LeanUri.URI :=
  LeanUri.URI.mk "http" (some "example.com") path none none

-- Test schemas
def simpleSchema : Schema := .Object {
  type := #[.StringType]
  title := some "Simple"
}

def schemaWithDefinitions : Schema := .Object {
  type := #[.ObjectType]
  definitions := some (.ofList [
    ("Address", Schema.Object { type := #[.StringType] }),
    ("Person", Schema.Object {
      type := #[.ObjectType]
      definitions := some (.ofList [
        ("ContactInfo", Schema.Object { type := #[.StringType] })
      ])
    })
  ])
}

def schemaWithCollision : Schema := .Object {
  type := #[.ObjectType]
  definitions := some (.ofList [
    ("User", Schema.Object { type := #[.StringType] }),
    ("user", Schema.Object { type := #[.IntegerType] })  -- Will collide after sanitization
  ])
}

namespace Test

open Testing

def extractBaseFromURITests : TestM Unit := testFunction "extractBaseFromURI tests" do
  testEq "Extract from user.json"
    (extractBaseFromURI (testURI "/schemas/user.json"))
    "User"

  testEq "Extract from path with no extension"
    (extractBaseFromURI (testURI "/api/person"))
    "Person"

  testEq "Extract from root"
    (extractBaseFromURI (testURI "/"))
    "Schema"

  testEq "Extract from dotfile"
    (extractBaseFromURI (testURI "/.config"))
    ".config"

  testEq "Extract from empty path"
    (extractBaseFromURI (LeanUri.URI.mk "" none "" none none))
    "Schema"

def extractSmartNameTests : TestM Unit := testFunction "extractSmartName tests" do
  let config : Config := {}

  testEq "Root schema (empty path)"
    (extractSmartName (testURI "/schemas/user.json") [] config)
    "User"

  testEq "Definition Address"
    (extractSmartName (testURI "/schemas/user.json") ["definitions", "Address"] config)
    "UserAddress"

  testEq "Nested definition"
    (extractSmartName (testURI "/schemas/user.json") ["definitions", "Person", "definitions", "ContactInfo"] config)
    "UserPersonContactInfo"

  testEq "Filter out generic segments"
    (extractSmartName (testURI "/api.json") ["properties", "items", "definitions", "Foo"] config)
    "ApiFoo"

def foldDefinitionsRecTests : TestM Unit := testFunction "foldDefinitionsRec tests" do
  -- Count schemas visited
  let count := foldDefinitionsRec schemaWithDefinitions [] (init := 0)
    fun acc _schema _path => acc + 1

  testEq "Visits root + 3 definitions"
    count
    4  -- Root, Address, Person, ContactInfo

  -- Collect paths
  let paths := foldDefinitionsRec schemaWithDefinitions [] (init := #[])
    fun acc _schema path => acc.push path

  testEq "Collects correct paths"
    paths
    #[[], ["definitions", "Address"], ["definitions", "Person"], ["definitions", "Person", "definitions", "ContactInfo"]]

def mkNameMapTests : TestM Unit := testFunction "mkNameMap tests" do
  let resolver := Resolver.empty
    |>.addSchema simpleSchema (testURI "/simple.json")
  let nameMap := mkNameMap resolver

  testEq "Simple schema gets capitalized name"
    (nameMap.get? ⟨testURI "/simple.json", []⟩)
    (some "Simple")  -- Uses title

  -- Test with definitions
  let resolver2 := Resolver.empty
    |>.addSchema schemaWithDefinitions (testURI "/user.json")
  let nameMap2 := mkNameMap resolver2

  testEq "Root schema"
    (nameMap2.get? ⟨testURI "/user.json", []⟩)
    (some "User")

  testEq "Address definition"
    (nameMap2.get? ⟨testURI "/user.json", ["definitions", "Address"]⟩)
    (some "UserAddress")

  testEq "Nested ContactInfo definition"
    (nameMap2.get? ⟨testURI "/user.json", ["definitions", "Person", "definitions", "ContactInfo"]⟩)
    (some "UserPersonContactInfo")

  -- Test collision handling
  let resolver3 := Resolver.empty
    |>.addSchema schemaWithCollision (testURI "/collision.json")
  let nameMap3 := mkNameMap resolver3

  testEq "First User keeps name"
    (nameMap3.get? ⟨testURI "/collision.json", ["definitions", "User"]⟩)
    (some "CollisionUser")

  testEq "Second user gets suffix"
    (nameMap3.get? ⟨testURI "/collision.json", ["definitions", "user"]⟩)
    (some "CollisionUser2")

#eval TestM.run do
  extractBaseFromURITests
  extractSmartNameTests
  foldDefinitionsRecTests
  mkNameMapTests
  printSummary

end Test
end ReferencesTests
