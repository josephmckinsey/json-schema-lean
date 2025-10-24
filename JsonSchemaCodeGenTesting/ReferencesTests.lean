import JsonSchemaCodeGen.References
import JsonSchema.Resolving
import JsonSchemaCodeGenTesting.TestUtils
import UriTesting.Helpers

-- Test reference resolution and name generation
section ReferencesTests

open JsonSchemaCodeGen
open JsonSchemaCodeGenTesting
open JsonSchema
open Lean

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

-- Test schemas with references
def schemaWithSimpleRef : Schema := .Object {
  type := #[.ObjectType]
  definitions := some (.ofList [
    ("A", Schema.Object {
      type := #[.StringType]
    }),
    ("B", Schema.Object {
      type := #[.ObjectType]
      ref := some (mkRef "#/definitions/A")
    })
  ])
}

def schemaWithMultipleRefs : Schema := .Object {
  type := #[.ObjectType]
  definitions := some (.ofList [
    ("A", Schema.Object { type := #[.StringType] }),
    ("B", Schema.Object { type := #[.IntegerType] }),
    ("C", Schema.Object {
      type := #[.ObjectType]
      oneOf := some #[
        Schema.Object { ref := some (mkRef "#/definitions/A") },
        Schema.Object { ref := some (mkRef "#/definitions/B") }
      ]
    })
  ])
}

def schemaWithCircularRef : Schema := .Object {
  type := #[.ObjectType]
  definitions := some (.ofList [
    ("Node", Schema.Object {
      type := #[.ObjectType]
      properties := some #[
        ("value", Schema.Object { type := #[.StringType] }),
        ("next", Schema.Object { ref := some (mkRef "#/definitions/Node") })
      ]
    })
  ])
}

def schemaWithChainedRefs : Schema := .Object {
  type := #[.ObjectType]
  definitions := some (.ofList [
    ("A", Schema.Object { ref := some (mkRef "#/definitions/B") }),
    ("B", Schema.Object { ref := some (mkRef "#/definitions/C") }),
    ("C", Schema.Object { type := #[.StringType] })
  ])
}

def extractSchemaRefsTests : TestM Unit := testFunction "extractSchemaRefs tests" do
  -- Test 1: Schema with no refs
  let resolver1 := Resolver.empty.addSchema simpleSchema (testURI "/simple.json")
  let nameMap1 := mkNameMap resolver1
  let schemaID1 := SchemaID.mk (testURI "/simple.json") []

  match extractSchemaRefs resolver1 schemaID1 nameMap1 with
  | .ok refs =>
      testEq "Schema with no refs returns empty array"
        refs.size
        0
  | .error e => test s!"Test failed: {e}" false; return -- early return

  -- Test 2: Schema with simple ref
  let resolver2 := Resolver.empty.addSchema schemaWithSimpleRef (testURI "/ref.json")
  let nameMap2 := mkNameMap resolver2
  let schemaIDB := SchemaID.mk (testURI "/ref.json") ["definitions", "B"]

  match extractSchemaRefs resolver2 schemaIDB nameMap2 with
  | .ok refs =>
      testEq "Schema B references A"
        refs.size
        1
      testEq "Reference points to A"
        refs[0]?
        (some (SchemaID.mk (testURI "/ref.json") ["definitions", "A"]))
  | .error e => test s!"Test failed: {e}" false; return

  -- Test 3: Schema with multiple refs (in oneOf)
  let resolver3 := Resolver.empty.addSchema schemaWithMultipleRefs (testURI "/multi.json")
  let nameMap3 := mkNameMap resolver3
  let schemaIDC := SchemaID.mk (testURI "/multi.json") ["definitions", "C"]

  match extractSchemaRefs resolver3 schemaIDC nameMap3 with
  | .ok refs =>
      testEq "Schema C references A and B"
        refs.size
        2
      -- Note: refs should contain both A and B
      let hasA := refs.any (· == SchemaID.mk (testURI "/multi.json") ["definitions", "A"])
      let hasB := refs.any (· == SchemaID.mk (testURI "/multi.json") ["definitions", "B"])
      testEq "Contains reference to A"
        hasA
        true
      testEq "Contains reference to B"
        hasB
        true
  | .error e => test s!"Test failed: {e}" false; return

  -- Test 4: Self-referencing schema (circular)
  let resolver4 := Resolver.empty.addSchema schemaWithCircularRef (testURI "/circular.json")
  let nameMap4 := mkNameMap resolver4
  let schemaIDNode := SchemaID.mk (testURI "/circular.json") ["definitions", "Node"]

  match extractSchemaRefs resolver4 schemaIDNode nameMap4 with
  | .ok refs =>
      testEq "Self-referencing schema"
        refs.size
        1
      testEq "Reference points to itself"
        refs[0]?
        (some schemaIDNode)
  | .error e => test s!"Test failed: {e}" false; return

def buildRefGraphTests : TestM Unit := testFunction "buildRefGraph tests" do
  -- Test 1: Simple acyclic graph (A ← B)
  let resolver1 := Resolver.empty.addSchema schemaWithSimpleRef (testURI "/ref.json")
  let nameMap1 := mkNameMap resolver1
  let namedSchemas1 := #[
    SchemaID.mk (testURI "/ref.json") [],
    SchemaID.mk (testURI "/ref.json") ["definitions", "A"],
    SchemaID.mk (testURI "/ref.json") ["definitions", "B"]
  ]

  match buildRefGraph namedSchemas1 nameMap1 resolver1 with
  | .ok graph =>
      testEq "Graph has 3 nodes"
        graph.adjList.size
        3
      testEq "Root has no outgoing edges"
        (graph.adjList[0]?.getD #[])
        #[]
      testEq "A has no outgoing edges"
        (graph.adjList[1]?.getD #[])
        #[]
      testEq "B has one outgoing edge to A (index 1)"
        (graph.adjList[2]?.getD #[])
        #[1]
  | .error e => test s!"Test failed: {e}" false; return

  -- Test 2: Graph with multiple refs (C → A, C → B)
  let resolver2 := Resolver.empty.addSchema schemaWithMultipleRefs (testURI "/multi.json")
  let nameMap2 := mkNameMap resolver2
  let namedSchemas2 := #[
    SchemaID.mk (testURI "/multi.json") [],
    SchemaID.mk (testURI "/multi.json") ["definitions", "A"],
    SchemaID.mk (testURI "/multi.json") ["definitions", "B"],
    SchemaID.mk (testURI "/multi.json") ["definitions", "C"]
  ]

  match buildRefGraph namedSchemas2 nameMap2 resolver2 with
  | .ok graph =>
      testEq "Graph has 4 nodes"
        graph.adjList.size
        4
      testEq "C has two outgoing edges"
        (graph.adjList[3]?.getD #[]).size
        2
      -- C should reference both A (index 1) and B (index 2)
      let cEdges := graph.adjList[3]?.getD #[]
      let hasEdgeToA := cEdges.contains 1
      let hasEdgeToB := cEdges.contains 2
      testEq "C has edge to A"
        hasEdgeToA
        true
      testEq "C has edge to B"
        hasEdgeToB
        true
  | .error e => test s!"Test failed: {e}" false; return

  -- Test 3: Self-referencing (circular)
  let resolver3 := Resolver.empty.addSchema schemaWithCircularRef (testURI "/circular.json")
  let nameMap3 := mkNameMap resolver3
  let namedSchemas3 := #[
    SchemaID.mk (testURI "/circular.json") [],
    SchemaID.mk (testURI "/circular.json") ["definitions", "Node"]
  ]

  match buildRefGraph namedSchemas3 nameMap3 resolver3 with
  | .ok graph =>
      testEq "Graph has 2 nodes"
        graph.adjList.size
        2
      testEq "Node has self-loop (edge to index 1)"
        (graph.adjList[1]?.getD #[])
        #[1]
  | .error e => test s!"Test failed: {e}" false; return

  -- Test 4: Chained refs (A → B → C)
  let resolver4 := Resolver.empty.addSchema schemaWithChainedRefs (testURI "/chain.json")
  let nameMap4 := mkNameMap resolver4
  let namedSchemas4 := #[
    SchemaID.mk (testURI "/chain.json") [],
    SchemaID.mk (testURI "/chain.json") ["definitions", "A"],
    SchemaID.mk (testURI "/chain.json") ["definitions", "B"],
    SchemaID.mk (testURI "/chain.json") ["definitions", "C"]
  ]

  match buildRefGraph namedSchemas4 nameMap4 resolver4 with
  | .ok graph =>
      testEq "Graph has 4 nodes"
        graph.adjList.size
        4
      testEq "A references B (index 2)"
        (graph.adjList[1]?.getD #[])
        #[2]
      testEq "B references C (index 3)"
        (graph.adjList[2]?.getD #[])
        #[3]
      testEq "C has no outgoing edges"
        (graph.adjList[3]?.getD #[])
        #[]
  | .error e => test s!"Test failed: {e}" false; return

-- Test SCC detection
def findSCCsTests : TestM Unit := testFunction "findSCCs tests" do
  -- Test 1: Acyclic graph (A ← B, no cycles)
  -- Graph: 0 → [], 1 → [], 2 → [1]
  let resolver1 := Resolver.empty.addSchema schemaWithSimpleRef (testURI "/ref.json")
  let nameMap1 := mkNameMap resolver1
  let namedSchemas1 := #[
    SchemaID.mk (testURI "/ref.json") [],
    SchemaID.mk (testURI "/ref.json") ["definitions", "A"],
    SchemaID.mk (testURI "/ref.json") ["definitions", "B"]
  ]

  match buildRefGraph namedSchemas1 nameMap1 resolver1 with
  | .ok graph =>
      let sccs := findSCCs graph
      testEq "Acyclic graph has 3 SCCs"
        sccs.size
        3
      -- Each node should be its own SCC
      testEq "Each SCC has size 1"
        (sccs.all (·.size == 1))
        true
      -- Check topological order: dependencies come before dependents
      -- A (index 1) should come before B (index 2) because B → A
      let aIndex := sccs.findIdx? (fun scc => scc.contains 1)
      let bIndex := sccs.findIdx? (fun scc => scc.contains 2)
      match aIndex, bIndex with
      | some ai, some bi =>
          test "A comes before B in topological order"
            (ai < bi)
      | _, _ => test "Failed to find A or B in SCCs" false
  | .error e => test s!"Test failed: {e}" false; return

  -- Test 2: Simple cycle (Node → Node)
  let resolver2 := Resolver.empty.addSchema schemaWithCircularRef (testURI "/circular.json")
  let nameMap2 := mkNameMap resolver2
  let namedSchemas2 := #[
    SchemaID.mk (testURI "/circular.json") [],
    SchemaID.mk (testURI "/circular.json") ["definitions", "Node"]
  ]

  match buildRefGraph namedSchemas2 nameMap2 resolver2 with
  | .ok graph =>
      let sccs := findSCCs graph
      testEq "Circular graph has 2 SCCs"
        sccs.size
        2
      -- Root should be its own SCC, Node should be its own SCC (self-loop)
      testEq "Self-referencing node forms SCC of size 1"
        (sccs.any (fun scc => scc.size == 1 && scc.contains 1))
        true
  | .error e => test s!"Test failed: {e}" false; return

  -- Test 3: Chain (A → B → C)
  let resolver3 := Resolver.empty.addSchema schemaWithChainedRefs (testURI "/chain.json")
  let nameMap3 := mkNameMap resolver3
  let namedSchemas3 := #[
    SchemaID.mk (testURI "/chain.json") [],
    SchemaID.mk (testURI "/chain.json") ["definitions", "A"],
    SchemaID.mk (testURI "/chain.json") ["definitions", "B"],
    SchemaID.mk (testURI "/chain.json") ["definitions", "C"]
  ]

  match buildRefGraph namedSchemas3 nameMap3 resolver3 with
  | .ok graph =>
      let sccs := findSCCs graph
      testEq "Chain graph has 4 SCCs"
        sccs.size
        4
      -- Each node should be its own SCC
      testEq "Each SCC has size 1"
        (sccs.all (·.size == 1))
        true
      -- Check topological order: C before B before A
      let aIndex := sccs.findIdx? (fun scc => scc.contains 1)
      let bIndex := sccs.findIdx? (fun scc => scc.contains 2)
      let cIndex := sccs.findIdx? (fun scc => scc.contains 3)
      match aIndex, bIndex, cIndex with
      | some ai, some bi, some ci =>
          test "C comes before B"
            (ci < bi)
          test "B comes before A"
            (bi < ai)
      | _, _, _ => test "Failed to find A, B, or C in SCCs" false
  | .error e => test s!"Test failed: {e}" false; return

-- Test schema with a real cycle (A → B → A)
def schemaWithCycle : Schema := .Object {
  type := #[.ObjectType]
  definitions := some (.ofList [
    ("A", Schema.Object {
      type := #[.ObjectType]
      ref := some (mkRef "#/definitions/B")
    }),
    ("B", Schema.Object {
      type := #[.ObjectType]
      ref := some (mkRef "#/definitions/A")
    })
  ])
}

-- Test schema with complex SCC (A → B → C → A)
def schemaWithComplexCycle : Schema := .Object {
  type := #[.ObjectType]
  definitions := some (.ofList [
    ("A", Schema.Object {
      type := #[.ObjectType]
      ref := some (mkRef "#/definitions/B")
    }),
    ("B", Schema.Object {
      type := #[.ObjectType]
      ref := some (mkRef "#/definitions/C")
    }),
    ("C", Schema.Object {
      type := #[.ObjectType]
      ref := some (mkRef "#/definitions/A")
    })
  ])
}

-- Test schema with multiple independent cycles
def schemaWithMultipleCycles : Schema := .Object {
  type := #[.ObjectType]
  definitions := some (.ofList [
    -- Cycle 1: A ↔ B
    ("A", Schema.Object {
      type := #[.ObjectType]
      ref := some (mkRef "#/definitions/B")
    }),
    ("B", Schema.Object {
      type := #[.ObjectType]
      ref := some (mkRef "#/definitions/A")
    }),
    -- Cycle 2: C ↔ D
    ("C", Schema.Object {
      type := #[.ObjectType]
      ref := some (mkRef "#/definitions/D")
    }),
    ("D", Schema.Object {
      type := #[.ObjectType]
      ref := some (mkRef "#/definitions/C")
    })
  ])
}

def findSCCsCycleTests : TestM Unit := testFunction "findSCCs cycle tests" do
  -- Test 4: Simple 2-node cycle (A → B → A)
  let resolver4 := Resolver.empty.addSchema schemaWithCycle (testURI "/cycle.json")
  let nameMap4 := mkNameMap resolver4
  let namedSchemas4 := #[
    SchemaID.mk (testURI "/cycle.json") [],
    SchemaID.mk (testURI "/cycle.json") ["definitions", "A"],
    SchemaID.mk (testURI "/cycle.json") ["definitions", "B"]
  ]

  match buildRefGraph namedSchemas4 nameMap4 resolver4 with
  | .ok graph =>
      let sccs := findSCCs graph
      testEq "Cycle graph has 2 SCCs"
        sccs.size
        2
      -- One SCC should contain both A and B
      let hasCycleOfTwo := sccs.any (fun scc => scc.size == 2)
      testEq "One SCC contains the cycle (A, B)"
        hasCycleOfTwo
        true
      -- Find the SCC containing the cycle
      let cycleSCC := sccs.find? (fun scc => scc.size == 2)
      match cycleSCC with
      | some scc =>
          testEq "Cycle SCC contains A (index 1)"
            (scc.contains 1)
            true
          testEq "Cycle SCC contains B (index 2)"
            (scc.contains 2)
            true
      | none => test "Failed to find cycle SCC" false
  | .error e => test s!"Test failed: {e}" false; return

  -- Test 5: Complex 3-node cycle (A → B → C → A)
  let resolver5 := Resolver.empty.addSchema schemaWithComplexCycle (testURI "/complex.json")
  let nameMap5 := mkNameMap resolver5
  let namedSchemas5 := #[
    SchemaID.mk (testURI "/complex.json") [],
    SchemaID.mk (testURI "/complex.json") ["definitions", "A"],
    SchemaID.mk (testURI "/complex.json") ["definitions", "B"],
    SchemaID.mk (testURI "/complex.json") ["definitions", "C"]
  ]

  match buildRefGraph namedSchemas5 nameMap5 resolver5 with
  | .ok graph =>
      let sccs := findSCCs graph
      testEq "Complex cycle graph has 2 SCCs"
        sccs.size
        2
      -- One SCC should contain A, B, and C
      let hasCycleOfThree := sccs.any (fun scc => scc.size == 3)
      testEq "One SCC contains the cycle (A, B, C)"
        hasCycleOfThree
        true
      -- Find the SCC containing the cycle
      let cycleSCC := sccs.find? (fun scc => scc.size == 3)
      match cycleSCC with
      | some scc =>
          testEq "Cycle SCC contains A (index 1)"
            (scc.contains 1)
            true
          testEq "Cycle SCC contains B (index 2)"
            (scc.contains 2)
            true
          testEq "Cycle SCC contains C (index 3)"
            (scc.contains 3)
            true
      | none => test "Failed to find cycle SCC" false
  | .error e => test s!"Test failed: {e}" false; return

  -- Test 6: Multiple independent cycles
  let resolver6 := Resolver.empty.addSchema schemaWithMultipleCycles (testURI "/multi-cycle.json")
  let nameMap6 := mkNameMap resolver6
  let namedSchemas6 := #[
    SchemaID.mk (testURI "/multi-cycle.json") [],
    SchemaID.mk (testURI "/multi-cycle.json") ["definitions", "A"],
    SchemaID.mk (testURI "/multi-cycle.json") ["definitions", "B"],
    SchemaID.mk (testURI "/multi-cycle.json") ["definitions", "C"],
    SchemaID.mk (testURI "/multi-cycle.json") ["definitions", "D"]
  ]

  match buildRefGraph namedSchemas6 nameMap6 resolver6 with
  | .ok graph =>
      let sccs := findSCCs graph
      testEq "Multiple cycles graph has 3 SCCs"
        sccs.size
        3
      -- Two SCCs should have size 2 (A-B cycle and C-D cycle)
      let twoNodeCycles := sccs.filter (·.size == 2)
      testEq "Two SCCs of size 2"
        twoNodeCycles.size
        2
      -- Check that A and B are in the same SCC
      let abSCC := sccs.find? (fun scc => scc.contains 1 && scc.contains 2)
      testEq "A and B are in same SCC"
        abSCC.isSome
        true
      -- Check that C and D are in the same SCC
      let cdSCC := sccs.find? (fun scc => scc.contains 3 && scc.contains 4)
      testEq "C and D are in same SCC"
        cdSCC.isSome
        true
  | .error e => test s!"Test failed: {e}" false; return

def allReferencesTests : TestM Unit := group "Reference Tests" do
  extractBaseFromURITests
  extractSmartNameTests
  foldDefinitionsRecTests
  mkNameMapTests
  extractSchemaRefsTests
  buildRefGraphTests
  findSCCsTests
  findSCCsCycleTests

end Test
end ReferencesTests
