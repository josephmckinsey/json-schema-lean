# Reference Resolution Design for JSON Schema CodeGen

## Overview

This document describes the design for supporting JSON Schema `$ref` references in the code generation module. Reference resolution is one of the most complex aspects of JSON Schema code generation because:

1. **Circular dependencies**: Schemas can reference each other in cycles, requiring mutual induction/recursion
2. **Name conflicts**: Multiple schemas may need unique, readable type names
3. **Topological ordering**: Non-circular dependencies must be defined before use

## Design Goals

1. **Correctness**: Generated code must compile and handle all valid reference patterns
2. **Readability**: Type names should be meaningful and follow Lean conventions
3. **Minimal mutual blocks**: Only use `mutual` when absolutely necessary (for cycles)
4. **Extensibility**: Design should allow future support for external schemas or custom names

## High-Level Strategy

The reference resolution process follows four phases:

```
┌─────────────────────────────────────────────────────────────────┐
│ Phase 1: Schema Collection & Naming                             │
│ - Identify all referenceable schemas (roots + definitions)      │
│ - Generate unique type names for each schema                    │
│ - Create rootURI + path → TypeName mapping                      │
└─────────────────────────────────────────────────────────────────┘
                              ↓
┌─────────────────────────────────────────────────────────────────┐
│ Phase 2: Dependency Analysis                                    │
│ - Build reference graph between schemas                         │
│ - Disallow references that do not go to roots + definitions     │
└─────────────────────────────────────────────────────────────────┘
                              ↓
┌─────────────────────────────────────────────────────────────────┐
│ Phase 3: Topological Sort with SCC Detection                    │
│ - Identify strongly connected components (mutual recursion)     │
│ - Topologically sort components                                 │
│ - Preserve input order where possible                           │
└─────────────────────────────────────────────────────────────────┘
                              ↓
┌─────────────────────────────────────────────────────────────────┐
│ Phase 4: Code Generation                                        │
│ - Process each component in order                               │
│ - Use name mapping to resolve $ref to type names                │
│ - Generate mutual blocks for SCCs with size > 1                 │
│ - Generate standalone definitions for SCCs with size = 1        │
└─────────────────────────────────────────────────────────────────┘
```

## Phase 1: Schema Collection & Naming

### 1.1 Identifying Referenceable Schemas

We identify schemas that can be referenced (and thus need named types) using the existing `Resolver`:

**Sources of referenceable schemas:**
- **Root schemas**: Each schema registered with `Resolver.addSchema` at a base URI
- **Definition schemas**: Schemas in `definitions` (and future `$defs`) fields
- **Schemas with `$id`**: Any schema with an explicit `$id` gets a resolvable identity

**Schemas we will NOT generate top-level types for:**
- **Inlined properties**: Field types in structures are aggressively inlined (current behavior)
- **oneOf/anyOf variants**: When inlineable, these become sum types `String ⊕ Int` (current behavior)
- **Unreferenced schemas**: If a schema is never referenced, we don't pre-generate it
- **Schemas in weird places**: If a scheme is only defined as a properties not in definition, then it should not be generated.
  If it is referenced, then this should cause an error.

This leverages the existing `Resolver.registerPaths` which already walks the schema tree and identifies referenceable locations.

### 1.2 Type Name Generation

For each referenceable schema, we generate a unique type name using the following priority:

1. **Title field**: If `schema.title` exists, use `sanitizeName(title)`
2. **Smart hierarchical path**: Extract meaningful name from URI + path
   - For `http://example.com/schemas/user.json#/definitions/Address` → `UserAddress`
   - For `#/definitions/Person/definitions/contactInfo` → `PersonContactInfo`
   - Algorithm: Take last component of URI (if file-like) + relevant path segments
3. **User-provided fallback**: Config option `defaultRootName` (e.g., "Schema", "TopLevel")

**Name collision resolution:**
- If a name is already taken, append a numeric suffix: `Address`, `Address2`, `Address3`
- Maintain a `Set String` of used names during this phase
- Record the mapping in `SchemaID → TypeName` map

**Smart hierarchical naming algorithm:**
```
extractSmartName(uri: URI, path: List String): String =
  // Get the base name from URI (last meaningful component)
  baseName := extractBaseFromURI(uri)

  // Get relevant path components (skip generic ones like "definitions")
  relevantPath := path.filter(fun s => s ∉ ["definitions", "properties", "items"])

  // Combine: capitalize and concatenate
  if relevantPath.isEmpty then
    sanitizeName(baseName)
  else
    sanitizeName(baseName + relevantPath.map(capitalize).join(""))
```

### 1.3 Data Structures

```lean
/-- Identifies a schema by its canonical URI and path -/
structure SchemaID where
  baseURI : URI
  path : List String
  deriving BEq, Hashable

/-- Mapping from schema locations to generated type names -/
abbrev NameMap := Std.HashMap SchemaID String
```

## Phase 2: Dependency Analysis

### 2.1 Reference Graph Construction

We build a directed graph where:
- **Nodes**: Each `SchemaID` (each named schema)
- **Edges**: `A → B` if schema A contains a `$ref` to schema B

We get the list of nodes by recursivey traversing every rootSchema in a resolver as well as recursively through
the `definitions` property. This gives us an `Array SchemaID` and `NameMap`.

**Important distinction:**
- We only track references between *named* schemas (ones in our NameMap)
- We track both "evil" and "safe" refs (borrowing terminology from `Resolving.lean`)
 by iterating using `foldStack`.

### 2.2 Reference Extraction

```lean
/-- Extract all $ref targets from a schema that point to named schemas -/
def extractSchemaRefs (resolver : Resolver) (rootURI : URI) (path : List String) : Except String (Array SchemaID) :=
  -- Get all resolved refs with resolver.resolvePath (currentBaseURI.resolveURIorRef ref)
  let schema := resolver.getSchema rootURI path
  let refs : Array SchemaID := schema.foldStack ...

  let badRefs := refs.filter fun schemaID => nameMap.contains schemaID
  if badRefs.isEmpty
    .ok refs
  else
    .error s!"Bad references found in schema {rootURI} at {path}"
```

### 2.3 Dependency Graph

```lean
/-- Directed graph of schema dependencies -/
structure RefGraph where
  adjList : Array (Array Nat) := .emptyWithCapacity
  index : Std.HashMap SchemaID Nat := .empty

/-- Build the reference graph from all named schemas -/
def buildRefGraph (namedSchemas : Array SchemaID) (nameMap : NameMap)
    (resolver : Resolver) : Except String RefGraph :=
  let index := namedSchemas.zipIdx.fold (init : Std.HashMap SchemaID Nat := .emptyWithCapacity) fun index (named, i) =>
    init.insert named i
  namedSchemas.zipIdx.foldlM (init : Array (Array Nat) := .empty) fun graph (named, i) => do
    let refs <- extractSchemaRefs resolver named.baseURI named.path
    let edges := refs.filterMap index.get?
    init.set i edges
```

## Phase 3: Topological Sorting with SCCs

### 3.1 Strongly Connected Components

We use **Tarjan's algorithm** to identify strongly connected components (SCCs). This algorithm:
- Finds all SCCs in a single depth-first traversal: O(V + E)
- Returns SCCs in **reverse topological order** automatically
- Can be modified to respect input ordering within SCCs

**Why Tarjan's over Kosaraju's:**
- Single pass (vs. two passes for Kosaraju)
- Naturally maintains discovery order, helping preserve input ordering
- A clean implementation exists in Mathlib4 that we can adapt (see below)

**Mathlib4 reference implementation:**
Mathlib4 has a Tarjan's SCC implementation at `Mathlib/Tactic/Order/Graph/Tarjan.lean` (used for the `order` tactic). While this is not a verified/proven implementation, it provides:
- Clean, modern Lean 4 code we can adapt
- Uses `StateM` monad for state management
- Returns SCC numbering via `lowlink` array (nodes with same `lowlink` value are in same SCC)
- We'll need to adapt it to:
  1. Return `Array (Array Nat)` of SCC components instead of just the `lowlink` array
  2. Work with our `RefGraph` structure instead of their `Graph` structure
  3. Preserve topological ordering of SCCs

### 3.2 Input Order Preservation

To preserve the initial alphabetical ordering as much as possible:

1. **Initial sorting**: We use the ordering (alphabetical most likely) given from `Array SchemaID`.
2. **Tarjan iteration order**: Process nodes in this order
3. **SCC internal order**: Within each SCC, maintain discovery order from traversal
4. **Tiebreaker**: When multiple nodes could be processed, choose smallest `Nat` first

This is achieved by:
```lean
/-- Tarjan's algorithm with input order preservation -/
def tarjanSCC (graph : RefGraph) : Array (Array SchemaID) :=
  -- Process nodes in inputOrder, but respect DFS discovery for SCC contents
  let state := [:graph.adjList.length].foldl (init := initialState) fun state nodeID =>
    if state.visited.contains nodeID then state
    else tarjanVisit graph nodeID state inputOrder

  state.sccs.reverse  -- SCCs are discovered in reverse topo order
```
See https://github.com/leanprover-community/mathlib4/blob/560872a203ef726bf76117856ece2872f8cff918/Mathlib/Tactic/Order/Graph/Tarjan.lean#L17-L29 for the reference implementation.

**Adapting Mathlib's Tarjan:**
```lean
/-- Adapted Tarjan state for our use case -/
structure TarjanState where
  visited : Array Bool
  id : Array Nat
  lowlink : Array Nat
  stack : Array Nat
  onStack : Array Bool
  time : Nat
  /-- NEW: Collect complete SCCs (not just lowlink values) -/
  sccs : Array (Array Nat) := #[]

/-- Adapted to work with RefGraph.adjList instead of Graph -/
partial def tarjanDFS (adjList : Array (Array Nat)) (v : Nat) : StateM TarjanState Unit := do
  -- Similar to Mathlib implementation but:
  -- - Use adjList[v]! to get edges (each edge is just a Nat, not an Edge structure)
  -- - When id[v] = lowlink[v], collect the full SCC and add to sccs array
  ...

/-- Returns Array of SCCs, each SCC is Array Nat of vertex indices -/
def findSCCs (graph : RefGraph) : Array (Array Nat) :=
  -- Initialize state and run Tarjan
  let s : TarjanState := { ... }
  (findSCCsImp graph.adjList).run s |>.snd.sccs
```

### 3.3 Topological Ordering

After SCC detection, we have:
- A list of SCCs in topologically sorted order
- Each SCC contains schemas that mutually reference each other

**Invariant**: For any two SCCs `A` and `B`, if `A` depends on `B`, then `B` appears before `A` in the list.

This ensures we can generate code in order where:
- Single-schema SCCs become standalone definitions
- Multi-schema SCCs become `mutual` blocks
- All dependencies are defined before use

## Phase 4: Code Generation

### 4.1 Generating Mutual Blocks

For each SCC with size > 1, we generate a `mutual ... end` block:

```lean
def generateMutualBlock (scc : Array SchemaID) (ctx : CodeGenContext)
    : Except String Format := do
  let mut typeDefs : Array TypeDefinition := #[]

  for named in scc do
    let schema := ctx.resolver.getSchema named.baseURI named.path
    let typeDef ← schemaToTypeDef schema (ctx.nameMap named) ctx
    typeDefs := typeDefs.push typeDef

  -- Build mutual block
  let declsWithInstances := typeDefs.map formatTypeDefWithInstances
  .ok ("mutual\n" ++ Std.Format.joinSep declsWithInstances.toList "\n\n" ++ "\nend")
```

### 4.2 Handling Dependencies in TypeDefinition

Currently `TypeDefinition.dependencies` holds inline nested types. With references:

**Before**: Dependencies only contained inlined field types (e.g., `PersonAddress` for a field)

**After**: Dependencies remain the same! Referenced types are NOT in dependencies because:
- They're in the global scope (generated at top level)
- They appear before the referencing type (topological order guarantees this)
- Only inline/nested types go in dependencies

This means the existing `flattenDependencies` logic continues to work unchanged.

### 4.3 Main Code Generation Loop

```lean
def generateAllSchemas (resolver : Resolver) (config : Config) : Except String String := do
  -- Phase 1: Collect and name all schemas
  let namedSchemasAndNames : Array (String × SchemaID) ← collectAndNameSchemas resolver config
  let nameMap := buildNameMap namedSchemasAndNames
  let namedSchemas := (namedSchemas.qsort (·.1 < ·.1)).map (·.2)

  -- Phase 2: Build reference graph
  let refGraph := buildRefGraph namedSchemas nameMap resolver

  -- Phase 2: Build reference graph
  let refGraph := buildRefGraph namedSchemas nameMap resolver

  -- Phase 3: Compute SCCs in topological order
  let sccs := tarjanSCC refGraph

  -- Phase 4: Generate code for each SCC
  let ctx : CodeGenContext := { resolver, nameMap, config }
  let mut outputs : Array Format := #[]

  for scc in sccs do
    let output ← if scc.size = 1 then
      -- Single schema: standalone definition
      let schemaID := namedSchemas[scc[0]!]!
      let schema <- resolver.getSchema schemaID
      schemaToFormat named.schema named.typeName ctx
    else
      -- Multiple schemas: mutual block
      let namedInSCC := scc.map (fun id => namedSchemas[id])
      generateMutualBlock namedInSCC ctx

    outputs := outputs.push output

  .ok (Std.Format.joinSep outputs.toList "\n\n" |>.pretty)
```

## External Reference Handling

For the initial implementation, we **error on external references** (refs to URIs not in the resolver):

```lean
if !nameMap.contains schemaID then
  .error s!"External reference to {ref} - not supported yet"
```

**Future extension points:**
1. **Callback for external schemas**: `Config.externalSchemaHandler : URI → Option Schema`
2. **Lazy loading**: Fetch external schemas on-demand during resolution
3. **Placeholder types**: Generate `opaque ExternalRef_Foo : Type` with TODO comments

The design accommodates these extensions through:
- The `NameMap` can be populated from external sources
- The resolver can be extended to fetch external schemas
- The error handling provides clear diagnostics for future enhancement

## Implementation Roadmap

### Step 1: Core Data Structures
- [x] `SchemaID` structure with `BEq` and `Hashable` instances
- [x] `CodeGenContext` structure

### Step 2: Schema Collection & Naming
- [x] `extractBaseFromURI`: Get meaningful base name from URI
- [x] `extractSmartName`: Smart hierarchical name generation
- [x] `foldDefinitionsRec`: Recursively fold over schema and all subdefinitions
- [x] `mkNameMap`: Walk resolver, collect all named schemas, and assign unique names with collision resolution
- [x] Tests for name generation with various URI patterns (17 tests in ReferencesTests.lean)

### Step 3: Reference Graph
- [ ] `extractSchemaRefs`: Extract refs from schema using existing `foldStack`
- [ ] `buildRefGraph`: Build dependency graph
- [ ] Tests for graph construction with simple and complex schemas

### Step 4: Topological Sort with SCCs
- [ ] Adapt Mathlib's `TarjanState` to collect full SCCs (not just lowlink)
- [ ] Adapt `tarjanDFS` to work with our `RefGraph.adjList` structure
- [ ] Modify SCC collection to build `Array (Array Nat)` of components
- [ ] `findSCCs`: Main entry point returning topologically sorted SCCs
- [ ] Tests with acyclic graphs, simple cycles, complex cycles
- [ ] Tests verifying topological order property
- [ ] Tests verifying input order preservation where possible

### Step 5: Code Generation Integration
- [ ] `generateMutualBlock`: Generate mutual recursion blocks
- [ ] `generateAllSchemas`: Main entry point

### Step 6: Testing & Validation
- [ ] Unit tests for each component
- [ ] Integration tests with real JSON schemas featuring refs
- [ ] Test cases:
  - Simple refs (definitions to definitions)
  - Nested refs (deep definition paths)
  - Circular refs (two-way, three-way, complex cycles)
  - Mixed cycles and acyclic deps
  - Name collision scenarios
- [ ] Verify generated code compiles
- [ ] Verify FromJson/ToJson roundtrip with refs

### Step 7: Documentation & Examples
- [ ] Update CLAUDE.md with reference support
- [ ] Add examples to test suite
- [ ] Document limitations (no external refs yet)

## Edge Cases & Considerations

### 1. Self-referencing schemas
```json
{
  "definitions": {
    "Node": {
      "type": "object",
      "properties": {
        "value": { "type": "string" },
        "next": { "$ref": "#/definitions/Node" }
      }
    }
  }
}
```
**Handling**: SCC of size 1 with self-loop. Generate standalone inductive (not mutual):
```lean
inductive Node where
  | mk (value : String) (next : Option Node)
```

### 2. Deep nesting with refs
```json
{
  "definitions": {
    "A": { "$ref": "#/definitions/B" },
    "B": { "$ref": "#/definitions/C" },
    "C": { "type": "string" }
  }
}
```
**Handling**: Topological order ensures `C` → `B` → `A`. Each is just an abbrev:
```lean
abbrev C := String
abbrev B := C
abbrev A := B
```

### 3. Mixing inline and ref
```json
{
  "definitions": {
    "Person": {
      "type": "object",
      "properties": {
        "name": { "type": "string" },
        "friend": { "$ref": "#/definitions/Person" }
      }
    }
  }
}
```
**Handling**: `name` field is inlined (not in NameMap), `friend` field references `Person` type:
```lean
inductive Person where
  | mk (name : String) (friend : Option Person)
```

### 4. Refs in oneOf/anyOf
```json
{
  "definitions": {
    "StringOrPerson": {
      "oneOf": [
        { "type": "string" },
        { "$ref": "#/definitions/Person" }
      ]
    },
    "Person": { ... }
  }
}
```
**Handling**: `Person` must be defined before `StringOrPerson` (topological order). The oneOf becomes:
```lean
inductive StringOrPerson where
  | case0 (val : String)
  | case1 (val : Person)
```

## Open Questions for Future Consideration

1. **allOf merging**: How should we handle `allOf` with `$ref`? Merge schemas or generate composition?
2. **Recursive array types**: `{ "type": "array", "items": { "$ref": "#" } }` - needs special handling
3. **Polymorphism**: Could we use Lean's type parameters for some schemas?
4. **Optimization**: Can we detect and eliminate trivial type aliases?
5. **Incremental generation**: Support for generating only changed schemas?

## References & Related Work

- **Existing code**: `JsonSchema/Resolving.lean` - resolver and loop detection
- **Mathlib4 Tarjan**: [`Mathlib/Tactic/Order/Graph/Tarjan.lean`](https://github.com/leanprover-community/mathlib4/blob/560872a203ef726bf76117856ece2872f8cff918/Mathlib/Tactic/Order/Graph/Tarjan.lean) - unverified but clean implementation to adapt
- **Lean docs**: [Mutual recursion](https://lean-lang.org/theorem_proving_in_lean4/induction_and_recursion.html#mutual-recursion)
- **Tarjan's algorithm**: [Wikipedia](https://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm)
- **JSON Schema spec**: [Draft 7 references](https://json-schema.org/draft-07/json-schema-core.html#rfc.section.8.3)

## Summary

This design provides a complete, principled approach to reference resolution that:

- ✅ Leverages existing Resolver infrastructure
- ✅ Generates readable, collision-free names
- ✅ Handles circular dependencies with mutual blocks
- ✅ Preserves input ordering where possible
- ✅ Integrates cleanly with existing TypeDefinition system
- ✅ Provides clear extension points for future work
- ✅ Matches the user's outlined strategy with concrete details

The implementation can be done incrementally, with each phase testable independently before moving to the next.
