import JsonSchema.Schema
import JsonSchema.Resolving
import JsonSchema.CodeGen.Config
import JsonSchema.PointerFragment
import Lean

namespace JsonSchema.CodeGen

open Lean

/-!
# Reference Resolution and Name Mapping

This module handles schema collection and name generation for code generation with `$ref` support.

## Design Note: Handling User-Provided Names

When generating code for a single schema with `schemaToFormat schema "MyTypeName"`, we need to
reconcile the user-provided name with the nameMap (which is needed for resolving references,
including self-references).

**Solution**: Always use the nameMap internally, but allow overrides:
- For single-schema generation: Create a temporary resolver, build nameMap, then override the
  root schema's entry with the user-provided name
- This allows self-referential schemas (e.g., trees) to work correctly
- Later, we can override any definition's name by simply modifying the nameMap

Example:
```lean
def schemaToFormat (schema : Schema) (typeName : String) (config : Config) := do
  let tempResolver := Resolver.empty.addSchema schema defaultURI
  let mut nameMap := mkNameMap tempResolver config
  nameMap := nameMap.insert ⟨defaultURI, []⟩ typeName  -- Override root name
  -- ... generate using nameMap-based system
```
-/

def resolveRefToName (ref : LeanUri.URI ⊕ LeanUri.RelativeRef) : SchemaGen String := do
  let resolver ← CodeGenContext.resolver <$> read
  let (rootURI, path) := resolver.resolvePath ((← getURI).resolveURIorRef ref)
  let name? ← read <&> fun ctx => ctx.nameMap.get? ⟨rootURI, path⟩
  match name? with
  | some name => pure name
  | none => .error s!"Reference {←getURI} -> {rootURI} {path} could not be found."

/-- Extract base name from URI path (e.g., "schemas/user.json" → "User")
    Similar to FilePath.fileStem but works on URI paths. -/
def extractBaseFromURI (uri : LeanUri.URI) : String :=
  -- Get the last component of the path
  let pathParts := uri.path.splitOn "/"
  let lastComponent := pathParts.getLast?.getD ""
  -- Remove extension (everything after last '.')
  let stem := match lastComponent.revPosOf '.' with
    | some ⟨0⟩ => lastComponent  -- Starts with '.', keep it all
    | some pos => lastComponent.extract ⟨0⟩ pos
    | none => lastComponent
  -- Capitalize first letter
  if stem.isEmpty then "Schema" else capitalize stem

/-- Generate smart hierarchical name from URI and path.

    Examples:
    - URI: "http://example.com/schemas/user.json", path: [] → "User"
    - URI: "http://example.com/schemas/user.json", path: ["definitions", "Address"] → "UserAddress"
    - URI: "#", path: ["definitions", "Person", "definitions", "ContactInfo"] → "PersonContactInfo"
-/
def extractSmartName (uri : LeanUri.URI) (path : List String) (config : Config) : String :=
  let baseName := extractBaseFromURI uri
  -- Filter out generic path segments like "definitions", "properties", "items"
  let genericSegments := ["definitions", "properties", "items", "additionalProperties",
                          "patternProperties", "oneOf", "anyOf", "allOf"]
  let relevantPath := path.filter (fun s => !genericSegments.contains s)

  -- Combine base name with relevant path components
  let combined := if relevantPath.isEmpty then
    baseName
  else
    baseName ++ (relevantPath.map capitalize |>.foldl (· ++ ·) "")

  config.sanitizeName combined

/-- Recursively fold over a schema and all subdefinitions.

    Including the root schema, we call `f` with the accumulated value,
    the definition schema, and the pull path to that definition. Then recursive
    process subdefinitions.
-/
partial def foldDefinitionsRec
    (schema : Schema)
    (currentPath : List String)
    (f : α → Schema → List String → α)
    (init : α)
    : α :=
  let init := f init schema currentPath.reverse
  match schema with
  | Schema.Boolean _ => init
  | Schema.Object o =>
      o.foldDefinitions (init := init) fun acc (key, defSchema) =>
        let defPath := key::"definitions"::currentPath
        foldDefinitionsRec defSchema defPath f acc

/-- Populate nameMap from resolver.

  Iterates through definitions recurisvely, assigns unique names to
  all schemas reachable through rootURIs as well as through subdefinitions.
-/
partial def mkNameMap (r : Resolver) (config : Config := {}) : Std.HashMap SchemaID String :=
  -- Fold over all root schemas and their definitions, building nameMap with collision resolution
  let initMap : Std.HashMap SchemaID String := .emptyWithCapacity
  let initSet : Std.HashSet String := .emptyWithCapacity
  let (nameMap, _usedNames) := r.rootSchemas.fold (init := (initMap, initSet))
    fun init rootURI rootSchema =>
      foldDefinitionsRec rootSchema [] (init := init) fun (nameMap, usedNames) schema path =>
        let schemaID := SchemaID.mk rootURI path

        -- Try to use title if available
        let titleName? := match schema with
          | Schema.Boolean _ => none
          | Schema.Object o => o.title.map config.sanitizeName

        -- Generate base name (either from title or smart extraction)
        let baseName := match titleName? with
          | some title => title
          | none => extractSmartName schemaID.baseURI schemaID.path config

        -- Handle collision: append numbers if name already taken
        let rec findUniqueName (name : String) (suffix : Nat)
            (collided : Bool := false) : String × Bool :=
          if usedNames.contains name then
            findUniqueName (baseName ++ toString suffix) (suffix + 1) true
          else
            (name, collided)

        let (finalName, _collided) := findUniqueName baseName 2
        (nameMap.insert schemaID finalName, usedNames.insert finalName)

  nameMap

/-!
## Phase 2: Reference Graph Construction

Build a directed graph where:
- Nodes: Each SchemaID (each named schema)
- Edges: A → B if schema A contains a $ref to schema B

We track all references (both "evil" and "safe" by iterating through the schema tree).
-/

/-- Directed graph of schema dependencies represented as adjacency list.
    Each node is identified by its index in the original namedSchemas array. -/
structure RefGraph where
  /-- Adjacency list: adjList[i] = array of indices that schema i references -/
  adjList : Array (Array Nat)
  /-- Map from SchemaID to its index in the adjacency list -/
  index : Std.HashMap SchemaID Nat

/-- Extract all $ref targets from a schema that point to named schemas.
    Returns the SchemaIDs of all referenced schemas.
    Only extracts "active" refs (not those buried in definitions). -/
partial def extractSchemaRefs (resolver : Resolver) (schemaID : SchemaID)
    (nameMap : Std.HashMap SchemaID String) : Except String (Array SchemaID) := do
  -- Get the schema at this location
  let schema? := resolver.getSchemaFromRoot? schemaID.baseURI schemaID.path
  let schema ← match schema? with
    | some s => .ok s
    | none => .error s!"Schema not found at {schemaID.baseURI} {schemaID.path}"

  -- Collect all refs using foldActive (skips nested definitions)
  let refs := schema.foldActive schemaID.path schemaID.baseURI (init := #[])
    fun refs s _path baseURI =>
      match s with
      | Schema.Boolean _ => refs
      | Schema.Object o =>
        match o.ref with
        | some ref =>
            -- Resolve the ref to its canonical location
            let resolvedURI := baseURI.resolveURIorRef ref
            let (rootURI, path) := resolver.resolvePath resolvedURI
            refs.push (SchemaID.mk rootURI path)
        | none => refs

  -- Filter to only include refs that point to named schemas
  let validRefs := refs.filter (nameMap.contains ·)
  let badRefs := refs.filter (!nameMap.contains ·)

  -- Error if there are any refs to non-named schemas
  if !badRefs.isEmpty then
    let badRefStrs := badRefs.map fun id => s!"{id.baseURI}#{JsonPointer.toString id.path}"
    .error s!"Bad references found in schema {schemaID.baseURI}#{JsonPointer.toString schemaID.path}: {badRefStrs.toList}"
  else
    .ok validRefs

/-- Build the reference graph from all named schemas.
    namedSchemas must be in a stable order (e.g., alphabetically sorted). -/
def buildRefGraph (namedSchemas : Array SchemaID) (nameMap : Std.HashMap SchemaID String)
    (resolver : Resolver) : Except String RefGraph := do
  -- Build index mapping SchemaID → Nat
  let index : Std.HashMap SchemaID Nat := namedSchemas.zipIdx.foldl
    (init := Std.HashMap.emptyWithCapacity (capacity := namedSchemas.size))
    fun map (schemaID, i) => map.insert schemaID i

  -- Build adjacency list by extracting refs from each schema
  let adjList ← namedSchemas.mapM fun schemaID => do
    let refs ← extractSchemaRefs resolver schemaID nameMap
    -- Convert SchemaIDs to indices
    let indices := refs.filterMap (index.get? ·)
    .ok indices

  .ok { adjList, index }

end JsonSchema.CodeGen
