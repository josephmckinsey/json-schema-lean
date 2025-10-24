import JsonSchema.Schema
import JsonSchema.Resolving
import JsonSchema.CodeGen.Config
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

end JsonSchema.CodeGen
