import JsonSchema.Schema
import JsonSchema.Validation
import JsonSchemaCodeGen.Config
import JsonSchemaCodeGen.InlineTypes
import JsonSchemaCodeGen.Abbreviations
import JsonSchemaCodeGen.Structures
import JsonSchemaCodeGen.Inductives
import JsonSchemaCodeGen.References

import Lean

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

namespace JsonSchemaCodeGen

open Lean JsonSchema

/-- Recursively flatten all dependencies from a TypeDefinition into a list -/
partial def flattenDependencies (typeDef : TypeDefinition) : List TypeDefinition :=
  let deps := typeDef.dependencies
  let nestedDeps := deps.flatMap flattenDependencies
  nestedDeps ++ deps

/-- Main schema to TypeDefinition conversion -/
partial def schemaToTypeDef (s : JsonSchema.Schema) (name : String)
    : SchemaGen TypeDefinition := withTypeName name do
  -- We are going to ignore refs for now, which we will fill in
  -- by providing all the name ahead of time in the config,
  -- and then parsing in the correct order (+ mutual types)
  parseInlineAbbrev s name <|>
  parseTupleAbbrev s name schemaToTypeDef <|>
  parseArrayAbbrev s name schemaToTypeDef <|>
  (match s with
    | .Object obj => withNewID s (
      -- Try enum first
      if let some enum := obj.enum then
        enumToInductive enum name
      -- Then try oneOf
      else if let some oneOf := obj.oneOf then
        oneOfToInductive oneOf name schemaToTypeDef
      -- Then try anyOf (treated same as oneOf for now)
      else if let some anyOf := obj.anyOf then
        anyOfToInductive anyOf name schemaToTypeDef
      -- Finally try object/structure
      else
        objectToStructure obj name schemaToTypeDef
    )
    | _ => throwWithContext "Cannot convert boolean schema to structure")

/-- Version of schemaToTypeDef for use in mutual blocks.
    Only generates structures and inductives (no abbreviations).
    For schemas that would normally be abbreviations (refs, simple types, arrays),
    generates single-field wrapper structures. -/
partial def schemaToTypeDefMutual (s : JsonSchema.Schema) (name : String)
    : SchemaGen TypeDefinition := withTypeName name do
  match s with
  | .Object obj => withNewID s (
      -- Try enum first
      if let some enum := obj.enum then
        enumToInductive enum name
      -- Then try oneOf
      else if let some oneOf := obj.oneOf then
        oneOfToInductive oneOf name schemaToTypeDefMutual
      -- Then try anyOf (treated same as oneOf for now)
      else if let some anyOf := obj.anyOf then
        anyOfToInductive anyOf name schemaToTypeDefMutual
      -- Then try object/structure
      else if obj.properties.isSome && !(obj.properties.getD #[]).isEmpty then
        objectToStructure obj name schemaToTypeDefMutual
      -- For everything else (refs, simple types, etc.), use wrapper struct
      else
        parseWrapperStruct s name
    )
  | _ => throwWithContext "Cannot convert boolean schema to structure in mutual block"

/-- Format a single TypeDefinition with optional instances based on config -/
def formatTypeDefWithInstances (td : TypeDefinition) (config : Config) : Format :=
  if !config.generateFromJson && !config.generateToJson then
    -- Without instances, just return the type declaration
    td.typeDecl
  else Id.run do
    -- With instances enabled, add custom instances based on config
    let mut instances : Array Format := #[]
    if config.generateFromJson then
      if let some fromImpl := td.fromJsonImpl then
        instances := instances.push fromImpl
    if config.generateToJson then
      if let some toImpl := td.toJsonImpl then
        instances := instances.push toImpl

    -- Only add spacing if we have instances
    if instances.isEmpty then
      return td.typeDecl
    else
      let instanceStr : Format := Std.Format.prefixJoin "\n\n" instances.toList
      return td.typeDecl ++ instanceStr

/-- Generate a mutual block for an SCC with multiple schemas -/
def generateMutualBlock (scc : Array Nat) (namedSchemas : Array SchemaID)
    (ctx : CodeGenContext) : Except String Format := do
  let mut typeDefs : Array TypeDefinition := #[]

  for idx in scc do
    let schemaID := namedSchemas[idx]!
    let schemaAndURI? := ctx.resolver.getSchemaAndURI? schemaID.baseURI schemaID.path
    let (schema, baseURI) ← match schemaAndURI? with
      | some s => .ok s
      | none => .error s!"Schema not found at {schemaID.baseURI} {schemaID.path}"

    let name? := ctx.nameMap.get? schemaID
    let name ← match name? with
      | some n => .ok n
      | none => .error s!"No name found for schema {schemaID.baseURI} {schemaID.path}"

    -- Use schemaToTypeDefMutual to avoid generating abbreviations in mutual blocks
    -- Set both baseURI and currentSchemaID for error reporting
    let typeDef ← (schemaToTypeDefMutual schema name).run {
      ctx with
        baseURI := baseURI
        currentSchemaID := some schemaID
    }
    typeDefs := typeDefs.push typeDef

  -- Build mutual block
  let declsWithInstances := typeDefs.map (formatTypeDefWithInstances · ctx.config)
  .ok ("mutual\n" ++ Std.Format.joinSep declsWithInstances.toList "\n\n" ++ "\nend")

/-- Generate code for all schemas in a Resolver with proper topological ordering -/
def generateAllSchemas (resolver : Resolver) (config : Config := {}) : Except String String := do
  -- Phase 1: Collect and name all schemas
  let nameMap := mkNameMap resolver config

  -- Get all schema IDs and sort them for stable ordering
  let namedSchemas := nameMap.toList.map (·.1) |>.toArray
  let namedSchemas := namedSchemas.qsort (fun a b =>
    let uriCmp := toString a.baseURI < toString b.baseURI
    if toString a.baseURI == toString b.baseURI then
      JsonPointer.toString a.path < JsonPointer.toString b.path
    else uriCmp
  )

  -- Phase 2: Build reference graph
  let refGraph ← buildRefGraph namedSchemas nameMap resolver

  -- Phase 3: Compute SCCs in topological order
  let sccs := findSCCs refGraph

  -- Phase 4: Generate code for each SCC
  let ctx : CodeGenContext := {
    resolver := resolver
    nameMap := nameMap
    config := config
    baseURI := default
  }
  let mut outputs : Array Format := #[]

  for scc in sccs do
    let output ← if scc.size == 1 then
      -- Single schema: standalone definition
      let schemaID := namedSchemas[scc[0]!]!
      let schemaAndURI? := resolver.getSchemaAndURI? schemaID.baseURI schemaID.path
      let (schema, baseURI) ← match schemaAndURI? with
        | some s => .ok s
        | none => .error s!"Schema not found at {schemaID.baseURI} {schemaID.path}"

      let name? := nameMap.get? schemaID
      let name ← match name? with
        | some n => .ok n
        | none => .error s!"No name found for schema {schemaID.baseURI} {schemaID.path}"

      let typeDef ← (schemaToTypeDef schema name).run {
        ctx with
          baseURI := baseURI
          currentSchemaID := some schemaID
      }

      -- Include dependencies
      let allDeps := flattenDependencies typeDef
      let depFormats := allDeps.map (formatTypeDefWithInstances · config)
      let mainFormat := formatTypeDefWithInstances typeDef config
      .ok (Std.Format.joinSep (depFormats ++ [mainFormat]) "\n\n")
    else
      -- Multiple schemas: mutual block
      generateMutualBlock scc namedSchemas ctx

    outputs := outputs.push output

  .ok (Std.Format.joinSep outputs.toList "\n\n" |>.pretty)

/-- Convert schema to TypeDefinition conversion (no definitions) -/
def schemaToFormat (s : JsonSchema.Schema) (typeName : String)
    (config : Config := {}) : Except String Format := do
  let name := config.sanitizeName typeName
  let ctx : CodeGenContext := {
    resolver := Resolver.empty.addSchema s,
    nameMap := .ofList [(⟨default, []⟩, name)]
    config := config
    baseURI := default
  }
  let typeDef ← (schemaToTypeDef s name).run ctx

  -- Flatten all nested dependencies
  let allDeps := flattenDependencies typeDef

  -- Format all dependencies with their instances
  let depFormats := allDeps.map (formatTypeDefWithInstances · config)
  let mainFormat := formatTypeDefWithInstances typeDef config

  -- Prepend dependencies before main definition
  return Std.Format.joinSep (depFormats ++ [mainFormat]) "\n\n"


/-- Convert a single Schema to String (not Format, to simplify) -/
def schemaToString (s : JsonSchema.Schema) (typeName : String)
    (config : Config := {}) : String :=
  match (schemaToFormat s typeName config) with
  | .ok f => f.pretty
  | .error e => s!"ERROR: {e}"


end JsonSchemaCodeGen
