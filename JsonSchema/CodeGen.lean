import JsonSchema.Schema
import JsonSchema.Validation
import JsonSchema.CodeGen.Config
import JsonSchema.CodeGen.Types
import JsonSchema.CodeGen.Structures
import JsonSchema.CodeGen.Inductives
import JsonSchema.CodeGen.References

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

namespace JsonSchema.CodeGen

open Lean

/-- Main schema to TypeDefinition conversion -/
def schemaToTypeDef (s : JsonSchema.Schema) (name : String)
    (config : Config := {}) : Except String TypeDefinition := do
  -- We are going to ignore refs for now, which we will fill in
  -- by providing all the name ahead of time in the config,
  -- and then parsing in the correct order (+ mutual types)
  parseInlineAbbrev s name

/-- Main schema to TypeDefinition conversion -/
def schemaToFormat (s : JsonSchema.Schema) (typeName : String)
    (config : Config := {}) : Except String Format := do
  let name := config.sanitizeName typeName
  let typeDef ← schemaToTypeDef s name config
  if config.generateInstances then
    let mut deriveInfo : Array Format := #[]
    let mut instances : Array Format := #[]
    if let some fromImpl := typeDef.fromJsonImpl then
      instances := instances.push fromImpl
    else
      deriveInfo := deriveInfo.push "FromJson"
    if let some toImpl := typeDef.toJsonImpl then
      instances := instances.push toImpl
      deriveInfo := deriveInfo.push "FromJson"
    let deriveStr : Format := if deriveInfo.isEmpty then
      .nil
    else
      .group (.nestD (
        "deriving " ++ Std.Format.joinSep deriveInfo.toList ("," ++ .line)
      ))
    let instanceStr : Format := Std.Format.prefixJoin "\n" instances.toList

    return typeDef.typeDecl ++ deriveStr ++ instanceStr
  return typeDef.typeDecl


/-- Main function to convert a Schema to String (not Format, to simplify) -/
def schemaToString (s : JsonSchema.Schema) (typeName : String)
    (config : Config := {}) : String :=
  match (schemaToFormat s typeName config) with
  | .ok f => f.pretty
  | .error e => s!"ERROR: {e}"

end JsonSchema.CodeGen
