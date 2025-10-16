import JsonSchema.Schema
import JsonSchema.Resolving
import JsonSchema.CodeGen.Config
import Lean

/-! # This is NOT READY. -/
namespace JsonSchema.CodeGen

open Lean

/-- TODO: Resolve a $ref to its definition

    This will handle:
    - Looking up #/definitions/TypeName
    - Resolving the reference using the Resolver
    - Name sanitization
    - Tracking already-resolved schemas to detect cycles
-/
def resolveRef (ref : LeanUri.URI ⊕ LeanUri.RelativeRef)
    (resolver : JsonSchema.Resolver)
    (alreadyResolved : Array String := #[])
    (config : Config := {}) : Except String String :=
  .error "Not yet implemented: resolveRef"

/-- TODO: Extract and sort all definitions for code generation

    This will handle:
    - Extracting definitions from a schema
    - Using the Resolver to follow references
    - Topological sorting to handle dependencies
    - Detecting circular references
-/
def extractDefinitions (schema : JsonSchema.Schema)
    (resolver : JsonSchema.Resolver)
    (config : Config := {}) : Except String (Array (String × JsonSchema.Schema)) :=
  .error "Not yet implemented: extractDefinitions"

/-- Context for code generation that tracks what's been generated -/
structure CodeGenContext where
  /-- Resolver for looking up $ref and definitions -/
  resolver : JsonSchema.Resolver
  /-- Names of schemas already generated (to detect cycles) -/
  generated : Array String := #[]
  /-- Configuration -/
  config : Config := {}

end JsonSchema.CodeGen
