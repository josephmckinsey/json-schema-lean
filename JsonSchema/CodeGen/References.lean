import JsonSchema.Schema
import JsonSchema.Resolving
import JsonSchema.CodeGen.Config
import Lean

namespace JsonSchema.CodeGen

open Lean

def resolveRefToName (ref : LeanUri.URI ⊕ LeanUri.RelativeRef) : SchemaGen String := do
  let resolver ← CodeGenContext.resolver <$> read
  let (rootURI, path) := resolver.resolvePath ((← get).resolveURIorRef ref)
  let name? ← read <&> fun ctx => ctx.nameMap.get? ⟨rootURI, path⟩
  match name? with
  | some name => pure name
  | none => .error s!"Reference {←get} -> {rootURI} {path} could not be found."

/-- Populate nameMap from resolver.

  Iterates through definitions recurisvely, assigns unique names to
  all schemas reachable through rootURIs as well as through subdefinitions.
-/
def mkNameMap (r : Resolver) : Std.HashMap SchemaID String := sorry

end JsonSchema.CodeGen
