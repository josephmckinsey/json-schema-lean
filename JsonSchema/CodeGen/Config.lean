import Lean
import LeanUri
import JsonSchema.Resolving
namespace JsonSchema.CodeGen

open Lean

/-- A complete type definition including the type declaration and optional JSON instances -/
structure TypeDefinition where
  /-- The main type declaration (structure, inductive, or abbrev) -/
  typeDecl : Std.Format
  /-- Optional FromJson instance implementation -/
  fromJsonImpl : Option Std.Format := none
  /-- Optional ToJson instance implementation -/
  toJsonImpl : Option Std.Format := none
  /-- Nested type definitions that should be prepended before this definition -/
  dependencies : List TypeDefinition := []
  /-- Extra doc comment for use in structures and inductives -/
  extraDocComment : Option Std.Format := none
deriving Inhabited

/-- Default name sanitization: replace invalid characters, handle keywords -/
def defaultSanitizeName (name : String) : String :=
  -- Replace < with "Of" and > with "" to get A<T> → AOfT
  let withOf := name.replace "<" "Of" |>.replace ">" ""
  let cleaned := withOf.toList.map fun c =>
    if c.isAlphanum then c
    else if c == '_' then c
    else '_'
  let result := String.mk cleaned
  -- Basic keyword avoidance (add more as needed)
  if ["def", "theorem", "structure", "inductive", "where", "match", "if", "then", "else"].contains result
  then result ++ "_"
  else if result.isEmpty || result.front.isDigit
  then "t_" ++ result  -- Prepend if starts with digit or empty
  else result

/-- Configuration for code generation -/
structure Config where
  /-- How to sanitize names to valid Lean identifiers -/
  sanitizeName : String → String := defaultSanitizeName
  /-- Indentation string -/
  indent : String := "  "
  /-- Whether to generate FromJson/ToJson instances -/
  generateInstances : Bool := false

/-- Capitalize first letter -/
def capitalize (s : String) : String :=
  if s.isEmpty then s
  else s.take 1 |>.toUpper ++ s.drop 1

/-- Identifies a schema by its canonical URI and path -/
structure SchemaID where
  baseURI : LeanUri.URI
  path : List String
deriving BEq, Hashable, Inhabited

instance : ToString SchemaID where
  toString id := (toString id.baseURI) ++ "#" ++ JsonPointer.toString id.path

/-- Extended code generation context with reference support -/
structure CodeGenContext where
  /-- Resolver for looking up schemas -/
  resolver : Resolver
  /-- Mapping from SchemaID to generated type name -/
  nameMap : Std.HashMap SchemaID String
  /-- Configuration -/
  config : Config
  /-- Base URI which gets updated as we traverse -/
  baseURI : LeanUri.URI

abbrev SchemaGen := ReaderT CodeGenContext (Except String ·)

def SchemaGen.run (gen : SchemaGen α) (ctx : CodeGenContext)
    : Except String α := ReaderT.run gen ctx

def SchemaGen.noCtxRun? (gen : SchemaGen α) : Except String α :=
  gen.run ⟨.empty, .emptyWithCapacity, {}, default⟩

def withNewID (s : Schema)
    (g : SchemaGen α) : SchemaGen α :=
  withReader (fun ctx => {
    ctx with baseURI := (s.getID? ctx.baseURI).getD ctx.baseURI
  }) g

def getConfig : SchemaGen Config := read <&> CodeGenContext.config

def getURI : SchemaGen LeanUri.URI := read <&> CodeGenContext.baseURI

def getRefNameFromID (id : SchemaID) : SchemaGen (Option String) := read <&> fun ctx =>
  ctx.nameMap.get? id

end JsonSchema.CodeGen
