import Lean
import LeanUri
import JsonSchema.Resolving
namespace JsonSchemaCodeGen

open Lean JsonSchema

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
  -- Best-effort keyword avoidance (Lean 4 has extensible syntax, so this is not exhaustive)
  let keywords := [
    -- Core language keywords
    "def", "theorem", "structure", "inductive", "class", "instance", "where",
    "match", "if", "then", "else", "let", "in", "fun", "do", "return",
    -- Control flow and loops
    "for", "while", "repeat", "unless", "break", "continue",
    -- Imports and namespaces
    "import", "open", "namespace", "section", "end", "export",
    -- Modifiers and attributes
    "private", "protected", "partial", "mutual", "axiom", "constant",
    "variable", "universe", "deriving", "extends", "with",
    -- Types and proofs
    "Type", "Prop", "Sort", "forall", "exists",
    -- Pattern matching
    "have", "show", "from", "by", "at",
    -- Other common keywords
    "macro", "syntax", "notation", "prefix", "infix", "postfix",
    "example", "opaque", "noncomputable", "unsafe", "extern",
    "abbrev", "scoped", "local"
  ]
  if keywords.contains result
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
  /-- Whether to generate FromJson instances -/
  generateFromJson : Bool := false
  /-- Whether to generate ToJson instances -/
  generateToJson : Bool := false
  /-- Whether to include the base URI filename in generated type names.
      When true: user.json with definition "Address" → "UserAddress"
      When false: user.json with definition "Address" → "Address" -/
  includeBaseNamePrefix : Bool := false

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

end JsonSchemaCodeGen
