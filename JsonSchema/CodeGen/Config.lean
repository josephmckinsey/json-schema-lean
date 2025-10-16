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

end JsonSchema.CodeGen
