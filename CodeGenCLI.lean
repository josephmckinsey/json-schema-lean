import JsonSchema.Schema
import JsonSchema.Resolving
import JsonSchemaCodeGen
import Lean.Data.Json

/-!
# JSON Schema to Lean Code Generator CLI

This executable takes a JSON Schema file and generates Lean code.

Usage:
  json-schema-codegen <input.json> [output.lean]

If output file is not specified, prints to stdout.
-/

open JsonSchema JsonSchemaCodeGen Lean

/-- Read JSON file and parse it as a Schema -/
def readSchemaFile (path : String) : IO (Except String Schema) := do
  let contents ← IO.FS.readFile path
  match Lean.Json.parse contents with
  | .error e => return .error s!"Failed to parse JSON: {e}"
  | .ok json =>
    match fromJson? json with
    | .error e => return .error s!"Failed to parse Schema: {e}"
    | .ok schema => return .ok schema

/-- Add necessary imports to generated code -/
def addImports (generatedCode : String) : String :=
  "import Lean.Data.Json\n\nopen Lean (Json)\n\n" ++ generatedCode

/-- Write generated code to file or stdout -/
def writeOutput (content : String) (outputPath? : Option String) : IO Unit := do
  let fullContent := addImports content
  match outputPath? with
  | none => IO.print fullContent
  | some path => IO.FS.writeFile path fullContent

/-- Main CLI entry point -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [] => do
    IO.eprintln "Usage: json-schema-codegen <input.json> [output.lean]"
    IO.eprintln ""
    IO.eprintln "Generates Lean code from a JSON Schema file."
    IO.eprintln "If output file is not specified, prints to stdout."
    return 1
  | [inputPath] => do
    -- Read and parse schema
    let schemaResult ← readSchemaFile inputPath
    match schemaResult with
    | .error e => do
      IO.eprintln s!"Error: {e}"
      return 1
    | .ok schema => do
      -- Create resolver with the schema
      let baseURI : LeanUri.URI := ⟨"file", none, inputPath, none, none⟩
      let resolver := Resolver.empty.addSchema schema baseURI

      -- Generate code without instances by default
      let config : Config := { generateFromJson := false, generateToJson := false }
      match generateAllSchemas resolver config with
      | .error e => do
        IO.eprintln s!"Code generation error: {e}"
        return 1
      | .ok output => do
        writeOutput output none
        return 0
  | [inputPath, outputPath] => do
    -- Read and parse schema
    let schemaResult ← readSchemaFile inputPath
    match schemaResult with
    | .error e => do
      IO.eprintln s!"Error: {e}"
      return 1
    | .ok schema => do
      -- Create resolver with the schema
      let baseURI : LeanUri.URI := ⟨"file", none, inputPath, none, none⟩
      let resolver := Resolver.empty.addSchema schema baseURI

      -- Generate code without instances by default
      let config : Config := { generateFromJson := false, generateToJson := false }
      match generateAllSchemas resolver config with
      | .error e => do
        IO.eprintln s!"Code generation error: {e}"
        return 1
      | .ok output => do
        writeOutput output (some outputPath)
        IO.println s!"Generated code written to {outputPath}"
        return 0
  | _ => do
    IO.eprintln "Error: Too many arguments"
    IO.eprintln "Usage: json-schema-codegen <input.json> [output.lean]"
    return 1
