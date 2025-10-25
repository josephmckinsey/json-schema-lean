# JSON-Schema Lean

## Description

An implementation of JSON Schema Draft 7 in Lean (GSoC 2024)

**Current Status**: 94.9% Draft 7 compliance (241 of 254 test cases passing)

## Build

```sh
lake build
```

### Docker Build

Build docker image:

```sh
docker build -f Dockerfile -t localhost/lean-jsonschema:latest .
# Or with Podman
podman build -f Dockerfile -t localhost/lean-jsonschema:latest .
```

## Code Generation

Generate Lean type definitions from JSON Schema files:

```bash
# Generate to stdout
lake exe schemaToLean schema.json

# Generate to file
lake exe schemaToLean schema.json output.lean
```

The code generator creates:
- Type definitions (structures, inductives, or type abbreviations)
- `FromJson` and `ToJson` instances
- Doc comments from schema descriptions
- Proper handling of references, definitions, and circular types

**Example:**

Input (`person.json`):
```json
{
  "type": "object",
  "title": "Person",
  "description": "A person object",
  "required": ["name", "age"],
  "properties": {
    "name": { "type": "string", "description": "The person's name" },
    "age": { "type": "integer", "description": "The person's age" },
    "email": { "type": "string" }
  }
}
```

Output:
```lean
import Lean.Data.Json

open Lean

/-- A person object -/
structure Person where
  /-- The person's name -/
  name : String
  /-- The person's age -/
  age : Int
  email : Option String

instance : FromJson Person where
  fromJson? j := do
    let name ← fromJson? (j.getObjValD "name")
    let age ← fromJson? (j.getObjValD "age")
    let email ← fromJson? (j.getObjValD "email")
    .ok { name, age, email }

instance : ToJson Person where
  toJson s := Json.mkObj [("name", toJson s.name), ("age", toJson s.age), ("email", toJson s.email)]
```

### Testing Code Generation

```bash
# Test all schemas in test-schemas/
./testCodeGen.sh
```

### Known Issues

The code generator works for most schemas but has some known limitations:

1. **FromJson/ToJson instances may not compile**: Generated FromJson/ToJson instances work for many cases but may produce compilation errors for complex schemas with deeply nested types or certain edge cases.

2. **Doc comments for inductives**: Documentation comments from schema descriptions are not always propagated correctly through inductive type definitions, particularly for nested variants.

## Testing

There are some tests in `lake test`, but most validation tests rely on `bowtie`:

Install [bowtie](https://docs.bowtie.report/en/stable/).

Run tests:

```sh
# Run core passing tests
./test.sh

# Test specific keyword
bowtie suite -i localhost/lean-jsonschema:latest \
  https://github.com/json-schema-org/JSON-Schema-Test-Suite/blob/main/tests/draft7/const.json \
  | bowtie summary --show failures

# Run full Draft 7 test suite
bowtie suite -i localhost/lean-jsonschema:latest \
  https://github.com/json-schema-org/JSON-Schema-Test-Suite/tree/main/tests/draft7 \
  | bowtie summary
```

## Design

For integration of this implementation with **Bowtie**, the project is (currently) divided into two main parts:

- **Main** : The entry point of the harness module, which invokes the harness repl.
- **Harness** : Command reader and dispatcher, handles stdin and stdout.
- **Implementation** : JSON Schema validation implementation in Lean.

### Implementation

Project Structure:

```
├── Dockerfile            # Dockerfile for Bowtie image
├── CodeGenCLI.lean       # CLI for JSON Schema to Lean code generation
├── Harness/              # Bowtie interface
│   ├── Command.lean
│   └── Harness.lean
├── JsonSchema/
│   ├── Error.lean        # Error types
│   ├── Format.lean       # Format validators (not yet integrated)
│   ├── Loader.lean       # Remote schema loading (TODO)
│   ├── PointerFragment.lean  # RFC 6901 JSON Pointer navigation
│   ├── Resolving.lean    # $ref/$id resolution and loop detection
│   ├── Schema.lean       # Schema data structures
│   ├── SchemaPointer.lean # Schema pointer utilities
│   └── Validation.lean   # Core validation logic
├── JsonSchemaCodeGen/    # Code generation from schemas
│   ├── CodeGen.lean      # Main entry point
│   ├── Config.lean       # Configuration
│   ├── Inductives.lean   # Enum/oneOf/anyOf generation
│   ├── References.lean   # $ref resolution for codegen
│   ├── Structures.lean   # Object/structure generation
│   └── Types.lean        # Simple type handling
├── JsonSchemaCodeGenTesting/  # Code generation tests
│   ├── IntegrationTests.lean
│   ├── ReferencesTests.lean
│   ├── Tests.lean
│   └── TestUtils.lean
├── JsonSchemaTesting/    # Validation tests
├── Main.lean             # Entry point for bowtie
├── TestRunner.lean       # Test runner for all tests
├── test.sh               # Validation test script (Bowtie)
├── testCodeGen.sh        # Code generation test script
├── test-schemas/         # Example JSON schemas for testing
├── lakefile.toml
└── lean-toolchain
```

#### Core Modules

**Harness**: Handles interaction between validator and Bowtie test harness
- Implements IHOP protocol (start, dialect, run, stop commands)
- Reads JSON commands from stdin, dispatches to validator, returns results to stdout

**JsonSchema/Schema.lean**: Schema data structure definitions
- `Schema`: Either `Boolean` or `Object SchemaObject`
- `SchemaObject`: Contains all JSON Schema keywords
- JSON parsing and serialization

**JsonSchema/Validation.lean**: Core validation logic
- Individual `validate*` functions for each keyword
- `validateObject`: Orchestrates all validations
- `validateWithResolver`: Main entry point with fuel-based recursion limiting

**JsonSchema/Resolving.lean**: Reference resolution
- `Resolver`: Registry of schemas by URI
- Handles `$ref`, `$id`, and `definitions`
- Loop detection via dependency graph analysis

**JsonSchema/PointerFragment.lean**: JSON Pointer (RFC 6901)
- Parses pointer strings like `/definitions/foo`
- Navigates schema structures for fragment resolution

## Usage Examples

### Minimal Example

```lean
import JsonSchema.Validation
import Lean

open Lean
open JsonSchema

-- Create a simple schema from JSON
def minimalSchema : Schema :=
  (fromJson? (Json.mkObj [("type", Json.str "string")])).toOption.get!

-- Validate data against the schema
#eval validate minimalSchema (Json.str "hello")  -- Except.ok ()
#eval validate minimalSchema (Json.num 42)       -- Error: wrong type
```

### Example with Resolver and $ref

```lean
import JsonSchema.Validation
import JsonSchema.Resolving
import Lean

open Lean
open JsonSchema

-- Schema with definitions and references
def schemaWithRefsJson : Json := Json.mkObj [
  ("$id", Json.str "https://example.com/person.json"),
  ("definitions", Json.mkObj [
    ("address", Json.mkObj [
      ("type", Json.str "object"),
      ("properties", Json.mkObj [
        ("street", Json.mkObj [("type", Json.str "string")]),
        ("city", Json.mkObj [("type", Json.str "string")])
      ]),
      ("required", Json.arr #[Json.str "street", Json.str "city"])
    ])
  ]),
  ("type", Json.str "object"),
  ("properties", Json.mkObj [
    ("name", Json.mkObj [("type", Json.str "string")]),
    ("home", Json.mkObj [("$ref", Json.str "#/definitions/address")]),
    ("work", Json.mkObj [("$ref", Json.str "#/definitions/address")])
  ]),
  ("required", Json.arr #[Json.str "name"])
]

def schemaWithRefs : Schema :=
  (fromJson? schemaWithRefsJson).toOption.get!

-- Create a resolver and register the schema
def resolver : Resolver :=
  Resolver.addSchema {} schemaWithRefs (LeanUri.URI.encode "https" "example.com" "/person.json")

-- Valid person with addresses
def validPersonData : Json := Json.mkObj [
  ("name", Json.str "Alice"),
  ("home", Json.mkObj [
    ("street", Json.str "123 Main St"),
    ("city", Json.str "Springfield")
  ]),
  ("work", Json.mkObj [
    ("street", Json.str "456 Office Blvd"),
    ("city", Json.str "Shelbyville")
  ])
]

-- Validate using the resolver
#eval validateWithResolver resolver default schemaWithRefs validPersonData
-- Success: Except.ok ()
```

See [JsonSchemaTesting/Examples.lean](JsonSchemaTesting/Examples.lean) for more examples.

## TODO List

- [x] Containerize (Docker Image)
- [x] Separated Json Schema validator and Harness module
- [x] Integrate with **Bowtie**
  - [x] Basic (run / start / dialect / stop) command dispatcher
  - [x] Read and run tests, return results
- [x] Add basic supports for JSON-Schema validation
- [ ] Complete keywords (Draft-7)
  - [x] type
  - [x] enum
  - [x] const
  - [x] minLength
  - [x] maxLength
  - [x] pattern
  - [x] minimum
  - [x] maximum
  - [x] exclusiveMinimum
  - [x] exclusiveMaximum
  - [x] required
  - [x] uniqueItems
  - [x] multipleOf
  - [x] allOf
  - [x] anyOf
  - [x] oneOf
  - [x] not
  - [x] items
  - [x] contains
  - [x] maxItems
  - [x] minItems
  - [x] maxProperties
  - [x] minProperties
  - [x] properties
  - [x] patternProperties
  - [x] additionalItems
  - [x] additionalProperties
  - [x] propertyNames
  - [x] dependencies
  - [x] if / then / else
  - [x] $ref / $id / definitions
- [ ] Load schema (and refs) from a file with file:// URI resolution
- [ ] Remote reference loading (i.e. http, https should load either beforehand or "on-demand")
- [ ] Draft 2019-09 support
- [ ] Draft 2020-12 support
- [ ] Docs

### Extra goodies

- [ ] Proofs of termination/correctness
- [x] Compile JSON Schema to Lean types like datamodel-code-generator (see Code Generation section)
  - [x] CLI tool (`schemaToLean`)
  - [x] Structures, inductives, enums
  - [x] FromJson/ToJson instances
  - [x] Reference resolution and topological ordering
  - [x] Circular/mutual type support
  - [x] Array item type handling
  - [x] Tuple type handling
- [ ] Create JSON Schema from Lean types
