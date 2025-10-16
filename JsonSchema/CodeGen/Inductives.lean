import JsonSchema.Schema
import JsonSchema.CodeGen.Config
import Lean

namespace JsonSchema.CodeGen

open Lean

/-- TODO: Convert an enum schema to an inductive type

    This will handle:
    - enum values → constructors
    - Name generation from values
-/
def enumToInductive (enum : Array Json) (typeName : String)
    (config : Config := {}) : Except String Format :=
  .error "Not yet implemented: enumToInductive"

/-- TODO: Convert a oneOf schema to an inductive type

    This will handle:
    - oneOf variants → constructors with payloads
    - Case naming
-/
def oneOfToInductive (variants : Array JsonSchema.Schema) (typeName : String)
    (config : Config := {}) : Except String Format :=
  .error "Not yet implemented: oneOfToInductive"

/-- TODO: Convert an anyOf schema to an inductive type

    This is more complex as anyOf allows overlapping types.
    May need to defer this for later.
-/
def anyOfToInductive (variants : Array JsonSchema.Schema) (typeName : String)
    (config : Config := {}) : Except String Format :=
  .error "Not yet implemented: anyOfToInductive"

end JsonSchema.CodeGen
