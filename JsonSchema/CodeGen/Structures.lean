import JsonSchema.Schema
import JsonSchema.CodeGen.Config
import Lean

namespace JsonSchema.CodeGen

open Lean

/-- TODO: Convert an object schema to a structure definition

    This will handle:
    - properties → struct fields
    - required vs optional fields
    - nested objects
    - doc comments from descriptions
-/
def objectToStructure (obj : JsonSchema.SchemaObject) (typeName : String)
    (config : Config := {}) : Except String Format :=
  .error "Not yet implemented: objectToStructure"

end JsonSchema.CodeGen
