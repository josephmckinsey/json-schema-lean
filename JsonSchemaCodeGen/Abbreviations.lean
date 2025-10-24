import JsonSchema.Schema
import JsonSchemaCodeGen.Config
import JsonSchemaCodeGen.References
import JsonSchemaCodeGen.InlineTypes
import Lean

namespace JsonSchemaCodeGen

open Lean JsonSchema

def parseInlineAbbrev (s : JsonSchema.Schema) (name : String)
    : SchemaGen TypeDefinition :=
  parseInline s <&> fun form =>
    let combined := combineDocStrings s.getDocString form.extraDocComment
    let docComment := if combined.isEmpty then .nil else mkDocComment combined ++ .line
    {
      typeDecl := docComment ++ (
        Std.Format.group <|
          .nest 2 (
            f!"abbrev {name} :=" ++ .line ++ form.typeDecl
            ))
      fromJsonImpl := form.fromJsonImpl <&> fun fromJsonImpl =>
        .nestD ("instance : FromJson {name} where\n" ++
          .group (.nestD "fromJson? j :=" ++ .line ++ fromJsonImpl)
        )
      toJsonImpl := form.fromJsonImpl <&> fun fromJsonImpl =>
        .nestD ("instance : ToJson {name} where\n" ++
          .group (.nestD "toJson x :=" ++ .line ++ fromJsonImpl)
        )
    }

end JsonSchemaCodeGen
