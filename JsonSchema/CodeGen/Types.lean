import JsonSchema.Schema
import JsonSchema.CodeGen.Config
import Lean

namespace JsonSchema.CodeGen

open Lean

/-- Create a doc comment from a description -/
def mkDocComment (desc : String) : Format :=
  .text s!"/-- {desc} -/"

/-- Get the Lean type name for a single JsonType -/
def jsonTypeToLean : JsonSchema.JsonType → String
  | .StringType => "String"
  | .IntegerType => "Int"
  | .NumberType => "Float"
  | .BooleanType => "Bool"
  | .NullType => "Unit"
  | .ObjectType => "Json"  -- Generic fallback
  | .ArrayType => "Array Json"  -- Generic fallback
  | .AnyType => "Json"

/-- Extract type name from a schema (from title or ref) -/
def extractTypeName? (s : JsonSchema.Schema) : Option String :=
  match s with
  | .Boolean _ => none
  | .Object obj =>
    obj.title <|> (obj.ref >>= fun ref =>
      match ref with
      | .inr relRef =>
        -- Extract last component from #/definitions/TypeName
        let parts := relRef.fragment.getD "" |>.splitOn "/"
        parts.getLast?
      | .inl _ => none
    )

/-- Determine if a schema represents an optional type (has null in types) -/
def hasNullType (types : Array JsonSchema.JsonType) : Bool :=
  types.contains .NullType

/-- Get non-null types from type array -/
def nonNullTypes (types : Array JsonSchema.JsonType) : Array JsonSchema.JsonType :=
  types.filter (· != .NullType)

def getBoolType (b : Bool) : String :=
  if b then "Unit" else "Empty"

def isSimple (o : JsonSchema.SchemaObject) : Except String Unit := do
  if o.const.isSome then return -- constants are always simple
  if o.ref.isSome then return -- Refs are always simple
  if o.allOf.isSome then .error "allOf is not simple"
  if o.anyOf.isSome then .error "anyOf is not simple"
  if o.oneOf.isSome then .error "oneOf is not simple"
  if o.type.contains .ObjectType then .error "object type possible"
  -- These don't necessary make a type complex, but it
  -- probably should be a struct or inductive if these exist.
  if o.contains.isSome then .error "contains is not simple"
  if o.not.isSome then .error "not is not simple"
  if o.ifSchema.isSome then .error "if is not simple"
  if o.thenSchema.isSome then .error "then is not simple"
  if o.elseSchema.isSome then .error "else is not simple"
  if o.dependencies.isSome then .error "dependencies is not simple"
  -- These can't reay be inlined if they exist
  if o.enum.isSome then .error "enum is not simple"
  if o.pattern.isSome then .error "pattern is not simple"

partial def jsonRepr (j : Json) (prec : Nat) : Format :=
  let subRepr : Repr Json := ⟨jsonRepr⟩
  .group <| match j with
  | .arr x => Format.nest 2  <| Repr.addAppParen (.text "Json.arr" ++ .line ++
    (@reprPrec _ (@Array.instRepr _ subRepr) x max_prec)) prec
  | .obj kvPairs => Format.nest 2 <| Repr.addAppParen (.text "Json.obj" ++ .line ++
    (@reprPrec _ (@Std.TreeMap.Raw.instRepr _ _ _ _ subRepr) kvPairs max_prec)) prec
  | .str s => Format.nest 2 <| Repr.addAppParen ("Json.str" ++ .line ++ reprPrec s max_prec) prec
  | .num n => Format.nest 2 <| Repr.addAppParen ("Json.num" ++ .line ++ reprPrec n max_prec) prec
  | .null => "Json.null"
  | .bool b => Repr.addAppParen ("Json.bool " ++ repr b) prec

local instance : Repr Json := ⟨jsonRepr⟩

def parseConstant (o : JsonSchema.SchemaObject) :
    Except String (String × Format) := do
  match o.const with
  | some c => .ok ("Unit", repr c)
  | none => .error "Could not find constant"

def parseRef (o : JsonSchema.SchemaObject) : Except String String :=
  match o.ref with
  | some _ => .ok "NotImplemented"
  | none => .error "Could not find ref"

def parseAnyType (types : Array JsonSchema.JsonType) : Except String String :=
  if types.contains .AnyType then .ok "Json" else .error "Could not find any type"

def parseSimpleType (o : JsonSchema.SchemaObject) : Except String String :=
  parseAnyType o.type <|>
  match (o.type.qsort (lt := fun x y => (compare x y).isLT)).toList with
  | [x] => .ok (jsonTypeToLean x)
  | [.NullType, x] => .ok ("Option " ++ jsonTypeToLean x)
  | [] => .error "Type list is empty"
  | .NullType::xs =>
    .ok ("Option (" ++ (String.intercalate " ⊕ " (xs.map jsonTypeToLean)) ++ ")")
  | xs => .ok (String.intercalate " ⊕ " (xs.map jsonTypeToLean))

/-- Inline types such as String ⊕ Int do not need complicated definitions.
-/
def parseInline (s : JsonSchema.Schema) : Except String Format :=
  match s with
  | .Boolean b => pure (getBoolType b)
  | .Object o => do
  isSimple o
  parseRef o <|>
  (parseConstant o <&> Prod.fst) <|>
  parseSimpleType o

def parseInlineAbbrev (s : JsonSchema.Schema) (name : String) : Except String Format :=
  parseInline s <&> fun form =>
    .group <| .nest 2 (f!"abbrev {name} :=" ++ .line ++ form)

end JsonSchema.CodeGen
