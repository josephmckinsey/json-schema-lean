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

def Test := Unit

instance : FromJson Test where
  fromJson? j := if j == Json.str "3" then .ok () else .error "Could not parse"


def getConstantFromJsonTerm (j : Json) : Format :=
  f!"if j == {reprPrec j 50} then" ++
      .nestD (.line ++ repr (.ok () : Except String Unit)) ++
      (.line ++ "else") ++ .nestD (
        .line ++ repr (.error s!"Could not match constant {repr j}" : Except String Unit))

def getConstantToJsonTerm (j : Json) : Format := repr j

def parseConstant (o : JsonSchema.SchemaObject) :
    Except String TypeDefinition := do
  match o.const with
  | some c => .ok (.mk "Unit" (getConstantFromJsonTerm c) (getConstantToJsonTerm c))
  | none => .error "Could not find constant"

def parseRef (o : JsonSchema.SchemaObject) : Except String TypeDefinition :=
  match o.ref with
  | some _ => .ok { typeDecl := "NotImplemented" }
  | none => .error "Could not find ref"

def parseAnyType (types : Array JsonSchema.JsonType) : Except String TypeDefinition :=
  if types.contains .AnyType then .ok { typeDecl := "Json" } else .error "Could not find any type"

#check (inferInstance : FromJson String).fromJson? 3 <|>
  ((inferInstance : FromJson String).fromJson? 3)

#check (.inl "string" : String ⊕ Int ⊕ Float)


def depthToInlInr (inner : Format) (total : Nat) (current : Nat) : Format :=
  if current == 0 then
    ".inl" ++ .line ++ inner
  else if current + 1 == total then
    Nat.repeat (fun inner => ".inr" ++ .line ++ Std.Format.paren inner) (total - 1) inner
  else
    Nat.repeat (fun inner => ".inr" ++ .line ++ Std.Format.paren inner) current
      (".inl" ++ .line ++ Std.Format.paren inner)

/-- Get the `fromJson? j := {?}` term for a sum of types (not including null) -/
def getFromJsonListSum (xs : List JsonSchema.JsonType) : Format :=
  Std.Format.joinSep (xs.zipIdx.map (fun (x, i) =>
    let inner := s!"(inferInstance : FromJson {jsonTypeToLean x}).fromJson? j"
    let f : Format := .group (.nestD ("(fun x =>" ++ Std.Format.line ++ depthToInlInr "x" xs.length i ++ ")"))
    Std.Format.group (.nestD (f ++ Std.Format.line ++ "<$>" ++ Std.Format.line ++ "(" ++ inner ++ ")"
      ))
  )) (" <|>" ++ .line)

def getToJsonListSum (length : Nat) : Format :=
  .group ("match x with\n" ++ Std.Format.joinSep ((List.range length).map (fun i =>
    let pattern : Format := .group (.nestD (depthToInlInr "x" length i))
    "| " ++ pattern ++ " => toJson x"
  )) "\n")

def Test' := String ⊕ Int

instance : ToJson Test' where
  toJson x := match x with
  | .inl x => toJson x
  | .inr x => toJson x

#check Option.toJson

def parseSimpleType (o : JsonSchema.SchemaObject) : Except String TypeDefinition :=
  parseAnyType o.type <|>
  match (o.type.qsort (lt := fun x y => (compare x y).isLT)).toList with
  -- Type classes can be derived
  | [x] => .ok { typeDecl := jsonTypeToLean x }
  | [.NullType, x] => .ok { typeDecl := "Option " ++ jsonTypeToLean x }
  | [] => .error "Type list is empty"
  -- Type classes can probably not be derived
  | .NullType::xs =>
    .ok {
      typeDecl := "Option (" ++ (String.intercalate " ⊕ " (xs.map jsonTypeToLean)) ++ ")"
      fromJsonImpl := Std.Format.text "Option.fromJson?" ++ .line ++
        Std.Format.paren (getFromJsonListSum xs)
      toJsonImpl := Std.Format.text "@Option.toJson" ++ .line ++ "_" ++
        .line ++ f!"⟨fun x => {getToJsonListSum xs.length}⟩" ++
        .line ++ (Std.Format.text "x"),
    }
  | xs => .ok {
      typeDecl := String.intercalate " ⊕ " (xs.map jsonTypeToLean)
      fromJsonImpl := getFromJsonListSum xs
      toJsonImpl := getToJsonListSum xs.length
  }

/-- Inline types such as String ⊕ Int do not need complicated definitions.
-/
def parseInline (s : JsonSchema.Schema) : Except String TypeDefinition :=
  match s with
  | .Boolean b => pure { typeDecl := getBoolType b }
  | .Object o => do
  isSimple o
  parseRef o <|>
  parseConstant o <|>
  parseSimpleType o

def parseInlineAbbrev (s : JsonSchema.Schema) (name : String) :
    Except String TypeDefinition :=
  parseInline s <&> fun form =>
    {
      typeDecl := s.getDoc ++ (
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

end JsonSchema.CodeGen
