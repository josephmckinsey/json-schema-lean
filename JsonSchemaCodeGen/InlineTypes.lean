import JsonSchema.Schema
import JsonSchemaCodeGen.Config
import JsonSchemaCodeGen.References
import Lean

namespace JsonSchemaCodeGen

open Lean JsonSchema

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
  if o.items.isSome then .error "items array is not simple"
  -- Objects with properties are not simple (need to be structures)
  -- But objects with no properties can fall back to Json
  if o.type.contains .ObjectType && (o.properties.getD #[] |>.isEmpty |>.not) then
    .error "object type possible"
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

scoped instance : Repr Json := ⟨jsonRepr⟩

def getConstantFromJsonTerm (j : Json) : Format :=
  f!"if j == {reprPrec j 50} then" ++
      .nestD (.line ++ repr (.ok () : Except String Unit)) ++
      (.line ++ "else") ++ .nestD (
        .line ++ repr (.error s!"Could not match constant {repr j}" : Except String Unit))

def getConstantToJsonTerm (j : Json) : Format := repr j

def parseConstant (o : JsonSchema.SchemaObject) : Except String TypeDefinition := do
  match o.const with
  | some c => .ok {
    typeDecl := "Unit"
    fromJsonImpl := getConstantFromJsonTerm c
    toJsonImpl := getConstantToJsonTerm c
  }
  | none => .error "Could not find constant"

def parseRef (o : JsonSchema.SchemaObject) : SchemaGen TypeDefinition :=
  match o.ref with
  | some ref => resolveRefToName ref <&> fun name => { typeDecl := name }
  | none => .error "Could not find ref"

def parseAnyType (types : Array JsonSchema.JsonType) : Except String TypeDefinition :=
  if types.contains .AnyType then .ok { typeDecl := "Json" }
  else .error "Could not find any type"

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

def parseSimpleType (o : JsonSchema.SchemaObject) (prec : Nat := 0) : Except String TypeDefinition :=
  parseAnyType o.type <|>
  match (o.type.qsort (lt := fun x y => (compare x y).isLT)).toList with
  -- Special case: null type needs custom FromJson/ToJson instances
  | [.NullType] => .ok {
    typeDecl := "Unit"
    fromJsonImpl := "if j == Json.null then .ok () else .error s!\"Expected null, got {j}\""
    toJsonImpl := "Json.null"
  }
  -- Type classes can be derived for other single types
  | [x] => .ok { typeDecl := jsonTypeToLean x }
  | [.NullType, x] =>
    let inner := jsonTypeToLean x
    let typeDecl := if prec >= max_prec then ("(Option " ++ inner ++ ")") else "Option " ++ inner
    .ok { typeDecl := typeDecl }
  | [] => .error "Type list is empty"
  -- Type classes can probably not be derived
  | .NullType::xs =>
    let sumType := String.intercalate " ⊕ " (xs.map jsonTypeToLean)
    let typeDecl := if prec >= max_prec then ("(Option (" ++ sumType ++ "))") else "Option (" ++ sumType ++ ")"
    .ok {
      typeDecl := typeDecl
      fromJsonImpl := Std.Format.text "Option.some" ++ .line ++ "<$>" ++ .line ++
        Std.Format.paren (getFromJsonListSum xs)
      toJsonImpl := Std.Format.text "@Option.toJson" ++ .line ++ "_" ++
        .line ++ f!"⟨fun x => {getToJsonListSum xs.length}⟩" ++
        .line ++ (Std.Format.text "x"),
    }
  | xs =>
    let sumType := String.intercalate " ⊕ " (xs.map jsonTypeToLean)
    -- ⊕ has precedence 30, so parenthesize if context has precedence > 30
    let typeDecl := if prec > 30 then "(" ++ sumType ++ ")" else sumType
    .ok {
      typeDecl := typeDecl
      fromJsonImpl := getFromJsonListSum xs
      toJsonImpl := getToJsonListSum xs.length
    }

/-- Try to parse anyOf as an inlineable sum type.
    This succeeds if all variants can be parsed with the recurse function. -/
def parseInlineableAnyOf (variants : Array JsonSchema.Schema)
    (recurse : JsonSchema.Schema → Nat → SchemaGen TypeDefinition)
    (prec : Nat := 0) : SchemaGen TypeDefinition := do
  -- Try to parse each variant as an inline type, collecting descriptions
  let mut typeDefsList : List TypeDefinition := []
  let mut descriptionList : List (Option String) := []
  for variant in variants do
    let typeDef ← recurse variant max_prec
    typeDefsList := typeDef :: typeDefsList
    -- Extract description from variant schema
    let desc := match variant with
      | .Boolean _ => none
      | .Object obj => obj.description
    descriptionList := desc :: descriptionList

  let typeDefs := typeDefsList.reverse
  let descriptions := descriptionList.reverse

  -- Build sum type from all variant type declarations
  let sumType := String.intercalate " ⊕ " (typeDefs.map (·.typeDecl.pretty))
  -- ⊕ has precedence 30, so parenthesize if context has precedence > 30
  let typeDecl := if prec > 30 then "(" ++ sumType ++ ")" else sumType

  -- Build FromJson instance that tries each variant in order
  let fromJsonCases := typeDefs.zipIdx.map fun (typeDef, idx) =>
    let inner := match typeDef.fromJsonImpl with
      | some customParser => customParser
      | none => "fromJson? j"
    let wrapper : Format := Std.Format.group (Std.Format.nestD ("(fun x =>" ++ Std.Format.line ++ depthToInlInr "x" typeDefs.length idx ++ ")"))
    Std.Format.group (Std.Format.nestD (wrapper ++ Std.Format.line ++ "<$>" ++ Std.Format.line ++ "(" ++ inner ++ ")"))
  let fromJsonImpl := Std.Format.joinSep fromJsonCases (" <|>" ++ Std.Format.line)

  -- Build ToJson instance that matches on the sum type
  let toJsonCases : List Format := typeDefs.zipIdx.map fun (typeDef, idx) =>
    let pattern : Format := Std.Format.group (Std.Format.nestD (depthToInlInr "x" typeDefs.length idx))
    let serializer := match typeDef.toJsonImpl with
      | some customToJson => customToJson
      | none => "toJson x"
    "| " ++ pattern ++ " =>" ++ .group (.nestD (.line ++ serializer))
  let toJsonImpl := Std.Format.group ("match x with\n" ++ Std.Format.joinSep toJsonCases "\n")

  -- Only create extraDocComment if there are actual descriptions
  let nonEmptyDescs := descriptions.filterMap (fun desc => desc.filter (!·.isEmpty))
  let extraDocComment := if nonEmptyDescs.isEmpty then none
    else some (Std.Format.joinSep (nonEmptyDescs.map Std.Format.text) .line)

  pure {
    typeDecl := typeDecl
    fromJsonImpl := fromJsonImpl
    toJsonImpl := toJsonImpl
    extraDocComment := extraDocComment
  }

/-- Try to parse oneOf as an inlineable sum type.
    For inlining purposes, oneOf is treated the same as anyOf. -/
def parseInlineableOneOf (variants : Array JsonSchema.Schema)
    (recurse : JsonSchema.Schema → Nat → SchemaGen TypeDefinition)
    (prec : Nat := 0) : SchemaGen TypeDefinition :=
  parseInlineableAnyOf variants recurse prec

/-- Try to parse a homogeneous array where the item type is inlineable.

    This handles: {"type": "array", "items": simpleSchema} → Array Type
    Only succeeds if the item schema can be parsed inline.
-/
def parseInlineableArray (itemSchema : JsonSchema.Schema)
    (recurse : JsonSchema.Schema → Nat → SchemaGen TypeDefinition)
    (prec : Nat := 0) : SchemaGen TypeDefinition := do
  -- Try to parse the item type inline
  let itemTypeDef ← recurse itemSchema max_prec

  -- Build the array type
  let typeDecl := if prec >= max_prec then
    "(Array " ++ itemTypeDef.typeDecl ++ ")"
  else
    "Array " ++ itemTypeDef.typeDecl

  -- Build FromJson instance if item has custom parser
  let fromJsonImpl := itemTypeDef.fromJsonImpl.map fun itemFromJson =>
    Std.Format.text "Array.fromJson?" ++ .line ++
      Std.Format.paren itemFromJson

  -- Build ToJson instance if item has custom serializer
  let toJsonImpl := itemTypeDef.toJsonImpl.map fun itemToJson =>
    Std.Format.text "@Array.toJson" ++ .line ++ "_" ++
      .line ++ "⟨fun x => " ++ itemToJson ++ "⟩" ++
      .line ++ Std.Format.text "x"

  pure {
    typeDecl := typeDecl
    fromJsonImpl := fromJsonImpl
    toJsonImpl := toJsonImpl
    dependencies := itemTypeDef.dependencies
    extraDocComment := itemTypeDef.extraDocComment
  }

def buildTupleFormat (vars : List Format) : Format :=
  match vars with
  | [] => "()"
  | [v] => v
  | vars => "(" ++ .nestD (Std.Format.joinSep vars ("," ++ .line)) ++ ")"

/-- Generate a simple FromJson instance for a tuple with named item types.

    This version assumes all item types already have FromJson instances defined,
    so it just calls `fromJson?` for each element.

    Generates code like:
    ```
    do
      let x0 ← fromJson? =<< j.getArrVal? 0
      let x1 ← fromJson? =<< j.getArrVal? 1
      ...
      .ok (x0, x1, ...)
    ```
-/
def getTupleFromJsonSimple (len : Nat) : Option Format :=
  if len < 2 then none
  else
    let varNames := List.range len |>.map (fun i => s!"x{i}")

    let parseStmts : List Format := varNames.zipIdx.map fun (varName, idx) =>
      s!"let {varName} ← fromJson? =<< j.getArrVal? {idx}"

    let tupleExpr := buildTupleFormat (varNames.map .text)

    let fullParser :=
      .nestD ("do\n" ++
        Std.Format.joinSep parseStmts "\n" ++ "\n" ++
        s!".ok {tupleExpr}")

    some fullParser

/-- Generate a simple ToJson instance for a tuple with named item types.

    This version assumes all item types already have ToJson instances defined,
    so it just calls `toJson` for each element.

    Generates code like:
    ```
    match x with
    | (x0, x1, ...) => Json.arr #[toJson x0, toJson x1, ...]
    ```
-/
def getTupleToJsonSimple (len : Nat) : Option Format :=
  if len < 2 then none
  else
    let varNames := List.range len |>.map (fun i => s!"x{i}")

    let pattern := buildTupleFormat (varNames.map .text)

    let serializations : List Format := varNames.map fun varName =>
      s!"toJson {varName}"

    let arrayElems := Std.Format.joinSep serializations ("," ++ .line)

    let fullSerializer :=
      .nestD ("match x with\n| " ++ pattern ++ " => Json.arr #[" ++ arrayElems ++ "]")

    some fullSerializer

/-- Generate a FromJson instance for a tuple type.

    Generates code like:
    ```
    do
      let x0 ← fromJson? <$> j.getArrVal? 0
      let x1 ← fromJson? <$> j.getArrval? 1
      ...
      .ok (x0, x1, ...)
    ```
-/
def getTupleFromJson (itemTypeDefs : List TypeDefinition) : Option Format :=
  let len := itemTypeDefs.length
  if len < 2 then none
  else
    let varNames := List.range len |>.map (fun i => s!"x{i}")

    let parseStmts : List Format := (itemTypeDefs.zip varNames).zipIdx.map fun ((typeDef, varName), idx) =>
      match typeDef.fromJsonImpl with
      | some customParser =>
        s!"let {varName} ← " ++ .group (.nestD ("(" ++ .line ++
          "fun j =>" ++ .line ++ customParser ++ .line ++
        s!") =<< (j.getArrVal? {idx})"))
      | none =>
        s!"let {varName} ← fromJson? =<< j.getArrVal? {idx}"

    let tupleExpr := buildTupleFormat (varNames.map .text)

    let fullParser :=
      .nestD ("do\n" ++
        Std.Format.joinSep parseStmts "\n" ++ "\n" ++
        s!".ok {tupleExpr}")

    some fullParser

/-- Generate a ToJson instance for a tuple type.

    Generates code like:
    ```
    match x with
    | (x0, x1, ...) => Json.arr #[toJson x0, toJson x1, ...]
    ```
-/
def getTupleToJson (itemTypeDefs : List TypeDefinition) : Option Format :=
  let len := itemTypeDefs.length
  if len < 2 then none
  else
    let varNames := List.range len |>.map (fun i => s!"x{i}")

    -- Build the pattern using buildTupleFormat
    let pattern := buildTupleFormat (varNames.map .text)

    -- Generate serialization for each element
    let serializations : List Format := itemTypeDefs.zipIdx.map fun (typeDef, idx) =>
      let varName := s!"x{idx}"
      match typeDef.toJsonImpl with
      | some customSerializer =>
        -- Use custom serializer, substituting x for the variable
        .group (.paren (s!"let x := {varName};" ++ .line ++ customSerializer))
      | none =>
        s!"toJson {varName}"

    let arrayElems := Std.Format.joinSep serializations ("," ++ .line)

    let fullSerializer :=
      .nestD ("match x with\n| " ++ pattern ++ " => Json.arr #[" ++ arrayElems ++ "]")

    some fullSerializer

/-- Try to parse a tuple type (fixed-length array).

    This handles: {"type": "array", "items": [schema1, schema2, ...], "minItems": n, "maxItems": n}
    → Type1 × Type2 × ...

    Only succeeds if:
    - items is a Tuple (array of schemas)
    - minItems == maxItems == array length (fixed size)
    - All item schemas can be parsed inline
-/
def parseInlineableTuple (itemSchemas : Array JsonSchema.Schema) (minItems maxItems : Option Nat)
    (recurse : JsonSchema.Schema → Nat → SchemaGen TypeDefinition)
    (prec : Nat := 0) : SchemaGen TypeDefinition := do
  -- Check that this is a fixed-length tuple
  let len := itemSchemas.size
  if len < 2 then
    .error "Tuple must have at least 2 items"

  match minItems, maxItems with
  | some min, some max =>
    if min != len || max != len then
      .error s!"minItems ({min}) and maxItems ({max}) must equal items length ({len})"
  | _, _ =>
    .error "Tuple requires both minItems and maxItems to be set"

  -- Parse all item schemas
  let mut itemTypeDefsAux : List TypeDefinition := []
  let mut allDeps : List TypeDefinition := []
  for itemSchema in itemSchemas do
    let itemTypeDef ← recurse itemSchema 35 -- precedence for ×
    itemTypeDefsAux := itemTypeDef :: itemTypeDefsAux
    allDeps := itemTypeDef.dependencies ++ allDeps

  let itemTypeDefs := itemTypeDefsAux.reverse

  -- Build right-nested tuple type: A × B × C is actually A × (B × C)
  let buildTupleType (types : List TypeDefinition) : Format :=
    match types with
    | [] => "Unit"  -- shouldn't happen
    | types => Std.Format.joinSep (types.map fun t => t.typeDecl) " × "

  let tupleType := buildTupleType itemTypeDefs
  let typeDecl := if prec >= 35 then "(" ++ tupleType ++ ")" else tupleType

  -- Always generate custom instances for tuples
  let fromJsonImpl := getTupleFromJson itemTypeDefs
  let toJsonImpl := getTupleToJson itemTypeDefs

  pure {
    typeDecl := typeDecl
    fromJsonImpl := fromJsonImpl
    toJsonImpl := toJsonImpl
    dependencies := allDeps.reverse
    extraDocComment := none
  }

/-- Inline types such as String ⊕ Int do not need complicated definitions.
    The prec parameter determines whether to add parentheses for function application.

    It DOES modify the baseURI.
-/
partial def parseInline (s : JsonSchema.Schema) (prec : Nat := 0)
    : SchemaGen TypeDefinition :=
  match s with
  | .Boolean b => pure { typeDecl := getBoolType b }
  | .Object o => withNewID s do
  parseRef o <|>
  (parseConstant o : SchemaGen TypeDefinition) <|>
  (do isSimple o; parseSimpleType o prec) <|>
  (if let some anyOf := o.anyOf then
    parseInlineableAnyOf anyOf (fun s p => parseInline s p) prec
  else .error "no anyOf") <|>
  (if let some oneOf := o.oneOf then
    parseInlineableOneOf oneOf (fun s p => parseInline s p) prec
  else .error "no oneOf") <|>
  (if let some (.Tuple itemSchemas) := o.items then
    parseInlineableTuple itemSchemas o.minItems o.maxItems (fun s p => parseInline s p) prec
  else .error "no inlineable tuple") <|>
  (if let some (.Single itemSchema) := o.items then
    parseInlineableArray itemSchema (fun s p => parseInline s p) prec
  else .error "no inlineable array")

def mkDocComment (s : Std.Format) : Format :=
  .nestD ("/-- " ++ s ++ " -/")

def combineDocStrings (topDoc : Std.Format) (extraComment : Option Std.Format) : Format :=
  match topDoc, extraComment with
  | .nil, none => .nil
  | .nil, some extra => extra
  | doc, none => doc
  | doc, some extra => if extra.isEmpty then doc else doc ++ "\n\n" ++ extra

end JsonSchemaCodeGen
