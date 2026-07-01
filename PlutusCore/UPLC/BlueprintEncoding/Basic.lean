import Lean

import PlutusCore.IsData
import PlutusCore.UPLC.PlutusScript
import PlutusCore.UPLC.ScriptEncoding.Basic
import PlutusCore.UPLC.Term

namespace PlutusCore.UPLC.BlueprintEncoding

open Lean Elab Command Term Meta
open PlutusCore.UPLC.PlutusScript
open PlutusCore.UPLC.ScriptEncoding.Internal (singleCborEncodedScriptFromHex?)
open PlutusCore.IsData (IsData)

/-! ## CIP-57 Plutus Blueprint import

This module implements the `#import_blueprints` command, which reads a CIP-57
`plutus.json` blueprint file at compile time and emits Lean definitions for
each validator.

For each validator it produces:
- `<ns>.<title> : PlutusScript`
- `<ns>.<title>_hash : String`  (when hash present)
- `<ns>.<title>_paramCount : Nat`  (when unapplied params > 0)
- Lean `structure` or `inductive` for datum/redeemer/parameter schemas,
  together with `IsData` instances, when the schema can be expressed in terms
  of the built-in Plutus types.
- `<ns> : BlueprintInfo`  — human-readable summary of the whole blueprint.
-/

/-! ### Public summary types -/

/-- A Plutus on-chain type parsed from a CIP-57 JSON Schema. -/
inductive PlutusType where
  | integer    : PlutusType
  | bytestring : PlutusType
  | string     : PlutusType
  | bool       : PlutusType
  | unit       : PlutusType
  | void       : PlutusType
  | data       : PlutusType
  | list       (items : PlutusType)                                               : PlutusType
  | map        (keys values : PlutusType)                                         : PlutusType
  | pair       (left right : PlutusType)                                          : PlutusType
  /-- A single constructor: optional name, 0-based index, field (name × type) pairs. -/
  | constr     (title : Option String) (index : Nat)
               (fields : List (Option String × PlutusType))                       : PlutusType
  /-- Sum type. -/
  | anyOf      (variants : List PlutusType)                                       : PlutusType
  | opaque     (name : String)                                                    : PlutusType
  deriving Repr, Inhabited

/-- A typed slot (datum, redeemer, or parameter) from a CIP-57 validator. -/
structure SchemaInfo where
  /-- Slot label, e.g. `"datum"`, `"_redeemer"`, `"multisigHash"`. -/
  title    : Option String
  /-- Lean-safe type name resolved from the `definitions` section (e.g. `"MultisigRedeemer"`). -/
  typeName : Option String
  /-- Fully-resolved Plutus type. -/
  ptype    : PlutusType
  deriving Repr, Inhabited

/-- Metadata for one validator entry in a CIP-57 blueprint. -/
structure ValidatorInfo where
  title       : String
  description : Option String
  hash        : Option String
  /-- The compiled Plutus script, if present in the blueprint. -/
  script      : Option PlutusScript
  datum       : Option SchemaInfo
  redeemer    : Option SchemaInfo
  parameters  : Array SchemaInfo
  deriving Repr, Inhabited

/-- Top-level summary of a CIP-57 blueprint file. -/
structure BlueprintInfo where
  title         : String
  description   : Option String
  version       : String
  plutusVersion : String
  license       : Option String
  validators    : Array ValidatorInfo
  deriving Repr

/-! ### Internal JSON parsing -/

namespace Internal

structure BlueprintPreamble where
  title         : String
  description   : Option String
  version       : String
  plutusVersion : String
  license       : Option String

structure BlueprintValidator where
  title        : String
  description  : Option String
  compiledCode : Option String
  hash         : Option String
  datum        : Option SchemaInfo
  redeemer     : Option SchemaInfo
  parameters   : Array SchemaInfo

structure Blueprint where
  preamble   : BlueprintPreamble
  validators : Array BlueprintValidator

-- ---------------------------------------------------------------------------
-- JSON helpers
-- ---------------------------------------------------------------------------

private def getStr (j : Lean.Json) (key : String) : Except String String :=
  match j.getObjVal? key with
  | .ok (.str s) => .ok s
  | .ok _        => .error s!"field '{key}' must be a string"
  | .error _     => .error s!"missing required field '{key}'"

private def getOptStr (j : Lean.Json) (key : String) : Option String :=
  match j.getObjVal? key with
  | .ok (.str s) => .some s
  | _            => .none

/-- Decode JSON Pointer token escapes: `~1` → `/`, then `~0` → `~`. -/
private def decodeJsonPointer (s : String) : String :=
  String.intercalate "~" (String.intercalate "/" (s.splitOn "~1") |>.splitOn "~0")

-- ---------------------------------------------------------------------------
-- Schema / PlutusType parsing
-- ---------------------------------------------------------------------------

private partial def parseSchemaType (defs : Lean.Json) (j : Lean.Json) (depth : Nat) : PlutusType :=
  if depth == 0 then .opaque "<max depth>" else
  match j.getObjVal? "$ref" with
  | .ok (.str ref) =>
    let defsPrefix := "#/definitions/"
    let key := if ref.startsWith defsPrefix
                 then decodeJsonPointer (ref.drop defsPrefix.length)
                 else ref
    match defs.getObjVal? key with
    | .ok defn => parseSchemaType defs defn (depth - 1)
    | _        => .opaque key
  | _ =>
  let anyOneOf := match j.getObjVal? "anyOf" with
    | .ok (.arr a) => some a
    | _ => match j.getObjVal? "oneOf" with
      | .ok (.arr a) => some a
      | _ => none
  match anyOneOf with
  | some arr =>
    let variants := arr.toList.map (parseSchemaType defs · (depth - 1))
    match variants with
    | [single] => single
    | _        => .anyOf variants
  | none =>
  match j.getObjVal? "dataType" with
  | .ok (.str dt) =>
    match dt with
    | "#integer" | "integer" => .integer
    | "#bytestring" | "bytestring" | "bytes" => .bytestring
    | "#string"    => .string
    | "#boolean"   => .bool
    | "#unit"      => .unit
    | "#void"      => .void
    | "list" =>
      let items := match j.getObjVal? "items" with
        | .ok i => parseSchemaType defs i (depth - 1)
        | _     => .data
      .list items
    | "map" =>
      let keys   := match j.getObjVal? "keys"   with | .ok k => parseSchemaType defs k (depth-1) | _ => .data
      let values := match j.getObjVal? "values" with | .ok v => parseSchemaType defs v (depth-1) | _ => .data
      .map keys values
    | "pair" =>
      let left  := match j.getObjVal? "left"  with | .ok l => parseSchemaType defs l (depth-1) | _ => .data
      let right := match j.getObjVal? "right" with | .ok r => parseSchemaType defs r (depth-1) | _ => .data
      .pair left right
    | "constructor" =>
      let title  := getOptStr j "title"
      let index  := match j.getObjVal? "index" with
        | .ok (.num n) => n.mantissa.toNat
        | _            => 0
      let fields := match j.getObjVal? "fields" with
        | .ok (.arr arr) =>
          arr.toList.map fun f =>
            let ftitle  := getOptStr f "title"
            let fschema := match f.getObjVal? "schema" with | .ok s => s | _ => f
            (ftitle, parseSchemaType defs fschema (depth - 1))
        | _ => []
      .constr title index fields
    | _ => .opaque dt
  | _ =>
  match getOptStr j "title" with
  | some "Data" => .data
  | _           => .data

/-- Extract the Lean-friendly type name from a `$ref` by looking up the
    definition's `"title"` field, falling back to the decoded key. -/
private def extractTypeName (defs : Lean.Json) (schema : Lean.Json) : Option String :=
  match schema.getObjVal? "$ref" with
  | .ok (.str ref) =>
    let defsPrefix := "#/definitions/"
    if ref.startsWith defsPrefix then
      let key := decodeJsonPointer (ref.drop defsPrefix.length)
      let fromTitle := match defs.getObjVal? key with
        | .ok defn => getOptStr defn "title"
        | _        => none
      some (fromTitle.getD key)
    else none
  | _ => none

private def parseSchemaInfo (defs : Lean.Json) (j : Lean.Json) : SchemaInfo :=
  let schema := match j.getObjVal? "schema" with | .ok s => s | _ => j
  { title    := getOptStr j "title"
    typeName := extractTypeName defs schema
    ptype    := parseSchemaType defs schema 20 }

-- ---------------------------------------------------------------------------
-- Blueprint parsing
-- ---------------------------------------------------------------------------

private def parsePreamble (j : Lean.Json) : Except String BlueprintPreamble := do
  return {
    title         := ← getStr j "title"
    description   := getOptStr j "description"
    version       := ← getStr j "version"
    plutusVersion := ← getStr j "plutusVersion"
    license       := getOptStr j "license"
  }

private def parseValidator (defs : Lean.Json) (j : Lean.Json) : Except String BlueprintValidator := do
  let datum      := match j.getObjVal? "datum"      with | .ok d => some (parseSchemaInfo defs d) | _ => none
  let redeemer   := match j.getObjVal? "redeemer"   with | .ok r => some (parseSchemaInfo defs r) | _ => none
  let parameters := match j.getObjVal? "parameters" with
    | .ok (.arr arr) => arr.map (parseSchemaInfo defs)
    | _              => #[]
  return {
    title        := ← getStr j "title"
    description  := getOptStr j "description"
    compiledCode := getOptStr j "compiledCode"
    hash         := getOptStr j "hash"
    datum
    redeemer
    parameters
  }

def parseBlueprint (s : String) : Except String Blueprint := do
  let json ← Lean.Json.parse s
  let preamble ← match json.getObjVal? "preamble" with
    | .ok j    => parsePreamble j
    | .error e => .error s!"missing 'preamble': {e}"
  let defs := match json.getObjVal? "definitions" with | .ok d => d | _ => .null
  let validators ← match json.getObjVal? "validators" with
    | .ok (.arr arr) => arr.mapM (parseValidator defs)
    | .ok _          => .error "'validators' must be an array"
    | .error e       => .error s!"missing 'validators': {e}"
  return { preamble, validators }

def sanitizeName (s : String) : String :=
  String.mk <| s.data.map fun c => if c.isAlphanum || c == '_' then c else '_'

def plutusVersionToLangExpr (v : String) : Except String Expr :=
  match v with
  | "v1" => .ok (mkConst ``PlutusLanguage.PlutusV1)
  | "v2" => .ok (mkConst ``PlutusLanguage.PlutusV2)
  | "v3" => .ok (mkConst ``PlutusLanguage.PlutusV3)
  | _    => .error s!"Unknown plutusVersion '{v}'"

private def mkAbbrevDecl (name : Name) (type value : Expr) : Declaration :=
  .defnDecl {
    name        := name
    levelParams := []
    type        := type
    value       := value
    hints       := .abbrev
    safety      := .safe
  }

-- ---------------------------------------------------------------------------
-- Expression builders for BlueprintInfo values
-- ---------------------------------------------------------------------------

private def mkOptStrExpr : Option String → Expr
  | .none   => mkApp  (.const ``Option.none [.zero]) (.const ``String [])
  | .some s => mkApp2 (.const ``Option.some [.zero]) (.const ``String []) (mkStrLit s)

mutual
  partial def buildPlutusTypeExpr : PlutusType → Expr
    | .integer    => .const ``PlutusType.integer []
    | .bytestring => .const ``PlutusType.bytestring []
    | .string     => .const ``PlutusType.string []
    | .bool       => .const ``PlutusType.bool []
    | .unit       => .const ``PlutusType.unit []
    | .void       => .const ``PlutusType.void []
    | .data       => .const ``PlutusType.data []
    | .opaque n   => mkApp (.const ``PlutusType.opaque []) (mkStrLit n)
    | .list items => mkApp (.const ``PlutusType.list []) (buildPlutusTypeExpr items)
    | .map k v    => mkApp2 (.const ``PlutusType.map  []) (buildPlutusTypeExpr k) (buildPlutusTypeExpr v)
    | .pair l r   => mkApp2 (.const ``PlutusType.pair []) (buildPlutusTypeExpr l) (buildPlutusTypeExpr r)
    | .anyOf vs   => mkApp  (.const ``PlutusType.anyOf  []) (buildPTListExpr vs)
    | .constr t i fs =>
        mkAppN (.const ``PlutusType.constr [])
          #[mkOptStrExpr t, mkNatLit i, buildFieldListExpr fs]

  partial def buildPTListExpr (ts : List PlutusType) : Expr :=
    ts.foldr
      (fun t acc => mkApp3 (.const ``List.cons [.zero]) (.const ``PlutusType [])
                           (buildPlutusTypeExpr t) acc)
      (mkApp (.const ``List.nil [.zero]) (.const ``PlutusType []))

  partial def buildFieldListExpr (fields : List (Option String × PlutusType)) : Expr :=
    let pairTyp := mkApp2 (.const ``Prod [.zero, .zero])
                          (mkApp (.const ``Option [.zero]) (.const ``String []))
                          (.const ``PlutusType [])
    fields.foldr
      (fun (t, p) acc =>
        let pair := mkApp4 (.const ``Prod.mk [.zero, .zero])
                           (mkApp (.const ``Option [.zero]) (.const ``String []))
                           (.const ``PlutusType [])
                           (mkOptStrExpr t)
                           (buildPlutusTypeExpr p)
        mkApp3 (.const ``List.cons [.zero]) pairTyp pair acc)
      (mkApp (.const ``List.nil [.zero]) pairTyp)
end

private def buildSchemaInfoExpr (si : SchemaInfo) : Expr :=
  mkAppN (.const ``SchemaInfo.mk [])
    #[mkOptStrExpr si.title, mkOptStrExpr si.typeName, buildPlutusTypeExpr si.ptype]

private def buildOptSchemaInfoExpr : Option SchemaInfo → Expr
  | .none    => mkApp  (.const ``Option.none [.zero]) (.const ``SchemaInfo [])
  | .some si => mkApp2 (.const ``Option.some [.zero]) (.const ``SchemaInfo [])
                       (buildSchemaInfoExpr si)

private def buildSchemaInfoArrayExpr (arr : Array SchemaInfo) : Expr :=
  let nilExpr  := mkApp  (.const ``List.nil  [.zero]) (.const ``SchemaInfo [])
  let listExpr := arr.toList.foldr
    (fun si acc => mkApp3 (.const ``List.cons [.zero]) (.const ``SchemaInfo [])
                          (buildSchemaInfoExpr si) acc)
    nilExpr
  mkApp2 (.const ``Array.mk [.zero]) (.const ``SchemaInfo []) listExpr

-- `optScriptExpr` is the expression for `Option PlutusScript` — a constant reference
-- to the already-emitted script definition, so the AST is not duplicated.
private def buildValidatorInfoExpr (v : BlueprintValidator) (optScriptExpr : Expr) : Expr :=
  mkAppN (.const ``ValidatorInfo.mk [])
    #[mkStrLit v.title, mkOptStrExpr v.description, mkOptStrExpr v.hash,
      optScriptExpr,
      buildOptSchemaInfoExpr v.datum,
      buildOptSchemaInfoExpr v.redeemer,
      buildSchemaInfoArrayExpr v.parameters]

def buildBlueprintInfoExpr (pre : BlueprintPreamble) (viExprs : Array Expr) : Expr :=
  let nilExpr  := mkApp  (.const ``List.nil  [.zero]) (.const ``ValidatorInfo [])
  let listExpr := viExprs.toList.foldr
    (fun e acc => mkApp3 (.const ``List.cons [.zero]) (.const ``ValidatorInfo []) e acc)
    nilExpr
  let arrExpr  := mkApp2 (.const ``Array.mk [.zero]) (.const ``ValidatorInfo []) listExpr
  mkAppN (.const ``BlueprintInfo.mk [])
    #[mkStrLit pre.title, mkOptStrExpr pre.description, mkStrLit pre.version,
      mkStrLit pre.plutusVersion, mkOptStrExpr pre.license, arrExpr]

-- ---------------------------------------------------------------------------
-- Lean type / IsData instance code generation from PlutusType schemas
-- ---------------------------------------------------------------------------

/-- `open` command added inside every generated namespace block so that
    generated code can use the same short names as `IsData.Basic`. -/
private def openDecl : String :=
  "open PlutusCore.Data PlutusCore.Integer PlutusCore.ByteString PlutusCore.IsData"

/-- Map a `PlutusType` to a Lean type name string using the short names
    brought into scope by `openDecl`. Falls back to `Data` for complex types. -/
private partial def plutusTypeToTypeStr : PlutusType → String
  | .integer    => "Integer"
  | .bytestring => "ByteString"
  | .bool       => "Bool"
  | .unit | .void => "Unit"
  | .data       => "Data"
  | .string     => "String"
  | .list t     => "(List " ++ plutusTypeToTypeStr t ++ ")"
  | .pair a b   => "(" ++ plutusTypeToTypeStr a ++ " × " ++ plutusTypeToTypeStr b ++ ")"
  | .map k v    => "(List (" ++ plutusTypeToTypeStr k ++ " × " ++ plutusTypeToTypeStr v ++ "))"
  | _           => "Data"

/-- Generate a Lean expression string that encodes `fieldExpr` as `Data`. -/
private def encodeFieldStr (fieldExpr : String) : PlutusType → String
  | .integer    => "Data.I (" ++ fieldExpr ++ ")"
  | .bytestring => "Data.B (" ++ fieldExpr ++ ")"
  | .bool       => "if (" ++ fieldExpr ++ ") then Data.Constr 1 [] else Data.Constr 0 []"
  | .unit | .void => "Data.Constr 0 []"
  | .data       => "(" ++ fieldExpr ++ ")"
  | _           => "IsData.toData (" ++ fieldExpr ++ ")"

/-- Generate a Lean expression string that decodes a `Data` value.
    Produces `Option T` where `T = plutusTypeToTypeStr ftype`. -/
private def decodeFieldStr (dataExpr : String) : PlutusType → String
  | .integer    => "(match " ++ dataExpr ++ " with | Data.I _x => some _x | _ => none)"
  | .bytestring => "(match " ++ dataExpr ++ " with | Data.B _x => some _x | _ => none)"
  | .bool       => "(match " ++ dataExpr ++ " with | Data.Constr 0 [] => some false | Data.Constr 1 [] => some true | _ => none)"
  | .unit | .void => "(match " ++ dataExpr ++ " with | Data.Constr 0 [] => some () | _ => none)"
  | .data       => "(some " ++ dataExpr ++ ")"
  | t           => "(IsData.fromData " ++ dataExpr ++ " : Option " ++ plutusTypeToTypeStr t ++ ")"

/-- Returns `true` when every variant is a no-field constructor (simple enum). -/
private def isSimpleEnum (variants : List PlutusType) : Bool :=
  variants.all fun
    | .constr _ _ [] => true
    | _              => false

/-- Parse a Lean command from a generated string (for code gen). -/
private def parseCommand (s : String) : CommandElabM Syntax := do
  match Lean.Parser.runParserCategory (← getEnv) `command s with
  | .ok stx  => return stx
  | .error e => throwError s!"Failed to parse generated command:\n{e}\n---\n{s}"

/-- Run `action` with the namespace temporarily set to `ns` (absolute path).
    Saves and restores the full scope stack so that opens added by `action`
    don't leak into the caller's namespace, and any exception still restores. -/
private def withTempNamespace (ns : Name) (action : CommandElabM Unit) : CommandElabM Unit := do
  let savedScopes := (← get).scopes
  -- Point the top scope at the absolute target namespace
  modifyScope fun s => { s with currNamespace := ns }
  try
    action
  catch e =>
    let postEnv := (← get).env
    modify fun st => { st with scopes := savedScopes, env := postEnv }
    throw e
  let postEnv := (← get).env
  modify fun st => { st with scopes := savedScopes, env := postEnv }

-- ---------------------------------------------------------------------------
-- Emit an enum inductive (anyOf with no-field constructors) + IsData instance.
-- ---------------------------------------------------------------------------

private def emitEnumType (ns : Name) (typeName : String)
    (variants : List PlutusType) : CommandElabM Unit := do
  let shortName := sanitizeName typeName
  if shortName.isEmpty then return
  -- Skip if already defined
  if (← getEnv).find? (Name.mkStr ns shortName) |>.isSome then return

  let constrs : List (String × Nat) := variants.filterMap fun
    | .constr (some t) idx [] => some (sanitizeName t, idx)
    | _ => none
  if constrs.isEmpty then return

  let ctorLines := constrs.foldl (fun acc (cname, _) => acc ++ "  | " ++ cname ++ "\n") ""
  let toArms := constrs.foldl (fun acc (cname, idx) =>
    acc ++ "    | ." ++ cname ++ " => Data.Constr " ++ toString idx ++ " []\n") ""
  let fromArms := constrs.foldl (fun acc (cname, idx) =>
    acc ++ "    | Data.Constr " ++ toString idx ++ " [] => some (" ++ shortName ++ "." ++ cname ++ ")\n") ""

  withTempNamespace ns do
    -- Bring PlutusCore short names into scope for the declarations below
    elabCommand (← parseCommand openDecl)
    elabCommand (← parseCommand (
      "inductive " ++ shortName ++ " where\n" ++ ctorLines ++ "  deriving Repr"))
    elabCommand (← parseCommand (
      "instance : IsData " ++ shortName ++ " where\n" ++
      "  toData x := match x with\n" ++ toArms ++
      "  fromData x := match x with\n" ++ fromArms ++
      "    | _ => none"))

-- ---------------------------------------------------------------------------
-- Emit a struct type (single constructor, named fields) + IsData instance.
-- ---------------------------------------------------------------------------

private def emitStructType (ns : Name) (typeName : String) (idx : Nat)
    (fields : List (Option String × PlutusType)) : CommandElabM Unit := do
  let shortName := sanitizeName typeName
  if shortName.isEmpty then return
  -- Only generate when every field has a name
  let namedFields := fields.filterMap fun (mname, pt) => mname.map (·, pt)
  if namedFields.length != fields.length || namedFields.isEmpty then return
  -- Skip if already defined
  if (← getEnv).find? (Name.mkStr ns shortName) |>.isSome then return

  let fieldLines := namedFields.foldl (fun acc (fname, ftype) =>
    acc ++ "  " ++ sanitizeName fname ++ " : " ++ plutusTypeToTypeStr ftype ++ "\n") ""

  -- toData body using short names from openDecl
  let encLines := namedFields.map fun (fname, ftype) =>
    encodeFieldStr ("d." ++ sanitizeName fname) ftype
  let toDataBody :=
    "Data.Constr " ++ toString idx ++
    " [" ++ String.intercalate ", " encLines ++ "]"

  -- fromData: pattern match on Constr idx [_v0, _v1, ...]
  let varNames := (List.range namedFields.length).map fun i => "_v" ++ toString i
  let patVarList := "[" ++ String.intercalate ", " varNames ++ "]"
  let pat := "Data.Constr " ++ toString idx ++ " " ++ patVarList

  -- Build bind chain from right (innermost) to left (outermost)
  let fieldsWithIdx := (List.range namedFields.length).zip namedFields
  let innermost :=
    "some (" ++ shortName ++ ".mk " ++
    String.intercalate " " (namedFields.map (sanitizeName ∘ Prod.fst)) ++ ")"
  let chain := fieldsWithIdx.reverse.foldl
    (fun acc (i, fname, ftype) =>
      "(" ++ decodeFieldStr ("_v" ++ toString i) ftype ++ ").bind (fun " ++ sanitizeName fname ++ " => " ++ acc ++ ")")
    innermost

  let fromDataBody :=
    "| " ++ pat ++ " => " ++ chain ++ "\n" ++
    "        | _ => none"

  withTempNamespace ns do
    -- Bring PlutusCore short names into scope for the declarations below
    elabCommand (← parseCommand openDecl)
    elabCommand (← parseCommand (
      "structure " ++ shortName ++ " where\n" ++ fieldLines ++ "  deriving Repr"))
    elabCommand (← parseCommand (
      "instance : IsData " ++ shortName ++ " where\n" ++
      "  toData d := " ++ toDataBody ++ "\n" ++
      "  fromData x := match x with\n" ++
      "        " ++ fromDataBody))

-- ---------------------------------------------------------------------------
-- Dispatch: choose which generator to call for a given SchemaInfo.
-- ---------------------------------------------------------------------------

/-- Attempt to emit a Lean type + `IsData` instance for a schema slot.
    Silently skips schemas that can't be expressed. -/
private def tryEmitSchemaType (ns : Name) (si : SchemaInfo) : CommandElabM Unit := do
  let some typeName := si.typeName | return
  match si.ptype with
  | .anyOf variants =>
    if isSimpleEnum variants then
      emitEnumType ns typeName variants
  | .constr (some cTitle) idx fields =>
    emitStructType ns cTitle idx fields
  | .constr none idx fields =>
    emitStructType ns typeName idx fields
  | _ => return

end Internal

open Internal

/-!
### `#import_blueprints` command

Syntax:
```
#import_blueprints <Namespace> <"path/to/plutus.json">
```

Emits (per validator with `compiledCode`):
- `Namespace.sanitized_title : PlutusScript`
- `Namespace.sanitized_title_hash : String`
- `Namespace.sanitized_title_paramCount : Nat`  (when > 0)
- Lean types + `IsData` instances for datum/redeemer/parameters when the schema
  is a simple struct or enum expressible in built-in Plutus types.
- `Namespace : BlueprintInfo`  (top-level inspectable summary)
-/
syntax (name := import_blueprints) "#import_blueprints" ident str : command

@[command_elab import_blueprints]
def importBlueprintsImpl : CommandElab := fun stx => do
  let nsIdent  := stx[1]
  let pathLit  := stx[2]
  let some filepath := pathLit.isStrLit? | throwErrorAt pathLit "string literal expected"
  let ns := nsIdent.getId

  let content  ← liftM (IO.FS.readFile (System.FilePath.mk filepath))
  let blueprint ← match parseBlueprint content with
    | .ok b    => pure b
    | .error e => throwError s!"Failed to parse blueprint '{filepath}': {e}"

  let langExpr ← match plutusVersionToLangExpr blueprint.preamble.plutusVersion with
    | .ok e    => pure e
    | .error e => throwError e

  let mut viExprs : Array Expr := #[]

  for validator in blueprint.validators do
    -- Emit Lean types + IsData instances for datum / redeemer / parameters
    if let some si := validator.datum    then tryEmitSchemaType ns si
    if let some si := validator.redeemer then tryEmitSchemaType ns si
    for si in validator.parameters do      tryEmitSchemaType ns si

    -- Emit PlutusScript (and related) declarations
    match validator.compiledCode with
    | .none =>
      logInfo s!"Blueprint: '{validator.title}' has no compiledCode, skipping"
    | .some code =>
      match singleCborEncodedScriptFromHex? (String.trim code) with
      | .error msg =>
        throwError s!"Blueprint: failed to decode '{validator.title}': {msg}"
      | .ok prog =>
        let sanitized  := sanitizeName validator.title
        let scriptName := Name.mkStr ns sanitized

        let scriptDecl ← liftTermElabM do
          pure <| mkAbbrevDecl scriptName
            (mkConst ``PlutusScript)
            (mkApp2 (mkConst ``PlutusScript.mk) langExpr (toExpr prog))
        liftCoreM <| addAndCompile scriptDecl

        if let .some hash := validator.hash then
          liftCoreM <| addAndCompile <| mkAbbrevDecl
            (Name.mkStr ns (sanitized ++ "_hash")) (mkConst ``String) (mkStrLit hash)

        if validator.parameters.size > 0 then
          liftCoreM <| addAndCompile <| mkAbbrevDecl
            (Name.mkStr ns (sanitized ++ "_paramCount"))
            (mkConst ``Nat) (toExpr validator.parameters.size)

        -- Reference the already-emitted constant (avoids duplicating the compiled AST)
        let optScriptExpr :=
          mkApp2 (.const ``Option.some [.zero]) (.const ``PlutusScript [])
                 (.const scriptName [])
        viExprs := viExprs.push (buildValidatorInfoExpr validator optScriptExpr)

  -- Emit top-level BlueprintInfo value
  liftCoreM <| addAndCompile <|
    mkAbbrevDecl ns (mkConst ``BlueprintInfo) (buildBlueprintInfoExpr blueprint.preamble viExprs)

end PlutusCore.UPLC.BlueprintEncoding
