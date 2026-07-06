import PlutusCore.UPLC.Term

namespace PlutusCore.UPLC.Shape

namespace Internal

open Std

open PlutusCore.UPLC.Term

inductive TermShape
  | Anything
  | TypeVar       (name         : Nat)
  | Alternatives  (options      : List TermShape)
  | Function      (input output : TermShape)
  | Delay         (delayed      : TermShape)
  | ConInteger
  | ConByteString
  | ConString
  | ConUnit
  | ConBool
  | ConList       -- TODO: add datalist and pairdatalist
  | ConPair       -- TODO: add pairdata
  | Data          -- TODO: add data shape
  | ConBls12_381_G1_element
  | ConBls12_381_G2_element
  | ConBls12_381_MlResult
  | Nothing       -- bottom type
  deriving Repr, BEq

namespace TermShape

private def greekVar (n : Nat) : String :=
  let letters := #["α", "β", "γ", "δ", "ε", "ζ", "η", "θ", "ι", "κ", "λ", "μ",
                   "ν", "ξ", "ο", "π", "ρ", "σ", "τ", "υ", "φ", "χ", "ψ", "ω"]
  match letters[n]? with
  | some s => s
  | none   => "τ" ++ toString n

mutual

protected def toString : TermShape → String
  | .Anything                => "Anything"
  | .TypeVar n               => greekVar n
  | .Alternatives options    => String.intercalate " | " (toStringAlts options)
  | .Function input output    =>
      let lhs := match input with
        | .Function _ _ => "(" ++ TermShape.toString input ++ ")"
        | _             => TermShape.toString input
      lhs ++ " → " ++ TermShape.toString output
  | .Delay delayed           => "Delay (" ++ TermShape.toString delayed ++ ")"
  | .ConInteger              => "Int"
  | .ConByteString           => "ByteString"
  | .ConString               => "String"
  | .ConUnit                 => "Unit"
  | .ConBool                 => "Bool"
  | .ConList                 => "List"
  | .ConPair                 => "Pair"
  | .Data                    => "Data"
  | .ConBls12_381_G1_element => "G1"
  | .ConBls12_381_G2_element => "G2"
  | .ConBls12_381_MlResult   => "MlResult"
  | .Nothing                 => "Nothing"

private def toStringAlts : List TermShape → List String
  | []        => []
  | s :: rest =>
      let str := match s with
        | .Function _ _ => "(" ++ TermShape.toString s ++ ")"
        | _             => TermShape.toString s
      str :: toStringAlts rest

end

instance : ToString TermShape := ⟨TermShape.toString⟩

end TermShape

def unifyAlternatives (shapes : List TermShape) : TermShape :=
  let flat := shapes.flatMap (λ
    | .Alternatives opts => opts
    | .Nothing           => []
    | other              => [other]
  )
  if flat.isEmpty || flat.contains .Anything then
    .Anything
  else
    let deduped := flat.foldl (λ acc s => if acc.contains s then acc else acc ++ [s]) []
    match deduped with
    | []  => .Anything   -- unreachable (flat is non-empty), kept for totality
    | [s] => s
    | _   => .Alternatives deduped

structure VarTable where
  variables    : HashMap String TermShape
  types        : HashMap Nat    TermShape
  nextTypeName : Nat
  deriving Repr

namespace VarTable

@[simp]
def empty : VarTable := ⟨HashMap.emptyWithCapacity, HashMap.emptyWithCapacity, 0⟩

@[simp]
def getVarType (t : VarTable) (name : String) : TermShape :=
  HashMap.getD t.variables name .Nothing

@[simp]
def setVarType (t : VarTable) (name : String) (x : TermShape) : VarTable :=
  { t with variables := HashMap.insert t.variables name x }

def nextTypeVar (t : VarTable) : TermShape × VarTable :=
  (.TypeVar t.nextTypeName, { t with nextTypeName := t.nextTypeName + 1 })

def setType (t : VarTable) (name : Nat) (x : TermShape) : VarTable :=
  { t with types := HashMap.insert t.types name x }

def unrollType (t : VarTable) (x : Nat) : TermShape :=
  match HashMap.get? t.types x with
  | some (.TypeVar y) => if y < x then unrollType t y else .TypeVar x
  | some shape        => shape
  | none              => .TypeVar x

def evalType (t : VarTable) : TermShape → TermShape
  | .TypeVar  name         => unrollType t name
  | .Function input output => .Function (evalType t input) (evalType t output)
  | other                  => other

mutual

def unify (t : VarTable) (a b : TermShape) : TermShape × VarTable :=
  match a, b with
  | .TypeVar tx, .TypeVar ty =>
      if tx == ty
        then (.TypeVar tx, t)
        else
          let (hi, lo) := if tx < ty then (ty, tx) else (tx, ty)
          (.TypeVar lo, setType t hi (.TypeVar lo))
  | .TypeVar ty, x
  | x          , .TypeVar ty => (x, setType t ty x)
  | .Anything  , y           => (y, t)
  | x          , .Anything   => (x, t)
  | .Function i1 o1, .Function i2 o2 =>
      let (i, t')  := unify t  i1 i2
      let (o, t'') := unify t' o1 o2
      if i == .Nothing || o == .Nothing
        then (.Nothing, t'')
        else (.Function i o, t'')
  | .Delay d1, .Delay d2 =>
      let (d, t') := unify t d1 d2
      if d == .Nothing then (.Nothing, t') else (.Delay d, t')
  | .Alternatives xs, y =>
      let (rs, t') := unifyAll t xs y
      (if rs.all (· == .Nothing) then .Nothing else unifyAlternatives rs, t')
  | x, .Alternatives ys =>
      let (rs, t') := unifyAll t ys x
      (if rs.all (· == .Nothing) then .Nothing else unifyAlternatives rs, t')
  | x          , y           => if x == y then (x, t) else (.Nothing, t)
  termination_by sizeOf a + sizeOf b

def unifyAll (t : VarTable) (shapes : List TermShape) (other : TermShape) : List TermShape × VarTable :=
  match shapes with
  | []        => ([], t)
  | s :: rest =>
      let (r , t')  := unify t s other
      let (rs, t'') := unifyAll t' rest other
      (r :: rs, t'')
  termination_by sizeOf shapes + sizeOf other

end

end VarTable

open BuiltinFun in
def shapeOfBuiltin (t : VarTable) : BuiltinFun → TermShape × VarTable
  -- Integer
  | AddInteger | SubtractInteger | MultiplyInteger
  | DivideInteger | QuotientInteger | RemainderInteger | ModInteger =>
      (.Function .ConInteger (.Function .ConInteger .ConInteger), t)
  | EqualsInteger | LessThanInteger | LessThanEqualsInteger =>
      (.Function .ConInteger (.Function .ConInteger .ConBool), t)
  | ExpModInteger =>
      (.Function .ConInteger (.Function .ConInteger (.Function .ConInteger .ConInteger)), t)
  -- ByteString
  | AppendByteString =>
      (.Function .ConByteString (.Function .ConByteString .ConByteString), t)
  | ConsByteString =>
      (.Function .ConInteger (.Function .ConByteString .ConByteString), t)
  | SliceByteString =>
      (.Function .ConInteger (.Function .ConInteger (.Function .ConByteString .ConByteString)), t)
  | LengthOfByteString =>
      (.Function .ConByteString .ConInteger, t)
  | IndexByteString =>
      (.Function .ConByteString (.Function .ConInteger .ConInteger), t)
  | EqualsByteString | LessThanByteString | LessThanEqualsByteString =>
      (.Function .ConByteString (.Function .ConByteString .ConBool), t)
  -- Cryptography (hashes)
  | Sha2_256 | Sha3_256 | Blake2b_256 | Keccak_256 | Blake2b_224 | Ripemd_160 =>
      (.Function .ConByteString .ConByteString, t)
  -- Cryptography (signature verification)
  | VerifyEd25519Signature | VerifyEcdsaSecp256k1Signature | VerifySchnorrSecp256k1Signature =>
      (.Function .ConByteString (.Function .ConByteString (.Function .ConByteString .ConBool)), t)
  -- Integer <-> ByteString conversions
  | IntegerToByteString =>
      (.Function .ConBool (.Function .ConInteger (.Function .ConInteger .ConByteString)), t)
  | ByteStringToInteger =>
      (.Function .ConBool (.Function .ConByteString .ConInteger), t)
  -- String
  | AppendString =>
      (.Function .ConString (.Function .ConString .ConString), t)
  | EqualsString =>
      (.Function .ConString (.Function .ConString .ConBool), t)
  | EncodeUtf8 =>
      (.Function .ConString .ConByteString, t)
  | DecodeUtf8 =>
      (.Function .ConByteString .ConString, t)
  -- Bool / Unit / Tracing (polymorphic in the result type)
  | IfThenElse =>
      let (a, t') := VarTable.nextTypeVar t
      (.Delay (.Function .ConBool (.Function a (.Function a a))), t')
  | ChooseUnit =>
      let (a, t') := VarTable.nextTypeVar t
      (.Delay (.Function .ConUnit (.Function a a)), t')
  | Trace =>
      let (a, t') := VarTable.nextTypeVar t
      (.Delay (.Function .ConString (.Function a a)), t')
  -- Pairs (polymorphic in both components)
  | FstPair =>
      let (a, t1) := VarTable.nextTypeVar t
      let (_, t2) := VarTable.nextTypeVar t1
      (.Delay (.Delay (.Function .ConPair a)), t2)
  | SndPair =>
      let (_, t1) := VarTable.nextTypeVar t
      let (b, t2) := VarTable.nextTypeVar t1
      (.Delay (.Delay (.Function .ConPair b)), t2)
  -- Lists (polymorphic in the element type)
  | ChooseList =>
      let (_, t1) := VarTable.nextTypeVar t
      let (r, t2) := VarTable.nextTypeVar t1
      (.Delay (.Delay (.Function .ConList (.Function r (.Function r r)))), t2)
  | MkCons =>
      let (a, t') := VarTable.nextTypeVar t
      (.Delay (.Function a (.Function .ConList .ConList)), t')
  | HeadList =>
      let (a, t') := VarTable.nextTypeVar t
      (.Delay (.Function .ConList a), t')
  | TailList =>
      let (_, t') := VarTable.nextTypeVar t
      (.Delay (.Function .ConList .ConList), t')
  | NullList =>
      let (_, t') := VarTable.nextTypeVar t
      (.Delay (.Function .ConList .ConBool), t')
  | DropList =>
      let (_, t') := VarTable.nextTypeVar t
      (.Delay (.Function .ConInteger (.Function .ConList .ConList)), t')
  -- Data
  | ChooseData =>
      let (r, t') := VarTable.nextTypeVar t
      (.Delay (.Function .Data
        (.Function r (.Function r (.Function r (.Function r (.Function r r)))))), t')
  | ConstrData =>
      (.Function .ConInteger (.Function .ConList .Data), t)
  | MapData | ListData =>
      (.Function .ConList .Data, t)
  | IData =>
      (.Function .ConInteger .Data, t)
  | BData =>
      (.Function .ConByteString .Data, t)
  | UnConstrData =>
      (.Function .Data .ConPair, t)
  | UnMapData | UnListData =>
      (.Function .Data .ConList, t)
  | UnIData =>
      (.Function .Data .ConInteger, t)
  | UnBData =>
      (.Function .Data .ConByteString, t)
  | EqualsData =>
      (.Function .Data (.Function .Data .ConBool), t)
  | MkPairData =>
      (.Function .Data (.Function .Data .ConPair), t)
  | MkNilData | MkNilPairData =>
      (.Function .ConUnit .ConList, t)
  | SerializeData =>
      (.Function .Data .ConByteString, t)
  -- BLS12-381 G1
  | Bls12_381_G1_add =>
      (.Function .ConBls12_381_G1_element (.Function .ConBls12_381_G1_element .ConBls12_381_G1_element), t)
  | Bls12_381_G1_neg =>
      (.Function .ConBls12_381_G1_element .ConBls12_381_G1_element, t)
  | Bls12_381_G1_scalarMul =>
      (.Function .ConInteger (.Function .ConBls12_381_G1_element .ConBls12_381_G1_element), t)
  | Bls12_381_G1_equal =>
      (.Function .ConBls12_381_G1_element (.Function .ConBls12_381_G1_element .ConBool), t)
  | Bls12_381_G1_hashToGroup =>
      (.Function .ConByteString (.Function .ConByteString .ConBls12_381_G1_element), t)
  | Bls12_381_G1_compress =>
      (.Function .ConBls12_381_G1_element .ConByteString, t)
  | Bls12_381_G1_uncompress =>
      (.Function .ConByteString .ConBls12_381_G1_element, t)
  | Bls12_381_G1_multiScalarMul =>
      (.Function .ConList (.Function .ConList .ConBls12_381_G1_element), t)
  -- BLS12-381 G2
  | Bls12_381_G2_add =>
      (.Function .ConBls12_381_G2_element (.Function .ConBls12_381_G2_element .ConBls12_381_G2_element), t)
  | Bls12_381_G2_neg =>
      (.Function .ConBls12_381_G2_element .ConBls12_381_G2_element, t)
  | Bls12_381_G2_scalarMul =>
      (.Function .ConInteger (.Function .ConBls12_381_G2_element .ConBls12_381_G2_element), t)
  | Bls12_381_G2_equal =>
      (.Function .ConBls12_381_G2_element (.Function .ConBls12_381_G2_element .ConBool), t)
  | Bls12_381_G2_hashToGroup =>
      (.Function .ConByteString (.Function .ConByteString .ConBls12_381_G2_element), t)
  | Bls12_381_G2_compress =>
      (.Function .ConBls12_381_G2_element .ConByteString, t)
  | Bls12_381_G2_uncompress =>
      (.Function .ConByteString .ConBls12_381_G2_element, t)
  | Bls12_381_G2_multiScalarMul =>
      (.Function .ConList (.Function .ConList .ConBls12_381_G2_element), t)
  -- BLS12-381 pairing
  | Bls12_381_millerLoop =>
      (.Function .ConBls12_381_G1_element (.Function .ConBls12_381_G2_element .ConBls12_381_MlResult), t)
  | Bls12_381_mulMlResult =>
      (.Function .ConBls12_381_MlResult (.Function .ConBls12_381_MlResult .ConBls12_381_MlResult), t)
  | Bls12_381_finalVerify =>
      (.Function .ConBls12_381_MlResult (.Function .ConBls12_381_MlResult .ConBool), t)
  -- Batch 5 (bitwise)
  | AndByteString | OrByteString | XorByteString =>
      (.Function .ConBool (.Function .ConByteString (.Function .ConByteString .ConByteString)), t)
  | ComplementByteString =>
      (.Function .ConByteString .ConByteString, t)
  | ReadBit =>
      (.Function .ConByteString (.Function .ConInteger .ConBool), t)
  | WriteBits =>
      (.Function .ConByteString (.Function .ConList (.Function .ConBool .ConByteString)), t)
  | ReplicateByte =>
      (.Function .ConInteger (.Function .ConInteger .ConByteString), t)
  | ShiftByteString | RotateByteString =>
      (.Function .ConByteString (.Function .ConInteger .ConByteString), t)
  | CountSetBits | FindFirstSetBit =>
      (.Function .ConByteString .ConInteger, t)

mutual

def shapeOfTerm (t : VarTable) : Term → TermShape × VarTable
  | .Var name                        => (VarTable.getVarType t name, t)
  | .Const (.Integer              _) => (.ConInteger               , t)
  | .Const (.ByteString           _) => (.ConByteString            , t)
  | .Const (.String               _) => (.ConString                , t)
  | .Const (.Unit                  ) => (.ConUnit                  , t)
  | .Const (.Bool                 _) => (.ConBool                  , t)
  | .Const (.ConstList            _) => (.ConList                  , t)
  | .Const (.ConstDataList        _) => (.ConList                  , t)
  | .Const (.ConstPairDataList    _) => (.ConList                  , t)
  | .Const (.Pair                 _) => (.ConPair                  , t)
  | .Const (.PairData             _) => (.ConPair                  , t)
  | .Const (.Data                 _) => (.Data                     , t)
  | .Const (.Bls12_381_G1_element _) => (.ConBls12_381_G1_element  , t)
  | .Const (.Bls12_381_G2_element _) => (.ConBls12_381_G2_element  , t)
  | .Const (.Bls12_381_MlResult   _) => (.ConBls12_381_MlResult    , t)
  | .Lam name body =>
      let (bShape, bTable) := shapeOfTerm (VarTable.setVarType t name .Anything) body
      let argShape         := VarTable.getVarType bTable name
      (.Function argShape bShape, { t with types := bTable.types, nextTypeName := bTable.nextTypeName })
  | .Apply fn (.Var name) =>
      let (fnShape , fnTable) := shapeOfTerm t fn
      let argShape            := VarTable.getVarType fnTable name
      match VarTable.evalType fnTable fnShape with
      | .Function input output =>
          let (refined, t') := VarTable.unify fnTable (VarTable.evalType fnTable input) argShape
          if refined == .Nothing
            then (.Nothing, t')
            else (VarTable.evalType t' output, VarTable.setVarType t' name refined)
      | _ => (.Nothing, fnTable)
  | .Apply fn arg =>
      let (fnShape , fnTable)  := shapeOfTerm t fn
      let (argShape, argTable) := shapeOfTerm fnTable arg
      match fnShape with
      | .Function .Anything         output => (output, argTable)
      | .Function (.TypeVar tyName) output =>
          (VarTable.evalType (VarTable.setType argTable tyName argShape) output, argTable)
      | .Function expected output =>
          if expected == argShape
            then (output  , argTable)
            else (.Nothing, argTable)
      | _ => (.Nothing, argTable)
  | .Builtin b => shapeOfBuiltin t b
  | .Delay term =>
      let (dShape, t') := shapeOfTerm t term
      (.Delay dShape, t')
  | .Force term =>
      match shapeOfTerm t term with
      | (.Delay delayed, t') => (delayed , t')
      | (_             , t') => (.Nothing, t')
  | .Error            => (.Nothing , t)
  | .Constr _ fields  => (.Anything, threadTerms t fields)
  | .Case scrut branches =>
      let (_, t')       := shapeOfTerm t scrut
      let (shapes, t'') := shapeOfBranches t' branches
      (unifyAlternatives shapes, t'')

def threadTerms (t : VarTable) : List Term → VarTable
  | []            => t
  | term :: rest  => threadTerms (shapeOfTerm t term).snd rest

def shapeOfBranches (t : VarTable) : List Term → List TermShape × VarTable
  | []           => ([], t)
  | term :: rest =>
      let (shape, t')   := shapeOfTerm t term
      let (rest' , t'') := shapeOfBranches t' rest
      (shape :: rest', t'')

end

def analyzeType (t : Term) : TermShape := Prod.fst (shapeOfTerm VarTable.empty t)

end Internal

export Internal
  (
    TermShape
    analyzeType
  )

end PlutusCore.UPLC.Shape
