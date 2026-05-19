import PlutusCore.List
import PlutusCore.UPLC.CekValue
import PlutusCore.UPLC.Term
import PlutusCore.UPLC.BuiltinFunctions.Utils

namespace PlutusCore.UPLC.BuiltinFunctions.List

namespace PLC
  open PlutusCore.List
  export PlutusCore.List (
    -- macro_rules chooseList imported implicitly
    mkCons
    headList
    tailList
    nullList
  )
end PLC

open PlutusCore.UPLC.Term
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.BuiltinFunctions.Utils

-- NOTE: Args are deliberately reversed on the Cek machine stack for performance

-- Define chooseList
def chooseList (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [listCase, nullCase, .VCon (.ConstList l)]
  | [listCase, nullCase, .VCon (.ConstDataList l)]
  | [listCase, nullCase, .VCon (.ConstPairDataList l)] => some (UPLC.chooseList l nullCase listCase)
  | _ => none

-- Define mkCons
def mkCons (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [.VCon (.ConstList xs), .VCon x] =>
      some (.VCon (.ConstList (PLC.mkCons x xs)))

  | [.VCon (.ConstDataList xs), .VCon (.Data x)] =>
      -- case for ConstDataList
      some (.VCon (.ConstDataList (PLC.mkCons x xs)))

  | [.VCon (.ConstPairDataList xs), .VCon (.PairData p)] =>
      -- case for ConsPairDataList
      some (.VCon (.ConstPairDataList (PLC.mkCons p xs)))
  | _ => none

-- Define headList
def headList (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [.VCon (.ConstList xs)] =>
      tryCatchSome (PLC.headList xs) (.VCon)

  | [.VCon (.ConstDataList xs)] =>
      -- case for ConstDataList
      tryCatchSome (PLC.headList xs) (.VCon ∘ .Data)

  | [.VCon (.ConstPairDataList xs)] =>
      -- case for ConstPairDataList
      tryCatchSome (PLC.headList xs) (.VCon ∘ .PairData)

  | _ => none

-- Define tailList
def tailList (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [.VCon (.ConstList xs)] =>
      tryCatchSome (PLC.tailList xs) (.VCon ∘ .ConstList)

  | [.VCon (.ConstDataList xs)] =>
      -- case for ConstDataList
      tryCatchSome (PLC.tailList xs) (.VCon ∘ .ConstDataList)

  | [.VCon (.ConstPairDataList xs)] =>
      -- case for ConstPairDataList
      tryCatchSome (PLC.tailList xs) (.VCon ∘ .ConstPairDataList)
  | _ => none

-- Define nullList
def nullList (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [.VCon (.ConstList xs)]
  | [.VCon (.ConstDataList xs)]
  | [.VCon (.ConstPairDataList xs)] =>
      some (.VCon (.Bool (PLC.nullList xs)))
  | _ => none

-- dropList n xs = xs.drop n (n < 0 treated as 0 via Int.toNat)
-- Eval args (reversed): [list, Integer n]
def dropList (Vs : List CekValue) : Option CekValue :=
  match Vs with
  | [.VCon (.ConstList xs), .VCon (.Integer n)] =>
      some (.VCon (.ConstList (xs.drop n.toNat)))
  | [.VCon (.ConstDataList xs), .VCon (.Integer n)] =>
      some (.VCon (.ConstDataList (xs.drop n.toNat)))
  | [.VCon (.ConstPairDataList xs), .VCon (.Integer n)] =>
      some (.VCon (.ConstPairDataList (xs.drop n.toNat)))
  | _ => none

end PlutusCore.UPLC.BuiltinFunctions.List
