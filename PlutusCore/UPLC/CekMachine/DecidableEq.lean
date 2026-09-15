import PlutusCore.UPLC.CekMachine
import PlutusCore.UPLC.Term.DecidableEq

/-! ## Decidable equality for the CEK machine types

The work is all in `CekValue`, which nests `List CekValue` and so is out of the deriving
handler's reach. `deriving BEq` does reach `CekValue`, but the derived comparison does not
reduce in the kernel, so `decide` cannot use it, and the hand-written comparison reduces.
`Environment`, `Stack`, `Frame` and `State` follow from it, each in one line. -/

namespace PlutusCore.UPLC.Builtins

-- `eqCekValue` below decides these. The handler reaches `ExpectedBuiltinArgs` because its
-- recursion is direct, not nested inside another type constructor as on `CekValue`.
deriving instance DecidableEq for ExpectedBuiltinArg
deriving instance DecidableEq for ExpectedBuiltinArgs

end PlutusCore.UPLC.Builtins

namespace PlutusCore.UPLC.CekValue

open PlutusCore.UPLC.Term
open PlutusCore.UPLC.Builtins

mutual
  def eqCekValue : CekValue → CekValue → Bool
    | .VCon a, .VCon b => eqConst a b
    | .VDelay t1 e1, .VDelay t2 e2 => eqTerm t1 t2 && eqCekValueList e1 e2
    | .VLam x t1 e1, .VLam y t2 e2 => x == y && eqTerm t1 t2 && eqCekValueList e1 e2
    | .VConstr i a, .VConstr j b => i == j && eqCekValueList a b
    | .VBuiltin f1 a1 s1, .VBuiltin f2 a2 s2 =>
        decide (f1 = f2) && eqCekValueList a1 a2 && decide (s1 = s2)
    | _, _ => false

  def eqCekValueList : List CekValue → List CekValue → Bool
    | [], [] => true
    | a :: as, b :: bs => eqCekValue a b && eqCekValueList as bs
    | _, _ => false
end

mutual
  theorem eqCekValue_true_imp_eq : ∀ a b : CekValue, eqCekValue a b = true → a = b
    | .VCon a, .VCon b, h => by
        simp only [eqCekValue] at h
        rw [eqConst_true_imp_eq a b h]
    | .VDelay t1 e1, .VDelay t2 e2, h => by
        simp only [eqCekValue, Bool.and_eq_true] at h
        rw [eqTerm_true_imp_eq t1 t2 h.1, eqCekValueList_true_imp_eq e1 e2 h.2]
    | .VLam x t1 e1, .VLam y t2 e2, h => by
        simp only [eqCekValue, Bool.and_eq_true, beq_iff_eq] at h
        rw [h.1.1, eqTerm_true_imp_eq t1 t2 h.1.2, eqCekValueList_true_imp_eq e1 e2 h.2]
    | .VConstr i a, .VConstr j b, h => by
        simp only [eqCekValue, Bool.and_eq_true, beq_iff_eq] at h
        rw [h.1, eqCekValueList_true_imp_eq a b h.2]
    | .VBuiltin f1 a1 s1, .VBuiltin f2 a2 s2, h => by
        simp only [eqCekValue, Bool.and_eq_true, decide_eq_true_eq] at h
        rw [h.1.1, eqCekValueList_true_imp_eq a1 a2 h.1.2, h.2]
    | .VCon _, .VDelay _ _, h | .VCon _, .VLam _ _ _, h
    | .VCon _, .VConstr _ _, h | .VCon _, .VBuiltin _ _ _, h
    | .VDelay _ _, .VCon _, h | .VDelay _ _, .VLam _ _ _, h
    | .VDelay _ _, .VConstr _ _, h | .VDelay _ _, .VBuiltin _ _ _, h
    | .VLam _ _ _, .VCon _, h | .VLam _ _ _, .VDelay _ _, h
    | .VLam _ _ _, .VConstr _ _, h | .VLam _ _ _, .VBuiltin _ _ _, h
    | .VConstr _ _, .VCon _, h | .VConstr _ _, .VDelay _ _, h
    | .VConstr _ _, .VLam _ _ _, h | .VConstr _ _, .VBuiltin _ _ _, h
    | .VBuiltin _ _ _, .VCon _, h | .VBuiltin _ _ _, .VDelay _ _, h
    | .VBuiltin _ _ _, .VLam _ _ _, h
    | .VBuiltin _ _ _, .VConstr _ _, h => by simp [eqCekValue] at h

  theorem eqCekValueList_true_imp_eq : ∀ a b : List CekValue, eqCekValueList a b = true → a = b
    | [], [], _ => rfl
    | a :: as, b :: bs, h => by
        simp only [eqCekValueList, Bool.and_eq_true] at h
        rw [eqCekValue_true_imp_eq a b h.1, eqCekValueList_true_imp_eq as bs h.2]
    | [], _ :: _, h | _ :: _, [], h => by simp [eqCekValueList] at h
end

mutual
  theorem eqCekValue_reflexive : ∀ a : CekValue, eqCekValue a a = true
    | .VCon a => by simp only [eqCekValue]; exact eqConst_reflexive a
    | .VDelay t e => by
        simp only [eqCekValue, Bool.and_eq_true]
        exact ⟨eqTerm_reflexive t, eqCekValueList_reflexive e⟩
    | .VLam _ t e => by
        simp only [eqCekValue, Bool.and_eq_true, beq_self_eq_true, true_and]
        exact ⟨eqTerm_reflexive t, eqCekValueList_reflexive e⟩
    | .VConstr _ a => by
        simp only [eqCekValue, Bool.and_eq_true, beq_self_eq_true, true_and]
        exact eqCekValueList_reflexive a
    | .VBuiltin _ a _ => by
        simp only [eqCekValue]
        simp [eqCekValueList_reflexive a]

  theorem eqCekValueList_reflexive : ∀ a : List CekValue, eqCekValueList a a = true
    | [] => by simp [eqCekValueList]
    | a :: as => by
        simp only [eqCekValueList, Bool.and_eq_true]
        exact ⟨eqCekValue_reflexive a, eqCekValueList_reflexive as⟩
end

theorem eqCekValue_false_imp_not_eq (a b : CekValue) : eqCekValue a b = false → a ≠ b :=
  fun h => eq_false_imp_ne eqCekValue_reflexive h

def CekValue.decEq (a b : CekValue) : Decidable (Eq a b) :=
  match h : eqCekValue a b with
  | true => isTrue (eqCekValue_true_imp_eq _ _ h)
  | false => isFalse (eqCekValue_false_imp_not_eq _ _ h)

instance : DecidableEq CekValue := CekValue.decEq

example : DecidableEq Environment := inferInstance

end PlutusCore.UPLC.CekValue

namespace PlutusCore.UPLC.CekMachine

open PlutusCore.UPLC.CekValue

deriving instance DecidableEq for Frame

example : DecidableEq Stack := inferInstance

/-! ### `State`, and every type a state is built from, which `BuiltinSemanticsVariant` is not -/

deriving instance DecidableEq for State

example : DecidableEq State := inferInstance

/-! ### `EvaluationResult`, what the budget aware path returns instead of a state -/

deriving instance DecidableEq for EvaluationResult

example : DecidableEq EvaluationResult := inferInstance

/-! ### `BEq` and `LawfulBEq`

Both arrive through `instBEqOfDecidableEq` and `instLawfulBEq`. These checks fail if a
hand-rolled `BEq` is ever added for one of these types. -/

example : LawfulBEq CekValue := inferInstance
example : LawfulBEq Environment := inferInstance
example : LawfulBEq Frame := inferInstance
example : LawfulBEq Stack := inferInstance
example : LawfulBEq State := inferInstance
example : LawfulBEq EvaluationResult := inferInstance

end PlutusCore.UPLC.CekMachine
