import PlutusCore.UPLC.CekMachine.DecidableEq
import PlutusCore.UPLC.Term.DecidableEq

namespace PlutusCore.UPLC.Term

example : DecidableEq Version := inferInstance
example : DecidableEq Program := inferInstance

/-! ### The two equalities on `Term` -/

example : (Term.Lam "x" Term.Error == Term.Lam "y" Term.Error) = true := rfl

example : Term.Lam "x" Term.Error ≠ Term.Lam "y" Term.Error := by decide

example : Term.Lam "x" Term.Error = Term.Lam "x" Term.Error := by decide

-- These catch a second `BEq Const` or `BEq Term` taking precedence over the hand-written ones.
example : (inferInstance : BEq Const) = instBEqConst := rfl

example : (inferInstance : BEq Term) = instBEqTerm := rfl

/-! ### A BLS12-381 constant, decided

`==` sends these through the `opaque` `bls12_381_G1_equal`, which does not reduce.
`Const.decEq` compares the underlying `Point`, which does. -/

example : Const.Bls12_381_G1_element Cryptograph.BLS12_381.g1
    = Const.Bls12_381_G1_element Cryptograph.BLS12_381.g1 := by decide

example : Const.Bls12_381_G1_element Cryptograph.BLS12_381.g1
    ≠ Const.Bls12_381_G1_element .infinity := by decide

/-! ### `LawfulBEq Const` does not synthesize -/

/-- error: failed to synthesize
  LawfulBEq Const

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth LawfulBEq Const

end PlutusCore.UPLC.Term

namespace PlutusCore.UPLC.CekValue

example : DecidableEq Environment := inferInstance

end PlutusCore.UPLC.CekValue

namespace PlutusCore.UPLC.CekMachine

open PlutusCore.UPLC.CekValue

example : DecidableEq Stack := inferInstance
example : DecidableEq State := inferInstance
example : DecidableEq EvaluationResult := inferInstance

/-! ### The two equalities on values, frames and states -/

section
open PlutusCore.UPLC.Term

private def t1 : Term := .Lam "x" .Error
private def t2 : Term := .Lam "y" .Error

#guard t1 == t2
#guard [t1] == [t2]
#guard CekValue.VDelay t1 [] == CekValue.VDelay t2 []
#guard State.Eval [] [] t1 == State.Eval [] [] t2
#guard Frame.CaseScrutinee [t1] [] == Frame.CaseScrutinee [t2] []

example : CekValue.VDelay t1 [] ≠ CekValue.VDelay t2 [] := by decide
example : State.Eval [] [] t1 ≠ State.Eval [] [] t2 := by decide
example : Frame.CaseScrutinee [t1] [] ≠ Frame.CaseScrutinee [t2] [] := by decide

-- `==` on a BLS constant runs but does not reduce, so these are guards rather than `decide` examples.
#guard CekValue.VCon (Const.Bls12_381_G1_element Cryptograph.BLS12_381.g1)
    == CekValue.VCon (Const.Bls12_381_G1_element Cryptograph.BLS12_381.g1)

#guard CekValue.VCon (Const.Bls12_381_G1_element Cryptograph.BLS12_381.g1)
    != CekValue.VCon (Const.Bls12_381_G1_element .infinity)

end

end PlutusCore.UPLC.CekMachine
