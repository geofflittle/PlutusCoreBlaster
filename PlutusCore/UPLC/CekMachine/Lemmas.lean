import PlutusCore.UPLC.CekMachine

namespace PlutusCore.UPLC.CekMachine

open PlutusCore.Default
open PlutusCore.UPLC.CekValue (CekValue)

/-! ## Fuel-free step iteration

`stepAbs`/`stepN` give a fuel-free iteration of `step` that absorbs `Halt`/`Error` (a no-op
once the machine is done), instead of raw `runSteps`'s fuel-exhaustion `Error`. The theorems
below relate the two and prove the fuel-composition facts needed to split a run into two
independently-analyzable pieces. -/

/-- `step` with `Halt`/`Error` absorbing (raw `step` sends both to `Error`; we want an
    iteration that just sits still once the machine is done). -/
def stepAbs (sv : BuiltinSemanticsVariant) (s : State) : State :=
  match s with
  | State.Halt V => State.Halt V
  | State.Error => State.Error
  | _ => step sv s

/-- Fuel-free iteration of `stepAbs`. -/
def stepN (sv : BuiltinSemanticsVariant) (s : State) : Nat → State
  | 0 => s
  | (k + 1) => stepN sv (stepAbs sv s) k

@[simp] theorem runSteps_halt (sv : BuiltinSemanticsVariant) (V : CekValue) (n : Nat) :
    runSteps sv (State.Halt V) n = State.Halt V := by
  cases n <;> rfl

@[simp] theorem runSteps_error (sv : BuiltinSemanticsVariant) (n : Nat) :
    runSteps sv State.Error n = State.Error := by
  cases n <;> rfl

/-- `stepAbs` agrees with `step` off `Halt`/`Error`, and is a no-op on them. -/
theorem stepAbs_not_halt_error (sv : BuiltinSemanticsVariant) (s : State)
    (h1 : ∀ V, s ≠ State.Halt V) (h2 : s ≠ State.Error) :
    stepAbs sv s = step sv s := by
  unfold stepAbs
  cases s with
  | Halt V => exact absurd rfl (h1 V)
  | Error => exact absurd rfl h2
  | Eval _ _ _ => rfl
  | Return _ _ => rfl

/-- One step of `runSteps` folds into one step of `stepAbs`. This is the key
    "fuel-free" reindexing: it holds UNCONDITIONALLY (no side hypothesis on `s`),
    because both sides already agree on the absorbing `Halt`/`Error` cases. -/
theorem runSteps_succ (sv : BuiltinSemanticsVariant) (s : State) (k : Nat) :
    runSteps sv s (k + 1) = runSteps sv (stepAbs sv s) k := by
  cases s with
  | Halt V => simp [stepAbs]
  | Error => simp [stepAbs]
  | Eval st rho t => rfl
  | Return st v => rfl

/-- Once halted at `m` steps, still halted at `m + k` steps for any extra fuel `k`. -/
theorem runSteps_halt_stable (sv : BuiltinSemanticsVariant) (s : State) (V : CekValue)
    (m k : Nat) (h : runSteps sv s m = State.Halt V) :
    runSteps sv s (m + k) = State.Halt V := by
  induction m generalizing s with
  | zero =>
      cases s with
      | Halt V' =>
          simp only [runSteps] at h
          cases h
          simp [runSteps_halt]
      | Error =>
          simp only [runSteps] at h
          injection h
      | Eval st rho t =>
          simp only [runSteps] at h
          injection h
      | Return st v =>
          simp only [runSteps] at h
          injection h
  | succ n ih =>
      rw [runSteps_succ] at h
      have : runSteps sv s (n + 1 + k) = runSteps sv (stepAbs sv s) (n + k) := by
        have heq : n + 1 + k = (n + k) + 1 := by omega
        rw [heq, runSteps_succ]
      rw [this]
      exact ih (stepAbs sv s) h

/-- The core fuel-composition lemma: running `m + n` steps from `s` equals running
    `n` more steps from the fuel-free `m`-step iterate `stepN sv s m`. Holds
    UNCONDITIONALLY (no fuel-exhaustion side condition), because `stepN`/`stepAbs`
    already absorb `Halt`/`Error`, so splitting never introduces a spurious `Error`
    the way splitting raw `runSteps` (whose `0, _ => Error` branch fires on real
    fuel exhaustion) would. -/
theorem runSteps_add (sv : BuiltinSemanticsVariant) (s : State) (m n : Nat) :
    runSteps sv s (m + n) = runSteps sv (stepN sv s m) n := by
  induction m generalizing s with
  | zero => simp [stepN]
  | succ k ih =>
      have heq : k + 1 + n = (k + n) + 1 := by omega
      rw [heq, runSteps_succ, ih (stepAbs sv s)]
      rfl

end PlutusCore.UPLC.CekMachine
