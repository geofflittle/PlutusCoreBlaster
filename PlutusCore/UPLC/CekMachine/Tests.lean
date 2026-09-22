import PlutusCore.UPLC.CekMachine.DecidableEq
import PlutusCore.UPLC.CekMachine.Lemmas

namespace PlutusCore.UPLC.CekMachine

open PlutusCore.Default
open PlutusCore.UPLC.CekValue (CekValue Environment)

/-! ## Concrete checks for the iteration of `step`. -/

def testSemanticsVariant : BuiltinSemanticsVariant :=
  PlutusCore.Default.Internal.BuiltinSemanticsVariant.defaultFunSemanticsVariantB

/-- A constant, which the machine evaluates in exactly two steps. -/
def testTerm : PlutusCore.UPLC.Term.Term :=
  PlutusCore.UPLC.Term.Term.Const (PlutusCore.UPLC.Term.Const.Integer 42)

/-- The unevaluated starting state for `testTerm`. -/
def testStart : State := State.Eval [] [] testTerm

/-- Where `testTerm` ends up. -/
def testResult : CekValue :=
  PlutusCore.UPLC.CekValue.CekValue.VCon (PlutusCore.UPLC.Term.Const.Integer 42)

-- `stepN` really iterates.
example : stepN testSemanticsVariant testStart 1
    = State.Return [] testResult := rfl
example : stepN testSemanticsVariant testStart 2
    = State.Halt testResult := rfl
example : stepN testSemanticsVariant testStart 1
    ≠ stepN testSemanticsVariant testStart 2 := by nofun

-- `step` returns a `Halt` state and `State.Error` unchanged.
example (V : CekValue) :
    step testSemanticsVariant (State.Halt V) = State.Halt V := rfl
example : step testSemanticsVariant State.Error = State.Error := rfl

-- On a non-terminal state it does not.
example : step testSemanticsVariant testStart ≠ testStart := by nofun

-- At zero fuel `stepN` is the identity.
example (s : State) : stepN testSemanticsVariant s 0 = s := rfl

-- Splitting through `runSteps` turns a halting run into an `Error`. Splitting
-- through `stepN` does not.
example : runSteps testSemanticsVariant testStart 1 = State.Error := rfl
example : runSteps testSemanticsVariant testStart 2
    = State.Halt testResult := rfl
example :
    runSteps testSemanticsVariant (runSteps testSemanticsVariant testStart 1) 1
      = State.Error := rfl
example :
    runSteps testSemanticsVariant (stepN testSemanticsVariant testStart 1) 1
      = State.Halt testResult := rfl

-- One step short of enough fuel the program is an `Error`, and past enough the halt
-- result does not change.
def testProgram : PlutusCore.UPLC.Term.Program :=
  PlutusCore.UPLC.Term.Program.Program (PlutusCore.UPLC.Term.Version.Version 1 1 0) testTerm

example : cekExecuteProgramWithSemanticVariant testSemanticsVariant testProgram [] 1
    = State.Error := rfl
example (m : Nat) :
    cekExecuteProgramWithSemanticVariant testSemanticsVariant testProgram [] (2 + m)
      = State.Halt testResult :=
  cekExecuteProgramWithSemanticVariant_halt_stable testSemanticsVariant testProgram []
    testResult 2 m rfl

/-! ### At a realistic size -/

/-- `Force (Delay (Force (Delay ... testTerm)))`, `n` layers deep. -/
def deepTerm : Nat → PlutusCore.UPLC.Term.Term
  | 0 => testTerm
  | n + 1 => .Force (.Delay (deepTerm n))

/-- `n` distinct values, so no two entries can be confused for each other. -/
def bigEnv (n : Nat) : Environment :=
  (List.range n).map fun i => PlutusCore.UPLC.CekValue.CekValue.VCon
    (PlutusCore.UPLC.Term.Const.Integer (Int.ofNat i))

/-- `n` application frames, each awaiting a distinct `Var`. -/
def bigStack (n : Nat) : Stack :=
  (List.range n).map fun i => Frame.LeftApplicationToTerm (PlutusCore.UPLC.Term.Term.Var i) []

/-- A ten-frame stack, a thirty-entry environment, and a thirty-deep term. -/
def bigState : State := State.Eval (bigStack 10) (bigEnv 30) (deepTerm 30)

/-- `bigState` with the entry at index 29, the very last one, replaced. -/
def bigStateAlt : State :=
  State.Eval (bigStack 10)
    ((bigEnv 30).set 29 (PlutusCore.UPLC.CekValue.CekValue.VCon
      (PlutusCore.UPLC.Term.Const.Integer 999)))
    (deepTerm 30)

example : bigState ≠ bigStateAlt := by nofun

/-! ### Checks that need the instances -/

-- The body at each `n` is a state disequality, decided by `DecidableEq State`.
example : ∀ n, n < 4 → stepN testSemanticsVariant testStart n ≠ State.Error := by decide

-- `eraseDups` and `count` compare states through `instBEqState`.
example : [bigState, bigStateAlt, bigState].eraseDups.length = 2 := by decide

example : ([bigState, bigStateAlt].count bigState) = 1 := by decide

-- Index two on the `testStart` run is terminal, and no earlier index is.
example : terminal (stepN testSemanticsVariant testStart 2) := by decide

example : ∀ i, i < 2 → ¬ terminal (stepN testSemanticsVariant testStart i) := by decide

-- The state at two is the state at every later index.
example (m : Nat) :
    stepN testSemanticsVariant testStart (2 + m)
      = stepN testSemanticsVariant testStart 2 :=
  stepN_fix testSemanticsVariant testStart 2 (by decide) m

/-! ### A `Data` constant through the machine -/

section
open PlutusCore.UPLC.Term

/-- A `Data` payload with a `Constr`, an `I`, a `B` and a nested `List`. -/
def testData : PlutusCore.Data.Data := .Constr 0 [.I 1, .B "ab", .List [.I 2]]

def dataTerm : Term := .Force (.Delay (.Const (.Data testData)))

/-- The unevaluated starting state for `testData`. -/
def testDataStart : State := State.Eval [] [] dataTerm

/-- The first `n` states of the run from `testDataStart`. -/
def dataTrace (n : Nat) : List State :=
  (List.range n).map (stepN testSemanticsVariant testDataStart)

/-- The run halts after five steps, on the `Data` constant inside the `Delay`. -/
theorem dataTrace_halts : stepN testSemanticsVariant testDataStart 5
    = State.Halt (CekValue.VCon (Const.Data testData)) := by decide

-- The first six states are distinct.
example : (dataTrace 6).Nodup := by decide

-- No index before five on this run is terminal.
example : ∀ i, i < 5 → ¬ terminal (stepN testSemanticsVariant testDataStart i) := by decide

-- The state at five and at every later index is halted on the `Data` constant.
example (m : Nat) :
    stepN testSemanticsVariant testDataStart (5 + m)
      = State.Halt (CekValue.VCon (Const.Data testData)) :=
  (stepN_fix testSemanticsVariant testDataStart 5 (by decide) m).trans dataTrace_halts

def dataProgram : Program :=
  Program.Program (Version.Version 1 1 0) dataTerm

-- One step short of enough fuel the program is an `Error`.
example : cekExecuteProgramWithSemanticVariant testSemanticsVariant dataProgram [] 4
    = State.Error := by decide

-- At five and at every larger fuel the program halts on the `Data` constant.
example : cekExecuteProgramWithSemanticVariant testSemanticsVariant dataProgram [] 5
    = State.Halt (CekValue.VCon (Const.Data testData)) := by decide

example (m : Nat) :
    cekExecuteProgramWithSemanticVariant testSemanticsVariant dataProgram [] (5 + m)
      = State.Halt (CekValue.VCon (Const.Data testData)) :=
  cekExecuteProgramWithSemanticVariant_halt_stable testSemanticsVariant dataProgram []
    (CekValue.VCon (Const.Data testData)) 5 m (by decide)

def equalsDataTerm : Term :=
  .Apply (.Apply (.Builtin .EqualsData) (.Const (.Data testData))) (.Const (.Data testData))

/-- The unevaluated starting state for `equalsDataTerm`. -/
def equalsDataStart : State := State.Eval [] [] equalsDataTerm

-- At index ten the builtin has halted on `true`.
example : stepN testSemanticsVariant equalsDataStart 10
    = State.Halt (CekValue.VCon (Const.Bool true)) := by decide

/-- `testData` with the entry of its nested `List` changed. -/
def neqData : PlutusCore.Data.Data := .Constr 0 [.I 1, .B "ab", .List [.I 3]]

def neqDataTerm : Term :=
  .Apply (.Apply (.Builtin .EqualsData) (.Const (.Data testData))) (.Const (.Data neqData))

/-- The unevaluated starting state for `neqDataTerm`. -/
def neqDataStart : State := State.Eval [] [] neqDataTerm

-- At index ten the builtin has halted on `false`.
example : stepN testSemanticsVariant neqDataStart 10
    = State.Halt (CekValue.VCon (Const.Bool false)) := by decide

-- None of the first eleven states of the `equalsDataStart` run is an `Error`.
example : ∀ n, n < 11 → stepN testSemanticsVariant equalsDataStart n ≠ State.Error := by decide

end

end PlutusCore.UPLC.CekMachine
