import PlutusCore.UPLC.CekMachine
<<<<<<< HEAD
<<<<<<< HEAD
import PlutusCore.UPLC.PlutusScript
=======
>>>>>>> a264431 (test: add Plutus conformance test suite (1134 test cases))
=======
import PlutusCore.UPLC.PlutusScript
>>>>>>> 792d81e (Fixes for compliance test suite)
import PlutusCore.UPLC.ScriptEncoding.Basic

/-- A variant of `#import_uplc` for conformance parse-error tests.
    Behaves identically on success; on any parse failure emits a fixed
    `"Parsing error"` message instead of the verbose diagnostic. -/
syntax (name := conformanceImportUplc) "#conformance_import_uplc" ident str : command

open Lean Elab Command Term in
@[command_elab conformanceImportUplc]
def conformanceImportUplcImpl : CommandElab := fun stx => do
  let declName := stx[1].getId
<<<<<<< HEAD
  let path ←
    match stx[2].isStrLit? with
    | some x => pure x
    | none   => throwError "empty path"
=======
  let path     := stx[2].isStrLit?.getD ""
>>>>>>> a264431 (test: add Plutus conformance test suite (1134 test cases))
  -- Read the file; any IO error counts as a parse error
  let content ← try IO.FS.readFile path catch _ => throwError "Parsing error"
  -- Parse the UPLC text; any parse error emits the standard message
  let prog ←
    match PlutusCore.UPLC.TextEncoding.programFromString content with
    | .ok p    => pure p
    | .error _ => throwError "Parsing error"
  logInfo s!"Successfully decoded textual '{path}'"
  -- Register the definition exactly as #import_uplc does
  let decl ← runTermElabM fun _ => do
    let progExpr := Lean.toExpr prog
    let t ← Meta.inferType progExpr
    return Declaration.defnDecl {
      name        := declName
      levelParams := []
      type        := t
      value       := progExpr
      hints       := .abbrev
      safety      := .safe
    }
  liftCoreM <| addAndCompile decl

namespace Tests.Conformance

open PlutusCore.UPLC.CekMachine
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.Term
<<<<<<< HEAD
<<<<<<< HEAD
open PlutusCore.UPLC.PlutusScript
=======
>>>>>>> a264431 (test: add Plutus conformance test suite (1134 test cases))
=======
open PlutusCore.UPLC.PlutusScript
>>>>>>> 792d81e (Fixes for compliance test suite)
open PlutusCore.UPLC.ExBudget
open PlutusCore.Default

-- Needed so that partial defs returning Term can compile in the mutual block below.
private instance : Inhabited Term := ⟨.Error⟩

-- Look up a variable in an Environment (most-recent binding wins).
private def envLookup : Environment → String → Option CekValue
  | .EmptyEnvironment            , _ => none
  | .NonEmptyEnvironment rest k v, x => if k == x then some v else envLookup rest x

-- All six helpers live in one mutual block so that cekValueBeq can call
-- closeTermWithEnv and alphaEqWith without forward-reference issues.
--
-- VLam and VDelay close their bodies using their environments before
-- alpha-comparing, so closures that differ only in how the environment
-- is folded into the body still compare as equal.
mutual
  -- Alpha-equivalence for Terms.
  -- ctx is a stack of (name-in-t1, name-in-t2) pairs introduced by binders we've descended into.
  -- Free variables must match by name; bound variables match by position.
<<<<<<< HEAD
  private def alphaEqWith (ctx : List (String × String)) : Term → Term → Bool
=======
  private partial def alphaEqWith (ctx : List (String × String)) : Term → Term → Bool
>>>>>>> a264431 (test: add Plutus conformance test suite (1134 test cases))
    | .Var x,         .Var y         =>
        match ctx.find? (fun p => p.1 == x) with
        | some (_, z) => z == y
        | none        => x == y
    | .Lam x b1,      .Lam y b2      => alphaEqWith ((x, y) :: ctx) b1 b2
    | .Apply f1 a1,   .Apply f2 a2   => alphaEqWith ctx f1 f2 && alphaEqWith ctx a1 a2
    | .Delay t1,      .Delay t2      => alphaEqWith ctx t1 t2
    | .Force t1,      .Force t2      => alphaEqWith ctx t1 t2
    | .Const c1,      .Const c2      => c1 == c2
    | .Builtin b1,    .Builtin b2    => b1 == b2
    | .Constr n1 ts1, .Constr n2 ts2 => n1 == n2 && alphaEqListWith ctx ts1 ts2
    | .Case s1 hs1,   .Case s2 hs2   => alphaEqWith ctx s1 s2 && alphaEqListWith ctx hs1 hs2
    | .Error,         .Error         => true
    | _,              _              => false

<<<<<<< HEAD
  private def alphaEqListWith (ctx : List (String × String)) : List Term → List Term → Bool
    | [],      []      => true
    | t :: ts, u :: us => alphaEqWith ctx t u && alphaEqListWith ctx ts us
    | _,       _       => false
end

mutual
  -- Convert a CekValue back to a Term for substitution.
  private def cekValueToTerm : Nat → CekValue → Term
    | p + 1, .VCon c            => .Const c
    | p + 1, .VLam x body env   => .Lam x (closeTermWithEnv env [x] p body)
    | p + 1, .VDelay body env   => .Delay (closeTermWithEnv env []  p body)
    | p + 1, .VConstr n args    => .Constr n (args.map (cekValueToTerm p))
    | p + 1, .VBuiltin f args _ => args.foldr (fun v acc => .Apply acc (cekValueToTerm p v)) (.Builtin f)
    | 0    , _                  => .Error

  -- Close a Term by substituting free variables (not in `bound`) from `env`.
  private def closeTermWithEnv (env : Environment) (bound : List String) : Nat → Term → Term
    | p + 1, .Var x =>
        if bound.contains x then .Var x
        else match envLookup env x with
             | some v => cekValueToTerm p v
             | none   => .Var x
    | p + 1, .Lam x body  => .Lam x (closeTermWithEnv env (x :: bound) p body)
    | p + 1, .Apply f a   => .Apply (closeTermWithEnv env bound p f) (closeTermWithEnv env bound p a)
    | p + 1, .Delay t     => .Delay (closeTermWithEnv env bound p t)
    | p + 1, .Force t     => .Force (closeTermWithEnv env bound p t)
    | p + 1, .Constr n ts => .Constr n (ts.map (closeTermWithEnv env bound p))
    | p + 1, .Case s hs   => .Case (closeTermWithEnv env bound p s) (hs.map (closeTermWithEnv env bound p))
    | _    , t            => t

  private def cekValueBeq : Nat → CekValue → CekValue → Bool
    | _    , .VCon c1,              .VCon c2              => c1 == c2
    | p + 1, .VConstr n1 args1,     .VConstr n2 args2     => n1 == n2 && cekValueListBeq p args1 args2
    | p + 1, .VBuiltin f1 args1 _,  .VBuiltin f2 args2 _  => f1 == f2 && cekValueListBeq p args1 args2
    | p + 1, .VLam x1 t1 env1,      .VLam x2 t2 env2      =>
        alphaEqWith [(x1, x2)] (closeTermWithEnv env1 [x1] p t1) (closeTermWithEnv env2 [x2] p t2)
    | p + 1, .VDelay t1 env1,       .VDelay t2 env2       =>
        alphaEqWith [] (closeTermWithEnv env1 [] p t1) (closeTermWithEnv env2 [] p t2)
    | _    , _              , _                           => false

  private def cekValueListBeq : Nat → List CekValue → List CekValue → Bool
    | p + 1, x :: xs, y :: ys => cekValueBeq p x y && cekValueListBeq p xs ys
    | _    , [],      []      => true
    | _    , _      , _       => false
end

=======
  private partial def alphaEqListWith (ctx : List (String × String)) : List Term → List Term → Bool
    | [],      []      => true
    | t :: ts, u :: us => alphaEqWith ctx t u && alphaEqListWith ctx ts us
    | _,       _       => false

  -- Convert a CekValue back to a Term for substitution.
  private partial def cekValueToTerm : CekValue → Term
    | .VCon c            => .Const c
    | .VLam x body env   => .Lam x (closeTermWithEnv env [x] body)
    | .VDelay body env   => .Delay (closeTermWithEnv env [] body)
    | .VConstr n args    => .Constr n (args.map cekValueToTerm)
    | .VBuiltin f args _ => args.foldr (fun v acc => .Apply acc (cekValueToTerm v)) (.Builtin f)

  -- Close a Term by substituting free variables (not in `bound`) from `env`.
  private partial def closeTermWithEnv (env : Environment) (bound : List String) : Term → Term
    | .Var x       =>
        if bound.contains x then .Var x
        else match envLookup env x with
             | some v => cekValueToTerm v
             | none   => .Var x
    | .Lam x body  => .Lam x (closeTermWithEnv env (x :: bound) body)
    | .Apply f a   => .Apply (closeTermWithEnv env bound f) (closeTermWithEnv env bound a)
    | .Delay t     => .Delay (closeTermWithEnv env bound t)
    | .Force t     => .Force (closeTermWithEnv env bound t)
    | .Constr n ts => .Constr n (ts.map (closeTermWithEnv env bound))
    | .Case s hs   => .Case (closeTermWithEnv env bound s) (hs.map (closeTermWithEnv env bound))
    | t            => t

  private partial def cekValueBeq : CekValue → CekValue → Bool
    | .VCon c1,              .VCon c2              => c1 == c2
    | .VConstr n1 args1,     .VConstr n2 args2     => n1 == n2 && cekValueListBeq args1 args2
    | .VBuiltin f1 args1 e1, .VBuiltin f2 args2 e2 => f1 == f2 && e1 == e2 && cekValueListBeq args1 args2
    | .VLam x1 t1 env1,      .VLam x2 t2 env2      =>
        alphaEqWith [(x1, x2)] (closeTermWithEnv env1 [x1] t1) (closeTermWithEnv env2 [x2] t2)
    | .VDelay t1 env1,       .VDelay t2 env2       =>
        alphaEqWith [] (closeTermWithEnv env1 [] t1) (closeTermWithEnv env2 [] t2)
    | _,                     _                     => false

  private partial def cekValueListBeq : List CekValue → List CekValue → Bool
    | [],      []      => true
    | x :: xs, y :: ys => cekValueBeq x y && cekValueListBeq xs ys
    | _,       _       => false
end

instance : BEq CekValue := ⟨cekValueBeq⟩

>>>>>>> a264431 (test: add Plutus conformance test suite (1134 test cases))
/-- A large step budget used for conformance test value evaluation.
    Set high enough that no conformance test should exhaust it. -/
def conformanceSteps : Nat := 10_000_000_000

/-- Int64 max; Haskell's budget arithmetic saturates at this value. -/
def int64Max : Nat := 9223372036854775807

/-- A large ExBudget used for conformance test budget evaluation.
    Must exceed any single-step cost that Haskell's Int64 arithmetic saturates
    (e.g. DropList with a very large n can cost ~2×10²² before saturation). -/
def conformanceMaxBudget : ExBudget :=
  { exBudgetCPU    := { unExCPU    := 100_000_000_000_000_000_000_000_000 }
  , exBudgetMemory := { unExMemory := 100_000_000_000_000_000_000_000_000 } }

/-- Check whether two programs evaluate to the same CekValue.
    Uses the step-limited evaluator with PlutusV3 semantics.
    Returns true iff both evaluate to the same ground value (or both error). -/
<<<<<<< HEAD
<<<<<<< HEAD
def programsEvalEquiv (p1 p2 : PlutusScript) : Bool :=
  match cekExecuteProgram p1.script [] conformanceSteps,
        cekExecuteProgram p2.script [] conformanceSteps with
  | State.Halt v1, State.Halt v2 => cekValueBeq conformanceSteps v1 v2
=======
def programsEvalEquiv (p1 p2 : Program) : Bool :=
  match cekExecuteProgram p1 [] conformanceSteps,
        cekExecuteProgram p2 [] conformanceSteps with
=======
def programsEvalEquiv (p1 p2 : PlutusScript) : Bool :=
  match cekExecuteProgram p1.script [] conformanceSteps,
        cekExecuteProgram p2.script [] conformanceSteps with
>>>>>>> 792d81e (Fixes for compliance test suite)
  | State.Halt v1, State.Halt v2 => v1 == v2
>>>>>>> a264431 (test: add Plutus conformance test suite (1134 test cases))
  | State.Error,   State.Error   => true
  | _,             _             => false

/-- Check whether a program evaluates to an error (evaluation failure). -/
<<<<<<< HEAD
<<<<<<< HEAD
def programEvalsToError (p : PlutusScript) : Bool :=
  match cekExecuteProgram p.script [] conformanceSteps with
=======
def programEvalsToError (p : Program) : Bool :=
  match cekExecuteProgram p [] conformanceSteps with
>>>>>>> a264431 (test: add Plutus conformance test suite (1134 test cases))
=======
def programEvalsToError (p : PlutusScript) : Bool :=
  match cekExecuteProgram p.script [] conformanceSteps with
>>>>>>> 792d81e (Fixes for compliance test suite)
  | State.Error => true
  | _           => false

/-- Check whether a program's cpu and memory budget matches the expected values.
    Uses PlutusV3 post-Conway semantics, which matches the conformance test defaults. -/
<<<<<<< HEAD
<<<<<<< HEAD
def budgetMatches (p : PlutusScript) (expectedCpu expectedMem : Nat) : Bool :=
  match cekExecuteProgramWithBudget p.script .plutusV3 .postConway [] conformanceMaxBudget with
  | EvaluationResult.Success _ b =>
      -- Haskell uses Int64 saturation arithmetic: costs exceeding Int64.max
      -- saturate to Int64.max rather than overflowing. Apply the same cap here.
      let actualCpu := min b.exBudgetCPU.unExCPU       int64Max
=======
def budgetMatches (p : Program) (expectedCpu expectedMem : Nat) : Bool :=
  match cekExecuteProgramWithBudget p .plutusV3 .postConway [] conformanceMaxBudget with
=======
def budgetMatches (p : PlutusScript) (expectedCpu expectedMem : Nat) : Bool :=
  match cekExecuteProgramWithBudget p.script .plutusV3 .postConway [] conformanceMaxBudget with
>>>>>>> 792d81e (Fixes for compliance test suite)
  | EvaluationResult.Success _ b =>
      -- Haskell uses Int64 saturation arithmetic: costs exceeding Int64.max
      -- saturate to Int64.max rather than overflowing. Apply the same cap here.
      let actualCpu := min b.exBudgetCPU.unExCPU    int64Max
>>>>>>> a264431 (test: add Plutus conformance test suite (1134 test cases))
      let actualMem := min b.exBudgetMemory.unExMemory int64Max
      actualCpu == expectedCpu && actualMem == expectedMem
  | _ => false

end Tests.Conformance
