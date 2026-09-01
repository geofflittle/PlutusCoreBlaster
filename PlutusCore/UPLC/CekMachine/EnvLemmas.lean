import PlutusCore.UPLC.CekMachine

-- Migration of sundae-v4's `Formalization/Scratch/EnvLemma.lean` (general CEK environment/
-- value step-indexed agreement metatheory, frozen source commit `50cd4f699` in that repo) onto
-- this repo's positional `Environment := List CekValue` / de Bruijn `Term.Var : Nat → Term`
-- representation (PR #21, merged `e708754`). Round 1: the foundational front portion only
-- (`envLookup`, `freeVars`, the `ValueAgree`/`EnvAgreeOn` step-indexed relation and its beta-
-- extension lemma, `step_var_agree`, `step_const_agree`). The remaining `Part 7` onward
-- (`Frame`/`Stack`/`State` agreement, the per-constructor `step_agree_*` family, the builtin-
-- congruence set piece, the multi-step chaining induction, and the closing counterexample
-- refuting the fully general fixed-fuel `eval_agree` statement) is deferred to a later round,
-- see this file's own closing comment for exactly what and why.
--
-- REPRESENTATION-CHANGE JUDGMENT CALLS made in this round (not mechanical renaming):
--
-- 1. `envLookup` used to pattern-match `Environment.EmptyEnvironment`/`NonEmptyEnvironment` and
--    branch on `String` equality. The new `Environment` is `abbrev Environment := List CekValue`
--    (`CekValue.lean`) and `step` itself looks a `Var` up positionally via
--    `List.get?Internal ρ i` (`CekMachine.lean` line 65) -- there is no analogue of
--    `ifBoundOtherwiseError` left to restate a lemma about (the real `step` inlines the lookup
--    directly), so `envLookup` here is a thin, `rfl`-transparent wrapper around
--    `List.get?Internal`, kept only so later proofs read the same way the old file's did.
--
-- 2. `freeVars` used to return `List String` (names). Under de Bruijn indexing "the free
--    variables of `M`" means the set of indices `M` reads THROUGH ALL of its own binders --
--    i.e. indices not bound within `M` itself. This is genuinely different content, not a
--    `String`-to-`Nat` relabeling: a `Lam`'s body binds a NEW index `0`, so computing the
--    body's free set relative to the OUTER (closure-captured) environment needs to both DROP
--    occurrences of the newly-bound index 0 (matching the old `.erase x`) AND SHIFT every
--    remaining free index down by one (no old-representation analogue at all, since names never
--    needed renumbering). `freeVarsUnderBinder` names this shift-and-drop operation explicitly.
--
-- 3. `beta_envAgreeOn_extend`: the pilot (git-bug `8c50efd`, `envLookup_skip`) already found that
--    this family's `hxy : x ≠ y` runtime name-disequality hypothesis has NO analogue under
--    positional indexing -- "the newly bound slot" is always index `0` by construction, so
--    "some other index" is always of the shifted form `i + 1`, a STATIC fact, not a runtime
--    check. This lemma is the `EnvAgreeOn`-level generalization of that same finding (the pilot
--    only checked the single-binding, hypothesis-free special case).
open PlutusCore.Default
open PlutusCore.UPLC.Term
open PlutusCore.UPLC.CekValue
open PlutusCore.UPLC.CekMachine

namespace PlutusCore.UPLC.CekMachine.EnvLemmas

-- ── Part 1: pure environment lookup. `List.get?Internal` is exactly what `step`'s own `Var`
-- case calls (`CekMachine.lean` line 65); wrapping it here is purely for readability parity with
-- the old file, it is definitionally transparent (`rfl`/`unfold` see straight through it). ──────

def envLookup (ρ : Environment) (i : Nat) : Option CekValue := List.get?Internal ρ i

@[simp] theorem envLookup_zero (V : CekValue) (ρ : Environment) :
    envLookup (V :: ρ) 0 = some V := rfl

@[simp] theorem envLookup_succ (V : CekValue) (ρ : Environment) (i : Nat) :
    envLookup (V :: ρ) (i + 1) = envLookup ρ i := rfl

-- ── Part 2: free variable INDICES of a Term (de Bruijn analogue of the old `List String`). ─────

/-- Shift-and-drop: given a body's own free-index set (computed as if it were a top-level term,
    so it still contains occurrences of a freshly-consumed binder at index 0), drop the
    newly-bound occurrences and shift every remaining index down by one. This is what a `Lam`'s
    body needs relative to its OUTER (closure-captured) environment -- the de Bruijn analogue of
    the old representation's `(freeVars M).erase x`, with an added shift that has no
    old-representation counterpart (names never needed renumbering, positions do). -/
def freeVarsUnderBinder (S : List Nat) : List Nat :=
  S.filterMap fun i => if i = 0 then none else some (i - 1)

def freeVars : Term → List Nat
  | .Var i => [i]
  | .Const _ => []
  | .Builtin _ => []
  | .Lam _ M => freeVarsUnderBinder (freeVars M)
  | .Apply M N => freeVars M ++ freeVars N
  | .Delay M => freeVars M
  | .Force M => freeVars M
  | .Constr _ Ms => (Ms.map freeVars).flatten
  | .Case N Ms => freeVars N ++ (Ms.map freeVars).flatten
  | .Error => []

def freeVarsList (Ms : List Term) : List Nat := (Ms.map freeVars).flatten

-- ── Part 3: the step-indexed value/environment agreement relation. Same step-indexing rationale
-- as the old file (self-referential closures defeat plain structural well-foundedness on the
-- Environment -- this is a fact about the CEK machine's runtime shape, not about String-vs-Nat
-- representation, so it carries over unchanged). ────────────────────────────────────────────────

/-- Unchanged from the old file verbatim: `fix_ValueAgreeShape` never inspects an `Environment`
    or a `Term.Var`/name at all, only the outer `CekValue` constructor (and, for `VCon`, the
    literal `Const`), so nothing about the representation change touches it. -/
def fix_ValueAgreeShape : CekValue → CekValue → Prop
  | .VCon c1, .VCon c2 => c1 = c2
  | .VDelay _ _, .VDelay _ _ => True
  | .VLam _ _ _, .VLam _ _ _ => True
  | .VConstr _ _, .VConstr _ _ => True
  | .VBuiltin _ _ _, .VBuiltin _ _ _ => True
  | _, _ => False

mutual
  def ValueAgree : Nat → CekValue → CekValue → Prop
    | 0, _, _ => True
    | _+1, .VCon c1, .VCon c2 => c1 = c2
    | n+1, .VDelay M1 ρ1, .VDelay M2 ρ2 =>
        M1 = M2 ∧ EnvAgreeOn n (freeVars M1) ρ1 ρ2
    | n+1, .VLam x1 M1 ρ1, .VLam x2 M2 ρ2 =>
        x1 = x2 ∧ M1 = M2 ∧ EnvAgreeOn n (freeVarsUnderBinder (freeVars M1)) ρ1 ρ2
    | n+1, .VConstr i1 vs1, .VConstr i2 vs2 =>
        i1 = i2 ∧ vs1.length = vs2.length ∧
          ∀ k (h1 : k < vs1.length) (h2 : k < vs2.length), ValueAgree n (vs1[k]) (vs2[k])
    | n+1, .VBuiltin b1 vs1 η1, .VBuiltin b2 vs2 η2 =>
        b1 = b2 ∧ η1 = η2 ∧ vs1.length = vs2.length ∧
          (∀ k (h1 : k < vs1.length) (h2 : k < vs2.length), ValueAgree n (vs1[k]) (vs2[k])) ∧
          (∀ k (h1 : k < vs1.length) (h2 : k < vs2.length), fix_ValueAgreeShape (vs1[k]) (vs2[k]))
    | _+1, _, _ => False

  def EnvAgreeOn : Nat → List Nat → Environment → Environment → Prop
    | n, S, ρ1, ρ2 =>
        ∀ i ∈ S,
          match envLookup ρ1 i, envLookup ρ2 i with
          | some v1, some v2 => ValueAgree n v1 v2
          | none, none => True
          | _, _ => False
end

-- Unchanged from the old file verbatim (per-constructor case analysis, no Environment content).
theorem fix_valueAgree_shape (n : Nat) (v1 v2 : CekValue) (h : ValueAgree (n + 1) v1 v2) :
    fix_ValueAgreeShape v1 v2 := by
  cases v1 with
  | VCon c1 =>
      cases v2 with
      | VCon c2 => simpa [ValueAgree, fix_ValueAgreeShape] using h
      | _ => exact absurd h (by simp [ValueAgree])
  | VDelay _ _ =>
      cases v2 with
      | VDelay _ _ => simp [fix_ValueAgreeShape]
      | _ => exact absurd h (by simp [ValueAgree])
  | VLam _ _ _ =>
      cases v2 with
      | VLam _ _ _ => simp [fix_ValueAgreeShape]
      | _ => exact absurd h (by simp [ValueAgree])
  | VConstr _ _ =>
      cases v2 with
      | VConstr _ _ => simp [fix_ValueAgreeShape]
      | _ => exact absurd h (by simp [ValueAgree])
  | VBuiltin _ _ _ =>
      cases v2 with
      | VBuiltin _ _ _ => simp [fix_ValueAgreeShape]
      | _ => exact absurd h (by simp [ValueAgree])

-- `beta_envAgreeOn_extend`: the environment-extension helper the VLam-beta step needs. Genuinely
-- restated, not mechanically reindexed -- see the pilot finding (git-bug `8c50efd`) in this
-- file's header: the old `hxy : y ≠ x` runtime name-disequality hypothesis has no positional
-- analogue, "the newly bound slot" is always index `0` by construction (`step`'s VLam-beta
-- arm conses: `State.Eval s (V :: ρ) M`, `CekMachine.lean` line 90), so the case split is on
-- `i = 0` vs `i = j + 1`, a static fact about the index shape, never a runtime check.
theorem beta_envAgreeOn_extend (n : Nat) (S : List Nat) (ρ1 ρ2 : Environment)
    (V1 V2 : CekValue) (hρ : EnvAgreeOn n (freeVarsUnderBinder S) ρ1 ρ2)
    (hV : ValueAgree n V1 V2) :
    EnvAgreeOn n S (V1 :: ρ1) (V2 :: ρ2) := by
  unfold EnvAgreeOn
  intro i hi
  unfold EnvAgreeOn at hρ
  cases i with
  | zero =>
      simp only [envLookup_zero]
      exact hV
  | succ j =>
      have hj' : j ∈ freeVarsUnderBinder S := by
        simp only [freeVarsUnderBinder, List.mem_filterMap]
        exact ⟨j + 1, hi, by simp⟩
      have := hρ j hj'
      simpa [envLookup_succ] using this

-- ── Part 4: one-step `Var`-lookup congruence, directly against the real `step`. Same statement
-- shape as the old file's `step_var_agree` (disjunction: both Return-and-agree, or both Error --
-- `EnvAgreeOn` only promises the two lookups AGREE, not that they hit). ────────────────────────

theorem step_var_agree (sv : PlutusCore.Default.BuiltinSemanticsVariant)
    (s : Stack) (ρ1 ρ2 : Environment) (S : List Nat) (i : Nat) (n : Nat)
    (hi : i ∈ S) (hagree : EnvAgreeOn n S ρ1 ρ2) :
    (∃ v1 v2, step sv (State.Eval s ρ1 (Term.Var i)) = State.Return s v1 ∧
              step sv (State.Eval s ρ2 (Term.Var i)) = State.Return s v2 ∧
              ValueAgree n v1 v2) ∨
    (step sv (State.Eval s ρ1 (Term.Var i)) = State.Error ∧
     step sv (State.Eval s ρ2 (Term.Var i)) = State.Error) := by
  unfold EnvAgreeOn at hagree
  have h := hagree i hi
  have hstep1 : step sv (State.Eval s ρ1 (Term.Var i)) =
      (match envLookup ρ1 i with | some V => State.Return s V | none => State.Error) := rfl
  have hstep2 : step sv (State.Eval s ρ2 (Term.Var i)) =
      (match envLookup ρ2 i with | some V => State.Return s V | none => State.Error) := rfl
  cases h1 : envLookup ρ1 i with
  | none =>
      rw [h1] at h
      cases h2 : envLookup ρ2 i with
      | none => right; rw [hstep1, hstep2, h1, h2]; exact ⟨rfl, rfl⟩
      | some v2 => simp [h2] at h
  | some v1 =>
      rw [h1] at h
      cases h2 : envLookup ρ2 i with
      | none => simp [h2] at h
      | some v2 =>
          simp only [h2] at h
          exact Or.inl ⟨v1, v2, by rw [hstep1, h1], by rw [hstep2, h2], h⟩

-- ── Part 5: the Const case, trivial (unchanged shape from the old file -- `Term.Const`'s own
-- constructor is unaffected by the de Bruijn migration, only `Term.Var` changed). ──────────────

theorem step_const_agree (sv : PlutusCore.Default.BuiltinSemanticsVariant)
    (s : Stack) (ρ1 ρ2 : Environment) (c : PlutusCore.UPLC.Term.Const) :
    step sv (State.Eval s ρ1 (Term.Term.Const c)) = State.Return s (CekValue.VCon c) ∧
    step sv (State.Eval s ρ2 (Term.Term.Const c)) = State.Return s (CekValue.VCon c) := by
  constructor <;> rfl

-- ── Part 7: monotonicity, and extending agreement to `Frame`/`Stack`/`State`. Representation-
-- AGNOSTIC bookkeeping (step-indexed logical-relations downward closure, and pure machine control
-- structure that never itself destructs a captured `Environment`) -- translated here essentially
-- unchanged from the old file, the only representation-specific spot is the VLam case picking up
-- `freeVarsUnderBinder (freeVars M1)` in place of the old `(freeVars M1).erase x1`, already
-- established as the right translation above. ──────────────────────────────────────────────────

private theorem mono_valueAgree_envAgreeOn : ∀ n : Nat,
    (∀ v1 v2 : CekValue, ValueAgree (n + 1) v1 v2 → ValueAgree n v1 v2) ∧
    (∀ (S : List Nat) (ρ1 ρ2 : Environment),
      EnvAgreeOn (n + 1) S ρ1 ρ2 → EnvAgreeOn n S ρ1 ρ2) := by
  intro n
  induction n with
  | zero =>
      refine ⟨fun v1 v2 _ => by simp [ValueAgree], ?_⟩
      intro S ρ1 ρ2 h
      unfold EnvAgreeOn at h ⊢
      intro i hi
      have hh := h i hi
      cases hl1 : envLookup ρ1 i with
      | none =>
          cases hl2 : envLookup ρ2 i with
          | none => simp
          | some v2 => simp [hl1, hl2] at hh
      | some v1 =>
          cases hl2 : envLookup ρ2 i with
          | none => simp [hl1, hl2] at hh
          | some v2 => simp [ValueAgree]
  | succ m ih =>
      obtain ⟨ihV, ihE⟩ := ih
      have monoV : ∀ v1 v2 : CekValue, ValueAgree (m + 1 + 1) v1 v2 → ValueAgree (m + 1) v1 v2 := by
        intro v1 v2 h
        cases v1 with
        | VCon c1 =>
            cases v2 with
            | VCon c2 => simpa [ValueAgree] using h
            | VDelay _ _ => exact absurd h (by simp [ValueAgree])
            | VLam _ _ _ => exact absurd h (by simp [ValueAgree])
            | VConstr _ _ => exact absurd h (by simp [ValueAgree])
            | VBuiltin _ _ _ => exact absurd h (by simp [ValueAgree])
        | VDelay M1 ρ1 =>
            cases v2 with
            | VCon _ => exact absurd h (by simp [ValueAgree])
            | VDelay M2 ρ2 =>
                simp only [ValueAgree] at h ⊢
                obtain ⟨hM, hE⟩ := h
                exact ⟨hM, ihE _ ρ1 ρ2 hE⟩
            | VLam _ _ _ => exact absurd h (by simp [ValueAgree])
            | VConstr _ _ => exact absurd h (by simp [ValueAgree])
            | VBuiltin _ _ _ => exact absurd h (by simp [ValueAgree])
        | VLam x1 M1 ρ1 =>
            cases v2 with
            | VCon _ => exact absurd h (by simp [ValueAgree])
            | VDelay _ _ => exact absurd h (by simp [ValueAgree])
            | VLam x2 M2 ρ2 =>
                simp only [ValueAgree] at h ⊢
                obtain ⟨hx, hM, hE⟩ := h
                exact ⟨hx, hM, ihE _ ρ1 ρ2 hE⟩
            | VConstr _ _ => exact absurd h (by simp [ValueAgree])
            | VBuiltin _ _ _ => exact absurd h (by simp [ValueAgree])
        | VConstr i1 vs1 =>
            cases v2 with
            | VCon _ => exact absurd h (by simp [ValueAgree])
            | VDelay _ _ => exact absurd h (by simp [ValueAgree])
            | VLam _ _ _ => exact absurd h (by simp [ValueAgree])
            | VConstr i2 vs2 =>
                simp only [ValueAgree] at h ⊢
                obtain ⟨hi, hlen, hpt⟩ := h
                exact ⟨hi, hlen, fun k h1 h2 => ihV _ _ (hpt k h1 h2)⟩
            | VBuiltin _ _ _ => exact absurd h (by simp [ValueAgree])
        | VBuiltin b1 vs1 η1 =>
            cases v2 with
            | VCon _ => exact absurd h (by simp [ValueAgree])
            | VDelay _ _ => exact absurd h (by simp [ValueAgree])
            | VLam _ _ _ => exact absurd h (by simp [ValueAgree])
            | VConstr _ _ => exact absurd h (by simp [ValueAgree])
            | VBuiltin b2 vs2 η2 =>
                simp only [ValueAgree] at h ⊢
                obtain ⟨hb, hη, hlen, hpt, hshape⟩ := h
                exact ⟨hb, hη, hlen, fun k h1 h2 => ihV _ _ (hpt k h1 h2), hshape⟩
      refine ⟨monoV, ?_⟩
      intro S ρ1 ρ2 h
      unfold EnvAgreeOn at h ⊢
      intro i hi
      have hh := h i hi
      cases hl1 : envLookup ρ1 i with
      | none =>
          cases hl2 : envLookup ρ2 i with
          | none => simp
          | some v2 => simp [hl1, hl2] at hh
      | some v1 =>
          cases hl2 : envLookup ρ2 i with
          | none => simp [hl1, hl2] at hh
          | some v2 =>
              simp only [hl1, hl2] at hh ⊢
              exact monoV v1 v2 hh

theorem ValueAgree_mono : ∀ (n : Nat) (v1 v2 : CekValue),
    ValueAgree (n + 1) v1 v2 → ValueAgree n v1 v2 :=
  fun n v1 v2 => (mono_valueAgree_envAgreeOn n).1 v1 v2

theorem EnvAgreeOn_mono (n : Nat) (S : List Nat) (ρ1 ρ2 : Environment) :
    EnvAgreeOn (n + 1) S ρ1 ρ2 → EnvAgreeOn n S ρ1 ρ2 :=
  (mono_valueAgree_envAgreeOn n).2 S ρ1 ρ2

-- `Frame`/`Stack` agreement: pure machine control structure, never itself destructs a captured
-- `Environment` (only forwards a fuel level to `ValueAgree`/`EnvAgreeOn`), so this is ordinary
-- structural recursion, same as the old file, `freeVars`'s new `List Nat` shape flows through
-- unchanged.

def FrameAgree (n : Nat) : Frame → Frame → Prop
  | .ForceFrame, .ForceFrame => True
  | .LeftApplicationToTerm M1 ρ1, .LeftApplicationToTerm M2 ρ2 =>
      M1 = M2 ∧ EnvAgreeOn n (freeVars M1) ρ1 ρ2
  | .LeftApplicationToValue v1, .LeftApplicationToValue v2 =>
      ValueAgree n v1 v2
  | .RightApplicationOfValue v1, .RightApplicationOfValue v2 =>
      ValueAgree n v1 v2
  | .ConstructorArgument i1 vs1 Ms1 ρ1, .ConstructorArgument i2 vs2 Ms2 ρ2 =>
      i1 = i2 ∧ Ms1 = Ms2 ∧ vs1.length = vs2.length ∧
        (∀ k (h1 : k < vs1.length) (h2 : k < vs2.length), ValueAgree n (vs1[k]) (vs2[k])) ∧
      EnvAgreeOn n (freeVarsList Ms1) ρ1 ρ2
  | .CaseScrutinee Ms1 ρ1, .CaseScrutinee Ms2 ρ2 =>
      Ms1 = Ms2 ∧ EnvAgreeOn n (freeVarsList Ms1) ρ1 ρ2
  | _, _ => False

def StackAgree (n : Nat) : Stack → Stack → Prop
  | [], [] => True
  | f1 :: s1, f2 :: s2 => FrameAgree n f1 f2 ∧ StackAgree n s1 s2
  | _, _ => False

theorem FrameAgree_mono (n : Nat) (f1 f2 : Frame) :
    FrameAgree (n + 1) f1 f2 → FrameAgree n f1 f2 := by
  intro h
  cases f1 with
  | ForceFrame =>
      cases f2 with
      | ForceFrame => simp [FrameAgree]
      | LeftApplicationToTerm _ _ => exact absurd h (by simp [FrameAgree])
      | LeftApplicationToValue _ => exact absurd h (by simp [FrameAgree])
      | RightApplicationOfValue _ => exact absurd h (by simp [FrameAgree])
      | ConstructorArgument _ _ _ _ => exact absurd h (by simp [FrameAgree])
      | CaseScrutinee _ _ => exact absurd h (by simp [FrameAgree])
  | LeftApplicationToTerm M1 ρ1 =>
      cases f2 with
      | ForceFrame => exact absurd h (by simp [FrameAgree])
      | LeftApplicationToTerm M2 ρ2 =>
          obtain ⟨hM, hE⟩ := h
          exact ⟨hM, EnvAgreeOn_mono n (freeVars M1) ρ1 ρ2 hE⟩
      | LeftApplicationToValue _ => exact absurd h (by simp [FrameAgree])
      | RightApplicationOfValue _ => exact absurd h (by simp [FrameAgree])
      | ConstructorArgument _ _ _ _ => exact absurd h (by simp [FrameAgree])
      | CaseScrutinee _ _ => exact absurd h (by simp [FrameAgree])
  | LeftApplicationToValue v1 =>
      cases f2 with
      | ForceFrame => exact absurd h (by simp [FrameAgree])
      | LeftApplicationToTerm _ _ => exact absurd h (by simp [FrameAgree])
      | LeftApplicationToValue v2 => exact ValueAgree_mono n v1 v2 h
      | RightApplicationOfValue _ => exact absurd h (by simp [FrameAgree])
      | ConstructorArgument _ _ _ _ => exact absurd h (by simp [FrameAgree])
      | CaseScrutinee _ _ => exact absurd h (by simp [FrameAgree])
  | RightApplicationOfValue v1 =>
      cases f2 with
      | ForceFrame => exact absurd h (by simp [FrameAgree])
      | LeftApplicationToTerm _ _ => exact absurd h (by simp [FrameAgree])
      | LeftApplicationToValue _ => exact absurd h (by simp [FrameAgree])
      | RightApplicationOfValue v2 => exact ValueAgree_mono n v1 v2 h
      | ConstructorArgument _ _ _ _ => exact absurd h (by simp [FrameAgree])
      | CaseScrutinee _ _ => exact absurd h (by simp [FrameAgree])
  | ConstructorArgument i1 vs1 Ms1 ρ1 =>
      cases f2 with
      | ForceFrame => exact absurd h (by simp [FrameAgree])
      | LeftApplicationToTerm _ _ => exact absurd h (by simp [FrameAgree])
      | LeftApplicationToValue _ => exact absurd h (by simp [FrameAgree])
      | RightApplicationOfValue _ => exact absurd h (by simp [FrameAgree])
      | ConstructorArgument i2 vs2 Ms2 ρ2 =>
          obtain ⟨hi, hMs, hlen, hpt, hE⟩ := h
          exact ⟨hi, hMs, hlen, fun k h1 h2 => ValueAgree_mono n _ _ (hpt k h1 h2),
                 EnvAgreeOn_mono n (freeVarsList Ms1) ρ1 ρ2 hE⟩
      | CaseScrutinee _ _ => exact absurd h (by simp [FrameAgree])
  | CaseScrutinee Ms1 ρ1 =>
      cases f2 with
      | ForceFrame => exact absurd h (by simp [FrameAgree])
      | LeftApplicationToTerm _ _ => exact absurd h (by simp [FrameAgree])
      | LeftApplicationToValue _ => exact absurd h (by simp [FrameAgree])
      | RightApplicationOfValue _ => exact absurd h (by simp [FrameAgree])
      | ConstructorArgument _ _ _ _ => exact absurd h (by simp [FrameAgree])
      | CaseScrutinee Ms2 ρ2 =>
          obtain ⟨hMs, hE⟩ := h
          exact ⟨hMs, EnvAgreeOn_mono n (freeVarsList Ms1) ρ1 ρ2 hE⟩

theorem StackAgree_mono (n : Nat) (s1 s2 : Stack) :
    StackAgree (n + 1) s1 s2 → StackAgree n s1 s2 := by
  induction s1 generalizing s2 with
  | nil =>
      cases s2 with
      | nil => intro _; simp [StackAgree]
      | cons f2 s2' => intro h; exact absurd h (by simp [StackAgree])
  | cons f1 s1' ih =>
      cases s2 with
      | nil => intro h; exact absurd h (by simp [StackAgree])
      | cons f2 s2' =>
          intro h
          obtain ⟨hf, hs⟩ := h
          exact ⟨FrameAgree_mono n f1 f2 hf, ih s2' hs⟩

def StateAgree (n : Nat) : State → State → Prop
  | .Eval s1 ρ1 M1, .Eval s2 ρ2 M2 =>
      M1 = M2 ∧ StackAgree n s1 s2 ∧ EnvAgreeOn n (freeVars M1) ρ1 ρ2
  | .Return s1 v1, .Return s2 v2 =>
      StackAgree n s1 s2 ∧ ValueAgree n v1 v2
  | .Halt v1, .Halt v2 => ValueAgree n v1 v2
  | .Error, .Error => True
  | _, _ => False

-- ── Part 7b (partial): one placeholder per real `step` Eval-side constructor, PROVED (not left
-- `sorry`), for every constructor whose own proof does not depend on the still-deferred builtin
-- congruence set piece (`bcong_evalBuiltin_agree`, Part 8) or fuel-genuineness investigation
-- (Part 9). Same uniform fuel convention as the old file (hypotheses at `n + 1`, conclusion at
-- `n`) for the same reason: every arm's own wiring downstream needs it, even one that does not
-- itself consume the extra fuel level. ─────────────────────────────────────────────────────────

theorem step_agree_lam (sv : PlutusCore.Default.BuiltinSemanticsVariant)
    (s1 s2 : Stack) (ρ1 ρ2 : Environment) (x : String) (M : Term) (n : Nat)
    (hs : StackAgree (n + 1) s1 s2)
    (hρ : EnvAgreeOn (n + 1) (freeVars (.Lam x M)) ρ1 ρ2) :
    StateAgree n (step sv (State.Eval s1 ρ1 (.Lam x M)))
                 (step sv (State.Eval s2 ρ2 (.Lam x M))) := by
  refine ⟨StackAgree_mono n s1 s2 hs, ?_⟩
  simp only [freeVars] at hρ
  cases n with
  | zero => simp [ValueAgree]
  | succ p =>
      unfold ValueAgree
      refine ⟨rfl, rfl, ?_⟩
      exact EnvAgreeOn_mono p _ ρ1 ρ2 (EnvAgreeOn_mono (p + 1) _ ρ1 ρ2 hρ)

theorem step_agree_delay (sv : PlutusCore.Default.BuiltinSemanticsVariant)
    (s1 s2 : Stack) (ρ1 ρ2 : Environment) (M : Term) (n : Nat)
    (hs : StackAgree (n + 1) s1 s2)
    (hρ : EnvAgreeOn (n + 1) (freeVars (.Delay M)) ρ1 ρ2) :
    StateAgree n (step sv (State.Eval s1 ρ1 (.Delay M)))
                 (step sv (State.Eval s2 ρ2 (.Delay M))) := by
  refine ⟨StackAgree_mono n s1 s2 hs, ?_⟩
  simp only [freeVars] at hρ
  cases n with
  | zero => simp [ValueAgree]
  | succ p =>
      unfold ValueAgree
      refine ⟨rfl, ?_⟩
      exact EnvAgreeOn_mono p _ ρ1 ρ2 (EnvAgreeOn_mono (p + 1) _ ρ1 ρ2 hρ)

theorem step_agree_force_eval (sv : PlutusCore.Default.BuiltinSemanticsVariant)
    (s1 s2 : Stack) (ρ1 ρ2 : Environment) (M : Term) (n : Nat)
    (hs : StackAgree (n + 1) s1 s2)
    (hρ : EnvAgreeOn (n + 1) (freeVars (.Force M)) ρ1 ρ2) :
    StateAgree n (step sv (State.Eval s1 ρ1 (.Force M)))
                 (step sv (State.Eval s2 ρ2 (.Force M))) := by
  refine ⟨rfl, ⟨by simp [FrameAgree], StackAgree_mono n s1 s2 hs⟩, ?_⟩
  simp only [freeVars] at hρ
  exact EnvAgreeOn_mono n _ ρ1 ρ2 hρ

theorem envAgreeOn_subset (n : Nat) (S S' : List Nat) (ρ1 ρ2 : Environment)
    (hsub : ∀ i, i ∈ S' → i ∈ S) (h : EnvAgreeOn n S ρ1 ρ2) : EnvAgreeOn n S' ρ1 ρ2 := by
  unfold EnvAgreeOn at h ⊢
  intro i hi
  exact h i (hsub i hi)

theorem step_agree_apply_eval (sv : PlutusCore.Default.BuiltinSemanticsVariant)
    (s1 s2 : Stack) (ρ1 ρ2 : Environment) (M N : Term) (n : Nat)
    (hs : StackAgree (n + 1) s1 s2)
    (hρ : EnvAgreeOn (n + 1) (freeVars (.Apply M N)) ρ1 ρ2) :
    StateAgree n (step sv (State.Eval s1 ρ1 (.Apply M N)))
                 (step sv (State.Eval s2 ρ2 (.Apply M N))) := by
  have hρ' : EnvAgreeOn (n + 1) (freeVars M ++ freeVars N) ρ1 ρ2 := by
    simpa [freeVars] using hρ
  have hM : EnvAgreeOn n (freeVars M) ρ1 ρ2 :=
    EnvAgreeOn_mono n (freeVars M) ρ1 ρ2
      (envAgreeOn_subset (n + 1) (freeVars M ++ freeVars N) (freeVars M) ρ1 ρ2
        (fun i hi => List.mem_append.2 (Or.inl hi)) hρ')
  have hN : EnvAgreeOn n (freeVars N) ρ1 ρ2 :=
    EnvAgreeOn_mono n (freeVars N) ρ1 ρ2
      (envAgreeOn_subset (n + 1) (freeVars M ++ freeVars N) (freeVars N) ρ1 ρ2
        (fun i hi => List.mem_append.2 (Or.inr hi)) hρ')
  show StateAgree n (State.Eval (Frame.LeftApplicationToTerm N ρ1 :: s1) ρ1 M)
                    (State.Eval (Frame.LeftApplicationToTerm N ρ2 :: s2) ρ2 M)
  exact ⟨rfl, ⟨⟨rfl, hN⟩, StackAgree_mono n s1 s2 hs⟩, hM⟩

theorem step_agree_constr_eval (sv : PlutusCore.Default.BuiltinSemanticsVariant)
    (s1 s2 : Stack) (ρ1 ρ2 : Environment) (i : Nat) (Ms : List Term) (n : Nat)
    (hs : StackAgree (n + 1) s1 s2)
    (hρ : EnvAgreeOn (n + 1) (freeVars (.Constr i Ms)) ρ1 ρ2) :
    StateAgree n (step sv (State.Eval s1 ρ1 (.Constr i Ms)))
                 (step sv (State.Eval s2 ρ2 (.Constr i Ms))) := by
  cases Ms with
  | nil =>
      show StateAgree n (State.Return s1 (CekValue.VConstr i []))
                        (State.Return s2 (CekValue.VConstr i []))
      refine ⟨StackAgree_mono n s1 s2 hs, ?_⟩
      cases n with
      | zero => simp [ValueAgree]
      | succ m => simp [ValueAgree]
  | cons M' Ms' =>
      have hρ' : EnvAgreeOn (n + 1) (freeVars M' ++ freeVarsList Ms') ρ1 ρ2 := by
        simpa [freeVars, freeVarsList] using hρ
      have hM' : EnvAgreeOn n (freeVars M') ρ1 ρ2 :=
        EnvAgreeOn_mono n (freeVars M') ρ1 ρ2
          (envAgreeOn_subset (n + 1) (freeVars M' ++ freeVarsList Ms') (freeVars M') ρ1 ρ2
            (fun i hi => List.mem_append.2 (Or.inl hi)) hρ')
      have hMs' : EnvAgreeOn n (freeVarsList Ms') ρ1 ρ2 :=
        EnvAgreeOn_mono n (freeVarsList Ms') ρ1 ρ2
          (envAgreeOn_subset (n + 1) (freeVars M' ++ freeVarsList Ms') (freeVarsList Ms') ρ1 ρ2
            (fun i hi => List.mem_append.2 (Or.inr hi)) hρ')
      show StateAgree n (State.Eval (Frame.ConstructorArgument i [] Ms' ρ1 :: s1) ρ1 M')
                        (State.Eval (Frame.ConstructorArgument i [] Ms' ρ2 :: s2) ρ2 M')
      refine ⟨rfl, ⟨⟨rfl, rfl, rfl, ?_, hMs'⟩, StackAgree_mono n s1 s2 hs⟩, hM'⟩
      intro k h1 h2
      simp at h1

theorem step_agree_case_eval (sv : PlutusCore.Default.BuiltinSemanticsVariant)
    (s1 s2 : Stack) (ρ1 ρ2 : Environment) (N : Term) (Ms : List Term) (n : Nat)
    (hs : StackAgree (n + 1) s1 s2)
    (hρ : EnvAgreeOn (n + 1) (freeVars (.Case N Ms)) ρ1 ρ2) :
    StateAgree n (step sv (State.Eval s1 ρ1 (.Case N Ms)))
                 (step sv (State.Eval s2 ρ2 (.Case N Ms))) := by
  have hρ' : EnvAgreeOn (n + 1) (freeVars N ++ freeVarsList Ms) ρ1 ρ2 := by
    simpa [freeVars, freeVarsList] using hρ
  have hN : EnvAgreeOn n (freeVars N) ρ1 ρ2 :=
    EnvAgreeOn_mono n (freeVars N) ρ1 ρ2
      (envAgreeOn_subset (n + 1) (freeVars N ++ freeVarsList Ms) (freeVars N) ρ1 ρ2
        (fun i hi => List.mem_append.2 (Or.inl hi)) hρ')
  have hMs : EnvAgreeOn n (freeVarsList Ms) ρ1 ρ2 :=
    EnvAgreeOn_mono n (freeVarsList Ms) ρ1 ρ2
      (envAgreeOn_subset (n + 1) (freeVars N ++ freeVarsList Ms) (freeVarsList Ms) ρ1 ρ2
        (fun i hi => List.mem_append.2 (Or.inr hi)) hρ')
  show StateAgree n (State.Eval (Frame.CaseScrutinee Ms ρ1 :: s1) ρ1 N)
                    (State.Eval (Frame.CaseScrutinee Ms ρ2 :: s2) ρ2 N)
  exact ⟨rfl, ⟨⟨rfl, hMs⟩, StackAgree_mono n s1 s2 hs⟩, hN⟩

theorem step_agree_builtin_eval (sv : PlutusCore.Default.BuiltinSemanticsVariant)
    (s1 s2 : Stack) (ρ1 ρ2 : Environment) (b : BuiltinFun) (n : Nat)
    (hs : StackAgree (n + 1) s1 s2) :
    StateAgree n (step sv (State.Eval s1 ρ1 (.Builtin b)))
                 (step sv (State.Eval s2 ρ2 (.Builtin b))) := by
  refine ⟨StackAgree_mono n s1 s2 hs, ?_⟩
  cases n with
  | zero => simp [ValueAgree]
  | succ p => simp [ValueAgree]

theorem step_agree_return_left_term (sv : PlutusCore.Default.BuiltinSemanticsVariant)
    (s1 s2 : Stack) (ρ1 ρ2 : Environment) (M : Term) (V1 V2 : CekValue) (n : Nat)
    (hs : StackAgree (n + 1) s1 s2)
    (hρ : EnvAgreeOn (n + 1) (freeVars M) ρ1 ρ2)
    (hV : ValueAgree (n + 1) V1 V2) :
    StateAgree n (step sv (State.Return (Frame.LeftApplicationToTerm M ρ1 :: s1) V1))
                 (step sv (State.Return (Frame.LeftApplicationToTerm M ρ2 :: s2) V2)) := by
  show StateAgree n (State.Eval (Frame.RightApplicationOfValue V1 :: s1) ρ1 M)
                    (State.Eval (Frame.RightApplicationOfValue V2 :: s2) ρ2 M)
  exact ⟨rfl, ⟨ValueAgree_mono n V1 V2 hV, StackAgree_mono n s1 s2 hs⟩,
         EnvAgreeOn_mono n (freeVars M) ρ1 ρ2 hρ⟩

end PlutusCore.UPLC.CekMachine.EnvLemmas

-- ── ROUND 1 SCOPE, honestly stated ──────────────────────────────────────────────────────────
--
-- TRANSLATED AND VERIFIED (this file, zero `sorry`, zero `error`, confirmed by a real
-- `lake build`, 26 declarations): `envLookup`, `freeVarsUnderBinder`/`freeVars`/`freeVarsList`,
-- `fix_ValueAgreeShape`, the `ValueAgree`/`EnvAgreeOn` mutual step-indexed relation,
-- `fix_valueAgree_shape`, `beta_envAgreeOn_extend`, `step_var_agree`, `step_const_agree` (old
-- Parts 1-6); the fuel-monotonicity pair `ValueAgree_mono`/`EnvAgreeOn_mono`, the `Frame`/
-- `Stack`/`State` agreement extension (`FrameAgree`/`StackAgree`/`StateAgree` plus
-- `FrameAgree_mono`/`StackAgree_mono`) and `envAgreeOn_subset` (old Part 7/7a); and 8 of the old
-- Part 7b's 13 per-constructor `step_agree_*` placeholders -- every one whose real proof does
-- NOT reach into the still-deferred builtin-congruence set piece: `step_agree_lam`,
-- `step_agree_delay`, `step_agree_force_eval`, `step_agree_apply_eval`,
-- `step_agree_constr_eval`, `step_agree_case_eval`, `step_agree_builtin_eval`,
-- `step_agree_return_left_term`.
--
-- DEFERRED to a later round, not attempted here, no placeholder `sorry` left standing for any of
-- it (nothing in THIS file references it):
--   - The remaining 5 of the old Part 7b's 13 `step_agree_*` placeholders --
--     `step_agree_return_right_value`, `step_agree_return_left_value` (both need Part 8's
--     builtin congruence for their VBuiltin-arity-exhausted sub-case), `step_agree_return_force`
--     (same, for its own VBuiltin sub-case), `step_agree_return_constr_arg`,
--     `step_agree_return_case_scrutinee` (both need the `retdispatch_*` helper family, old file
--     lines 1656-1805, which is itself representation-agnostic but not yet translated).
--   - Part 8, the ~395-line `bcong_evalBuiltin_agree` builtin-congruence set piece -- read in
--     full this round, confirmed REPRESENTATION-AGNOSTIC (it is entirely about `CekValue`/
--     `BuiltinFun`/`ExpectedBuiltinArgs` shape, which the de Bruijn migration did not touch at
--     all), so it is expected to translate near-mechanically once Part 7's `Frame`/`Stack`
--     agreement it depends on lands, not attempted yet purely for sequencing reasons.
--   - Part 9 (`fuelpres_*`, the fuel-genuineness investigation) and Part 10 (`stepAbs_agree`/
--     `stepN_agree_of_stateAgree`/`eval_agree`, the multi-step chaining induction).
--   - The closing `eac_*`/`eval_agree_as_stated_is_false` counterexample section, which refutes
--     the FULLY GENERAL fixed-fuel form of `eval_agree` -- confirmed read this round, its own
--     witness values (`eac_w1`/`eac_Vg1`/...) are stated directly against
--     `Environment.EmptyEnvironment`/`NonEmptyEnvironment`, so restating it needs the same
--     positional-environment translation as everything else here, not yet done. THIS IS A
--     DOCUMENTED NEGATIVE RESULT the old file is careful to preserve (see its own Part 6 note:
--     "never leave a live `sorry`'d claim whose negation is separately proven elsewhere in the
--     same file") -- a future round must carry the refutation across, not just the positive
--     theorems, or the migrated file would silently drop it.
