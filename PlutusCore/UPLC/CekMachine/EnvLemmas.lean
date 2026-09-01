import PlutusCore.UPLC.CekMachine

-- Migration of sundae-v4's `Formalization/Scratch/EnvLemma.lean` (general CEK environment/
-- value step-indexed agreement metatheory, frozen source commit `50cd4f699` in that repo) onto
-- this repo's positional `Environment := List CekValue` / de Bruijn `Term.Var : Nat → Term`
-- representation (PR #21, merged `e708754`), across multiple rounds. See this file's own closing
-- comment for exactly what is translated-and-verified vs. still deferred, and why.
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

-- ── Part 8: the builtin congruence set piece (`bcong_*`). Confirmed round 1 (see the closing
-- comment below): entirely about `CekValue`/`BuiltinFun`/`ExpectedBuiltinArgs` shape, which the
-- de Bruijn migration did not touch -- direct reads this round of every `PlutusCore/UPLC/
-- BuiltinFunctions/*.lean` file confirm the same function names, arities, and match structure as
-- the old file assumed (this whole directory predates PR #21). Only TWO declarations in this Part
-- carry real Environment content (`bcong_valueAgree_envAgreeOn_refl`/its two named accessors):
-- `List String` becomes `List Nat` and the VLam case's `(freeVars M).erase x` becomes
-- `freeVarsUnderBinder (freeVars M)`, exactly round 1's established translation. Every other
-- declaration here (including the ~370-line `bcong_evalBuiltin_agree` builtin-by-builtin master
-- theorem) is copied over verbatim -- it never destructs an `Environment` or a `Term.Var`/index at
-- all, only `CekValue`/`Const`/`Data.Data`/`BuiltinFun` shape. ───────────────────────────────────

open PlutusCore.UPLC.BuiltinFunctions.Evaluate
open PlutusCore.UPLC.BuiltinFunctions.Bitwise
open PlutusCore.UPLC.BuiltinFunctions.Bool
open PlutusCore.UPLC.BuiltinFunctions.ByteString
open PlutusCore.UPLC.BuiltinFunctions.Crypto
open PlutusCore.UPLC.BuiltinFunctions.Data
open PlutusCore.UPLC.BuiltinFunctions.Integer
open PlutusCore.UPLC.BuiltinFunctions.List
open PlutusCore.UPLC.BuiltinFunctions.Pair
open PlutusCore.UPLC.BuiltinFunctions.String
open PlutusCore.UPLC.BuiltinFunctions.Trace
open PlutusCore.UPLC.BuiltinFunctions.Unit

-- `fix_ValueAgreeShape`'s `VCon` clause is literal `Const` equality, so whenever `v1` literally IS
-- a `VCon`, shape agreement forces `v2` to be the LITERALLY IDENTICAL `VCon` (not merely a
-- matching outer shape). This is the fact every builtin's "discriminant/argument is `VCon`" branch
-- rests on. Unchanged from the old file (pure `CekValue` shape, no Environment content).
theorem bcong_shape_eq_of_vcon (v1 v2 : CekValue) (c : PlutusCore.UPLC.Term.Const)
    (h : fix_ValueAgreeShape v1 v2) (hv1 : v1 = CekValue.VCon c) : v2 = CekValue.VCon c := by
  subst hv1
  cases v2 <;> simp_all [fix_ValueAgreeShape]

-- `ValueAgree`/`EnvAgreeOn` are REFLEXIVE at every fuel level -- proved by the SAME mutual
-- induction on the fuel `n` that `mono_valueAgree_envAgreeOn` above already uses to sidestep the
-- self-referential-closure well-foundedness issue: the inductive hypothesis is applied at a
-- SMALLER fuel level to an ARBITRARY value (never recursing on the value's own structure), so a
-- self-referential closure is no obstacle here either. Needed below so that "the SAME input on
-- both sides" immediately gives `ValueAgree n v v` for whatever value a builtin call produces,
-- without having to separately know that builtin's output shape.
--
-- REPRESENTATION-SENSITIVE (unlike the rest of this Part): `S : List String` becomes
-- `S : List Nat`, `envLookup ρ x` becomes `envLookup ρ i`, and the VLam case's
-- `(freeVars M).erase x` becomes `freeVarsUnderBinder (freeVars M)`, matching round 1's
-- `ValueAgree`/`beta_envAgreeOn_extend` translation exactly.
private theorem bcong_valueAgree_envAgreeOn_refl : ∀ n : Nat,
    (∀ v : CekValue, ValueAgree n v v) ∧ (∀ (S : List Nat) (ρ : Environment), EnvAgreeOn n S ρ ρ) := by
  intro n
  induction n with
  | zero =>
      refine ⟨fun v => by simp [ValueAgree], fun S ρ => ?_⟩
      unfold EnvAgreeOn
      intro i _
      cases envLookup ρ i with
      | none => simp
      | some v => simp [ValueAgree]
  | succ m ih =>
      obtain ⟨ihV, ihE⟩ := ih
      have reflV : ∀ v : CekValue, ValueAgree (m + 1) v v := by
        intro v
        cases v with
        | VCon c => simp [ValueAgree]
        | VDelay M ρ =>
            unfold ValueAgree
            exact ⟨rfl, ihE (freeVars M) ρ⟩
        | VLam x M ρ =>
            unfold ValueAgree
            exact ⟨rfl, rfl, ihE (freeVarsUnderBinder (freeVars M)) ρ⟩
        | VConstr i vs =>
            unfold ValueAgree
            exact ⟨rfl, rfl, fun k _ _ => ihV (vs[k])⟩
        | VBuiltin b vs η =>
            unfold ValueAgree
            refine ⟨rfl, rfl, rfl, fun k _ _ => ihV (vs[k]), fun k _ _ => ?_⟩
            cases hv : vs[k] with
            | VCon c => simp [fix_ValueAgreeShape]
            | VDelay _ _ => simp [fix_ValueAgreeShape]
            | VLam _ _ _ => simp [fix_ValueAgreeShape]
            | VConstr _ _ => simp [fix_ValueAgreeShape]
            | VBuiltin _ _ _ => simp [fix_ValueAgreeShape]
      refine ⟨reflV, ?_⟩
      intro S ρ
      unfold EnvAgreeOn
      intro i _
      cases envLookup ρ i with
      | none => simp
      | some v => simp [reflV v]

theorem bcong_valueAgree_refl (n : Nat) (v : CekValue) : ValueAgree n v v :=
  (bcong_valueAgree_envAgreeOn_refl n).1 v

theorem bcong_envAgreeOn_refl (n : Nat) (S : List Nat) (ρ : Environment) : EnvAgreeOn n S ρ ρ :=
  (bcong_valueAgree_envAgreeOn_refl n).2 S ρ

-- Once two argument lists are LITERALLY equal, ANY (partial, possibly `tryCatchSome`/`Except`/
-- internal-guard-based) function agrees with itself trivially -- no per-builtin reasoning at all.
-- Unchanged from the old file.
theorem bcong_close_via_eq (g : List CekValue → Option CekValue) (xs : List CekValue) (n : Nat) :
    (∃ v1 v2, g xs = some v1 ∧ g xs = some v2 ∧ ValueAgree n v1 v2) ∨ (g xs = none ∧ g xs = none) := by
  cases g xs with
  | none => right; exact ⟨rfl, rfl⟩
  | some v => left; exact ⟨v, v, rfl, rfl, bcong_valueAgree_refl n v⟩

-- The one, fully builtin- and arity-independent DICHOTOMY every case below rests on: two argument
-- lists that agree (same length, pointwise `fix_ValueAgreeShape`) are either LITERALLY equal
-- (every position `VCon`-shaped on both sides, forced pointwise-equal by `bcong_shape_eq_of_vcon`),
-- or some position is NOT `VCon` on EITHER side (forced symmetric, since shape's non-`VCon`
-- clauses all require the SAME outer constructor). Proved by plain list induction, no
-- builtin-specific content. Unchanged from the old file (pure `CekValue` shape).
theorem bcong_list_agree_eq_or_non_vcon (xs1 xs2 : List CekValue)
    (hlen : xs1.length = xs2.length)
    (hshape : ∀ k (h1 : k < xs1.length) (h2 : k < xs2.length), fix_ValueAgreeShape (xs1[k]) (xs2[k])) :
    xs1 = xs2 ∨
    ∃ k, ∃ h1 : k < xs1.length, ∃ h2 : k < xs2.length,
      (¬ ∃ c, xs1[k] = CekValue.VCon c) ∧ (¬ ∃ c, xs2[k] = CekValue.VCon c) := by
  induction xs1 generalizing xs2 with
  | nil =>
      cases xs2 with
      | nil => left; rfl
      | cons _ _ => simp at hlen
  | cons v1 xs1' ih =>
      cases xs2 with
      | nil => simp at hlen
      | cons v2 xs2' =>
          have hlen' : xs1'.length = xs2'.length := by simpa using hlen
          have h0 : fix_ValueAgreeShape v1 v2 := by
            have := hshape 0 (by simp) (by simp)
            simpa using this
          have hshape' : ∀ k (h1 : k < xs1'.length) (h2 : k < xs2'.length),
              fix_ValueAgreeShape (xs1'[k]) (xs2'[k]) := by
            intro k hk1 hk2
            have := hshape (k + 1) (by simpa using hk1) (by simpa using hk2)
            simpa using this
          by_cases hv1 : ∃ c, v1 = CekValue.VCon c
          · obtain ⟨c, rfl⟩ := hv1
            have hv2 : v2 = CekValue.VCon c := bcong_shape_eq_of_vcon _ _ c h0 rfl
            subst hv2
            rcases ih xs2' hlen' hshape' with heq | ⟨k, hk1, hk2, hnv1, hnv2⟩
            · left; rw [heq]
            · right
              exact ⟨k + 1, by simpa using hk1, by simpa using hk2, by simpa using hnv1,
                     by simpa using hnv2⟩
          · right
            have hv2 : ¬ ∃ c, v2 = CekValue.VCon c := by
              rintro ⟨c, rfl⟩
              cases v1 with
              | VCon c1 => exact hv1 ⟨c1, rfl⟩
              | VDelay _ _ => simp [fix_ValueAgreeShape] at h0
              | VLam _ _ _ => simp [fix_ValueAgreeShape] at h0
              | VConstr _ _ => simp [fix_ValueAgreeShape] at h0
              | VBuiltin _ _ _ => simp [fix_ValueAgreeShape] at h0
            exact ⟨0, by simp, by simp, hv1, hv2⟩

-- The reusable STRICT-builtin closer: given the one per-builtin fact that a non-`VCon` position
-- forces `none` (arity-independent statement; discharged per-builtin below by a uniform,
-- arity-templated tactic), this needs NO OTHER builtin-specific input at all -- the "both literally
-- equal" branch is `bcong_close_via_eq`, generic over every `f` regardless of internal complexity.
-- Unchanged from the old file.
theorem bcong_strict_close (f : List CekValue → Option CekValue) (xs1 xs2 : List CekValue) (n : Nat)
    (hlen : xs1.length = xs2.length)
    (hshape : ∀ k (h1 : k < xs1.length) (h2 : k < xs2.length), fix_ValueAgreeShape (xs1[k]) (xs2[k]))
    (hnone_pos : ∀ (ys : List CekValue) (j : Nat) (hj : j < ys.length),
        (¬ ∃ c, ys[j] = CekValue.VCon c) → f ys = none) :
    (∃ v1 v2, f xs1 = some v1 ∧ f xs2 = some v2 ∧ ValueAgree n v1 v2) ∨
    (f xs1 = none ∧ f xs2 = none) := by
  rcases bcong_list_agree_eq_or_non_vcon xs1 xs2 hlen hshape with heq | ⟨k, hk1, hk2, hnv1, hnv2⟩
  · subst heq
    exact bcong_close_via_eq f xs1 n
  · right
    exact ⟨hnone_pos xs1 k hk1 hnv1, hnone_pos xs2 k hk2 hnv2⟩

-- THE MASTER THEOREM: real per-builtin congruence, over ALL 91 real `BuiltinFun` constructors.
-- Unchanged from the old file, verbatim -- confirmed this round, by direct read of every
-- `PlutusCore/UPLC/BuiltinFunctions/*.lean` file, that this directory's function names, arities
-- and per-builtin match structure are exactly what the old file assumed (untouched by PR #21).
-- (`maxHeartbeats` raised: the strict-builtin batches each run ONE shared tactic body, elaborated
-- separately per constructor, against a `simp`/`simp_all` set naming every function in its arity
-- batch -- more elaboration work per goal than the 200000 default budget allows.)
set_option maxHeartbeats 4000000 in
theorem bcong_evalBuiltin_agree (sv : PlutusCore.Default.BuiltinSemanticsVariant)
    (b : BuiltinFun) (xs1 xs2 : List CekValue) (n : Nat)
    (hlen : xs1.length = xs2.length)
    (hpt : ∀ k (h1 : k < xs1.length) (h2 : k < xs2.length), ValueAgree n (xs1[k]) (xs2[k]))
    (hshape : ∀ k (h1 : k < xs1.length) (h2 : k < xs2.length), fix_ValueAgreeShape (xs1[k]) (xs2[k])) :
    (∃ v1 v2, evaluateBuiltinFunction sv b xs1 = some v1 ∧ evaluateBuiltinFunction sv b xs2 = some v2 ∧
       ValueAgree n v1 v2) ∨
    (evaluateBuiltinFunction sv b xs1 = none ∧ evaluateBuiltinFunction sv b xs2 = none) := by
  cases b with
  | IfThenElse =>
      simp only [evaluateBuiltinFunction]
      rcases xs1 with _ | ⟨cf1, _ | ⟨ct1, _ | ⟨cond1, _ | ⟨_, _⟩⟩⟩⟩ <;>
        rcases xs2 with _ | ⟨cf2, _ | ⟨ct2, _ | ⟨cond2, _ | ⟨_, _⟩⟩⟩⟩ <;>
        first
        | (simp_all [ifThenElse]; done)
        | (have h2 : fix_ValueAgreeShape cond1 cond2 := hshape 2 (by simp) (by simp)
           have hct : ValueAgree n ct1 ct2 := hpt 1 (by simp) (by simp)
           have hcf : ValueAgree n cf1 cf2 := hpt 0 (by simp) (by simp)
           cases cond1 with
           | VCon c1 =>
               cases cond2 with
               | VCon c2 =>
                   have hc : c1 = c2 := by simpa [fix_ValueAgreeShape] using h2
                   subst hc
                   cases c1 with
                   | Bool bb =>
                       cases bb <;> simp only [ifThenElse, PLC.ifThenElse]
                       · exact Or.inl ⟨cf1, cf2, rfl, rfl, hcf⟩
                       · exact Or.inl ⟨ct1, ct2, rfl, rfl, hct⟩
                   | Integer _ | ByteString _ | String _ | Unit | ConstList _ | ConstDataList _
                   | ConstPairDataList _ | Pair _ | PairData _ | Data _ | Bls12_381_G1_element _
                   | Bls12_381_G2_element _ | Bls12_381_MlResult _ =>
                       right; exact ⟨by simp [ifThenElse], by simp [ifThenElse]⟩
               | _ => exact absurd h2 (by simp [fix_ValueAgreeShape])
           | VDelay _ _ =>
               cases cond2 with
               | VDelay _ _ => right; exact ⟨by simp [ifThenElse], by simp [ifThenElse]⟩
               | _ => exact absurd h2 (by simp [fix_ValueAgreeShape])
           | VLam _ _ _ =>
               cases cond2 with
               | VLam _ _ _ => right; exact ⟨by simp [ifThenElse], by simp [ifThenElse]⟩
               | _ => exact absurd h2 (by simp [fix_ValueAgreeShape])
           | VConstr _ _ =>
               cases cond2 with
               | VConstr _ _ => right; exact ⟨by simp [ifThenElse], by simp [ifThenElse]⟩
               | _ => exact absurd h2 (by simp [fix_ValueAgreeShape])
           | VBuiltin _ _ _ =>
               cases cond2 with
               | VBuiltin _ _ _ => right; exact ⟨by simp [ifThenElse], by simp [ifThenElse]⟩
               | _ => exact absurd h2 (by simp [fix_ValueAgreeShape]))
  | ChooseUnit =>
      simp only [evaluateBuiltinFunction]
      rcases xs1 with _ | ⟨v1, _ | ⟨u1, _ | ⟨_, _⟩⟩⟩ <;>
        rcases xs2 with _ | ⟨v2, _ | ⟨u2, _ | ⟨_, _⟩⟩⟩ <;>
        first
        | (simp_all [chooseUnit]; done)
        | (have h1 : fix_ValueAgreeShape u1 u2 := hshape 1 (by simp) (by simp)
           have hv : ValueAgree n v1 v2 := hpt 0 (by simp) (by simp)
           cases u1 with
           | VCon c1 =>
               cases u2 with
               | VCon c2 =>
                   have hc : c1 = c2 := by simpa [fix_ValueAgreeShape] using h1
                   subst hc
                   cases c1 with
                   | Unit => left; exact ⟨v1, v2, rfl, rfl, hv⟩
                   | Integer _ | ByteString _ | String _ | Bool _ | ConstList _ | ConstDataList _
                   | ConstPairDataList _ | Pair _ | PairData _ | Data _ | Bls12_381_G1_element _
                   | Bls12_381_G2_element _ | Bls12_381_MlResult _ =>
                       right; exact ⟨by simp [chooseUnit], by simp [chooseUnit]⟩
               | _ => exact absurd h1 (by simp [fix_ValueAgreeShape])
           | VDelay _ _ =>
               cases u2 with
               | VDelay _ _ => right; exact ⟨by simp [chooseUnit], by simp [chooseUnit]⟩
               | _ => exact absurd h1 (by simp [fix_ValueAgreeShape])
           | VLam _ _ _ =>
               cases u2 with
               | VLam _ _ _ => right; exact ⟨by simp [chooseUnit], by simp [chooseUnit]⟩
               | _ => exact absurd h1 (by simp [fix_ValueAgreeShape])
           | VConstr _ _ =>
               cases u2 with
               | VConstr _ _ => right; exact ⟨by simp [chooseUnit], by simp [chooseUnit]⟩
               | _ => exact absurd h1 (by simp [fix_ValueAgreeShape])
           | VBuiltin _ _ _ =>
               cases u2 with
               | VBuiltin _ _ _ => right; exact ⟨by simp [chooseUnit], by simp [chooseUnit]⟩
               | _ => exact absurd h1 (by simp [fix_ValueAgreeShape]))
  | Trace =>
      simp only [evaluateBuiltinFunction]
      rcases xs1 with _ | ⟨v1, _ | ⟨u1, _ | ⟨_, _⟩⟩⟩ <;>
        rcases xs2 with _ | ⟨v2, _ | ⟨u2, _ | ⟨_, _⟩⟩⟩ <;>
        first
        | (simp_all [trace]; done)
        | (have h1 : fix_ValueAgreeShape u1 u2 := hshape 1 (by simp) (by simp)
           have hv : ValueAgree n v1 v2 := hpt 0 (by simp) (by simp)
           cases u1 with
           | VCon c1 =>
               cases u2 with
               | VCon c2 =>
                   have hc : c1 = c2 := by simpa [fix_ValueAgreeShape] using h1
                   subst hc
                   cases c1 with
                   | String s => left; exact ⟨v1, v2, rfl, rfl, hv⟩
                   | Integer _ | ByteString _ | Unit | Bool _ | ConstList _ | ConstDataList _
                   | ConstPairDataList _ | Pair _ | PairData _ | Data _ | Bls12_381_G1_element _
                   | Bls12_381_G2_element _ | Bls12_381_MlResult _ =>
                       right; exact ⟨by simp [trace], by simp [trace]⟩
               | _ => exact absurd h1 (by simp [fix_ValueAgreeShape])
           | VDelay _ _ =>
               cases u2 with
               | VDelay _ _ => right; exact ⟨by simp [trace], by simp [trace]⟩
               | _ => exact absurd h1 (by simp [fix_ValueAgreeShape])
           | VLam _ _ _ =>
               cases u2 with
               | VLam _ _ _ => right; exact ⟨by simp [trace], by simp [trace]⟩
               | _ => exact absurd h1 (by simp [fix_ValueAgreeShape])
           | VConstr _ _ =>
               cases u2 with
               | VConstr _ _ => right; exact ⟨by simp [trace], by simp [trace]⟩
               | _ => exact absurd h1 (by simp [fix_ValueAgreeShape])
           | VBuiltin _ _ _ =>
               cases u2 with
               | VBuiltin _ _ _ => right; exact ⟨by simp [trace], by simp [trace]⟩
               | _ => exact absurd h1 (by simp [fix_ValueAgreeShape]))
  | ChooseList =>
      simp only [evaluateBuiltinFunction]
      rcases xs1 with _ | ⟨lc1, _ | ⟨nc1, _ | ⟨d1, _ | ⟨_, _⟩⟩⟩⟩ <;>
        rcases xs2 with _ | ⟨lc2, _ | ⟨nc2, _ | ⟨d2, _ | ⟨_, _⟩⟩⟩⟩ <;>
        first
        | (simp_all [chooseList]; done)
        | (have h2 : fix_ValueAgreeShape d1 d2 := hshape 2 (by simp) (by simp)
           have hlc : ValueAgree n lc1 lc2 := hpt 0 (by simp) (by simp)
           have hnc : ValueAgree n nc1 nc2 := hpt 1 (by simp) (by simp)
           cases d1 with
           | VCon c1 =>
               cases d2 with
               | VCon c2 =>
                   have hc : c1 = c2 := by simpa [fix_ValueAgreeShape] using h2
                   subst hc
                   cases c1 with
                   | ConstList l =>
                       by_cases he : l.isEmpty
                       · left; refine ⟨nc1, nc2, ?_, ?_, hnc⟩ <;> simp [chooseList, he]
                       · left; refine ⟨lc1, lc2, ?_, ?_, hlc⟩ <;> simp [chooseList, he]
                   | ConstDataList l =>
                       by_cases he : l = ([] : List PlutusCore.Data.Data)
                       · left; refine ⟨nc1, nc2, ?_, ?_, hnc⟩ <;> simp [chooseList, he]
                       · left; refine ⟨lc1, lc2, ?_, ?_, hlc⟩ <;> simp [chooseList, he]
                   | ConstPairDataList l =>
                       by_cases he : l = ([] : List (PlutusCore.Data.Data × PlutusCore.Data.Data))
                       · left; refine ⟨nc1, nc2, ?_, ?_, hnc⟩ <;> simp [chooseList, he]
                       · left; refine ⟨lc1, lc2, ?_, ?_, hlc⟩ <;> simp [chooseList, he]
                   | Integer _ | ByteString _ | String _ | Unit | Bool _ | Pair _ | PairData _
                   | Data _ | Bls12_381_G1_element _ | Bls12_381_G2_element _
                   | Bls12_381_MlResult _ =>
                       right; exact ⟨by simp [chooseList], by simp [chooseList]⟩
               | _ => exact absurd h2 (by simp [fix_ValueAgreeShape])
           | VDelay _ _ =>
               cases d2 with
               | VDelay _ _ => right; exact ⟨by simp [chooseList], by simp [chooseList]⟩
               | _ => exact absurd h2 (by simp [fix_ValueAgreeShape])
           | VLam _ _ _ =>
               cases d2 with
               | VLam _ _ _ => right; exact ⟨by simp [chooseList], by simp [chooseList]⟩
               | _ => exact absurd h2 (by simp [fix_ValueAgreeShape])
           | VConstr _ _ =>
               cases d2 with
               | VConstr _ _ => right; exact ⟨by simp [chooseList], by simp [chooseList]⟩
               | _ => exact absurd h2 (by simp [fix_ValueAgreeShape])
           | VBuiltin _ _ _ =>
               cases d2 with
               | VBuiltin _ _ _ => right; exact ⟨by simp [chooseList], by simp [chooseList]⟩
               | _ => exact absurd h2 (by simp [fix_ValueAgreeShape]))
  | ChooseData =>
      simp only [evaluateBuiltinFunction]
      rcases xs1 with
        _ | ⟨bC1, _ | ⟨iC1, _ | ⟨lC1, _ | ⟨mC1, _ | ⟨cC1, _ | ⟨d1, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩ <;>
        rcases xs2 with
          _ | ⟨bC2, _ | ⟨iC2, _ | ⟨lC2, _ | ⟨mC2, _ | ⟨cC2, _ | ⟨d2, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩ <;>
        first
        | (simp_all [chooseData]; done)
        | (have h5 : fix_ValueAgreeShape d1 d2 := hshape 5 (by simp) (by simp)
           have hbC : ValueAgree n bC1 bC2 := hpt 0 (by simp) (by simp)
           have hiC : ValueAgree n iC1 iC2 := hpt 1 (by simp) (by simp)
           have hlC : ValueAgree n lC1 lC2 := hpt 2 (by simp) (by simp)
           have hmC : ValueAgree n mC1 mC2 := hpt 3 (by simp) (by simp)
           have hcC : ValueAgree n cC1 cC2 := hpt 4 (by simp) (by simp)
           cases d1 with
           | VCon c1 =>
               cases d2 with
               | VCon c2 =>
                   have hc : c1 = c2 := by simpa [fix_ValueAgreeShape] using h5
                   subst hc
                   cases c1 with
                   | Data data =>
                       cases data with
                       | Constr _ _ =>
                           left; refine ⟨cC1, cC2, ?_, ?_, hcC⟩ <;> simp [chooseData]
                       | Map _ =>
                           left; refine ⟨mC1, mC2, ?_, ?_, hmC⟩ <;> simp [chooseData]
                       | List _ =>
                           left; refine ⟨lC1, lC2, ?_, ?_, hlC⟩ <;> simp [chooseData]
                       | I _ =>
                           left; refine ⟨iC1, iC2, ?_, ?_, hiC⟩ <;> simp [chooseData]
                       | B _ =>
                           left; refine ⟨bC1, bC2, ?_, ?_, hbC⟩ <;> simp [chooseData]
                   | Integer _ | ByteString _ | String _ | Unit | Bool _ | ConstList _
                   | ConstDataList _ | ConstPairDataList _ | Pair _ | PairData _
                   | Bls12_381_G1_element _ | Bls12_381_G2_element _ | Bls12_381_MlResult _ =>
                       right; exact ⟨by simp [chooseData], by simp [chooseData]⟩
               | _ => exact absurd h5 (by simp [fix_ValueAgreeShape])
           | VDelay _ _ =>
               cases d2 with
               | VDelay _ _ => right; exact ⟨by simp [chooseData], by simp [chooseData]⟩
               | _ => exact absurd h5 (by simp [fix_ValueAgreeShape])
           | VLam _ _ _ =>
               cases d2 with
               | VLam _ _ _ => right; exact ⟨by simp [chooseData], by simp [chooseData]⟩
               | _ => exact absurd h5 (by simp [fix_ValueAgreeShape])
           | VConstr _ _ =>
               cases d2 with
               | VConstr _ _ => right; exact ⟨by simp [chooseData], by simp [chooseData]⟩
               | _ => exact absurd h5 (by simp [fix_ValueAgreeShape])
           | VBuiltin _ _ _ =>
               cases d2 with
               | VBuiltin _ _ _ => right; exact ⟨by simp [chooseData], by simp [chooseData]⟩
               | _ => exact absurd h5 (by simp [fix_ValueAgreeShape]))
  -- ── STRICT builtins, batched by arity (the tactic body only depends on arity, not semantics;
  -- each `simp`/`simp_all` set lists every real definition name for its batch so the ONE shared
  -- tactic discharges whichever specific builtin `cases b` has already substituted in). NOTE: no
  -- `interval_cases` (Mathlib-only, unavailable here) -- `j`'s bound is peeled by plain `cases`. ────
  | LengthOfByteString | Sha2_256 | Sha3_256 | Blake2b_256 | EncodeUtf8 | DecodeUtf8 | FstPair
  | SndPair | HeadList | TailList | NullList | MapData | ListData | IData | BData | UnConstrData
  | UnMapData | UnListData | UnIData | UnBData | MkNilData | MkNilPairData | SerializeData
  | Bls12_381_G1_neg | Bls12_381_G1_compress | Bls12_381_G1_uncompress | Bls12_381_G2_neg
  | Bls12_381_G2_compress | Bls12_381_G2_uncompress | Keccak_256 | Blake2b_224
  | ComplementByteString | CountSetBits | FindFirstSetBit | Ripemd_160 =>
      apply bcong_strict_close _ xs1 xs2 n hlen hshape
      intro ys j hj hnv
      rcases ys with _ | ⟨v0, _ | ⟨v1, r⟩⟩
      · simp at hj
      · cases j with
        | zero =>
            cases v0 <;>
              simp_all [evaluateBuiltinFunction, lengthOfByteString, sha2_256, sha3_256,
                blake2b_256, encodeUtf8, decodeUtf8, fstPair, sndPair, headList, tailList,
                nullList, mapData, listData, iData, bData, unConstrData, unMapData, unListData,
                unIData, unBData, mkNilData, mkNilPairData, serializeData, bls12381G1Neg,
                bls12381G1Compress, bls12381G1Uncompress, bls12381G2Neg, bls12381G2Compress,
                bls12381G2Uncompress, keccak_256, blake2b_224, complementByteString, countSetBits,
                findFirstSetBit, ripemd_160]
        | succ j' => simp at hj
      · simp [evaluateBuiltinFunction, lengthOfByteString, sha2_256, sha3_256, blake2b_256,
          encodeUtf8, decodeUtf8, fstPair, sndPair, headList, tailList, nullList, mapData,
          listData, iData, bData, unConstrData, unMapData, unListData, unIData, unBData,
          mkNilData, mkNilPairData, serializeData, bls12381G1Neg, bls12381G1Compress,
          bls12381G1Uncompress, bls12381G2Neg, bls12381G2Compress, bls12381G2Uncompress,
          keccak_256, blake2b_224, complementByteString, countSetBits, findFirstSetBit,
          ripemd_160]
  | AddInteger | SubtractInteger | MultiplyInteger | DivideInteger | ModInteger | QuotientInteger
  | RemainderInteger | EqualsInteger | LessThanInteger | LessThanEqualsInteger | AppendByteString
  | ConsByteString | IndexByteString | EqualsByteString | LessThanByteString
  | LessThanEqualsByteString | AppendString | EqualsString | MkCons | ConstrData | EqualsData
  | MkPairData | Bls12_381_G1_add | Bls12_381_G1_scalarMul | Bls12_381_G1_equal
  | Bls12_381_G1_hashToGroup | Bls12_381_G2_add | Bls12_381_G2_scalarMul | Bls12_381_G2_equal
  | Bls12_381_G2_hashToGroup | Bls12_381_G1_multiScalarMul | Bls12_381_G2_multiScalarMul
  | Bls12_381_millerLoop | Bls12_381_mulMlResult | Bls12_381_finalVerify | ByteStringToInteger
  | ReadBit | ReplicateByte | ShiftByteString | RotateByteString | DropList =>
      apply bcong_strict_close _ xs1 xs2 n hlen hshape
      intro ys j hj hnv
      rcases ys with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, r⟩⟩⟩
      · simp at hj
      · simp [evaluateBuiltinFunction, addInteger, subtractInteger, multiplyInteger,
          divideInteger, modInteger, quotientInteger, remainderInteger, equalsInteger,
          lessThanInteger, lessThanEqualsInteger, appendByteString, consByteString,
          indexByteString, equalsByteString, lessThanByteString, lessThanEqualsByteString,
          appendString, equalsString, mkCons, constrData, equalsData, mkPairData, bls12381G1Add,
          bls12381G1ScalarMul, bls12381G1Equal, bls12381G1HashToGroup, bls12381G2Add,
          bls12381G2ScalarMul, bls12381G2Equal, bls12381G2HashToGroup, bls12381G1MultiScalarMul,
          bls12381G2MultiScalarMul, bls12381MillerLoop, bls12381MulMlResult, bls12381FinalVerify,
          byteStringToInteger, readBit, replicateByte, shiftByteString, rotateByteString,
          dropList]
      · cases j with
        | zero =>
            cases v0 <;>
              simp_all [evaluateBuiltinFunction, addInteger, subtractInteger, multiplyInteger,
                divideInteger, modInteger, quotientInteger, remainderInteger, equalsInteger,
                lessThanInteger, lessThanEqualsInteger, appendByteString, consByteString,
                indexByteString, equalsByteString, lessThanByteString, lessThanEqualsByteString,
                appendString, equalsString, mkCons, constrData, equalsData, mkPairData,
                bls12381G1Add, bls12381G1ScalarMul, bls12381G1Equal, bls12381G1HashToGroup,
                bls12381G2Add, bls12381G2ScalarMul, bls12381G2Equal, bls12381G2HashToGroup,
                bls12381G1MultiScalarMul, bls12381G2MultiScalarMul, bls12381MillerLoop,
                bls12381MulMlResult, bls12381FinalVerify, byteStringToInteger, readBit,
                replicateByte, shiftByteString, rotateByteString, dropList]
        | succ j' =>
            cases j' with
            | zero =>
                cases v1 <;>
                  simp_all [evaluateBuiltinFunction, addInteger, subtractInteger,
                    multiplyInteger, divideInteger, modInteger, quotientInteger,
                    remainderInteger, equalsInteger, lessThanInteger, lessThanEqualsInteger,
                    appendByteString, consByteString, indexByteString, equalsByteString,
                    lessThanByteString, lessThanEqualsByteString, appendString, equalsString,
                    mkCons, constrData, equalsData, mkPairData, bls12381G1Add,
                    bls12381G1ScalarMul, bls12381G1Equal, bls12381G1HashToGroup, bls12381G2Add,
                    bls12381G2ScalarMul, bls12381G2Equal, bls12381G2HashToGroup,
                    bls12381G1MultiScalarMul, bls12381G2MultiScalarMul, bls12381MillerLoop,
                    bls12381MulMlResult, bls12381FinalVerify, byteStringToInteger, readBit,
                    replicateByte, shiftByteString, rotateByteString, dropList]
            | succ j'' => simp only [List.length_cons, List.length_nil] at hj; omega
      · simp [evaluateBuiltinFunction, addInteger, subtractInteger, multiplyInteger,
          divideInteger, modInteger, quotientInteger, remainderInteger, equalsInteger,
          lessThanInteger, lessThanEqualsInteger, appendByteString, consByteString,
          indexByteString, equalsByteString, lessThanByteString, lessThanEqualsByteString,
          appendString, equalsString, mkCons, constrData, equalsData, mkPairData, bls12381G1Add,
          bls12381G1ScalarMul, bls12381G1Equal, bls12381G1HashToGroup, bls12381G2Add,
          bls12381G2ScalarMul, bls12381G2Equal, bls12381G2HashToGroup, bls12381G1MultiScalarMul,
          bls12381G2MultiScalarMul, bls12381MillerLoop, bls12381MulMlResult, bls12381FinalVerify,
          byteStringToInteger, readBit, replicateByte, shiftByteString, rotateByteString,
          dropList]
  | SliceByteString | VerifyEd25519Signature | VerifyEcdsaSecp256k1Signature
  | VerifySchnorrSecp256k1Signature | IntegerToByteString | AndByteString | OrByteString
  | XorByteString | WriteBits | ExpModInteger =>
      apply bcong_strict_close _ xs1 xs2 n hlen hshape
      intro ys j hj hnv
      rcases ys with _ | ⟨v0, _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, r⟩⟩⟩⟩
      · simp at hj
      · simp [evaluateBuiltinFunction, sliceByteString, verifyEd25519Signature,
          verifyEcdsaSecp256k1Signature, verifySchnorrSecp256k1Signature, integerToByteString,
          andByteString, orByteString, xorByteString, writeBits, expModInteger]
      · simp [evaluateBuiltinFunction, sliceByteString, verifyEd25519Signature,
          verifyEcdsaSecp256k1Signature, verifySchnorrSecp256k1Signature, integerToByteString,
          andByteString, orByteString, xorByteString, writeBits, expModInteger]
      · cases j with
        | zero =>
            cases v0 <;>
              simp_all [evaluateBuiltinFunction, sliceByteString, verifyEd25519Signature,
                verifyEcdsaSecp256k1Signature, verifySchnorrSecp256k1Signature,
                integerToByteString, andByteString, orByteString, xorByteString, writeBits,
                expModInteger]
        | succ j' =>
            cases j' with
            | zero =>
                cases v1 <;>
                  simp_all [evaluateBuiltinFunction, sliceByteString, verifyEd25519Signature,
                    verifyEcdsaSecp256k1Signature, verifySchnorrSecp256k1Signature,
                    integerToByteString, andByteString, orByteString, xorByteString, writeBits,
                    expModInteger]
            | succ j'' =>
                cases j'' with
                | zero =>
                    cases v2 <;>
                      simp_all [evaluateBuiltinFunction, sliceByteString,
                        verifyEd25519Signature, verifyEcdsaSecp256k1Signature,
                        verifySchnorrSecp256k1Signature, integerToByteString, andByteString,
                        orByteString, xorByteString, writeBits, expModInteger]
                | succ j''' => simp only [List.length_cons, List.length_nil] at hj; omega
      · simp [evaluateBuiltinFunction, sliceByteString, verifyEd25519Signature,
          verifyEcdsaSecp256k1Signature, verifySchnorrSecp256k1Signature, integerToByteString,
          andByteString, orByteString, xorByteString, writeBits, expModInteger]

-- ── Part 7b (completion): the 5 Return-side placeholders Part 8 unblocks, plus the `retdispatch_*`
-- helper family `step_agree_return_constr_arg`/`step_agree_return_case_scrutinee` need. Same
-- REPRESENTATION-AGNOSTIC status as Part 8 (no `Environment`/`Var`-index destructuring anywhere in
-- this section beyond what round 1's `EnvAgreeOn`/`freeVars`/`freeVarsUnderBinder`/
-- `beta_envAgreeOn_extend` already established), EXCEPT one real judgment call: the old file's
-- `step` had a separate `ifArgVOtherwiseError`/`ifArgQOtherwiseError` wrapper layer around the
-- `VBuiltin` arity dispatch, which (like `ifBoundOtherwiseError` in Part 1) genuinely no longer
-- exists here -- the real `step` (`CekMachine.lean` lines 87-116) inlines the `ExpectedBuiltinArgs`
-- dispatch directly via `ExpectedBuiltinArg.ArgV ⊙ η` / `a[ExpectedBuiltinArg.ArgV]` pattern
-- matches, so every `simp [step, ifArg...OtherwiseError]` below becomes plain `simp [step]` --
-- one fewer moving part, not a harder proof, confirmed by direct read of `step`'s real match arms
-- for `LeftApplicationToValue`/`RightApplicationOfValue`/`ForceFrame`. ─────────────────────────────

-- The real `step` equations for `Return (RightApplicationOfValue Vfunc :: s) Varg` and
-- `Return (LeftApplicationToValue Varg :: s) Vfunc` (`CekMachine.lean` lines 87-105) are the SAME
-- five equations with the frame-held value and the returned value trading places: whichever side is
-- the callable (`VLam`/`VBuiltin`) drives the match, and its counterpart plays "argument" in the
-- identical RHS either way. So the two top-level frame-popping equations agree pointwise as
-- functions of `(Vfunc, Varg)`, independent of which literal frame constructor carried which role.
-- This is the shared fact that lets `step_agree_return_left_value` below be derived directly from
-- `step_agree_return_right_value` instead of re-running the same five-way case split.
private theorem step_return_leftValue_eq_rightValue
    (sv : PlutusCore.Default.BuiltinSemanticsVariant) (s : Stack) (Vfunc Varg : CekValue) :
    step sv (State.Return (Frame.LeftApplicationToValue Varg :: s) Vfunc) =
    step sv (State.Return (Frame.RightApplicationOfValue Vfunc :: s) Varg) := by
  cases Vfunc with
  | VCon _ => simp [step]
  | VDelay _ _ => simp [step]
  | VConstr _ _ => simp [step]
  | VLam _ _ _ => simp [step]
  | VBuiltin _ _ η =>
      cases η with
      | One ι => cases ι <;> simp [step]
      | More ι _ => cases ι <;> simp [step]

-- Return (Frame.RightApplicationOfValue Vf :: s) V: generic over BOTH the frame's stored value `Vf`
-- (the function position, evaluated first) and the newly-returned `V` (the argument position).
-- Covers the ordinary-`Apply` beta step (`Vf = VLam x M ρ` -> `Eval s (V :: ρ) M`, THE hard case: it
-- is exactly here that `ValueAgree (n+1) (VLam x M ρ1) (VLam x M ρ2)` must be unfolded into
-- `EnvAgreeOn n (...) ρ1 ρ2` to build the new environment agreement, via `beta_envAgreeOn_extend`,
-- the one place in this whole family that genuinely spends the extra fuel level), the `VBuiltin`
-- arity-bookkeeping sub-arms (`ArgV` still-pending / `ArgV` fires `evalBuiltin`), and the
-- wildcard-`Error` fallback for every other `Vf` shape (`VCon`/`VConstr`/`VDelay`, not callable).
-- THE PRIMARY PROOF of this mirror pair (see `step_agree_return_left_value` below, now a direct
-- corollary via `step_return_leftValue_eq_rightValue`'s frame-swap identity).
theorem step_agree_return_right_value (sv : PlutusCore.Default.BuiltinSemanticsVariant)
    (s1 s2 : Stack) (Vf1 Vf2 V1 V2 : CekValue) (n : Nat)
    (hs : StackAgree (n + 1) s1 s2)
    (hVf : ValueAgree (n + 1) Vf1 Vf2) (hV : ValueAgree (n + 1) V1 V2) :
    StateAgree n (step sv (State.Return (Frame.RightApplicationOfValue Vf1 :: s1) V1))
                 (step sv (State.Return (Frame.RightApplicationOfValue Vf2 :: s2) V2)) := by
  cases Vf1 with
  | VCon c1 =>
      cases Vf2 with
      | VCon c2 => simp [step, StateAgree]
      | _ => exact absurd hVf (by simp [ValueAgree])
  | VDelay M1 ρ1 =>
      cases Vf2 with
      | VDelay M2 ρ2 => simp [step, StateAgree]
      | _ => exact absurd hVf (by simp [ValueAgree])
  | VConstr i1 vs1 =>
      cases Vf2 with
      | VConstr i2 vs2 => simp [step, StateAgree]
      | _ => exact absurd hVf (by simp [ValueAgree])
  | VLam x1 M1 ρ1 =>
      cases Vf2 with
      | VLam x2 M2 ρ2 =>
          obtain ⟨hx, hM, hρ⟩ :
              x1 = x2 ∧ M1 = M2 ∧ EnvAgreeOn n (freeVarsUnderBinder (freeVars M1)) ρ1 ρ2 := by
            simpa [ValueAgree] using hVf
          subst hx
          subst hM
          show StateAgree n (State.Eval s1 (V1 :: ρ1) M1) (State.Eval s2 (V2 :: ρ2) M1)
          exact ⟨rfl, StackAgree_mono n s1 s2 hs,
                 beta_envAgreeOn_extend n (freeVars M1) ρ1 ρ2 V1 V2 hρ (ValueAgree_mono n V1 V2 hV)⟩
      | _ => exact absurd hVf (by simp [ValueAgree])
  | VBuiltin b1 vs1 η1 =>
      cases Vf2 with
      | VBuiltin b2 vs2 η2 =>
          obtain ⟨hb, hη, hlen, hpt, hshape⟩ :
              b1 = b2 ∧ η1 = η2 ∧ vs1.length = vs2.length ∧
                (∀ k (h1 : k < vs1.length) (h2 : k < vs2.length), ValueAgree n (vs1[k]) (vs2[k])) ∧
                (∀ k (h1 : k < vs1.length) (h2 : k < vs2.length), fix_ValueAgreeShape (vs1[k]) (vs2[k])) := by
            simpa [ValueAgree] using hVf
          subst hb
          subst hη
          cases η1 with
          | One ι =>
              cases ι with
              | ArgQ => simp [step, StateAgree]
              | ArgV =>
                  -- `evalBuiltin` FIRES: combine the newly-applied `V1`/`V2` (position 0, agreeing
                  -- at `hV`'s own level `n+1`, downgraded via `ValueAgree_mono`/`fix_valueAgree_shape`)
                  -- with the already-accumulated `vs1`/`vs2` (positions ≥ 1, agreeing at level `n`
                  -- per `hpt`/`hshape`) into one combined pointwise-agreement fact over
                  -- `V1 :: vs1`/`V2 :: vs2`, then dispatch on `bcong_evalBuiltin_agree`'s own
                  -- two-way disjunction.
                  have hlenF : (V1 :: vs1).length = (V2 :: vs2).length := by simp [hlen]
                  have hptF : ∀ k (h1 : k < (V1 :: vs1).length) (h2 : k < (V2 :: vs2).length),
                      ValueAgree n ((V1 :: vs1)[k]) ((V2 :: vs2)[k]) := by
                    intro k h1 h2
                    cases k with
                    | zero => simpa using ValueAgree_mono n V1 V2 hV
                    | succ k' =>
                        have hk1' : k' < vs1.length := by simpa using h1
                        have hk2' : k' < vs2.length := by simpa using h2
                        simpa using hpt k' hk1' hk2'
                  have hshapeF : ∀ k (h1 : k < (V1 :: vs1).length) (h2 : k < (V2 :: vs2).length),
                      fix_ValueAgreeShape ((V1 :: vs1)[k]) ((V2 :: vs2)[k]) := by
                    intro k h1 h2
                    cases k with
                    | zero => simpa using fix_valueAgree_shape n V1 V2 hV
                    | succ k' =>
                        have hk1' : k' < vs1.length := by simpa using h1
                        have hk2' : k' < vs2.length := by simpa using h2
                        simpa using hshape k' hk1' hk2'
                  simp only [step, evalBuiltin]
                  rcases bcong_evalBuiltin_agree sv b1 (V1 :: vs1) (V2 :: vs2) n hlenF hptF hshapeF with
                    ⟨w1, w2, hw1, hw2, hw⟩ | ⟨hw1, hw2⟩
                  · simp only [hw1, hw2]
                    exact ⟨StackAgree_mono n s1 s2 hs, hw⟩
                  · simp [hw1, hw2, StateAgree]
          | More ι η' =>
              cases ι with
              | ArgQ => simp [step, StateAgree]
              | ArgV =>
                  simp only [step]
                  refine ⟨StackAgree_mono n s1 s2 hs, ?_⟩
                  cases n with
                  | zero => simp [ValueAgree]
                  | succ m =>
                      unfold ValueAgree
                      refine ⟨rfl, rfl, ?_, ?_, ?_⟩
                      · simp [hlen]
                      · intro k hk1 hk2
                        cases k with
                        | zero => exact ValueAgree_mono m V1 V2 (ValueAgree_mono (m + 1) V1 V2 hV)
                        | succ k' =>
                            have hk1' : k' < vs1.length := by simpa using hk1
                            have hk2' : k' < vs2.length := by simpa using hk2
                            exact ValueAgree_mono m _ _ (hpt k' hk1' hk2')
                      · intro k hk1 hk2
                        cases k with
                        | zero => exact fix_valueAgree_shape (m + 1) V1 V2 hV
                        | succ k' =>
                            have hk1' : k' < vs1.length := by simpa using hk1
                            have hk2' : k' < vs2.length := by simpa using hk2
                            exact hshape k' hk1' hk2'
      | _ => exact absurd hVf (by simp [ValueAgree])

-- Return (Frame.LeftApplicationToValue Vf :: s) V: the MIRROR of the arm above (frame holds the
-- pending ARGUMENT `Vf`, the newly-returned `V` is the function position) -- this order is reached
-- only via `Case`'s `folding` spine-argument mechanism (Pair/List/Data dispatch), never via ordinary
-- `Apply`. A DIRECT COROLLARY of `step_agree_return_right_value`:
-- `step_return_leftValue_eq_rightValue` rewrites this frame's `step` output into the Right-frame
-- shape with the two values' roles swapped, then the primary proof above closes it.
theorem step_agree_return_left_value (sv : PlutusCore.Default.BuiltinSemanticsVariant)
    (s1 s2 : Stack) (Vf1 Vf2 V1 V2 : CekValue) (n : Nat)
    (hs : StackAgree (n + 1) s1 s2)
    (hVf : ValueAgree (n + 1) Vf1 Vf2) (hV : ValueAgree (n + 1) V1 V2) :
    StateAgree n (step sv (State.Return (Frame.LeftApplicationToValue Vf1 :: s1) V1))
                 (step sv (State.Return (Frame.LeftApplicationToValue Vf2 :: s2) V2)) := by
  rw [step_return_leftValue_eq_rightValue sv s1 V1 Vf1,
      step_return_leftValue_eq_rightValue sv s2 V2 Vf2]
  exact step_agree_return_right_value sv s1 s2 V1 V2 Vf1 Vf2 n hs hV hVf

-- Return (Frame.ForceFrame :: s) V: generic over `V`. Covers, in one statement, the real `step`'s
-- three literal equations for this frame (`VDelay` pop, `VBuiltin` in `ArgQ`-still-pending shape,
-- `VBuiltin` in `ArgQ`-fires-`evalBuiltin` shape) AND the wildcard-`Error` fallback for every other
-- `V` shape (`VCon`/`VLam`/`VConstr`, all malformed UPLC at a `Force`).
theorem step_agree_return_force (sv : PlutusCore.Default.BuiltinSemanticsVariant)
    (s1 s2 : Stack) (V1 V2 : CekValue) (n : Nat)
    (hs : StackAgree (n + 1) s1 s2) (hV : ValueAgree (n + 1) V1 V2) :
    StateAgree n (step sv (State.Return (Frame.ForceFrame :: s1) V1))
                 (step sv (State.Return (Frame.ForceFrame :: s2) V2)) := by
  cases V1 with
  | VCon c1 =>
      cases V2 with
      | VCon c2 => simp [step, StateAgree]
      | _ => exact absurd hV (by simp [ValueAgree])
  | VDelay M1 ρ1 =>
      cases V2 with
      | VDelay M2 ρ2 =>
          obtain ⟨hM, hE⟩ : M1 = M2 ∧ EnvAgreeOn n (freeVars M1) ρ1 ρ2 := by
            simpa [ValueAgree] using hV
          subst hM
          show StateAgree n (State.Eval s1 ρ1 M1) (State.Eval s2 ρ2 M1)
          exact ⟨rfl, StackAgree_mono n s1 s2 hs, hE⟩
      | _ => exact absurd hV (by simp [ValueAgree])
  | VConstr i1 vs1 =>
      cases V2 with
      | VConstr i2 vs2 => simp [step, StateAgree]
      | _ => exact absurd hV (by simp [ValueAgree])
  | VLam x1 M1 ρ1 =>
      cases V2 with
      | VLam x2 M2 ρ2 => simp [step, StateAgree]
      | _ => exact absurd hV (by simp [ValueAgree])
  | VBuiltin b1 vs1 η1 =>
      cases V2 with
      | VBuiltin b2 vs2 η2 =>
          obtain ⟨hb, hη, hlen, hpt, hshape⟩ :
              b1 = b2 ∧ η1 = η2 ∧ vs1.length = vs2.length ∧
                (∀ k (h1 : k < vs1.length) (h2 : k < vs2.length), ValueAgree n (vs1[k]) (vs2[k])) ∧
                (∀ k (h1 : k < vs1.length) (h2 : k < vs2.length), fix_ValueAgreeShape (vs1[k]) (vs2[k])) := by
            simpa [ValueAgree] using hV
          subst hb
          subst hη
          cases η1 with
          | One ι =>
              cases ι with
              | ArgQ =>
                  -- `evalBuiltin` FIRES on both sides: `ForceFrame`'s `ArgQ` slot never conses a
                  -- newly-applied value onto the list (Force supplies no value, it only unlocks the
                  -- quoted argument), so `vs1`/`vs2` (already agreeing per `hpt`/`hshape`) are
                  -- exactly the arguments `bcong_evalBuiltin_agree` needs, no combining required.
                  simp only [step, evalBuiltin]
                  rcases bcong_evalBuiltin_agree sv b1 vs1 vs2 n hlen hpt hshape with
                    ⟨w1, w2, hw1, hw2, hw⟩ | ⟨hw1, hw2⟩
                  · simp only [hw1, hw2]
                    exact ⟨StackAgree_mono n s1 s2 hs, hw⟩
                  · simp [hw1, hw2, StateAgree]
              | ArgV => simp [step, StateAgree]
          | More ι η' =>
              cases ι with
              | ArgQ =>
                  simp only [step]
                  refine ⟨StackAgree_mono n s1 s2 hs, ?_⟩
                  cases n with
                  | zero => simp [ValueAgree]
                  | succ m =>
                      unfold ValueAgree
                      refine ⟨rfl, rfl, hlen, ?_, ?_⟩
                      · intro k hk1 hk2
                        exact ValueAgree_mono m _ _ (hpt k hk1 hk2)
                      · intro k hk1 hk2
                        exact hshape k hk1 hk2
              | ArgV => simp [step, StateAgree]
      | _ => exact absurd hV (by simp [ValueAgree])

-- ── `retdispatch_*` helpers for `step_agree_return_constr_arg` / `step_agree_return_case_scrutinee`.
-- Prefixed per the old file's own coordination rule so a sibling worktree's own new helpers cannot
-- collide with these by name. Pure `List`/`Stack`/`Const`/`Data.Data` bookkeeping throughout, no
-- `Environment`/`Var`-index content -- unchanged from the old file. ──────────────────────────────

-- Pointwise `ValueAgree n` agreement between two equal-length lists is preserved by
-- `List.reverse`: reversing both sides just permutes which index is compared, and
-- `List.getElem_reverse` says the reversed list's index `k` reads the original list's index
-- `length - 1 - k` -- since the two lists share the same length (`hlen`), that source index is
-- the SAME natural number on both sides, so `hpt` (already indexed generically) applies directly.
private theorem retdispatch_reverse_agree (n : Nat) (L1 L2 : List CekValue)
    (hlen : L1.length = L2.length)
    (hpt : ∀ k (h1 : k < L1.length) (h2 : k < L2.length), ValueAgree n (L1[k]) (L2[k])) :
    L1.reverse.length = L2.reverse.length ∧
      ∀ k (h1 : k < L1.reverse.length) (h2 : k < L2.reverse.length),
        ValueAgree n (L1.reverse[k]) (L2.reverse[k]) := by
  refine ⟨by simp [hlen], ?_⟩
  intro k h1 h2
  have hL1 : L1.reverse.length = L1.length := List.length_reverse
  have hL2 : L2.reverse.length = L2.length := List.length_reverse
  have e1 := List.getElem_reverse h1
  have e2 := List.getElem_reverse h2
  have hidx : L1.length - 1 - k = L2.length - 1 - k := by rw [hlen]
  rw [e1, e2]
  simp only [hidx]
  exact hpt (L2.length - 1 - k) (by omega) (by omega)

-- `folding` (the spine-argument frame-pusher `Case`'s dispatch uses, `CekMachine.lean`'s own
-- `where` clause on `step`) preserves `StackAgree`: it just wraps each element of an
-- agreeing/equal-length pointwise-agreeing list in its own `LeftApplicationToValue` frame, in the
-- same order, on top of an already-agreeing base stack.
private theorem retdispatch_folding_agree (n : Nat) (vs1 vs2 : List CekValue) (s1 s2 : Stack)
    (hlen : vs1.length = vs2.length)
    (hpt : ∀ k (h1 : k < vs1.length) (h2 : k < vs2.length), ValueAgree n (vs1[k]) (vs2[k]))
    (hs : StackAgree n s1 s2) :
    StackAgree n (step.folding vs1 s1) (step.folding vs2 s2) := by
  induction vs1 generalizing vs2 with
  | nil =>
      cases vs2 with
      | nil => simpa [step.folding] using hs
      | cons v2 vs2' => simp at hlen
  | cons v1 vs1' ih =>
      cases vs2 with
      | nil => simp at hlen
      | cons v2 vs2' =>
          have hlen' : vs1'.length = vs2'.length := by simpa using hlen
          have hpt' : ∀ k (h1 : k < vs1'.length) (h2 : k < vs2'.length),
              ValueAgree n (vs1'[k]) (vs2'[k]) := by
            intro k h1 h2
            have hk1 : k + 1 < (v1 :: vs1').length := by simpa using h1
            have hk2 : k + 1 < (v2 :: vs2').length := by simpa using h2
            have := hpt (k + 1) hk1 hk2
            simpa using this
          have h0 : ValueAgree n v1 v2 := by
            have hh1 : (0 : Nat) < (v1 :: vs1').length := by simp
            have hh2 : (0 : Nat) < (v2 :: vs2').length := by simp
            have := hpt 0 hh1 hh2
            simpa using this
          simp only [step.folding]
          exact ⟨h0, ih vs2' hlen' hpt'⟩

-- If `mi` is one of the terms in `Ms`, its free variables are among `Ms`'s combined free
-- variables (`freeVarsList`'s own `flatten`-of-`map` definition).
private theorem retdispatch_freeVars_subset_freeVarsList (mi : Term) (Ms : List Term)
    (hmi : mi ∈ Ms) : freeVars mi ⊆ freeVarsList Ms := by
  intro x hx
  simp only [freeVarsList, List.mem_flatten]
  exact ⟨freeVars mi, List.mem_map_of_mem hmi, hx⟩

-- `ValueAgree` is reflexive on any `VCon` value, at any fuel level (fuel 0 is vacuous; positive
-- fuel needs the SAME literal `Const`, which trivially holds against itself).
private theorem retdispatch_valueAgree_refl_vcon (n : Nat) (c : PlutusCore.UPLC.Term.Const) :
    ValueAgree n (CekValue.VCon c) (CekValue.VCon c) := by
  cases n with
  | zero => simp [ValueAgree]
  | succ m => simp [ValueAgree]

-- Same, packaged for the concrete 2-element `VCon`-wrapped spine lists the Pair/PairData/
-- ConstList/ConstDataList/ConstPairDataList `CaseScrutinee` dispatches build (identical on both
-- sides, since they're derived from the SAME shared constant once `ValueAgree`'s `VCon` clause has
-- forced literal equality).
private theorem retdispatch_valueAgree_refl_vcon_pair
    (n : Nat) (a b : PlutusCore.UPLC.Term.Const) :
    ∀ v ∈ [CekValue.VCon a, CekValue.VCon b], ValueAgree n v v := by
  intro v hv
  simp at hv
  rcases hv with rfl | rfl <;> exact retdispatch_valueAgree_refl_vcon n _

-- The common shape of a `CaseScrutinee` dispatch branch that does NOT push a spine (`Eval s ρ
-- mi`), generic over which index of `Ms` is selected.
private theorem retdispatch_case_builtin_no_fold (n : Nat) (s1 s2 : Stack) (ρ1 ρ2 : Environment)
    (Ms : List Term) (idx : Nat)
    (hs' : StackAgree n s1 s2) (hρ' : EnvAgreeOn (n + 1) (freeVarsList Ms) ρ1 ρ2) :
    StateAgree n (match Ms[idx]? with
                  | some mi => State.Eval s1 ρ1 mi
                  | none => State.Error)
                 (match Ms[idx]? with
                  | some mi => State.Eval s2 ρ2 mi
                  | none => State.Error) := by
  cases hmi : Ms[idx]? with
  | none => simp [StateAgree]
  | some mi =>
      have hmiMem : mi ∈ Ms := List.mem_of_getElem? hmi
      have hsubMi : freeVars mi ⊆ freeVarsList Ms :=
        retdispatch_freeVars_subset_freeVarsList mi Ms hmiMem
      exact ⟨rfl, hs', EnvAgreeOn_mono n (freeVars mi) ρ1 ρ2
        (envAgreeOn_subset (n + 1) (freeVarsList Ms) (freeVars mi) ρ1 ρ2 hsubMi hρ')⟩

-- The common shape of a `CaseScrutinee` dispatch branch that DOES push a spine (`Eval (folding Vs
-- s) ρ mi`), generic over the (identical-on-both-sides) spine `Vs` and which index of `Ms` is
-- selected.
private theorem retdispatch_case_builtin_fold (n : Nat) (s1 s2 : Stack) (ρ1 ρ2 : Environment)
    (Ms : List Term) (Vs : List CekValue) (idx : Nat)
    (hs' : StackAgree n s1 s2) (hρ' : EnvAgreeOn (n + 1) (freeVarsList Ms) ρ1 ρ2)
    (hrefl : ∀ v ∈ Vs, ValueAgree n v v) :
    StateAgree n (match Ms[idx]? with
                  | some mi => State.Eval (step.folding Vs s1) ρ1 mi
                  | none => State.Error)
                 (match Ms[idx]? with
                  | some mi => State.Eval (step.folding Vs s2) ρ2 mi
                  | none => State.Error) := by
  cases hmi : Ms[idx]? with
  | none => simp [StateAgree]
  | some mi =>
      have hmiMem : mi ∈ Ms := List.mem_of_getElem? hmi
      have hsubMi : freeVars mi ⊆ freeVarsList Ms :=
        retdispatch_freeVars_subset_freeVarsList mi Ms hmiMem
      refine ⟨rfl, ?_, EnvAgreeOn_mono n (freeVars mi) ρ1 ρ2
        (envAgreeOn_subset (n + 1) (freeVarsList Ms) (freeVars mi) ρ1 ρ2 hsubMi hρ')⟩
      have hpt : ∀ k (h1 : k < Vs.length) (h2 : k < Vs.length), ValueAgree n (Vs[k]) (Vs[k]) :=
        fun k h1 _ => hrefl (Vs[k]) (List.getElem_mem h1)
      exact retdispatch_folding_agree n Vs Vs s1 s2 rfl hpt hs'

-- The `VConstr` dispatch (index-select then fold its OWN accumulated element list) needs the
-- general (possibly-different-but-agreeing) form of the folding helper, not the reflexive one.
private theorem retdispatch_vconstr_case (sv : PlutusCore.Default.BuiltinSemanticsVariant)
    (s1 s2 : Stack) (ρ1 ρ2 : Environment) (Ms : List Term) (i : Nat)
    (vs1 vs2 : List CekValue) (n : Nat)
    (hs' : StackAgree n s1 s2) (hρ' : EnvAgreeOn (n + 1) (freeVarsList Ms) ρ1 ρ2)
    (hlen : vs1.length = vs2.length)
    (hpt : ∀ k (h1 : k < vs1.length) (h2 : k < vs2.length), ValueAgree n (vs1[k]) (vs2[k])) :
    StateAgree n
      (step sv (State.Return (Frame.CaseScrutinee Ms ρ1 :: s1) (CekValue.VConstr i vs1)))
      (step sv (State.Return (Frame.CaseScrutinee Ms ρ2 :: s2) (CekValue.VConstr i vs2))) := by
  simp only [step, List.get?Internal_eq_getElem?]
  cases hmi : Ms[i]? with
  | none => simp [StateAgree]
  | some mi =>
      have hmiMem : mi ∈ Ms := List.mem_of_getElem? hmi
      have hsubMi : freeVars mi ⊆ freeVarsList Ms :=
        retdispatch_freeVars_subset_freeVarsList mi Ms hmiMem
      refine ⟨rfl, ?_, EnvAgreeOn_mono n (freeVars mi) ρ1 ρ2
        (envAgreeOn_subset (n + 1) (freeVarsList Ms) (freeVars mi) ρ1 ρ2 hsubMi hρ')⟩
      exact retdispatch_folding_agree n vs1 vs2 s1 s2 hlen hpt hs'

-- Return (Frame.ConstructorArgument i Vs Ms ρ :: s) V: generic over `Vs`/`Ms` (covers the real
-- `step`'s TWO literal equations, "continue" (`Ms = M :: Ms'`, push the next argument) and "finish"
-- (`Ms = []`, `Return s (VConstr i (reverse (V :: Vs)))`), in one statement).
theorem step_agree_return_constr_arg (sv : PlutusCore.Default.BuiltinSemanticsVariant)
    (s1 s2 : Stack) (ρ1 ρ2 : Environment) (i : Nat)
    (Vs1 Vs2 : List CekValue) (Ms : List Term) (V1 V2 : CekValue) (n : Nat)
    (hs : StackAgree (n + 1) s1 s2)
    (hρ : EnvAgreeOn (n + 1) (freeVarsList Ms) ρ1 ρ2)
    (hVsLen : Vs1.length = Vs2.length)
    (hVs : ∀ k (h1 : k < Vs1.length) (h2 : k < Vs2.length), ValueAgree (n + 1) (Vs1[k]) (Vs2[k]))
    (hV : ValueAgree (n + 1) V1 V2) :
    StateAgree n (step sv (State.Return (Frame.ConstructorArgument i Vs1 Ms ρ1 :: s1) V1))
                 (step sv (State.Return (Frame.ConstructorArgument i Vs2 Ms ρ2 :: s2) V2)) := by
  cases Ms with
  | cons M' Ms' =>
      show StateAgree n (State.Eval (Frame.ConstructorArgument i (V1 :: Vs1) Ms' ρ1 :: s1) ρ1 M')
                        (State.Eval (Frame.ConstructorArgument i (V2 :: Vs2) Ms' ρ2 :: s2) ρ2 M')
      have hs' : StackAgree n s1 s2 := StackAgree_mono n s1 s2 hs
      have hVsLen' : (V1 :: Vs1).length = (V2 :: Vs2).length := by simpa using hVsLen
      have hVs' : ∀ k (h1 : k < (V1 :: Vs1).length) (h2 : k < (V2 :: Vs2).length),
          ValueAgree n ((V1 :: Vs1)[k]) ((V2 :: Vs2)[k]) := by
        intro k h1 h2
        cases k with
        | zero => exact ValueAgree_mono n V1 V2 hV
        | succ k' =>
            have hk1' : k' < Vs1.length := by simpa using h1
            have hk2' : k' < Vs2.length := by simpa using h2
            exact ValueAgree_mono n _ _ (hVs k' hk1' hk2')
      have hflv : freeVarsList (M' :: Ms') = freeVars M' ++ freeVarsList Ms' := by
        simp [freeVarsList]
      have hsub1 : freeVars M' ⊆ freeVarsList (M' :: Ms') := by
        rw [hflv]; exact List.subset_append_left _ _
      have hsub2 : freeVarsList Ms' ⊆ freeVarsList (M' :: Ms') := by
        rw [hflv]; exact List.subset_append_right _ _
      have hρ1 : EnvAgreeOn n (freeVars M') ρ1 ρ2 :=
        EnvAgreeOn_mono n (freeVars M') ρ1 ρ2 (envAgreeOn_subset (n + 1) _ _ ρ1 ρ2 hsub1 hρ)
      have hρ2 : EnvAgreeOn n (freeVarsList Ms') ρ1 ρ2 :=
        EnvAgreeOn_mono n (freeVarsList Ms') ρ1 ρ2 (envAgreeOn_subset (n + 1) _ _ ρ1 ρ2 hsub2 hρ)
      exact ⟨rfl, ⟨⟨rfl, rfl, hVsLen', hVs', hρ2⟩, hs'⟩, hρ1⟩
  | nil =>
      show StateAgree n (State.Return s1 (CekValue.VConstr i (List.reverse (V1 :: Vs1))))
                        (State.Return s2 (CekValue.VConstr i (List.reverse (V2 :: Vs2))))
      cases n with
      | zero => exact ⟨StackAgree_mono 0 s1 s2 hs, by simp [ValueAgree]⟩
      | succ m =>
          refine ⟨StackAgree_mono (m + 1) s1 s2 hs, ?_⟩
          have hVsLen' : (V1 :: Vs1).length = (V2 :: Vs2).length := by simpa using hVsLen
          have hVs' : ∀ k (h1 : k < (V1 :: Vs1).length) (h2 : k < (V2 :: Vs2).length),
              ValueAgree m ((V1 :: Vs1)[k]) ((V2 :: Vs2)[k]) := by
            intro k h1 h2
            cases k with
            | zero => exact ValueAgree_mono m V1 V2 (ValueAgree_mono (m + 1) V1 V2 hV)
            | succ k' =>
                have hk1' : k' < Vs1.length := by simpa using h1
                have hk2' : k' < Vs2.length := by simpa using h2
                exact ValueAgree_mono m _ _ (ValueAgree_mono (m + 1) _ _ (hVs k' hk1' hk2'))
          obtain ⟨hlenR, hptR⟩ := retdispatch_reverse_agree m (V1 :: Vs1) (V2 :: Vs2) hVsLen' hVs'
          show ValueAgree (m + 1) (CekValue.VConstr i (List.reverse (V1 :: Vs1)))
                                  (CekValue.VConstr i (List.reverse (V2 :: Vs2)))
          unfold ValueAgree
          exact ⟨rfl, hlenR, hptR⟩

-- Return (Frame.CaseScrutinee Ms ρ :: s) V: generic over `V`. Covers, in one statement, the real
-- `step`'s CaseScrutinee equations for this frame -- `VConstr` (index-select, no spine args) and the
-- `VCon`-constant "caseBuiltin" dispatches (Integer/Bool/Unit/Pair/PairData/ConstList/
-- ConstDataList/ConstPairDataList, several of which push spine args via `folding`, i.e.
-- `LeftApplicationToValue` frames consumed later by `step_agree_return_left_value` above) -- AND the
-- wildcard-`Error` fallback for every non-dispatchable `V` shape (`VLam`/`VDelay`/`VBuiltin`, or an
-- out-of-range/wrong-arity constant). Unchanged from the old file (pure `CekValue`/`Const` content,
-- confirmed by direct read that `CekMachine.lean`'s real `CaseScrutinee` match arms are identical).
theorem step_agree_return_case_scrutinee (sv : PlutusCore.Default.BuiltinSemanticsVariant)
    (s1 s2 : Stack) (ρ1 ρ2 : Environment) (Ms : List Term) (V1 V2 : CekValue) (n : Nat)
    (hs : StackAgree (n + 1) s1 s2)
    (hρ : EnvAgreeOn (n + 1) (freeVarsList Ms) ρ1 ρ2)
    (hV : ValueAgree (n + 1) V1 V2) :
    StateAgree n (step sv (State.Return (Frame.CaseScrutinee Ms ρ1 :: s1) V1))
                 (step sv (State.Return (Frame.CaseScrutinee Ms ρ2 :: s2) V2)) := by
  have hs' : StackAgree n s1 s2 := StackAgree_mono n s1 s2 hs
  cases V1 with
  | VConstr i1 vs1 =>
      cases V2 with
      | VConstr i2 vs2 =>
          obtain ⟨hi, hlen, hpt⟩ :
              i1 = i2 ∧ vs1.length = vs2.length ∧
                ∀ k (h1 : k < vs1.length) (h2 : k < vs2.length), ValueAgree n (vs1[k]) (vs2[k]) := by
            simpa [ValueAgree] using hV
          subst hi
          exact retdispatch_vconstr_case sv s1 s2 ρ1 ρ2 Ms i1 vs1 vs2 n hs' hρ hlen hpt
      | _ => exact absurd hV (by simp [ValueAgree])
  | VCon c1 =>
      cases V2 with
      | VCon c2 =>
          have hc : c1 = c2 := by simpa [ValueAgree] using hV
          rw [← hc]
          cases c1 with
          | Integer m =>
              simp only [step]
              rcases Bool.eq_false_or_eq_true (0 ≤ m && m.toNat < Ms.length) with heq | heq
              · simp only [heq, if_true]
                exact retdispatch_case_builtin_no_fold n s1 s2 ρ1 ρ2 Ms m.toNat hs' hρ
              · simp [heq, StateAgree]
          | Bool b =>
              cases b with
              | false =>
                  simp only [step]
                  by_cases hlen : Ms.length == 1 || Ms.length == 2
                  · simp only [hlen, if_true]
                    exact retdispatch_case_builtin_no_fold n s1 s2 ρ1 ρ2 Ms 0 hs' hρ
                  · simp [hlen, StateAgree]
              | true =>
                  simp only [step]
                  by_cases hlen : Ms.length == 2
                  · simp only [hlen, if_true]
                    exact retdispatch_case_builtin_no_fold n s1 s2 ρ1 ρ2 Ms 1 hs' hρ
                  · simp [hlen, StateAgree]
          | Unit =>
              simp only [step]
              by_cases hlen : Ms.length == 1
              · simp only [hlen, if_true]
                exact retdispatch_case_builtin_no_fold n s1 s2 ρ1 ρ2 Ms 0 hs' hρ
              · simp [hlen, StateAgree]
          | Pair p =>
              simp only [step]
              by_cases hlen : Ms.length == 1
              · simp only [hlen, if_true]
                exact retdispatch_case_builtin_fold n s1 s2 ρ1 ρ2 Ms
                  [CekValue.VCon p.1, CekValue.VCon p.2] 0
                  hs' hρ (retdispatch_valueAgree_refl_vcon_pair n p.1 p.2)
              · simp [hlen, StateAgree]
          | PairData p =>
              simp only [step]
              by_cases hlen : Ms.length == 1
              · simp only [hlen, if_true]
                exact retdispatch_case_builtin_fold n s1 s2 ρ1 ρ2 Ms
                  [CekValue.VCon (Const.Data p.1), CekValue.VCon (Const.Data p.2)] 0
                  hs' hρ (retdispatch_valueAgree_refl_vcon_pair n (Const.Data p.1) (Const.Data p.2))
              · simp [hlen, StateAgree]
          | ConstList l =>
              cases l with
              | nil =>
                  simp only [step]
                  by_cases hlen : Ms.length == 2
                  · simp only [hlen, if_true]
                    exact retdispatch_case_builtin_no_fold n s1 s2 ρ1 ρ2 Ms 1 hs' hρ
                  · simp [hlen, StateAgree]
              | cons c cs =>
                  simp only [step]
                  by_cases hlen : Ms.length == 1 || Ms.length == 2
                  · simp only [hlen, if_true]
                    exact retdispatch_case_builtin_fold n s1 s2 ρ1 ρ2 Ms
                      [CekValue.VCon c, CekValue.VCon (Const.ConstList cs)] 0
                      hs' hρ (retdispatch_valueAgree_refl_vcon_pair n c (Const.ConstList cs))
                  · simp [hlen, StateAgree]
          | ConstDataList l =>
              cases l with
              | nil =>
                  simp only [step]
                  by_cases hlen : Ms.length == 2
                  · simp only [hlen, if_true]
                    exact retdispatch_case_builtin_no_fold n s1 s2 ρ1 ρ2 Ms 1 hs' hρ
                  · simp [hlen, StateAgree]
              | cons c cs =>
                  simp only [step]
                  by_cases hlen : Ms.length == 1 || Ms.length == 2
                  · simp only [hlen, if_true]
                    exact retdispatch_case_builtin_fold n s1 s2 ρ1 ρ2 Ms
                      [CekValue.VCon (Const.Data c), CekValue.VCon (Const.ConstDataList cs)] 0
                      hs' hρ (retdispatch_valueAgree_refl_vcon_pair n (Const.Data c) (Const.ConstDataList cs))
                  · simp [hlen, StateAgree]
          | ConstPairDataList l =>
              cases l with
              | nil =>
                  simp only [step]
                  by_cases hlen : Ms.length == 2
                  · simp only [hlen, if_true]
                    exact retdispatch_case_builtin_no_fold n s1 s2 ρ1 ρ2 Ms 1 hs' hρ
                  · simp [hlen, StateAgree]
              | cons c cs =>
                  simp only [step]
                  by_cases hlen : Ms.length == 1 || Ms.length == 2
                  · simp only [hlen, if_true]
                    exact retdispatch_case_builtin_fold n s1 s2 ρ1 ρ2 Ms
                      [CekValue.VCon (Const.PairData c), CekValue.VCon (Const.ConstPairDataList cs)] 0
                      hs' hρ (retdispatch_valueAgree_refl_vcon_pair n (Const.PairData c) (Const.ConstPairDataList cs))
                  · simp [hlen, StateAgree]
          | ByteString _ => simp [step, StateAgree]
          | String _ => simp [step, StateAgree]
          | Data _ => simp [step, StateAgree]
          | Bls12_381_G1_element _ => simp [step, StateAgree]
          | Bls12_381_G2_element _ => simp [step, StateAgree]
          | Bls12_381_MlResult _ => simp [step, StateAgree]
      | _ => exact absurd hV (by simp [ValueAgree])
  | VDelay _ _ =>
      cases V2 with
      | VDelay _ _ => simp [step, StateAgree]
      | _ => exact absurd hV (by simp [ValueAgree])
  | VLam _ _ _ =>
      cases V2 with
      | VLam _ _ _ => simp [step, StateAgree]
      | _ => exact absurd hV (by simp [ValueAgree])
  | VBuiltin _ _ _ =>
      cases V2 with
      | VBuiltin _ _ _ => simp [step, StateAgree]
      | _ => exact absurd hV (by simp [ValueAgree])

-- ── Part 7c: THE COMPOSITION -- the one-step invariant, dispatching to every placeholder above.
-- This is the deliverable: if it did not type-check against the 13 `step_agree_*` signatures (plus
-- `step_var_agree`/`step_const_agree` and the 4 monotonicity facts), the seam would be cut wrong
-- and the signatures above would need to change, not this proof. The `Var i` case is NOT routed
-- through `step_var_agree` (already proven, but for a SINGLE shared stack `s` on both sides, since
-- Var-lookup never touches the stack -- here `s1 ≠ s2` in general, only `StackAgree`-related, so
-- that signature doesn't directly compose): re-derived directly from `envLookup` + `hρ`, generic
-- over both stacks independently, the same content `step_var_agree` already established. ──────────
theorem step_agree_invariant (sv : PlutusCore.Default.BuiltinSemanticsVariant)
    (n : Nat) (S1 S2 : State) (h : StateAgree (n + 1) S1 S2) :
    StateAgree n (step sv S1) (step sv S2) := by
  cases S1 with
  | Eval s1 ρ1 M1 =>
    cases S2 with
    | Eval s2 ρ2 M2 =>
      obtain ⟨hM, hs, hρ⟩ := h
      subst hM
      cases M1 with
      | Var i =>
          have hi : i ∈ freeVars (Term.Var i) := by simp [freeVars]
          unfold EnvAgreeOn at hρ
          have hlookup := hρ i hi
          have hstep1 : step sv (State.Eval s1 ρ1 (Term.Var i)) =
              (match envLookup ρ1 i with | some V => State.Return s1 V | none => State.Error) := rfl
          have hstep2 : step sv (State.Eval s2 ρ2 (Term.Var i)) =
              (match envLookup ρ2 i with | some V => State.Return s2 V | none => State.Error) := rfl
          cases hl1 : envLookup ρ1 i with
          | none =>
              rw [hl1] at hlookup
              cases hl2 : envLookup ρ2 i with
              | none => rw [hstep1, hstep2, hl1, hl2]; simp [StateAgree]
              | some v2 => simp [hl2] at hlookup
          | some v1 =>
              rw [hl1] at hlookup
              cases hl2 : envLookup ρ2 i with
              | none => simp [hl2] at hlookup
              | some v2 =>
                  simp only [hl2] at hlookup
                  rw [hstep1, hstep2, hl1, hl2]
                  exact ⟨StackAgree_mono n s1 s2 hs, ValueAgree_mono n v1 v2 hlookup⟩
      | Const c =>
          rw [show step sv (State.Eval s1 ρ1 (Term.Term.Const c)) = State.Return s1 (CekValue.VCon c)
                from rfl,
              show step sv (State.Eval s2 ρ2 (Term.Term.Const c)) = State.Return s2 (CekValue.VCon c)
                from rfl]
          refine ⟨StackAgree_mono n s1 s2 hs, ?_⟩
          cases n with
          | zero => simp [ValueAgree]
          | succ m => simp [ValueAgree]
      | Builtin b => exact step_agree_builtin_eval sv s1 s2 ρ1 ρ2 b n hs
      | Lam x M => exact step_agree_lam sv s1 s2 ρ1 ρ2 x M n hs hρ
      | Apply M N => exact step_agree_apply_eval sv s1 s2 ρ1 ρ2 M N n hs hρ
      | Delay M => exact step_agree_delay sv s1 s2 ρ1 ρ2 M n hs hρ
      | Force M => exact step_agree_force_eval sv s1 s2 ρ1 ρ2 M n hs hρ
      | Constr i Ms => exact step_agree_constr_eval sv s1 s2 ρ1 ρ2 i Ms n hs hρ
      | Case N Ms => exact step_agree_case_eval sv s1 s2 ρ1 ρ2 N Ms n hs hρ
      | Error => simp [step, StateAgree]
    | Return _ _ => exact absurd h (by simp [StateAgree])
    | Halt _ => exact absurd h (by simp [StateAgree])
    | Error => exact absurd h (by simp [StateAgree])
  | Return s1 v1 =>
    cases S2 with
    | Return s2 v2 =>
      obtain ⟨hs, hv⟩ := h
      cases s1 with
      | nil =>
        cases s2 with
        | nil => exact ValueAgree_mono n v1 v2 hv
        | cons f2 s2' => exact absurd hs (by simp [StackAgree])
      | cons f1 s1' =>
        cases s2 with
        | nil => exact absurd hs (by simp [StackAgree])
        | cons f2 s2' =>
          obtain ⟨hf, hs'⟩ := hs
          cases f1 with
          | ForceFrame =>
              cases f2 with
              | ForceFrame => exact step_agree_return_force sv s1' s2' v1 v2 n hs' hv
              | _ => exact absurd hf (by simp [FrameAgree])
          | LeftApplicationToTerm M ρ1 =>
              cases f2 with
              | LeftApplicationToTerm M' ρ2 =>
                  obtain ⟨hMeq, hρf⟩ := hf
                  subst hMeq
                  exact step_agree_return_left_term sv s1' s2' ρ1 ρ2 M v1 v2 n hs' hρf hv
              | _ => exact absurd hf (by simp [FrameAgree])
          | RightApplicationOfValue vf1 =>
              cases f2 with
              | RightApplicationOfValue vf2 =>
                  exact step_agree_return_right_value sv s1' s2' vf1 vf2 v1 v2 n hs' hf hv
              | _ => exact absurd hf (by simp [FrameAgree])
          | LeftApplicationToValue vf1 =>
              cases f2 with
              | LeftApplicationToValue vf2 =>
                  exact step_agree_return_left_value sv s1' s2' vf1 vf2 v1 v2 n hs' hf hv
              | _ => exact absurd hf (by simp [FrameAgree])
          | ConstructorArgument i vs1 Ms ρ1 =>
              cases f2 with
              | ConstructorArgument i' vs2 Ms' ρ2 =>
                  obtain ⟨hieq, hMseq, hvslen, hvsagree, hρf⟩ := hf
                  subst hieq
                  subst hMseq
                  exact step_agree_return_constr_arg sv s1' s2' ρ1 ρ2 i vs1 vs2 Ms v1 v2 n
                    hs' hρf hvslen hvsagree hv
              | _ => exact absurd hf (by simp [FrameAgree])
          | CaseScrutinee Ms ρ1 =>
              cases f2 with
              | CaseScrutinee Ms' ρ2 =>
                  obtain ⟨hMseq, hρf⟩ := hf
                  subst hMseq
                  exact step_agree_return_case_scrutinee sv s1' s2' ρ1 ρ2 Ms v1 v2 n hs' hρf hv
              | _ => exact absurd hf (by simp [FrameAgree])
    | Eval _ _ _ => exact absurd h (by simp [StateAgree])
    | Halt _ => exact absurd h (by simp [StateAgree])
    | Error => exact absurd h (by simp [StateAgree])
  | Halt v1 =>
    cases S2 with
    | Halt v2 => simp [step, StateAgree]
    | Eval _ _ _ => exact absurd h (by simp [StateAgree])
    | Return _ _ => exact absurd h (by simp [StateAgree])
    | Error => exact absurd h (by simp [StateAgree])
  | Error =>
    cases S2 with
    | Error => simp [step, StateAgree]
    | Eval _ _ _ => exact absurd h (by simp [StateAgree])
    | Return _ _ => exact absurd h (by simp [StateAgree])
    | Halt _ => exact absurd h (by simp [StateAgree])

-- ── beta_return_right_value_counterexample: unchanged from the old file's own content and
-- purpose (a machine-checked replay confirming the fixed `VBuiltin` clause of `ValueAgree`
-- still defeats the historical broken-clause witness), restated only against this repo's
-- `VLam`/`Environment` shapes (`VLam` keeps its display-only `String` field even under de Bruijn
-- indexing, per `CekValue.lean`'s own header comment; `Environment.EmptyEnvironment` becomes the
-- empty list `[]`). ─────────────────────────────────────────────────────────────────────────────
section BetaReturnRightValueCounterexample

-- Vf1: a VBuiltin one arg short of firing AddInteger, with a well-typed accumulated arg.
def beta_ce_Vf1 : CekValue :=
  CekValue.VBuiltin BuiltinFun.AddInteger [CekValue.VCon (Const.Integer 5)] (.One .ArgV)

-- Vf2: same b/η/arity, but the accumulated arg is a VLam instead of a VCon -- under the ORIGINAL
-- (broken) clause this was only legal because `ValueAgree 0` (the fuel the VBuiltin clause gave
-- its accumulated-arg list) is vacuously True for ANY pair of values.
def beta_ce_Vf2 : CekValue :=
  CekValue.VBuiltin BuiltinFun.AddInteger [CekValue.VLam "y" Term.Error []] (.One .ArgV)

def beta_ce_V1 : CekValue := CekValue.VCon (Const.Integer 3)
def beta_ce_V2 : CekValue := CekValue.VCon (Const.Integer 3)

def beta_ce_sv : PlutusCore.Default.BuiltinSemanticsVariant := default

-- Side 1 fires `evaluateBuiltinFunction` on an all-VCon list and Returns `VCon (Integer 8)`.
#eval step beta_ce_sv
  (State.Return (Frame.RightApplicationOfValue beta_ce_Vf1 :: ([] : Stack)) beta_ce_V1)
-- Side 2 feeds a VLam where AddInteger's pattern needs a VCon, falls to `_ => none`, hence Error.
#eval step beta_ce_sv
  (State.Return (Frame.RightApplicationOfValue beta_ce_Vf2 :: ([] : Stack)) beta_ce_V2)

-- CONFIRMATION the fix (`fix_ValueAgreeShape`, the conjunct added to `ValueAgree`'s `VBuiltin`
-- clause) defeats this exact witness, same conclusion as the old file: `beta_ce_Vf1`'s
-- accumulated element `VCon (Integer 5)` and `beta_ce_Vf2`'s `VLam "y" Term.Error []` are a
-- `VCon`-vs-`VLam` outer-constructor mismatch, so `fix_ValueAgreeShape` refutes them
-- unconditionally, regardless of fuel -- a genuine, checked (not `sorry`'d) proof, not a guess.
example : ¬ ValueAgree 1 beta_ce_Vf1 beta_ce_Vf2 := by
  simp [beta_ce_Vf1, beta_ce_Vf2, ValueAgree, fix_ValueAgreeShape]

end BetaReturnRightValueCounterexample

-- ── Part 9 (fuelpres_*): the fuel-GENUINITY investigation -- for each of the 13 `step_agree_*`
-- placeholders above, does it need its uniform "hypotheses at n+1, conclusion at n" convention for
-- REAL, or is that convention just a deliberate uniformity choice paying for something the
-- underlying `step` case never actually costs? Every theorem below is NEW and ADDITIVE (nothing
-- above this line is touched); every name is prefixed `fuelpres_` per the old file's own
-- coordination rule, carried over unchanged.
--
-- THE ANSWER, unchanged from the old file's own finding (this is a fact about `ValueAgree`'s own
-- recursive shape, which round 1 already established translates unchanged -- confirmed directly
-- this round by rereading the mutual definition above, not assumed): fuel is lost at EXACTLY one
-- structural point -- unfolding an ALREADY-WRAPPED `ValueAgree` hypothesis on a closure-shaped
-- value (`VLam`, `VDelay`, or a `VBuiltin` with a non-empty accumulated argument list) to reach
-- what it says about the value's OWN captured contents. `ValueAgree`'s own clauses (Part 3) always
-- state that fact ONE level below the wrapping level (`ValueAgree (n+1) (VLam ...) (VLam ...)`
-- unfolds to `EnvAgreeOn n (...)`, never `EnvAgreeOn (n+1)`) -- this is definitional, not a
-- proof-search artifact, so no amount of cleverness recovers the missing level once the value is
-- already wrapped. By contrast, CONSTRUCTING a fresh wrapped value (a fresh `VLam`/`VDelay`/
-- `VConstr`, or a `VBuiltin` either freshly built with `[]` or re-consing onto its OWN
-- already-agreeing accumulated list) from a RAW, not-yet-wrapped `EnvAgreeOn`/`ValueAgree`
-- hypothesis costs NOTHING extra: if that raw hypothesis is supplied at the SAME level `N` as the
-- wrapping value's own promised level, downgrading it ONCE (via `EnvAgreeOn_mono`/
-- `ValueAgree_mono`) to `N - 1` for the wrapping clause's own internal need is exactly the "one
-- level of slack" a same-level hypothesis always carries relative to a "one-level-lower" internal
-- requirement. `FrameAgree`/`StackAgree` (Part 7a) never cost anything either way (confirmed
-- already, that Part's own definition never forwards a downgraded level): pushing or popping a
-- frame forwards whatever level it is given, unchanged.
--
-- CONSEQUENCE: "genuinely fuel-consuming" = the placeholder's own `step` equation, on some
-- internal branch, DESTRUCTURES an already-wrapped closure-shaped `ValueAgree` hypothesis to reach
-- an `Eval` state or a brand-new, unrelated `Return` value (i.e. it ESCAPES the wrapping
-- structure). "Genuinely fuel-preserving" = every other branch: pure control-flow (push/pop a
-- frame), or CONSTRUCTING a fresh wrapped value from raw hypotheses, or RE-WRAPPING an existing
-- partial application's accumulated arguments into another `VBuiltin` of the same shape (the "one
-- level lost unwrapping" and "one level lost wrapping again" exactly cancel). Five genuinely-costly
-- sub-cases exist, same five as the old file found, at the same five `step` branches (this repo's
-- `step`, read in full above/in `CekMachine.lean`, has the exact same branch structure as the old
-- file's -- only the `Var`/`Environment` shape changed, and none of these five obstructions touch
-- either): `VLam`-beta construction of a NEW environment (`RightApplicationOfValue`/
-- `LeftApplicationToValue`), the `VBuiltin`-arity-JUST-exhausted `evalBuiltin`-fires sub-case (both
-- mirror placeholders, and `ForceFrame`'s analogous sub-case), `VDelay`-pop under `ForceFrame`, and
-- `CaseScrutinee`'s `VConstr`-scrutinee dispatch (destructuring the incoming `VConstr`'s own
-- accumulated element list to build `folding`'s spine of `LeftApplicationToValue` frames, which --
-- unlike `ValueAgree`/`EnvAgreeOn` -- is NOT fuel-indexed and so needs its elements at the FULL
-- outer level, not one below it).

open PlutusCore.UPLC.Builtins

-- 1/13, `step_agree_lam`: CONSTRUCTS a fresh `VLam` from a raw `EnvAgreeOn` hypothesis --
-- preserving.
theorem fuelpres_lam_eval (sv : PlutusCore.Default.BuiltinSemanticsVariant)
    (s1 s2 : Stack) (ρ1 ρ2 : Environment) (x : String) (M : Term) (n : Nat)
    (hs : StackAgree n s1 s2)
    (hρ : EnvAgreeOn n (freeVars (.Lam x M)) ρ1 ρ2) :
    StateAgree n (step sv (State.Eval s1 ρ1 (.Lam x M)))
                 (step sv (State.Eval s2 ρ2 (.Lam x M))) := by
  refine ⟨hs, ?_⟩
  simp only [freeVars] at hρ
  cases n with
  | zero => simp [ValueAgree]
  | succ p =>
      unfold ValueAgree
      exact ⟨rfl, rfl, EnvAgreeOn_mono p _ ρ1 ρ2 hρ⟩

-- 2/13, `step_agree_delay`: same construction pattern as `step_agree_lam` -- preserving.
theorem fuelpres_delay_eval (sv : PlutusCore.Default.BuiltinSemanticsVariant)
    (s1 s2 : Stack) (ρ1 ρ2 : Environment) (M : Term) (n : Nat)
    (hs : StackAgree n s1 s2)
    (hρ : EnvAgreeOn n (freeVars (.Delay M)) ρ1 ρ2) :
    StateAgree n (step sv (State.Eval s1 ρ1 (.Delay M)))
                 (step sv (State.Eval s2 ρ2 (.Delay M))) := by
  refine ⟨hs, ?_⟩
  simp only [freeVars] at hρ
  cases n with
  | zero => simp [ValueAgree]
  | succ p =>
      unfold ValueAgree
      exact ⟨rfl, EnvAgreeOn_mono p _ ρ1 ρ2 hρ⟩

-- 3/13, `step_agree_force_eval`: pure control flow (push `ForceFrame`, no value touched) --
-- preserving, and in fact needs no monotonicity at all (the pushed frame and the sub-evaluation
-- get the incoming hypotheses back verbatim).
theorem fuelpres_force_eval (sv : PlutusCore.Default.BuiltinSemanticsVariant)
    (s1 s2 : Stack) (ρ1 ρ2 : Environment) (M : Term) (n : Nat)
    (hs : StackAgree n s1 s2)
    (hρ : EnvAgreeOn n (freeVars (.Force M)) ρ1 ρ2) :
    StateAgree n (step sv (State.Eval s1 ρ1 (.Force M)))
                 (step sv (State.Eval s2 ρ2 (.Force M))) := by
  refine ⟨rfl, ⟨by simp [FrameAgree], hs⟩, ?_⟩
  simpa [freeVars] using hρ

-- 4/13, `step_agree_apply_eval`: pure control flow (push `LeftApplicationToTerm`) -- preserving.
theorem fuelpres_apply_eval (sv : PlutusCore.Default.BuiltinSemanticsVariant)
    (s1 s2 : Stack) (ρ1 ρ2 : Environment) (M N : Term) (n : Nat)
    (hs : StackAgree n s1 s2)
    (hρ : EnvAgreeOn n (freeVars (.Apply M N)) ρ1 ρ2) :
    StateAgree n (step sv (State.Eval s1 ρ1 (.Apply M N)))
                 (step sv (State.Eval s2 ρ2 (.Apply M N))) := by
  have hρ' : EnvAgreeOn n (freeVars M ++ freeVars N) ρ1 ρ2 := by simpa [freeVars] using hρ
  have hM : EnvAgreeOn n (freeVars M) ρ1 ρ2 :=
    envAgreeOn_subset n (freeVars M ++ freeVars N) (freeVars M) ρ1 ρ2
      (fun i hi => List.mem_append.2 (Or.inl hi)) hρ'
  have hN : EnvAgreeOn n (freeVars N) ρ1 ρ2 :=
    envAgreeOn_subset n (freeVars M ++ freeVars N) (freeVars N) ρ1 ρ2
      (fun i hi => List.mem_append.2 (Or.inr hi)) hρ'
  show StateAgree n (State.Eval (Frame.LeftApplicationToTerm N ρ1 :: s1) ρ1 M)
                    (State.Eval (Frame.LeftApplicationToTerm N ρ2 :: s2) ρ2 M)
  exact ⟨rfl, ⟨⟨rfl, hN⟩, hs⟩, hM⟩

-- 5/13, `step_agree_constr_eval`: `nil` builds a fresh empty-list `VConstr` (trivially preserving,
-- vacuous elementwise clause); `cons` is pure control flow (push `ConstructorArgument`) --
-- preserving throughout.
theorem fuelpres_constr_eval (sv : PlutusCore.Default.BuiltinSemanticsVariant)
    (s1 s2 : Stack) (ρ1 ρ2 : Environment) (i : Nat) (Ms : List Term) (n : Nat)
    (hs : StackAgree n s1 s2)
    (hρ : EnvAgreeOn n (freeVars (.Constr i Ms)) ρ1 ρ2) :
    StateAgree n (step sv (State.Eval s1 ρ1 (.Constr i Ms)))
                 (step sv (State.Eval s2 ρ2 (.Constr i Ms))) := by
  cases Ms with
  | nil =>
      show StateAgree n (State.Return s1 (CekValue.VConstr i []))
                        (State.Return s2 (CekValue.VConstr i []))
      refine ⟨hs, ?_⟩
      cases n with
      | zero => simp [ValueAgree]
      | succ m => simp [ValueAgree]
  | cons M' Ms' =>
      have hρ' : EnvAgreeOn n (freeVars M' ++ freeVarsList Ms') ρ1 ρ2 := by
        simpa [freeVars, freeVarsList] using hρ
      have hM' : EnvAgreeOn n (freeVars M') ρ1 ρ2 :=
        envAgreeOn_subset n (freeVars M' ++ freeVarsList Ms') (freeVars M') ρ1 ρ2
          (fun i hi => List.mem_append.2 (Or.inl hi)) hρ'
      have hMs' : EnvAgreeOn n (freeVarsList Ms') ρ1 ρ2 :=
        envAgreeOn_subset n (freeVars M' ++ freeVarsList Ms') (freeVarsList Ms') ρ1 ρ2
          (fun i hi => List.mem_append.2 (Or.inr hi)) hρ'
      show StateAgree n (State.Eval (Frame.ConstructorArgument i [] Ms' ρ1 :: s1) ρ1 M')
                        (State.Eval (Frame.ConstructorArgument i [] Ms' ρ2 :: s2) ρ2 M')
      refine ⟨rfl, ⟨⟨rfl, rfl, rfl, ?_, hMs'⟩, hs⟩, hM'⟩
      intro k h1 h2
      simp at h1

-- 6/13, `step_agree_case_eval`: pure control flow (push `CaseScrutinee`) -- preserving.
theorem fuelpres_case_eval (sv : PlutusCore.Default.BuiltinSemanticsVariant)
    (s1 s2 : Stack) (ρ1 ρ2 : Environment) (N : Term) (Ms : List Term) (n : Nat)
    (hs : StackAgree n s1 s2)
    (hρ : EnvAgreeOn n (freeVars (.Case N Ms)) ρ1 ρ2) :
    StateAgree n (step sv (State.Eval s1 ρ1 (.Case N Ms)))
                 (step sv (State.Eval s2 ρ2 (.Case N Ms))) := by
  have hρ' : EnvAgreeOn n (freeVars N ++ freeVarsList Ms) ρ1 ρ2 := by
    simpa [freeVars, freeVarsList] using hρ
  have hN : EnvAgreeOn n (freeVars N) ρ1 ρ2 :=
    envAgreeOn_subset n (freeVars N ++ freeVarsList Ms) (freeVars N) ρ1 ρ2
      (fun i hi => List.mem_append.2 (Or.inl hi)) hρ'
  have hMs : EnvAgreeOn n (freeVarsList Ms) ρ1 ρ2 :=
    envAgreeOn_subset n (freeVars N ++ freeVarsList Ms) (freeVarsList Ms) ρ1 ρ2
      (fun i hi => List.mem_append.2 (Or.inr hi)) hρ'
  show StateAgree n (State.Eval (Frame.CaseScrutinee Ms ρ1 :: s1) ρ1 N)
                    (State.Eval (Frame.CaseScrutinee Ms ρ2 :: s2) ρ2 N)
  exact ⟨rfl, ⟨⟨rfl, hMs⟩, hs⟩, hN⟩

-- 7/13, `step_agree_builtin_eval`: builds `VBuiltin b [] (α b)` -- the accumulated list is `[]`,
-- so the elementwise clause is vacuous regardless of fuel; does not even need `ρ`/`hρ` as input --
-- preserving, and in fact fuel-independent altogether.
theorem fuelpres_builtin_eval (sv : PlutusCore.Default.BuiltinSemanticsVariant)
    (s1 s2 : Stack) (ρ1 ρ2 : Environment) (b : BuiltinFun) (n : Nat)
    (hs : StackAgree n s1 s2) :
    StateAgree n (step sv (State.Eval s1 ρ1 (.Builtin b)))
                 (step sv (State.Eval s2 ρ2 (.Builtin b))) := by
  refine ⟨hs, ?_⟩
  cases n with
  | zero => simp [ValueAgree]
  | succ p => simp [ValueAgree]

-- 8/13, `step_agree_return_left_term`: pure control flow (push `RightApplicationOfValue`, `V` is
-- never inspected) -- preserving.
theorem fuelpres_return_left_term (sv : PlutusCore.Default.BuiltinSemanticsVariant)
    (s1 s2 : Stack) (ρ1 ρ2 : Environment) (M : Term) (V1 V2 : CekValue) (n : Nat)
    (hs : StackAgree n s1 s2)
    (hρ : EnvAgreeOn n (freeVars M) ρ1 ρ2)
    (hV : ValueAgree n V1 V2) :
    StateAgree n (step sv (State.Return (Frame.LeftApplicationToTerm M ρ1 :: s1) V1))
                 (step sv (State.Return (Frame.LeftApplicationToTerm M ρ2 :: s2) V2)) := by
  show StateAgree n (State.Eval (Frame.RightApplicationOfValue V1 :: s1) ρ1 M)
                    (State.Eval (Frame.RightApplicationOfValue V2 :: s2) ρ2 M)
  exact ⟨rfl, ⟨hV, hs⟩, hρ⟩

-- ── 9/13, `step_agree_return_right_value`: split per real `step` branch on the frame's stored
-- function value `Vf`. `VCon`/`VDelay`/`VConstr` (not callable) and the `VBuiltin` `ArgQ`-mismatch
-- sub-cases are Error/Error unconditionally (fuel-irrelevant); `VBuiltin`'s `More`-arity (re-wrap,
-- not escape) is preserving; `VLam`-beta and `VBuiltin`'s `One`-arity (`evalBuiltin` FIRES, escapes
-- the wrapping) are IMPOSSIBLE at the same level -- documented below, no theorem stated for either.

-- Shape predicate for `RightApplicationOfValue`/`LeftApplicationToValue`'s dispatch: a value is
-- APPLICATION-dispatchable exactly when `step`'s real match arms for these frames do something
-- other than fall to the wildcard `Error` arm.
def isAppDispatchable : CekValue → Prop
  | .VLam _ _ _ => True
  | .VBuiltin _ _ (.One .ArgV) => True
  | .VBuiltin _ _ (.More .ArgV _) => True
  | _ => False

private theorem step_return_right_value_error_of_not_dispatchable
    (sv : PlutusCore.Default.BuiltinSemanticsVariant) (s : Stack) (Vf V : CekValue)
    (h : ¬ isAppDispatchable Vf) :
    step sv (State.Return (Frame.RightApplicationOfValue Vf :: s) V) = State.Error := by
  cases Vf with
  | VCon _ => simp [step]
  | VDelay _ _ => simp [step]
  | VConstr _ _ => simp [step]
  | VLam _ _ _ => exact absurd (by simp [isAppDispatchable]) h
  | VBuiltin b vs η =>
      cases η with
      | One ι =>
          cases ι with
          | ArgV => exact absurd (by simp [isAppDispatchable]) h
          | ArgQ => simp [step]
      | More ι η' =>
          cases ι with
          | ArgV => exact absurd (by simp [isAppDispatchable]) h
          | ArgQ => simp [step]

theorem fuelpres_return_right_value_wildcard (sv : PlutusCore.Default.BuiltinSemanticsVariant)
    (s1 s2 : Stack) (Vf1 Vf2 V1 V2 : CekValue) (n : Nat)
    (h1 : ¬ isAppDispatchable Vf1) (h2 : ¬ isAppDispatchable Vf2) :
    StateAgree n (step sv (State.Return (Frame.RightApplicationOfValue Vf1 :: s1) V1))
                 (step sv (State.Return (Frame.RightApplicationOfValue Vf2 :: s2) V2)) := by
  rw [step_return_right_value_error_of_not_dispatchable sv s1 Vf1 V1 h1,
      step_return_right_value_error_of_not_dispatchable sv s2 Vf2 V2 h2]
  simp [StateAgree]

-- `VBuiltin` arity NOT YET exhausted: `V` is consed onto the accumulated list and a NEW `VBuiltin`
-- (same remaining arity `η'`) is re-wrapped -- unwrapping `hV1/hV2`'s own agreement one level below
-- `n` (forced) and re-wrapping at `n` (needing exactly one level below `n`) cancel exactly.
theorem fuelpres_return_right_value_vbuiltin_more_argv
    (sv : PlutusCore.Default.BuiltinSemanticsVariant)
    (s1 s2 : Stack) (b : BuiltinFun) (vs1 vs2 : List CekValue) (η' : ExpectedBuiltinArgs)
    (V1 V2 : CekValue) (n : Nat)
    (hs : StackAgree n s1 s2)
    (hlen : vs1.length = vs2.length)
    (hpt : ∀ k (h1 : k < vs1.length) (h2 : k < vs2.length), ValueAgree n (vs1[k]) (vs2[k]))
    (hshape : ∀ k (h1 : k < vs1.length) (h2 : k < vs2.length), fix_ValueAgreeShape (vs1[k]) (vs2[k]))
    (hV : ValueAgree n V1 V2) :
    StateAgree n
      (step sv (State.Return
        (Frame.RightApplicationOfValue (CekValue.VBuiltin b vs1 (.More .ArgV η')) :: s1) V1))
      (step sv (State.Return
        (Frame.RightApplicationOfValue (CekValue.VBuiltin b vs2 (.More .ArgV η')) :: s2) V2)) := by
  simp only [step]
  refine ⟨hs, ?_⟩
  cases n with
  | zero => simp [ValueAgree]
  | succ m =>
      unfold ValueAgree
      refine ⟨rfl, rfl, ?_, ?_, ?_⟩
      · simp [hlen]
      · intro k hk1 hk2
        cases k with
        | zero => exact ValueAgree_mono m V1 V2 hV
        | succ k' =>
            have hk1' : k' < vs1.length := by simpa using hk1
            have hk2' : k' < vs2.length := by simpa using hk2
            exact ValueAgree_mono m _ _ (hpt k' hk1' hk2')
      · intro k hk1 hk2
        cases k with
        | zero => exact fix_valueAgree_shape m V1 V2 hV
        | succ k' =>
            have hk1' : k' < vs1.length := by simpa using hk1
            have hk2' : k' < vs2.length := by simpa using hk2
            exact hshape k' hk1' hk2'

-- OBSTRUCTION 1/5 (`VLam`-beta, `step_agree_return_right_value`'s hardest sub-case): the real
-- `step` equation is `Return (RightApplicationOfValue (VLam x M ρ1)) V1 => Eval s1 (V1 :: ρ1) M`.
-- Proving `StateAgree N` of the two resulting `Eval` states needs `EnvAgreeOn N (freeVars M)
-- (V1 :: ρ1) (V2 :: ρ2)`, which by `beta_envAgreeOn_extend` needs BOTH `EnvAgreeOn N
-- (freeVarsUnderBinder (freeVars M)) ρ1 ρ2` and `ValueAgree N V1 V2` AT THE SAME LEVEL `N`. But the
-- only route to the first fact is unfolding the ALREADY-WRAPPED hypothesis `ValueAgree N (VLam x M
-- ρ1) (VLam x M ρ2)` via `ValueAgree`'s own `VLam` clause -- for wrapping level `N = n+1`, this
-- gives `EnvAgreeOn n (...) = EnvAgreeOn (N-1) (...)`, ONE LEVEL BELOW `N`, definitionally, with no
-- other route to more. `EnvAgreeOn_mono` only ever goes DOWNWARD, so there is no way to promote the
-- extracted `EnvAgreeOn (N-1)` fact back up to the `EnvAgreeOn N` `beta_envAgreeOn_extend` needs.
-- The achievable output is therefore `StateAgree (N-1)`, exactly the ORIGINAL placeholder's own
-- "(n+1) hypothesis to n conclusion" shape restated with `N = n+1` -- confirming the loss here is
-- real, not an artifact of the uniform convention, and unchanged from the old file's finding (this
-- entire argument is about `ValueAgree`'s own recursive shape, not about `Var`/`Environment`
-- representation).

-- OBSTRUCTION 2/5 (`VBuiltin` arity JUST exhausted, `One`/`ArgV`, `evalBuiltin` FIRES): the real
-- equation is `Return (RightApplicationOfValue (VBuiltin b vs1 (One ArgV))) V1 => evalBuiltin sv s1
-- b (V1 :: vs1)`, an ESCAPE from the wrapping `VBuiltin` structure into a brand-new value with no
-- `VBuiltin` wrapper left to "give back" a level to. `bcong_evalBuiltin_agree` (Part 8, confirmed
-- above to be level-PRESERVING, same `n` in and out) is itself not the bottleneck: the loss is
-- entirely upstream, in what level `vs1`/`vs2`'s own pointwise agreement can be extracted at --
-- `ValueAgree`'s `VBuiltin` clause gives the accumulated list's elements at `ValueAgree n` for a
-- WRAPPING level `n+1`, again ONE LEVEL BELOW the wrapping hypothesis's own level `N`, forced, with
-- no route to `N` itself (the freshly-applied `V1`/`V2` are no better: they arrive at `ValueAgree
-- N` directly, one level ABOVE what `vs1` can supply, so combining them into one pointwise fact
-- over `V1 :: vs1` forces the whole list down to the WEAKER `vs1` ceiling, `N - 1`). So the
-- combined input to `bcong_evalBuiltin_agree` is capped at `N - 1`, and so is its output --
-- `StateAgree (N - 1)`, not `StateAgree N`. Same mechanism as the `VLam`-beta case (destructuring
-- an already-wrapped closure-shaped value), just on `VBuiltin`'s accumulated-argument field instead
-- of `VLam`'s captured environment.

-- ── 10/13, `step_agree_return_left_value`: the MIRROR of #9 above (the returned value `V` plays
-- the "function" role, the frame's stored value `Vf` plays the "argument" role) -- identical fuel
-- genuinity split, same two obstructions (`VLam`-beta, `VBuiltin` `One`/`ArgV`-fires), for the
-- exact same reasons with the two roles swapped; not re-derived in full, only restated as
-- theorems.

private theorem step_return_left_value_error_of_not_dispatchable
    (sv : PlutusCore.Default.BuiltinSemanticsVariant) (s : Stack) (Vf V : CekValue)
    (h : ¬ isAppDispatchable V) :
    step sv (State.Return (Frame.LeftApplicationToValue Vf :: s) V) = State.Error := by
  cases V with
  | VCon _ => simp [step]
  | VDelay _ _ => simp [step]
  | VConstr _ _ => simp [step]
  | VLam _ _ _ => exact absurd (by simp [isAppDispatchable]) h
  | VBuiltin b vs η =>
      cases η with
      | One ι =>
          cases ι with
          | ArgV => exact absurd (by simp [isAppDispatchable]) h
          | ArgQ => simp [step]
      | More ι η' =>
          cases ι with
          | ArgV => exact absurd (by simp [isAppDispatchable]) h
          | ArgQ => simp [step]

theorem fuelpres_return_left_value_wildcard (sv : PlutusCore.Default.BuiltinSemanticsVariant)
    (s1 s2 : Stack) (Vf1 Vf2 V1 V2 : CekValue) (n : Nat)
    (h1 : ¬ isAppDispatchable V1) (h2 : ¬ isAppDispatchable V2) :
    StateAgree n (step sv (State.Return (Frame.LeftApplicationToValue Vf1 :: s1) V1))
                 (step sv (State.Return (Frame.LeftApplicationToValue Vf2 :: s2) V2)) := by
  rw [step_return_left_value_error_of_not_dispatchable sv s1 Vf1 V1 h1,
      step_return_left_value_error_of_not_dispatchable sv s2 Vf2 V2 h2]
  simp [StateAgree]

theorem fuelpres_return_left_value_vbuiltin_more_argv
    (sv : PlutusCore.Default.BuiltinSemanticsVariant)
    (s1 s2 : Stack) (Vf1 Vf2 : CekValue) (b : BuiltinFun) (vs1 vs2 : List CekValue)
    (η' : ExpectedBuiltinArgs) (n : Nat)
    (hs : StackAgree n s1 s2)
    (hlen : vs1.length = vs2.length)
    (hpt : ∀ k (h1 : k < vs1.length) (h2 : k < vs2.length), ValueAgree n (vs1[k]) (vs2[k]))
    (hshape : ∀ k (h1 : k < vs1.length) (h2 : k < vs2.length), fix_ValueAgreeShape (vs1[k]) (vs2[k]))
    (hVf : ValueAgree n Vf1 Vf2) :
    StateAgree n
      (step sv (State.Return (Frame.LeftApplicationToValue Vf1 :: s1)
        (CekValue.VBuiltin b vs1 (.More .ArgV η'))))
      (step sv (State.Return (Frame.LeftApplicationToValue Vf2 :: s2)
        (CekValue.VBuiltin b vs2 (.More .ArgV η')))) := by
  simp only [step]
  refine ⟨hs, ?_⟩
  cases n with
  | zero => simp [ValueAgree]
  | succ m =>
      unfold ValueAgree
      refine ⟨rfl, rfl, ?_, ?_, ?_⟩
      · simp [hlen]
      · intro k hk1 hk2
        cases k with
        | zero => exact ValueAgree_mono m Vf1 Vf2 hVf
        | succ k' =>
            have hk1' : k' < vs1.length := by simpa using hk1
            have hk2' : k' < vs2.length := by simpa using hk2
            exact ValueAgree_mono m _ _ (hpt k' hk1' hk2')
      · intro k hk1 hk2
        cases k with
        | zero => exact fix_valueAgree_shape m Vf1 Vf2 hVf
        | succ k' =>
            have hk1' : k' < vs1.length := by simpa using hk1
            have hk2' : k' < vs2.length := by simpa using hk2
            exact hshape k' hk1' hk2'

-- ── 11/13, `step_agree_return_force`: split per real `step` branch on the popped value `V`.
-- `VCon`/`VConstr`/`VLam` (not `Force`-able) and the `VBuiltin` `ArgV`-mismatch sub-cases are
-- Error/Error unconditionally; `VBuiltin`'s `More`-arity (re-wrap, `ArgQ` succeeds without firing)
-- is preserving; `VDelay`-pop and `VBuiltin`'s `One`/`ArgQ` (`evalBuiltin` FIRES) are IMPOSSIBLE at
-- the same level -- documented below.

-- Shape predicate for `ForceFrame`'s dispatch: dispatchable shapes are `VDelay` or a `VBuiltin`
-- next expecting a quoted argument (`ArgQ`); everything else falls to the wildcard `Error` arm.
def isForceDispatchable : CekValue → Prop
  | .VDelay _ _ => True
  | .VBuiltin _ _ (.One .ArgQ) => True
  | .VBuiltin _ _ (.More .ArgQ _) => True
  | _ => False

private theorem step_return_force_error_of_not_dispatchable
    (sv : PlutusCore.Default.BuiltinSemanticsVariant) (s : Stack) (V : CekValue)
    (h : ¬ isForceDispatchable V) :
    step sv (State.Return (Frame.ForceFrame :: s) V) = State.Error := by
  cases V with
  | VCon _ => simp [step]
  | VConstr _ _ => simp [step]
  | VLam _ _ _ => simp [step]
  | VDelay _ _ => exact absurd (by simp [isForceDispatchable]) h
  | VBuiltin b vs η =>
      cases η with
      | One ι =>
          cases ι with
          | ArgQ => exact absurd (by simp [isForceDispatchable]) h
          | ArgV => simp [step]
      | More ι η' =>
          cases ι with
          | ArgQ => exact absurd (by simp [isForceDispatchable]) h
          | ArgV => simp [step]

theorem fuelpres_return_force_wildcard (sv : PlutusCore.Default.BuiltinSemanticsVariant)
    (s1 s2 : Stack) (V1 V2 : CekValue) (n : Nat)
    (h1 : ¬ isForceDispatchable V1) (h2 : ¬ isForceDispatchable V2) :
    StateAgree n (step sv (State.Return (Frame.ForceFrame :: s1) V1))
                 (step sv (State.Return (Frame.ForceFrame :: s2) V2)) := by
  rw [step_return_force_error_of_not_dispatchable sv s1 V1 h1,
      step_return_force_error_of_not_dispatchable sv s2 V2 h2]
  simp [StateAgree]

-- `VBuiltin` arity not yet exhausted under `Force`/`ArgQ`: the accumulated list `vs1`/`vs2` is
-- RE-WRAPPED unchanged into `VBuiltin b vs1 η'` -- no fresh value is consed (Force supplies
-- nothing), so unwrapping (`vs1` capped one level below the popped value's own level `n`, forced)
-- and re-wrapping (needing exactly one level below the OUTPUT's level `n`) cancel exactly, same
-- mechanism as `fuelpres_return_right_value_vbuiltin_more_argv` above.
theorem fuelpres_return_force_vbuiltin_more_argq (sv : PlutusCore.Default.BuiltinSemanticsVariant)
    (s1 s2 : Stack) (b : BuiltinFun) (vs1 vs2 : List CekValue) (η' : ExpectedBuiltinArgs) (n : Nat)
    (hs : StackAgree n s1 s2)
    (hlen : vs1.length = vs2.length)
    (hpt : ∀ k (h1 : k < vs1.length) (h2 : k < vs2.length), ValueAgree n (vs1[k]) (vs2[k]))
    (hshape : ∀ k (h1 : k < vs1.length) (h2 : k < vs2.length), fix_ValueAgreeShape (vs1[k]) (vs2[k])) :
    StateAgree n
      (step sv (State.Return (Frame.ForceFrame :: s1)
        (CekValue.VBuiltin b vs1 (.More .ArgQ η'))))
      (step sv (State.Return (Frame.ForceFrame :: s2)
        (CekValue.VBuiltin b vs2 (.More .ArgQ η')))) := by
  simp only [step]
  refine ⟨hs, ?_⟩
  cases n with
  | zero => simp [ValueAgree]
  | succ m =>
      unfold ValueAgree
      refine ⟨rfl, rfl, hlen, ?_, ?_⟩
      · intro k hk1 hk2; exact ValueAgree_mono m _ _ (hpt k hk1 hk2)
      · intro k hk1 hk2; exact hshape k hk1 hk2

-- OBSTRUCTION 3/5 (`VDelay`-pop): `Return (ForceFrame :: s) (VDelay M ρ1) => Eval s ρ1 M`, needing
-- `EnvAgreeOn N (freeVars M) ρ1 ρ2`. The only route is unfolding the already-wrapped `ValueAgree N
-- (VDelay M ρ1) (VDelay M ρ2)` via `ValueAgree`'s `VDelay` clause: wrapping level `N = n+1` gives
-- `EnvAgreeOn n (...) = EnvAgreeOn (N-1) (...)`, one level below `N`, definitionally, with (as in
-- `VLam`-beta above) no route back up via `EnvAgreeOn_mono`. Best achievable: `StateAgree (N-1)`.
--
-- OBSTRUCTION 4/5 (`VBuiltin` arity JUST exhausted, `One`/`ArgQ`, `evalBuiltin` FIRES -- the exact
-- analogue of Obstruction 2/5 above but without even a freshly-applied value to combine): `Return
-- (ForceFrame :: s) (VBuiltin b vs1 (One ArgQ)) => evalBuiltin sv s b vs1`, an escape from the
-- `VBuiltin` wrapper into a brand-new value. `vs1`/`vs2`'s own pointwise agreement is capped at
-- `N - 1` by `ValueAgree`'s `VBuiltin` clause for the SAME reason as Obstruction 2/5 (wrapping
-- level `N` only ever gives elements at `N - 1`), so `bcong_evalBuiltin_agree`'s output is capped
-- at `N - 1` too. Best achievable: `StateAgree (N-1)`.

-- 12/13, `step_agree_return_constr_arg`: BOTH real `step` equations CONSTRUCT (never destructure
-- an already-wrapped value) -- "continue" pushes a fresh `ConstructorArgument` frame holding
-- `V1 :: Vs1` (Frame agreement is fuel-free, needs its elements at the SAME level as the frame
-- itself, exactly what a same-level `hV`/`hVs` already supplies); "finish" builds a fresh
-- `VConstr` from `V1 :: Vs1` (needs elements one level below the NEW value's own wrapping level,
-- again exactly what a same-level hypothesis has slack for) -- preserving throughout, no
-- obstruction.
theorem fuelpres_return_constr_arg (sv : PlutusCore.Default.BuiltinSemanticsVariant)
    (s1 s2 : Stack) (ρ1 ρ2 : Environment) (i : Nat)
    (Vs1 Vs2 : List CekValue) (Ms : List Term) (V1 V2 : CekValue) (n : Nat)
    (hs : StackAgree n s1 s2)
    (hρ : EnvAgreeOn n (freeVarsList Ms) ρ1 ρ2)
    (hVsLen : Vs1.length = Vs2.length)
    (hVs : ∀ k (h1 : k < Vs1.length) (h2 : k < Vs2.length), ValueAgree n (Vs1[k]) (Vs2[k]))
    (hV : ValueAgree n V1 V2) :
    StateAgree n (step sv (State.Return (Frame.ConstructorArgument i Vs1 Ms ρ1 :: s1) V1))
                 (step sv (State.Return (Frame.ConstructorArgument i Vs2 Ms ρ2 :: s2) V2)) := by
  cases Ms with
  | cons M' Ms' =>
      show StateAgree n (State.Eval (Frame.ConstructorArgument i (V1 :: Vs1) Ms' ρ1 :: s1) ρ1 M')
                        (State.Eval (Frame.ConstructorArgument i (V2 :: Vs2) Ms' ρ2 :: s2) ρ2 M')
      have hVsLen' : (V1 :: Vs1).length = (V2 :: Vs2).length := by simpa using hVsLen
      have hVs' : ∀ k (h1 : k < (V1 :: Vs1).length) (h2 : k < (V2 :: Vs2).length),
          ValueAgree n ((V1 :: Vs1)[k]) ((V2 :: Vs2)[k]) := by
        intro k h1 h2
        cases k with
        | zero => exact hV
        | succ k' =>
            have hk1' : k' < Vs1.length := by simpa using h1
            have hk2' : k' < Vs2.length := by simpa using h2
            exact hVs k' hk1' hk2'
      have hflv : freeVarsList (M' :: Ms') = freeVars M' ++ freeVarsList Ms' := by
        simp [freeVarsList]
      have hsub1 : freeVars M' ⊆ freeVarsList (M' :: Ms') := by
        rw [hflv]; exact List.subset_append_left _ _
      have hsub2 : freeVarsList Ms' ⊆ freeVarsList (M' :: Ms') := by
        rw [hflv]; exact List.subset_append_right _ _
      have hρ1 : EnvAgreeOn n (freeVars M') ρ1 ρ2 :=
        envAgreeOn_subset n _ _ ρ1 ρ2 hsub1 hρ
      have hρ2 : EnvAgreeOn n (freeVarsList Ms') ρ1 ρ2 :=
        envAgreeOn_subset n _ _ ρ1 ρ2 hsub2 hρ
      exact ⟨rfl, ⟨⟨rfl, rfl, hVsLen', hVs', hρ2⟩, hs⟩, hρ1⟩
  | nil =>
      show StateAgree n (State.Return s1 (CekValue.VConstr i (List.reverse (V1 :: Vs1))))
                        (State.Return s2 (CekValue.VConstr i (List.reverse (V2 :: Vs2))))
      cases n with
      | zero => exact ⟨hs, by simp [ValueAgree]⟩
      | succ m =>
          refine ⟨hs, ?_⟩
          have hVsLen' : (V1 :: Vs1).length = (V2 :: Vs2).length := by simpa using hVsLen
          have hVs' : ∀ k (h1 : k < (V1 :: Vs1).length) (h2 : k < (V2 :: Vs2).length),
              ValueAgree m ((V1 :: Vs1)[k]) ((V2 :: Vs2)[k]) := by
            intro k h1 h2
            cases k with
            | zero => exact ValueAgree_mono m V1 V2 hV
            | succ k' =>
                have hk1' : k' < Vs1.length := by simpa using h1
                have hk2' : k' < Vs2.length := by simpa using h2
                exact ValueAgree_mono m _ _ (hVs k' hk1' hk2')
          obtain ⟨hlenR, hptR⟩ := retdispatch_reverse_agree m (V1 :: Vs1) (V2 :: Vs2) hVsLen' hVs'
          show ValueAgree (m + 1) (CekValue.VConstr i (List.reverse (V1 :: Vs1)))
                                  (CekValue.VConstr i (List.reverse (V2 :: Vs2)))
          unfold ValueAgree
          exact ⟨rfl, hlenR, hptR⟩

-- ── 13/13, `step_agree_return_case_scrutinee`: split per real `step` branch on the popped
-- scrutinee value `V`. `VDelay`/`VLam`/`VBuiltin` (not `Case`-dispatchable) are Error/Error
-- unconditionally; the 8 `VCon`-constant "caseBuiltin" dispatches are preserving (their spine
-- values, where they push one, are FRESHLY built from the literally-equal decoded constant
-- fields, reflexively agreeing at ANY level, never destructured from an already-wrapped
-- hypothesis); `VConstr`-dispatch is IMPOSSIBLE at the same level -- documented below.

-- Same-level replacements for `retdispatch_case_builtin_no_fold`/`_fold` (which take their own
-- `EnvAgreeOn` hypothesis at `n + 1`, matching the placeholder's uniform convention): identical
-- content, just without the trailing `EnvAgreeOn_mono` downgrade, since here the hypothesis
-- already arrives at the conclusion's own level `n`.
private theorem fuelpres_case_builtin_no_fold (n : Nat) (s1 s2 : Stack) (ρ1 ρ2 : Environment)
    (Ms : List Term) (idx : Nat)
    (hs' : StackAgree n s1 s2) (hρ' : EnvAgreeOn n (freeVarsList Ms) ρ1 ρ2) :
    StateAgree n (match Ms[idx]? with
                  | some mi => State.Eval s1 ρ1 mi
                  | none => State.Error)
                 (match Ms[idx]? with
                  | some mi => State.Eval s2 ρ2 mi
                  | none => State.Error) := by
  cases hmi : Ms[idx]? with
  | none => simp [StateAgree]
  | some mi =>
      have hmiMem : mi ∈ Ms := List.mem_of_getElem? hmi
      have hsubMi : freeVars mi ⊆ freeVarsList Ms :=
        retdispatch_freeVars_subset_freeVarsList mi Ms hmiMem
      exact ⟨rfl, hs', envAgreeOn_subset n (freeVarsList Ms) (freeVars mi) ρ1 ρ2 hsubMi hρ'⟩

private theorem fuelpres_case_builtin_fold (n : Nat) (s1 s2 : Stack) (ρ1 ρ2 : Environment)
    (Ms : List Term) (Vs : List CekValue) (idx : Nat)
    (hs' : StackAgree n s1 s2) (hρ' : EnvAgreeOn n (freeVarsList Ms) ρ1 ρ2)
    (hrefl : ∀ v ∈ Vs, ValueAgree n v v) :
    StateAgree n (match Ms[idx]? with
                  | some mi => State.Eval (step.folding Vs s1) ρ1 mi
                  | none => State.Error)
                 (match Ms[idx]? with
                  | some mi => State.Eval (step.folding Vs s2) ρ2 mi
                  | none => State.Error) := by
  cases hmi : Ms[idx]? with
  | none => simp [StateAgree]
  | some mi =>
      have hmiMem : mi ∈ Ms := List.mem_of_getElem? hmi
      have hsubMi : freeVars mi ⊆ freeVarsList Ms :=
        retdispatch_freeVars_subset_freeVarsList mi Ms hmiMem
      refine ⟨rfl, ?_, envAgreeOn_subset n (freeVarsList Ms) (freeVars mi) ρ1 ρ2 hsubMi hρ'⟩
      have hpt : ∀ k (h1 : k < Vs.length) (h2 : k < Vs.length), ValueAgree n (Vs[k]) (Vs[k]) :=
        fun k h1 _ => hrefl (Vs[k]) (List.getElem_mem h1)
      exact retdispatch_folding_agree n Vs Vs s1 s2 rfl hpt hs'

-- Shape predicate for `CaseScrutinee`'s dispatch: dispatchable shapes are `VConstr` and `VCon`
-- (the latter dispatches further, per-constant, inside `fuelpres_return_case_scrutinee_vcon`
-- below); `VDelay`, `VLam`, and any `VBuiltin` all fall to the wildcard `Error` arm.
def isCaseDispatchable : CekValue → Prop
  | .VConstr _ _ => True
  | .VCon _ => True
  | _ => False

private theorem step_return_case_scrutinee_error_of_not_dispatchable
    (sv : PlutusCore.Default.BuiltinSemanticsVariant) (s : Stack) (ρ : Environment)
    (Ms : List Term) (V : CekValue) (h : ¬ isCaseDispatchable V) :
    step sv (State.Return (Frame.CaseScrutinee Ms ρ :: s) V) = State.Error := by
  cases V with
  | VDelay _ _ => simp [step]
  | VLam _ _ _ => simp [step]
  | VBuiltin _ _ _ => simp [step]
  | VCon _ => exact absurd (by simp [isCaseDispatchable]) h
  | VConstr _ _ => exact absurd (by simp [isCaseDispatchable]) h

theorem fuelpres_return_case_scrutinee_wildcard (sv : PlutusCore.Default.BuiltinSemanticsVariant)
    (s1 s2 : Stack) (ρ1 ρ2 : Environment) (Ms : List Term) (V1 V2 : CekValue) (n : Nat)
    (h1 : ¬ isCaseDispatchable V1) (h2 : ¬ isCaseDispatchable V2) :
    StateAgree n (step sv (State.Return (Frame.CaseScrutinee Ms ρ1 :: s1) V1))
                 (step sv (State.Return (Frame.CaseScrutinee Ms ρ2 :: s2) V2)) := by
  rw [step_return_case_scrutinee_error_of_not_dispatchable sv s1 ρ1 Ms V1 h1,
      step_return_case_scrutinee_error_of_not_dispatchable sv s2 ρ2 Ms V2 h2]
  simp [StateAgree]

theorem fuelpres_return_case_scrutinee_vcon (sv : PlutusCore.Default.BuiltinSemanticsVariant)
    (s1 s2 : Stack) (ρ1 ρ2 : Environment) (Ms : List Term) (c : PlutusCore.UPLC.Term.Const)
    (n : Nat)
    (hs : StackAgree n s1 s2)
    (hρ : EnvAgreeOn n (freeVarsList Ms) ρ1 ρ2) :
    StateAgree n (step sv (State.Return (Frame.CaseScrutinee Ms ρ1 :: s1) (CekValue.VCon c)))
                 (step sv (State.Return (Frame.CaseScrutinee Ms ρ2 :: s2) (CekValue.VCon c))) := by
  cases c with
  | Integer m =>
      simp only [step]
      rcases Bool.eq_false_or_eq_true (0 ≤ m && m.toNat < Ms.length) with heq | heq
      · simp only [heq, if_true]
        exact fuelpres_case_builtin_no_fold n s1 s2 ρ1 ρ2 Ms m.toNat hs hρ
      · simp [heq, StateAgree]
  | Bool b =>
      cases b with
      | false =>
          simp only [step]
          by_cases hlen : Ms.length == 1 || Ms.length == 2
          · simp only [hlen, if_true]
            exact fuelpres_case_builtin_no_fold n s1 s2 ρ1 ρ2 Ms 0 hs hρ
          · simp [hlen, StateAgree]
      | true =>
          simp only [step]
          by_cases hlen : Ms.length == 2
          · simp only [hlen, if_true]
            exact fuelpres_case_builtin_no_fold n s1 s2 ρ1 ρ2 Ms 1 hs hρ
          · simp [hlen, StateAgree]
  | Unit =>
      simp only [step]
      by_cases hlen : Ms.length == 1
      · simp only [hlen, if_true]
        exact fuelpres_case_builtin_no_fold n s1 s2 ρ1 ρ2 Ms 0 hs hρ
      · simp [hlen, StateAgree]
  | Pair p =>
      simp only [step]
      by_cases hlen : Ms.length == 1
      · simp only [hlen, if_true]
        exact fuelpres_case_builtin_fold n s1 s2 ρ1 ρ2 Ms
          [CekValue.VCon p.1, CekValue.VCon p.2] 0
          hs hρ (retdispatch_valueAgree_refl_vcon_pair n p.1 p.2)
      · simp [hlen, StateAgree]
  | PairData p =>
      simp only [step]
      by_cases hlen : Ms.length == 1
      · simp only [hlen, if_true]
        exact fuelpres_case_builtin_fold n s1 s2 ρ1 ρ2 Ms
          [CekValue.VCon (Const.Data p.1), CekValue.VCon (Const.Data p.2)] 0
          hs hρ (retdispatch_valueAgree_refl_vcon_pair n (Const.Data p.1) (Const.Data p.2))
      · simp [hlen, StateAgree]
  | ConstList l =>
      cases l with
      | nil =>
          simp only [step]
          by_cases hlen : Ms.length == 2
          · simp only [hlen, if_true]
            exact fuelpres_case_builtin_no_fold n s1 s2 ρ1 ρ2 Ms 1 hs hρ
          · simp [hlen, StateAgree]
      | cons c cs =>
          simp only [step]
          by_cases hlen : Ms.length == 1 || Ms.length == 2
          · simp only [hlen, if_true]
            exact fuelpres_case_builtin_fold n s1 s2 ρ1 ρ2 Ms
              [CekValue.VCon c, CekValue.VCon (Const.ConstList cs)] 0
              hs hρ (retdispatch_valueAgree_refl_vcon_pair n c (Const.ConstList cs))
          · simp [hlen, StateAgree]
  | ConstDataList l =>
      cases l with
      | nil =>
          simp only [step]
          by_cases hlen : Ms.length == 2
          · simp only [hlen, if_true]
            exact fuelpres_case_builtin_no_fold n s1 s2 ρ1 ρ2 Ms 1 hs hρ
          · simp [hlen, StateAgree]
      | cons c cs =>
          simp only [step]
          by_cases hlen : Ms.length == 1 || Ms.length == 2
          · simp only [hlen, if_true]
            exact fuelpres_case_builtin_fold n s1 s2 ρ1 ρ2 Ms
              [CekValue.VCon (Const.Data c), CekValue.VCon (Const.ConstDataList cs)] 0
              hs hρ (retdispatch_valueAgree_refl_vcon_pair n (Const.Data c) (Const.ConstDataList cs))
          · simp [hlen, StateAgree]
  | ConstPairDataList l =>
      cases l with
      | nil =>
          simp only [step]
          by_cases hlen : Ms.length == 2
          · simp only [hlen, if_true]
            exact fuelpres_case_builtin_no_fold n s1 s2 ρ1 ρ2 Ms 1 hs hρ
          · simp [hlen, StateAgree]
      | cons c cs =>
          simp only [step]
          by_cases hlen : Ms.length == 1 || Ms.length == 2
          · simp only [hlen, if_true]
            exact fuelpres_case_builtin_fold n s1 s2 ρ1 ρ2 Ms
              [CekValue.VCon (Const.PairData c), CekValue.VCon (Const.ConstPairDataList cs)] 0
              hs hρ (retdispatch_valueAgree_refl_vcon_pair n (Const.PairData c)
                (Const.ConstPairDataList cs))
          · simp [hlen, StateAgree]
  | ByteString _ => simp [step, StateAgree]
  | String _ => simp [step, StateAgree]
  | Data _ => simp [step, StateAgree]
  | Bls12_381_G1_element _ => simp [step, StateAgree]
  | Bls12_381_G2_element _ => simp [step, StateAgree]
  | Bls12_381_MlResult _ => simp [step, StateAgree]

-- OBSTRUCTION 5/5 (`VConstr`-scrutinee dispatch): `Return (CaseScrutinee Ms ρ1 :: s) (VConstr i
-- vs1) => Eval (folding vs1 s) ρ1 mi` (via `Ms[i]?`). The elements `vs1`/`vs2` are destructured
-- from the ALREADY-WRAPPED hypothesis `ValueAgree N (VConstr i vs1) (VConstr i vs2)` --
-- `ValueAgree`'s `VConstr` clause (deliberately left with the SAME "one level below wrapping"
-- shape as `VBuiltin`) gives `vs1`/`vs2` agreement at `N - 1` only, forced, for the same reason as
-- every other destructuring case above. Unlike the earlier obstructions, though, the consumer here
-- is NOT `ValueAgree`/`EnvAgreeOn` (which would happily accept `N - 1` for its own next wrapping
-- level) -- it is `StackAgree`/`FrameAgree` (`step.folding` builds `LeftApplicationToValue`
-- frames, and `FrameAgree`'s own clause for that constructor needs `ValueAgree n` at EXACTLY its
-- own outer level `n`, NOT `n - 1`, since `Frame`/`Stack` agreement is -- deliberately -- NOT
-- fuel-indexed at all). So the conclusion `StateAgree N (Eval (folding vs1 s1) ρ1 mi) (...)` needs
-- `StackAgree N (folding vs1 s1) (folding vs2 s2)`, which needs `vs1`/`vs2` agreement at the FULL
-- level `N`, but only `N - 1` is available. Best achievable: `StateAgree (N - 1)`. (This is exactly
-- the reason the same-level companion fails here while the uniform `(n+1) -> n` placeholder
-- succeeds: the uniform convention's extra "+1" of slack is precisely what was masking this cost.)

end PlutusCore.UPLC.CekMachine.EnvLemmas

-- ── CUMULATIVE SCOPE (rounds 1-3), honestly stated -- status only, no difficulty/effort prose
-- (per this project's own "file headers assert only checkable facts" discipline); a stale prior
-- version of this comment (round-1-only) has been replaced here rather than left to drift. ──────
--
-- TRANSLATED AND VERIFIED (this file, zero `sorry` in any actual declaration -- every remaining
-- `sorry` occurrence in the file is inside a comment/string literal, not a proof term -- zero
-- `error`, confirmed by a real `lake build` of both this file's own target and the full
-- `Lemmas.Basic` aggregation target, 80 named declarations total):
--   - Round 1 (old Parts 1-6, 7/7a): `envLookup`, `freeVarsUnderBinder`/`freeVars`/`freeVarsList`,
--     `fix_ValueAgreeShape`, the `ValueAgree`/`EnvAgreeOn` mutual step-indexed relation,
--     `fix_valueAgree_shape`, `beta_envAgreeOn_extend`, `step_var_agree`, `step_const_agree`,
--     `ValueAgree_mono`/`EnvAgreeOn_mono`, `FrameAgree`/`StackAgree`/`StateAgree` plus their own
--     monotonicity, `envAgreeOn_subset`, and 8 of the old Part 7b's 13 `step_agree_*`
--     placeholders (every one not needing the builtin-congruence set piece).
--   - Round 2 (old Part 8, the remaining Part 7b placeholders, Part 7c): the full `bcong_*`
--     builtin-congruence family (9 declarations, all 91 real `BuiltinFun` constructors), the 5
--     remaining `step_agree_return_*` placeholders plus their own `retdispatch_*` helper family
--     (8 declarations) and one bridging private lemma, and `step_agree_invariant` -- THE master
--     one-step CEK agreement theorem, composing all 13 `step_agree_*` cases against the real
--     `step` function.
--   - Round 3 (old Part 9, the `fuelpres_*` fuel-genuineness family): for every one of the 13
--     `step_agree_*` cases, whether stepping preserves the SAME fuel level or genuinely needs to
--     drop one, and exactly when. `beta_ce_*` fixtures (the historical broken-clause
--     counterexample replay, restated against this repo's `VLam String Term Environment`/`[]`
--     shapes) plus `fuelpres_lam_eval` through `fuelpres_return_case_scrutinee_vcon`, plus the
--     `isAppDispatchable`/`isForceDispatchable`/`isCaseDispatchable` shape predicates. Confirmed,
--     not assumed, that this fuel arithmetic is representation-independent: `ValueAgree`'s own
--     recursive shape (round 1's translation, rechecked directly this round) gives every
--     closure-shaped clause -- `VLam`, `VDelay`, `VConstr`, `VBuiltin` -- its captured content
--     exactly one level below the wrapping level, unchanged by the `String`-to-`Nat`/positional-
--     `Environment` migration, so the old file's five genuinely-costly obstructions (`VLam`-beta,
--     `VBuiltin`-arity-just-exhausted under both `RightApplicationOfValue`/`ForceFrame`,
--     `VDelay`-pop, `VConstr`-scrutinee dispatch) carry over identically. All five obstructions
--     are documented in comments (no theorem stated for an impossible claim, matching the old
--     file's own discipline), not left as a `sorry`'d false statement.
--
-- DEFERRED to a later round, not attempted, no placeholder `sorry` left standing for any of it
-- (nothing in this file references it):
--   - Part 10 (`stepAbs_agree`/`stepN_agree_of_stateAgree`/`stepN_add`/`stepN_error_absorbing`/
--     `FrameAgree_refl`/`StackAgree_refl`/`eval_agree`, the multi-step chaining induction lifting
--     `step_agree_invariant` across an arbitrary number of `stepN` iterations). Its own
--     `stepAbs`/`stepN` names collide with Layer 0's already-pushed `stepAbs`/`stepN` in
--     `PlutusCore/UPLC/CekMachine/Lemmas.lean` (fork commit `b7a4bb5`), a real blocker to resolve
--     (reuse Layer 0's definitions, do not redefine) before this Part can be attempted.
--   - The closing `eac_*`/`eval_agree_as_stated_is_false` counterexample section, refuting the
--     FULLY GENERAL fixed-fuel form of `eval_agree` -- a DOCUMENTED NEGATIVE RESULT the old file
--     is careful to preserve, still needs positional-`List CekValue` literal reconstruction, not
--     yet done. A future round must carry the refutation across, not just the positive theorems,
--     or the migrated file would silently drop it.
