namespace PlutusCore.UPLC.CekMachine

/-! ## General any-length round induction

A reusable induction principle for proofs that walk a list one element at a time, where each
step either reaches the goal directly or hands off to a strictly shorter list via one "round".
This shape recurs across CEK-machine termination, safety, and correctness proofs, any argument
of the form "process one list element per macro-step, until either done or one element shorter",
so it is extracted here once as a general combinator instead of being re-derived by hand at each
call site.

Fully polymorphic: the destination space `σ`, the accompanying payload `α`, and the list's
element type `β` are all abstract, and the only property of "reachability" used is a
caller-supplied transitive relation `Reach`. This file has zero PlutusCore/CEK-specific content
in its statement or proof, it is colocated here because its real-world use so far is
CEK-machine proofs, not because it depends on anything CEK-specific. -/

universe u v w

/-- General any-length round-induction scaffold. `σ` is the ambient space of destinations a
    round can land in. `α` is whatever payload accompanies the list being inducted over (an
    environment, a pair of environments, a second list, ...). `β` is the list's own element
    type. `E l x` is the starting destination for payload `x` with `l` remaining. `I l x` is the
    invariant every real instance needs threaded, available to both leaves, and the "continue"
    branch must re-establish it at the new payload. `Reach` is a caller-supplied transitive
    relation on `σ`, the only property of "reachability" this lemma ever uses. `Q l x y` is
    whatever property the round's ultimate destination `y` must satisfy, free to depend on
    `l`/`x` too (needed when the target itself is a function of what remains, e.g. a
    recursively-defined spec).

    The "continue" branch of `hround` owes exactly one extra obligation beyond reaching the next
    payload: transport, `∀ y, Q t x' y → Q (h :: t) x y`, whatever the shorter round's own
    witness proves about `y` must already imply what the current round needs, since `y` is the
    same final destination either way. For a payload/list-independent `Q`, transport is
    definitionally `fun _ h => h`. -/
theorem anyLength_roundInduction {σ : Type u} {α : Type v} {β : Type w}
    (Reach : σ → σ → Prop)
    (hReach_trans : ∀ a b c, Reach a b → Reach b c → Reach a c)
    (E : List β → α → σ) (I : List β → α → Prop) (Q : List β → α → σ → Prop)
    (hnil : ∀ x, I [] x → ∃ y, Reach (E [] x) y ∧ Q [] x y)
    (hround : ∀ h t x, I (h :: t) x →
      (∃ y, Reach (E (h :: t) x) y ∧ Q (h :: t) x y) ∨
      (∃ x', I t x' ∧ Reach (E (h :: t) x) (E t x') ∧
        ∀ y, Q t x' y → Q (h :: t) x y)) :
    ∀ (l : List β) (x : α), I l x → ∃ y, Reach (E l x) y ∧ Q l x y := by
  intro l
  induction l with
  | nil => intro x hx; exact hnil x hx
  | cons h t ih =>
      intro x hx
      rcases hround h t x hx with ⟨y, hRy, hQy⟩ | ⟨x', hIx', hR, htrans⟩
      · exact ⟨y, hRy, hQy⟩
      · obtain ⟨y, hRy', hQy'⟩ := ih x' hIx'
        exact ⟨y, hReach_trans _ _ _ hR hRy', htrans y hQy'⟩

end PlutusCore.UPLC.CekMachine
