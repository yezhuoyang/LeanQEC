import QStab.MultiStep

/-! # Generic invariant framework

A state invariant bundles a predicate on active states with proofs
that it holds initially and is preserved by every single-step transition.
-/

namespace QStab

/-- A state invariant: a predicate that holds initially and is preserved
    by all transitions between active states. -/
structure Invariant (P : QECParams) where
  /-- The predicate on states -/
  holds : State P → Prop
  /-- Holds for the initial state -/
  holds_init : holds (State.init P)
  /-- Preserved by every single step between active states -/
  preservation : ∀ s s' : State P,
    holds s → Step P (.active s) (.active s') → holds s'

namespace Invariant

/-- Helper: an invariant holds for the underlying state of any ExecState
    reachable from init. -/
private theorem holds_of_reachable_aux {P : QECParams} (inv : Invariant P)
    (e : ExecState P)
    (hrun : MultiStep P (.active (State.init P)) e) :
    inv.holds e.state := by
  induction hrun with
  | refl => exact inv.holds_init
  | tail _ step ih =>
    cases step with
    | type0 s i p' hp hC => exact inv.preservation _ _ ih (Step.type0 s i p' hp hC)
    | type1 s i p' hp mf hC => exact inv.preservation _ _ ih (Step.type1 s i p' hp mf hC)
    | type2 s ev he mf hC => exact inv.preservation _ _ ih (Step.type2 s ev he mf hC)
    | type3 s hC => exact inv.preservation _ _ ih (Step.type3 s hC)
    | measure s nc hN => exact inv.preservation _ _ ih (Step.measure s nc hN)
    | halt s _ => exact ih
    | budget_exhausted s _ => exact ih

/-- An invariant holds for any active state reachable from init. -/
theorem holds_of_reachable {P : QECParams} (inv : Invariant P)
    (s : State P)
    (hrun : MultiStep P (.active (State.init P)) (.active s)) :
    inv.holds s :=
  holds_of_reachable_aux inv (.active s) hrun

/-- An invariant holds for the underlying state of any done state reachable from init. -/
theorem holds_at_done {P : QECParams} (inv : Invariant P)
    (s : State P)
    (hrun : Run P (.done s)) :
    inv.holds s :=
  holds_of_reachable_aux inv (.done s) hrun

/-- An invariant holds for the underlying state of any error state reachable from init. -/
theorem holds_at_error {P : QECParams} (inv : Invariant P)
    (s : State P)
    (hrun : Run P (.error s)) :
    inv.holds s :=
  holds_of_reachable_aux inv (.error s) hrun

/-- Conjunction of two invariants is an invariant. -/
def conj {P : QECParams} (inv₁ inv₂ : Invariant P) : Invariant P where
  holds := fun s => inv₁.holds s ∧ inv₂.holds s
  holds_init := ⟨inv₁.holds_init, inv₂.holds_init⟩
  preservation := fun s s' ⟨h1, h2⟩ step =>
    ⟨inv₁.preservation s s' h1 step, inv₂.preservation s s' h2 step⟩

/-- Implication: if inv₁ implies inv₂ on all reachable states, and inv₁ is an invariant,
    then inv₂ holds on all reachable states too. -/
theorem holds_of_implies {P : QECParams} (inv₁ : Invariant P) (p : State P → Prop)
    (h : ∀ s, inv₁.holds s → p s) (s : State P)
    (hrun : MultiStep P (.active (State.init P)) (.active s)) :
    p s :=
  h s (inv₁.holds_of_reachable s hrun)

end Invariant

end QStab
