import QStab.Invariant

/-! # Constant error flow invariant (Lemma 5)

For any fixed budget level t and constant error vector E⃗:
  p(σ) = (C < t) ∨ { (C = t) ∧ (Ẽ = E⃗) }

When the budget is at a fixed level, the error flow is constant.
-/

namespace QStab.Invariants

/-- Constant error flow invariant: when C = t, Ẽ is a fixed vector E_const. -/
def constantErrorFlowInvariant (P : QECParams) (t : Nat) (E_const : ErrorVec P.n)
    : Invariant P where
  holds := fun s =>
    s.C < t ∨ (s.C = t ∧ s.E_tilde = E_const)
  holds_init := sorry
  preservation := sorry

/-- Simplified: when C = 0, the error flow is constant (Lemma 2 + Lemma 5). -/
def constantErrorFlowZero (P : QECParams) (E_const : ErrorVec P.n)
    : Invariant P where
  holds := fun s =>
    s.C = 0 → s.E_tilde = E_const
  holds_init := sorry
  preservation := sorry

end QStab.Invariants
