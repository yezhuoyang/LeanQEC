import QStab.Invariant

/-! # Error propagation invariant (Theorem 5)

λ_0 + λ_1 + r·λ_2 + λ_3 ≥ λ_E

The weighted error count bounds the total error weight.
This relies on the back-action weight bound: |e| ≤ r for all e ∈ B¹(T_s).
-/

namespace QStab.Invariants

/-- Error propagation invariant:
    λ_E ≤ λ_0 + λ_1 + r * λ_2 + λ_3. -/
def errorPropagationInvariant (P : QECParams) : Invariant P where
  holds := fun s => s.lam_E ≤ s.cnt0 + s.cnt1 + P.r * s.cnt2 + s.cnt3
  holds_init := sorry
  preservation := sorry

end QStab.Invariants
