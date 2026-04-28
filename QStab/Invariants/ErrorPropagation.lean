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
  holds_init := by
    simp [State.init]
  preservation := by
    intro s s' h step
    cases step with
    | type0 s i p' hp hC =>
      show s.lam_E + 1 ≤ (s.cnt0 + 1) + s.cnt1 + P.r * s.cnt2 + s.cnt3
      omega
    | type1 s i p' hp hC =>
      show s.lam_E + 1 ≤ s.cnt0 + (s.cnt1 + 1) + P.r * s.cnt2 + s.cnt3
      omega
    | type2 s ev he hC =>
      have hwe := backAction_weight_bound P s.coord.x ev he
      show s.lam_E + ErrorVec.weight ev ≤ s.cnt0 + s.cnt1 + P.r * (s.cnt2 + 1) + s.cnt3
      have : P.r * (s.cnt2 + 1) = P.r * s.cnt2 + P.r := Nat.mul_succ P.r s.cnt2
      omega
    | type3 s hC =>
      show s.lam_E ≤ s.cnt0 + s.cnt1 + P.r * s.cnt2 + (s.cnt3 + 1)
      omega
    | measure s nc hN =>
      simp at h ⊢; exact h

end QStab.Invariants
