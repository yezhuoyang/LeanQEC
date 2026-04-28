import QStab.Invariant

/-! # Constant error flow invariant (Lemma 5)

For any fixed budget level t and constant error vector E⃗:
  p(σ) = (C < t) ∨ { (C = t) ∧ (Ẽ = E⃗) }

When the budget is at a fixed level, the error flow is constant.

Note: For the two-phase proof, this invariant is instantiated at t=0 from
an intermediate state σ_mid where C=0, not from σ_init.
-/

namespace QStab.Invariants

/-- Preservation of the constant error flow property across all transitions.
    This is the key lemma: the predicate (C < t) ∨ (C = t ∧ Ẽ = E_const)
    is preserved by every active→active transition. -/
theorem constantErrorFlow_preservation {P : QECParams} (t : Nat) (E_const : ErrorVec P.n)
    (s s' : State P)
    (h : s.C < t ∨ (s.C = t ∧ s.E_tilde = E_const))
    (step : Step P (.active s) (.active s')) :
    s'.C < t ∨ (s'.C = t ∧ s'.E_tilde = E_const) := by
  cases step with
  | type0 s i p' hp hC =>
    left; show s.C - 1 < t
    cases h with | inl h => omega | inr h => omega
  | type1 s i p' hp hC =>
    left; show s.C - 1 < t
    cases h with | inl h => omega | inr h => omega
  | type2 s ev he hC =>
    left; show s.C - 1 < t
    cases h with | inl h => omega | inr h => omega
  | type3 s hC =>
    left; show s.C - 1 < t
    cases h with | inl h => omega | inr h => omega
  | measure s nc hN =>
    cases h with
    | inl h => left; rw [measureStep_C]; exact h
    | inr h =>
      obtain ⟨hC, hE⟩ := h
      right; exact ⟨by rw [measureStep_C]; exact hC, by rw [measureStep_E_tilde]; exact hE⟩

/-- Constant error flow as full Invariant when C_budget < t.
    This is the version that holds from σ_init (left disjunct is trivially true). -/
def constantErrorFlowInvariant (P : QECParams) (t : Nat) (E_const : ErrorVec P.n)
    (ht : P.C_budget < t) : Invariant P where
  holds := fun s => s.C < t ∨ (s.C = t ∧ s.E_tilde = E_const)
  holds_init := by left; simp [State.init]; exact ht
  preservation := fun s s' h step => constantErrorFlow_preservation t E_const s s' h step

end QStab.Invariants
