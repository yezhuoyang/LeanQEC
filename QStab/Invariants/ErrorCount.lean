import QStab.Invariant

/-! # Error count invariant

λ_0 + λ_1 + λ_2 + λ_3 + C = C_budget

The total number of injected errors plus the remaining budget equals the initial budget.
Equivalently: λ_0 + λ_1 + λ_2 + λ_3 = C_budget - C.
-/

namespace QStab.Invariants

/-- Error count invariant: totalErrors + C = C_budget.
    Formulated with addition to avoid Nat subtraction issues. -/
def errorCountInvariant (P : QECParams) : Invariant P where
  holds := fun s => s.totalErrors + s.C = P.C_budget
  holds_init := by
    simp [State.init, State.totalErrors]
  preservation := by
    intro s s' h step
    cases step with
    | type0 s i p hp hC =>
      simp [State.totalErrors] at h ⊢; omega
    | type1 s i p hp hC =>
      simp [State.totalErrors] at h ⊢; omega
    | type2 s e he hC =>
      simp [State.totalErrors] at h ⊢; omega
    | type3 s hC =>
      simp [State.totalErrors] at h ⊢; omega
    | measure s next_coord hNext =>
      simp [State.totalErrors, measureStep] at h ⊢; omega

/-- Corollary: C ≤ C_budget always holds. -/
theorem C_le_budget {P : QECParams} (s : State P)
    (h : (errorCountInvariant P).holds s) : s.C ≤ P.C_budget := by
  simp [errorCountInvariant, State.totalErrors] at h
  omega

end QStab.Invariants
