import QStab.Invariant

/-! # Error count invariant

λ_0 + λ_1 + λ_2 + λ_3 = C_budget - C

The total number of injected errors equals the budget spent.
-/

namespace QStab.Invariants

/-- Error count invariant: totalErrors = C_budget - C. -/
def errorCountInvariant (P : QECParams) : Invariant P where
  holds := fun s => s.totalErrors = P.C_budget - s.C
  holds_init := sorry
  preservation := sorry

/-- Corollary: C ≤ C_budget always holds. -/
theorem C_le_budget {P : QECParams} (s : State P)
    (h : (errorCountInvariant P).holds s) : s.C ≤ P.C_budget := sorry

end QStab.Invariants
