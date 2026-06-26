-- Quick test to see if simp closes P.C_budget ≤ P.C_budget
example (C_budget : Nat) : C_budget ≤ C_budget := by
  simp
