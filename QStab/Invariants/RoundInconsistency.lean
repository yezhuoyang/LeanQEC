import QStab.Invariant

/-! # Round inconsistency invariant (Theorem 6)

C_budget - C ≥ RI / 2,  equivalently: 2 * (C_budget - C) ≥ RI

One error can cause at most 2 consecutive rounds of inconsistency.
The proof uses induction on rounds and the consistent consecutive round lemma.
-/

namespace QStab.Invariants

/-- Round inconsistency invariant:
    RI ≤ 2 * (C_budget - C). -/
def roundInconsistencyInvariant (P : QECParams) : Invariant P where
  holds := fun s => s.RI ≤ 2 * (P.C_budget - s.C)
  holds_init := sorry
  preservation := sorry

/-- Maximum RI bound: RI < y (round index). -/
def maxRI_Invariant (P : QECParams) : Invariant P where
  holds := fun s => s.RI ≤ s.coord.y.val
  holds_init := sorry
  preservation := sorry

/-- Consistent consecutive round lemma (Lemma 7):
    If no errors injected in two consecutive rounds y=t, y=t+1,
    then F is all-zero at the end of round t+1. -/
theorem consistent_consecutive_rounds {P : QECParams}
    (s : State P)
    -- At end of round t+1 with no errors in rounds t and t+1
    (hC_const : s.C = P.C_budget)  -- simplified: no errors at all
    (hRoundEnd : s.coord.isRoundEnd)
    (hy : 0 < s.coord.y.val) :
    ∀ j : Fin P.numStab, s.F j = false := sorry

end QStab.Invariants
