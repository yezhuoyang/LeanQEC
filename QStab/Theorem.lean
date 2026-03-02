import QStab.Invariants.ErrorCount
import QStab.Invariants.ZeroBudget
import QStab.Invariants.RegisterInit
import QStab.Invariants.ConstantErrorFlow
import QStab.Invariants.SyndromeCorrectness
import QStab.Invariants.ErrorPropagation
import QStab.Invariants.RoundInconsistency

/-! # Main fault-tolerance theorem

Combines all invariants to prove that under a sufficient error budget,
any execution reaching σ_done satisfies the fault-tolerance predicate p_FT:
  p_FT(σ) = (λ_E ≤ d/2) ∧ ∀ s, I[T_s] = Parity(T_s, Ẽ)
-/

namespace QStab

open Invariants

/-- The fault-tolerance predicate p_FT (Eq. 7):
    The error weight is correctable and syndrome is correct. -/
def faultTolerant (P : QECParams) (s : State P) : Prop :=
  2 * s.lam_E ≤ P.d ∧
  ∀ j : Fin P.numStab,
    s.I_syn j = ErrorVec.parity (P.stabilizers j) s.E_tilde

/-- Error count invariant is always true. -/
theorem error_count_holds (P : QECParams) (s : State P)
    (hrun : Run P (.done s)) :
    s.totalErrors = P.C_budget - s.C := sorry

/-- Error propagation bound at done state:
    lam_E ≤ cnt0 + cnt1 + r * cnt2 + cnt3 ≤ r * C_budget. -/
theorem error_propagation_at_done (P : QECParams) (s : State P)
    (hrun : Run P (.done s)) :
    s.lam_E ≤ P.r * P.C_budget := sorry

/-- Round inconsistency bound at done state:
    RI ≤ 2 * C_budget. -/
theorem round_inconsistency_at_done (P : QECParams) (s : State P)
    (hrun : Run P (.done s)) :
    s.RI ≤ 2 * P.C_budget := sorry

/-- Post-selection: if RI ≥ 2 * C_budget in rounds before R,
    then C = 0 in the last round by the round inconsistency invariant. -/
theorem budget_zero_last_round (P : QECParams) (s : State P)
    (hrun : Run P (.done s))
    (hRI : s.RI ≥ 2 * P.C_budget) :
    s.C = 0 := sorry

/-- Syndrome correctness at done state when C = 0. -/
theorem syndrome_correct_at_done (P : QECParams) (s : State P)
    (hrun : Run P (.done s))
    (hC : s.C = 0) :
    ∀ j : Fin P.numStab,
      s.I_syn j = ErrorVec.parity (P.stabilizers j) s.E_tilde := sorry

/-- **Main Theorem: Fault-tolerance under error budget.**

    For an [[n,k,d]] code with back-action bound r and
    error budget C_budget = ⌊(d-1)/(2r)⌋,
    any execution reaching σ_done satisfies p_FT. -/
theorem fault_tolerance (P : QECParams) (s_final : State P)
    (hrun : Run P (.done s_final))
    (hbudget : 2 * P.r * P.C_budget < P.d) :
    faultTolerant P s_final := sorry

/-- Corollary: with C_budget = ⌊(d-1)/(2r)⌋, the error is correctable. -/
theorem correctable_under_threshold (P : QECParams) (s_final : State P)
    (hrun : Run P (.done s_final))
    (hbudget : P.C_budget = (P.d - 1) / (2 * P.r)) :
    2 * s_final.lam_E < P.d := sorry

end QStab
