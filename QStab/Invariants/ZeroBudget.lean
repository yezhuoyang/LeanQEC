import QStab.Invariant

/-! # Zero budget invariant (Lemma 3)

C = 0 is an absorbing condition: once the budget is exhausted,
only measurement steps and halt/error transitions are possible.
-/

namespace QStab.Invariants

/-- If C = 0 in state s and we step to active s', then C = 0 in s'.
    This follows because all error injections require C > 0,
    and measurement does not change C. -/
theorem zero_budget_preserved {P : QECParams} (s s' : State P)
    (hC : s.C = 0) (hstep : Step P (.active s) (.active s')) :
    s'.C = 0 := sorry

/-- When C = 0, the only non-error transition is measurement or halt. -/
theorem zero_budget_only_measure {P : QECParams} (s : State P)
    (hC : s.C = 0) (s' : ExecState P) (hstep : Step P (.active s) s') :
    (∃ s'', s' = .active s'' ∧ s''.C = 0) ∨
    (∃ s'', s' = .done s'') ∨
    (∃ s'', s' = .error s'') := sorry

/-- Lemma 2 (Error budget consumed): When C = 0, the state can always
    reach σ_done via measurement steps alone. -/
theorem budget_consumed_reaches_done {P : QECParams} (s : State P)
    (hC : s.C = 0) :
    ∃ s_final, MultiStep P (.active s) (.done s_final) := sorry

end QStab.Invariants
