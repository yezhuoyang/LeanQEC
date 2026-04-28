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
    s'.C = 0 := by
  cases hstep with
  | type0 _ _ _ _ hC' => omega
  | type1 _ _ _ _ hC' => omega
  | type2 _ _ _ hC' => omega
  | type3 _ hC' => omega
  | measure _ nc _ => simp [hC]

/-- When C = 0, the only non-error transition is measurement or halt. -/
theorem zero_budget_only_measure {P : QECParams} (s : State P)
    (hC : s.C = 0) (s' : ExecState P) (hstep : Step P (.active s) s') :
    (∃ s'', s' = .active s'' ∧ s''.C = 0) ∨
    (∃ s'', s' = .done s'') ∨
    (∃ s'', s' = .error s'') := by
  cases hstep with
  | type0 _ _ _ _ hC' => omega
  | type1 _ _ _ _ hC' => omega
  | type2 _ _ _ hC' => omega
  | type3 _ hC' => omega
  | measure s nc hNext =>
    left; exact ⟨measureStep P s nc, rfl, by simp [hC]⟩
  | halt s _ => right; left; exact ⟨s, rfl⟩
  | budget_exhausted s _ => right; right; exact ⟨s, rfl⟩

/-- Lemma 2 (Error budget consumed): When C = 0, the state can always
    reach σ_done via measurement steps alone. -/
theorem budget_consumed_reaches_done {P : QECParams} (s : State P)
    (hC : s.C = 0) :
    ∃ s_final, MultiStep P (.active s) (.done s_final) := by
  -- Induction on remaining coordinates
  suffices h : ∀ (n : Nat) (s : State P), s.C = 0 →
    P.numStab * P.R - s.coord.toLinear ≤ n →
    ∃ s_final, MultiStep P (.active s) (.done s_final)
  from h _ s hC (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro s hC hrem
    exact absurd (QECParams.Coord.toLinear_bound s.coord) (by omega)
  | succ k ih =>
    intro s hC hrem
    by_cases hnext : s.coord.next = none
    · exact ⟨s, step_to_multi (Step.halt s hnext)⟩
    · obtain ⟨nc, hnc⟩ := Option.ne_none_iff_exists'.mp hnext
      have step : Step P (.active s) (.active (measureStep P s nc)) :=
        Step.measure s nc hnc
      have hC' : (measureStep P s nc).C = 0 := by simp [hC]
      have h_lt : s.coord.toLinear < nc.toLinear := QECParams.Coord.next_toLinear_lt hnc
      have h_coord : (measureStep P s nc).coord = nc := by simp
      have h_rem' : P.numStab * P.R - (measureStep P s nc).coord.toLinear ≤ k := by
        rw [h_coord]; omega
      obtain ⟨s_final, h_reach⟩ := ih (measureStep P s nc) hC' h_rem'
      exact ⟨s_final, (step_to_multi step).trans h_reach⟩

end QStab.Invariants
