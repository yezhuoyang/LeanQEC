import QStab.Paper.GenericReachableBridge
import QStab.Paper.SurfaceD3OperationalIffParam

/-!
# Re-deriving the d=3 X-side theorem from the generic template

Demonstrates that the distance-agnostic
`Paper.GenericReachableBridge.nonSuccess_op_d_circ_ge_d` directly
implies the d=3 X-side headline (already in
`Paper.SurfaceD3OperationalIffParam.nonFailing_op_d_circ_ge_3`),
showing the abstraction captures the d=3 proof.

The same template, with a different (d, allHooks, isSuccess, finite-check)
instantiation, gives the headline for any d. For d ≥ 4, the only
distance-specific work is supplying the finite check
`∀ E ∈ reachableE allHooks (d − 1), isSuccess E = false`
— which scales with d (handled by `native_decide` for small d, by
sampling + structural arguments or external SAT for larger d).

**Zero `sorry`. Standard axioms only.**
-/

namespace QStab.Paper.SurfaceD3FromGeneric

open QStab QStab.Paper.GenericReachableBridge
     QStab.Paper.SurfaceD3OperationalIffParam
     QStab.Paper.SurfaceD3Classification

/-- The d=3 hooks-upper-bound: any back-action element is in `schedAllHooks`. -/
theorem schedCode_hooks_bound (sched : Surface3Sched) :
    hooksUpperBound (schedCode sched) (schedAllHooks sched) := by
  intro stab_idx e he
  exact schedHooksAt_subset sched stab_idx e he

/-- The d=3 reachable set, expressed via the generic `reachableE`. -/
theorem schedReachableE_eq_generic (sched : Surface3Sched) (n : Nat) :
    schedReachableE sched n = reachableE (schedAllHooks sched) n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show schedReachableE sched (k+1) = reachableE (schedAllHooks sched) (k+1)
    unfold schedReachableE reachableE
    rw [ih]

/-- d=3 X-side headline re-derived from the generic template. -/
theorem nonFailing_op_d_circ_ge_3_from_generic :
    ∀ sched : Surface3Sched,
      classOf sched ≠ SchedClass.Failing →
      ∀ (s : State (schedCode sched)),
        MultiStep (schedCode sched)
          (.active (State.init (schedCode sched))) (.active s) →
        isSuccessState s.E_tilde = false := by
  intro sched h_not_failing s hreach
  -- Instantiate the generic theorem.
  apply nonSuccess_op_d_circ_ge_d
    (schedCode sched) (schedAllHooks sched)
    (schedCode_hooks_bound sched) isSuccessState ?_ s hreach
  -- The finite check: no element of reachableE _ 2 is success.
  intro E hE
  -- Convert to the d=3 reachable set, then apply native_decide finite check.
  have hE' : E ∈ schedReachableE sched (schedCode sched).C_budget := by
    rw [schedReachableE_eq_generic]; exact hE
  have h_check := schedReachableE_2_not_success_if_not_failing sched h_not_failing
  rw [List.all_eq_true] at h_check
  have h_budget : (schedCode sched).C_budget = 2 := rfl
  rw [h_budget] at hE'
  have := h_check E hE'
  simpa using this

end QStab.Paper.SurfaceD3FromGeneric
