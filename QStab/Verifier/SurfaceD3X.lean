import QStab.Verifier
import QStab.Paper.SurfaceD3FromGeneric

/-!
# Surface code d=3 X-side fault-tolerance bundle (parametric over scheduling)

Packages the d=3 X-side distance theorem as a `QStabFTBundle`,
parametric over a non-Failing scheduling. Demonstrates the generic
`QStabFTBundle.ofReachInv` constructor on a code that uses the
aligned/perpendicular-spread proof rather than the BB-style
chain-attack discharge.

Joint X+Z is the next iter (uses `SurfaceD3JointXZ`).

## Usage

For any concrete scheduling, instantiate as:
```
def my_bundle : QStabFTBundle :=
  surface_d3_X_bundle sched (by decide)  -- classOf sched ≠ Failing
```
-/

namespace QStab.Verifier.SurfaceD3X

open QStab QStab.Verifier
  QStab.Paper.GenericReachableBridge
  QStab.Paper.SurfaceD3Classification
  QStab.Paper.SurfaceD3OperationalIffParam
  QStab.Paper.SurfaceD3FromGeneric

/-- The finite check for surface d=3, X-side, for any non-Failing scheduling.
    Re-states `schedReachableE_2_not_success_if_not_failing` in the
    `reachableE allHooks C_budget` form that `ofReachInv` expects. -/
private theorem finite_check (sched : Surface3Sched)
    (h_nf : classOf sched ≠ SchedClass.Failing) :
    ∀ E ∈ reachableE (schedAllHooks sched) (schedCode sched).C_budget,
      isSuccessState E = false := by
  intro E hE
  have hE' : E ∈ schedReachableE sched (schedCode sched).C_budget := by
    rw [schedReachableE_eq_generic]; exact hE
  have h_check := schedReachableE_2_not_success_if_not_failing sched h_nf
  rw [List.all_eq_true] at h_check
  have h_budget : (schedCode sched).C_budget = 2 := rfl
  rw [h_budget] at hE'
  have := h_check E hE'
  simpa using this

/-- Surface code d=3 X-side fault-tolerance bundle, parametric over a
    non-Failing scheduling. Failure predicate: `isSuccessState E = true`. -/
def surface_d3_X_bundle (sched : Surface3Sched)
    (h_nf : classOf sched ≠ SchedClass.Failing) : QStabFTBundle :=
  QStabFTBundle.ofReachInv
    (schedCode sched)
    (schedAllHooks sched)
    (schedCode_hooks_bound sched)
    isSuccessState
    (finite_check sched h_nf)

theorem surface_d3_X_verified (sched : Surface3Sched)
    (h_nf : classOf sched ≠ SchedClass.Failing) :
    verifyQStab (surface_d3_X_bundle sched h_nf) = true := rfl

end QStab.Verifier.SurfaceD3X
