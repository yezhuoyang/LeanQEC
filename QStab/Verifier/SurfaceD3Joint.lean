import QStab.Verifier
import QStab.Paper.SurfaceD3JointXZ

/-!
# Surface code d=3 joint X+Z fault-tolerance bundle (parametric over scheduling)

Packages the joint X+Z surface-code d=3 distance theorem
(`joint_nonFailing_op_d_circ_ge_3`) as a `QStabFTCertificate`, parametric
over a full scheduling `sched : Surface3SchedFull` with both sides
non-Failing.

Uses `MultiStep`-reachability itself as the dynamic invariant — a
trivially preserved invariant whose `holds s` is the MultiStep
witness needed by the existing parametric theorem. Cleaner than
writing an invariant-form wrapper of the existing 100-line proof.
-/

namespace QStab.Verifier.SurfaceD3Joint

open QStab QStab.Verifier
  QStab.Paper.SurfaceD3Classification
  QStab.Paper.SurfaceD3OperationalIffParam
  QStab.Paper.SurfaceD3OperationalIffParamZ
  QStab.Paper.SurfaceD3JointXZ

/-- MultiStep-reachability as a dynamic invariant. Trivially preserved
    by any step (`MultiStep.tail`). -/
private def reachableInv (sched : Surface3SchedFull) :
    Invariant (schedCodeFull sched) where
  holds s := MultiStep (schedCodeFull sched)
    (.active (State.init (schedCodeFull sched))) (.active s)
  holds_init := Relation.ReflTransGen.refl
  preservation := fun _ _ hms step => Relation.ReflTransGen.tail hms step

/-- Surface code d=3 joint X+Z fault-tolerance bundle, parametric over
    a non-Failing full scheduling. Failure: `isSuccessStateFull E = true`. -/
def surface_d3_joint_certificate (sched : Surface3SchedFull)
    (h_X_nf : classOf sched.1 ≠ SchedClass.Failing)
    (h_Z_nf : classOfZ sched.2 ≠ SchedClass.Failing) : QStabFTCertificate where
  P       := schedCodeFull sched
  failure := fun E => isSuccessStateFull E = true
  inv     := reachableInv sched
  static  := true
  bridge  := fun _ s hms hfail => by
    -- C_budget = 2 for schedCodeFull, so C_budget - s.C ≤ 2 always.
    have hbudget : (schedCodeFull sched).C_budget - s.C ≤ 2 := by
      have : (schedCodeFull sched).C_budget = 2 := rfl
      omega
    have h_no : isSuccessStateFull s.E_tilde = false :=
      joint_nonFailing_op_d_circ_ge_3 sched h_X_nf h_Z_nf s hms hbudget
    rw [h_no] at hfail
    exact Bool.false_ne_true hfail

theorem surface_d3_joint_verified (sched : Surface3SchedFull)
    (h_X_nf : classOf sched.1 ≠ SchedClass.Failing)
    (h_Z_nf : classOfZ sched.2 ≠ SchedClass.Failing) :
    verifyQStab (surface_d3_joint_certificate sched h_X_nf h_Z_nf) = true := rfl

/-- Joint X+Z d_circ ≥ 3 for any non-Failing surface d=3 scheduling,
    derived from the bundle via the generic `verifyQStab_sound`. -/
theorem surface_d3_joint_d_circ_ge_3_via_bundle
    (sched : Surface3SchedFull)
    (h_X_nf : classOf sched.1 ≠ SchedClass.Failing)
    (h_Z_nf : classOfZ sched.2 ≠ SchedClass.Failing) :
    ∀ s : State (schedCodeFull sched),
      MultiStep (schedCodeFull sched)
        (.active (State.init (schedCodeFull sched))) (.active s) →
      ¬ (isSuccessStateFull s.E_tilde = true) :=
  verifyQStab_sound (surface_d3_joint_certificate sched h_X_nf h_Z_nf)
    (surface_d3_joint_verified sched h_X_nf h_Z_nf)

end QStab.Verifier.SurfaceD3Joint
