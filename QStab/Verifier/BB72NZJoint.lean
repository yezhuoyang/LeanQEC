import QStab.Verifier
import QStab.Paper.BB72ZAxiomsProven

/-!
# BB[[72, 12, 6]] NZ-scheduling joint X+Z fault-tolerance bundle

Packages the BB72 NZ-scheduling joint distance theorem
(`bb_NZ_joint_d_circ_ge_6`) as a `QStabFTBundle`, demonstrating that
the generic `verifyQStab_sound` theorem applies to BB72 without
code-specific re-proving.

## Structure
  * `P = bb_jointCode` (NZ scheduling, joint X+Z back-action sets).
  * `failure E = (bb_isSuccessJoint E = true)` — joint logical failure.
  * `inv = bb_jointBridgeInv` — xPart ∈ X-reachable ∧ zPart ∈ Z-reachable.
  * `static = true` (the SAT-style chain-attack discharges live behind
    `bb_NZ_no_X_attack_below_6` and `bb_NZ_no_Z_attack_below_6`, both
    Lean theorems now).
  * `bridge` invokes `bb_NZ_no_joint_success_of_invariant`.
-/

namespace QStab.Verifier.BB72NZJoint

open QStab QStab.Verifier QStab.Paper.BB72Instance
  QStab.Paper.BB72JointInstance

/-- BB72 NZ-scheduling joint X+Z fault-tolerance bundle. -/
def bb72_NZ_joint_bundle : QStabFTBundle where
  P       := bb_jointCode
  failure := fun E => bb_isSuccessJoint E = true
  inv     := bb_jointBridgeInv
  static  := true
  bridge  := fun _ s hinv hfail => by
    have h := bb_NZ_no_joint_success_of_invariant s hinv
    rw [h] at hfail
    exact Bool.false_ne_true hfail

/-- The bundle passes the generic verifier. -/
theorem bb72_NZ_joint_verified :
    verifyQStab bb72_NZ_joint_bundle = true := rfl

/-- The headline derived from the generic soundness theorem applied
    to the bundle: every reachable state has no joint success. -/
theorem bb72_NZ_joint_d_circ_ge_6_via_bundle :
    ∀ s : State bb_jointCode,
      MultiStep bb_jointCode (.active (State.init bb_jointCode)) (.active s) →
      ¬ (bb_isSuccessJoint s.E_tilde = true) :=
  verifyQStab_sound bb72_NZ_joint_bundle bb72_NZ_joint_verified

end QStab.Verifier.BB72NZJoint
