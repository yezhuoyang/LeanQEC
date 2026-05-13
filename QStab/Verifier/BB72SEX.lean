import QStab.Verifier
import QStab.Paper.BB72SEAxiomsProven

/-!
# BB[[72, 12, 6]] SE-scheduling X-side fault-tolerance bundle

Packages the BB72 SE-scheduling X-side distance theorem
(`bb_NZ_SE_no_X_attack_below_6`) as a `QStabFTBundle`.

Joint X+Z for SE is NOT yet proven (Z-side SE would need another
~145 min of native_decide compute). This bundle is X-side only,
demonstrating that the verifier framework handles a different
scheduling on the same code.

## Structure
  * `P = bb_se_code` (SE scheduling).
  * `failure E = (bb_se_isSuccess E = true)` — X-side logical failure.
  * `inv` = X-side reachability via the generic `reachInv` framework.
  * `static = true`.
  * `bridge` invokes `bb_NZ_SE_no_X_attack_below_6` after mono-lifting
    the reachability depth to `C_budget`.
-/

namespace QStab.Verifier.BB72SEX

open QStab QStab.Verifier QStab.Paper.GenericReachableBridge
  QStab.Paper.BB72SEInstance

/-- BB72 SE-scheduling X-side fault-tolerance bundle.
    Joint (X+Z) is NOT yet covered for the SE scheduling. -/
def bb72_SE_X_bundle : QStabFTBundle where
  P       := bb_se_code
  failure := fun E => bb_se_isSuccess E = true
  inv     := reachInv bb_se_code bb_se_allHooks bb_se_hooks_bound
  static  := true
  bridge  := fun _ s hinv hfail => by
    -- hinv : s.E_tilde ∈ reachableE bb_se_allHooks (C_budget - s.C) ∧ s.C ≤ C_budget
    obtain ⟨h_in, _h_C⟩ := hinv
    have h_le : bb_se_code.C_budget - s.C ≤ bb_se_code.C_budget := Nat.sub_le _ _
    have h_in_full : s.E_tilde ∈ reachableE bb_se_allHooks bb_se_code.C_budget :=
      reachableE_mono_le bb_se_allHooks h_le _ h_in
    have h_no : bb_se_isSuccess s.E_tilde = false :=
      bb_NZ_SE_no_X_attack_below_6 s.E_tilde h_in_full
    rw [h_no] at hfail
    exact Bool.false_ne_true hfail

theorem bb72_SE_X_verified :
    verifyQStab bb72_SE_X_bundle = true := rfl

/-- SE-scheduling X-side d_circ ≥ 6 derived from the bundle. -/
theorem bb72_SE_X_d_circ_ge_6_via_bundle :
    ∀ s : State bb_se_code,
      MultiStep bb_se_code (.active (State.init bb_se_code)) (.active s) →
      ¬ (bb_se_isSuccess s.E_tilde = true) :=
  verifyQStab_sound bb72_SE_X_bundle bb72_SE_X_verified

end QStab.Verifier.BB72SEX
