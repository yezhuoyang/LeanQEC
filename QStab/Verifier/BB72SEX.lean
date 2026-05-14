import QStab.Verifier
import QStab.Paper.BB72SEAxiomsProven

/-!
# BB[[72, 12, 6]] SE-scheduling X-side fault-tolerance bundle

Packages the BB72 SE-scheduling X-side distance theorem
(`bb_NZ_SE_no_X_attack_below_6`) as a `QStabFTCertificate`.

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
    Joint (X+Z) is NOT yet covered for the SE scheduling.
    Uses the generic `QStabFTCertificate.ofReachInv` constructor — the
    chain-attack discharge lives entirely inside the static
    finite-check witness `bb_NZ_SE_no_X_attack_below_6`. -/
def bb72_SE_X_certificate : QStabFTCertificate :=
  QStabFTCertificate.ofReachInv
    bb_se_code
    bb_se_allHooks
    bb_se_hooks_bound
    bb_se_isSuccess
    bb_NZ_SE_no_X_attack_below_6

theorem bb72_SE_X_verified :
    verifyQStab bb72_SE_X_certificate = true := rfl

/-- SE-scheduling X-side d_circ ≥ 6 derived from the bundle. -/
theorem bb72_SE_X_d_circ_ge_6_via_bundle :
    ∀ s : State bb_se_code,
      MultiStep bb_se_code (.active (State.init bb_se_code)) (.active s) →
      ¬ (bb_se_isSuccess s.E_tilde = true) :=
  verifyQStab_sound bb72_SE_X_certificate bb72_SE_X_verified

end QStab.Verifier.BB72SEX
