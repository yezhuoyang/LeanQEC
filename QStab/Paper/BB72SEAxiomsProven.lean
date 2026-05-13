import QStab.Paper.BB72SEChainAttackFull
import QStab.Paper.BB72ReachableEBridge

/-!
# Final SE-side discharge: bb_NZ_SE_no_X_attack_below_6 is a theorem

Composes the SE chain attack discharge (`bb_chain_attack_SE_le_5`)
with the reachableE → chain XOR bridge (`reachableE_xContent_chain_SE`)
and the bb_se_isSuccess bridge (which is identical to bb_isSuccess).
-/

namespace QStab.Paper.BB72ReachableEBridgeSE

open QStab QStab.Paper.BB72Instance QStab.Paper.BB72SEInstance QStab.Paper.BB72BVSE
open QStab.Paper.GenericReachableBridge
open QStab.Paper.BB72ReachableEBridge

/-- bb_se_isSuccess and bb_isSuccess are definitionally equal. -/
theorem bb_se_isSuccess_eq_bb_isSuccess (E : ErrorVec 72) :
    bb_se_isSuccess E = bb_isSuccess E := rfl

/-- If `bb_se_isSuccess (xContent E) = false`, then `bb_se_isSuccess E = false`.
    Reuses the X-side `bb_isSuccess_of_xContent_false`. -/
theorem bb_se_isSuccess_of_xContent_false (E : ErrorVec 72)
    (h : bb_se_isSuccess (xContent E) = false) : bb_se_isSuccess E = false := by
  rw [bb_se_isSuccess_eq_bb_isSuccess] at h ⊢
  exact bb_isSuccess_of_xContent_false E h

open QStab.Paper.BB72SEChainAttackFull in
/-- **Main result**: discharges `bb_NZ_SE_no_X_attack_below_6`. -/
theorem bb_NZ_SE_no_X_attack_below_6_proven :
    ∀ E ∈ reachableE bb_se_allHooks bb_se_code.C_budget, bb_se_isSuccess E = false := by
  intro E hE
  have hbudget : bb_se_code.C_budget = 5 := by rfl
  rw [hbudget] at hE
  obtain ⟨chain, hlen, hxor⟩ := reachableE_xContent_chain_SE 5 E hE
  have h_chain_false : bb_chain_attack_SE chain = false :=
    bb_chain_attack_SE_le_5 chain hlen
  have h_xc_false : bb_se_isSuccess (xContent E) = false := by
    unfold bb_chain_attack_SE at h_chain_false
    rw [hxor] at h_chain_false
    exact h_chain_false
  exact bb_se_isSuccess_of_xContent_false E h_xc_false

end QStab.Paper.BB72ReachableEBridgeSE

namespace QStab.Paper.BB72SEInstance

open QStab QStab.Paper.GenericReachableBridge

/-- **PROVEN** (formerly axiom): BB72 SE per-scheduling X-side check. -/
theorem bb_NZ_SE_no_X_attack_below_6 :
    ∀ E ∈ reachableE bb_se_allHooks bb_se_code.C_budget, bb_se_isSuccess E = false :=
  QStab.Paper.BB72ReachableEBridgeSE.bb_NZ_SE_no_X_attack_below_6_proven

/--
**BB [[72, 12, 6]] with SE scheduling: X-side `d_circ ≥ 6`.**
Same conclusion as `bb_NZ_d_circ_ge_6`, but for the shift-equivariant
scheduling. Now unconditional.
-/
theorem bb_SE_d_circ_ge_6 :
    ∀ (s : State bb_se_code),
      MultiStep bb_se_code (.active (State.init bb_se_code)) (.active s) →
      bb_se_isSuccess s.E_tilde = false := by
  intro s hreach
  exact nonSuccess_op_d_circ_ge_d
    bb_se_code bb_se_allHooks bb_se_hooks_bound bb_se_isSuccess
    bb_NZ_SE_no_X_attack_below_6 s hreach

end QStab.Paper.BB72SEInstance
