import QStab.Paper.BB72ReachableEBridgeZ

/-!
# BB72 NZ Z-side static-DEM check: small-k discharged in Lean

Mirror of `BB72ChainCheck` for the Z-side. Discharges k=1 and k=2 by
direct `native_decide`. Larger k will use the BV/syndrome bridge.
-/

namespace QStab.Paper.BB72ChainCheckZ

open QStab QStab.Paper.BB72JointInstance QStab.Paper.BB72ReachableEBridgeZ

/-- **No single Z-mech is a successful Z-side attack.** Verified by
    `native_decide` over 252 cases. Unconditional. -/
theorem bb_chain_1_no_attack_Z :
    ∀ i : Fin 252, bb_isSuccessZside (bb_zMech i) = false := by
  native_decide

/-- **No 2-mech Z-chain is a successful Z-side attack.** Verified by
    `native_decide` over 252² = 63,504 ordered pairs. Unconditional. -/
theorem bb_chain_2_no_attack_Z :
    ∀ i j : Fin 252,
      bb_isSuccessZside (ErrorVec.mul (bb_zMech i) (bb_zMech j)) = false := by
  native_decide

end QStab.Paper.BB72ChainCheckZ
