import QStab.QHL.Verify.SurfaceRowsCommuteDefined.BulkBoundaryCombos

/-!
# Rows-commute definedness — NonAdjacentPins

The bulk–bulk non-adjacent closer and the 8 non-adjacent pins (each `comm_deriv_wf`).
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

set_option maxHeartbeats 1600000

/-! ## Non-adjacent (non-overlap) closer: BULK-BULK NON-ADJ (→ pairCommutePointwise_WF) -/

theorem bbnaPinAt_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)}
    {hW : SFormula.Deriv Δ (bbnaPinF D).weaken}
    {hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken)}
    {hBulkK1 : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b true))}
    {hBulkK2 : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b true))}
    {hKindK1 : SFormula.Deriv Δ (.eqBool (SC.closed (baseKindGuardTA (dP3 D) k1P3)) (SC.b false))}
    {hKindK2 : SFormula.Deriv Δ (.eqBool (SC.closed (baseKindGuardTA (dP3 D) k2P3)) (SC.b true))}
    {hNonAdj : SFormula.Deriv Δ (.eqBool (SC.closed (bbnaNonAdjTA D)) (SC.b true))}
    {hBandK1 : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true))}
    {hBandK2 : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))}
    {rho : Env 3} {E : PartialStabilizer}
    (wW : DerivWF hW Surface.code.body (D.distance + 2) rho E)
    (wq : DerivWF hq Surface.code.body (D.distance + 2) rho E)
    (wBulkK1 : DerivWF hBulkK1 Surface.code.body (D.distance + 2) rho E)
    (wBulkK2 : DerivWF hBulkK2 Surface.code.body (D.distance + 2) rho E)
    (wKindK1 : DerivWF hKindK1 Surface.code.body (D.distance + 2) rho E)
    (wKindK2 : DerivWF hKindK2 Surface.code.body (D.distance + 2) rho E)
    (wNonAdj : DerivWF hNonAdj Surface.code.body (D.distance + 2) rho E)
    (wBandK1 : DerivWF hBandK1 Surface.code.body (D.distance + 2) rho E)
    (wBandK2 : DerivWF hBandK2 Surface.code.body (D.distance + 2) rho E) :
    DerivWF (bbnaPinAt D hW hq hBulkK1 hBulkK2 hKindK1 hKindK2 hNonAdj hBandK1 hBandK2)
      Surface.code.body (D.distance + 2) rho E := by
  unfold bbnaPinAt
  comm_deriv_wf

theorem pairCommuteBulkBulkNonAdj_WF (D : OddSurfaceDistance) {Γ : List (SFormula 2)}
    {hEntryA : SFormula.Deriv Γ (entryAQuant D)} {hEntryB : SFormula.Deriv Γ (entryBQuant D)}
    {hk1X : SFormula.Deriv Γ (k1IsX D true)} {hExcl1 : SFormula.Deriv Γ (typeExclF D k1P)}
    {hBulkK1 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true))}
    {hKindK1 : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k1P)) (SC.b false))}
    {hBulkK2 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true))}
    {hKindK2 : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k2P)) (SC.b true))}
    {hNonAdj : SFormula.Deriv Γ (.eqBool (SC.closed (bbnaNonAdjTA2 D)) (SC.b true))}
    {hPin : SFormula.Deriv Γ (bbnaPinF D)}
    {rho : Env 2} {E : PartialStabilizer}
    (wEntryA : DerivWF hEntryA Surface.code.body (D.distance + 2) rho E)
    (wEntryB : DerivWF hEntryB Surface.code.body (D.distance + 2) rho E)
    (wHk1X : DerivWF hk1X Surface.code.body (D.distance + 2) rho E)
    (wHExcl1 : DerivWF hExcl1 Surface.code.body (D.distance + 2) rho E)
    (wHBulkK1 : DerivWF hBulkK1 Surface.code.body (D.distance + 2) rho E)
    (wHKindK1 : DerivWF hKindK1 Surface.code.body (D.distance + 2) rho E)
    (wHBulkK2 : DerivWF hBulkK2 Surface.code.body (D.distance + 2) rho E)
    (wHKindK2 : DerivWF hKindK2 Surface.code.body (D.distance + 2) rho E)
    (wHNonAdj : DerivWF hNonAdj Surface.code.body (D.distance + 2) rho E)
    (wHPin : DerivWF hPin Surface.code.body (D.distance + 2) rho E)
    (hCtx : SFormula.ContextHolds Surface.code.body (D.distance + 2) rho E Γ) :
    DerivWF (pairCommuteBulkBulkNonAdj D hEntryA hEntryB hk1X hExcl1 hBulkK1 hKindK1 hBulkK2
        hKindK2 hNonAdj hPin) Surface.code.body (D.distance + 2) rho E := by
  unfold pairCommuteBulkBulkNonAdj
  refine pairCommutePointwise_WF D wEntryA wEntryB ?wAntiXZ ?wAntiZX hCtx
  case wAntiXZ =>
    intro x Δ' lift liftWF hLA wLA hLB wLB
    have wBulkK1Δ := liftWF (cw1_WF (derivWF_weakenFresh wHBulkK1))
    have wBulkK2Δ := liftWF (cw1_WF (derivWF_weakenFresh wHBulkK2))
    have wKindK1Δ := liftWF (cw1_WF (derivWF_weakenFresh wHKindK1))
    have wKindK2Δ := liftWF (cw1_WF (derivWF_weakenFresh wHKindK2))
    have wNonAdjΔ := liftWF (cw1_WF (derivWF_weakenFresh wHNonAdj))
    have wPinΔ := liftWF (cw1_WF (derivWF_weakenFresh wHPin))
    have wBandK1 := bhBandK1FromX_WF D wBulkK1Δ wLA
    have wBandK2 := bhBandK2FromZ_WF D wBulkK2Δ wLB
    exact derivWF_botElim (bbnaPinAt_WF D wPinΔ (liftWF (derivWF_hyp _))
      wBulkK1Δ wBulkK2Δ wKindK1Δ wKindK2Δ wNonAdjΔ wBandK1 wBandK2)
  case wAntiZX =>
    intro x Δ' lift liftWF hLA wLA hLB wLB
    have wk1Xd := liftWF (cw1_WF (derivWF_weakenFresh wHk1X))
    have wExcl1d := liftWF (cw1_WF (derivWF_weakenFresh wHExcl1))
    have wxnbz := derivWF_andElimLeft' wExcl1d
    have wxnrz := derivWF_andElimLeft' (derivWF_andElimRight' wExcl1d)
    have wxnlz := derivWF_andElimLeft' (derivWF_andElimRight' (derivWF_andElimRight' wExcl1d))
    refine withLeafG_WF D (.var _) _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro Δ'' lift2 liftWF2 hI wI
      exact leafNotPandZ_WF D (.var _) Pauli.I rfl wI (liftWF2 wLA)
    · intro Δ'' lift2 liftWF2 hL wL hb wb hk wk
      exact eqBoolContra_WF _ wk (derivWF_mp (derivWF_mp (liftWF2 wxnbz) (liftWF2 wk1Xd)) wb)
    · intro Δ'' lift2 liftWF2 hX wX hb wb hk wk
      exact leafNotPandZ_WF D (.var _) Pauli.X rfl wX (liftWF2 wLA)
    · intro Δ'' lift2 liftWF2 hX wX hb wb ht wt
      exact leafNotPandZ_WF D (.var _) Pauli.X rfl wX (liftWF2 wLA)
    · intro Δ'' lift2 liftWF2 hL wL hb wb ht wt hr wr
      exact eqBoolContra_WF _ wr
        (derivWF_mp (derivWF_mp (derivWF_mp (liftWF2 wxnrz) (liftWF2 wk1Xd)) wb) wt)
    · intro Δ'' lift2 liftWF2 hL wL hb wb ht wt hr wr hlc wlc
      exact eqBoolContra_WF _ wlc
        (derivWF_mp (derivWF_mp (derivWF_mp (derivWF_mp (liftWF2 wxnlz) (liftWF2 wk1Xd)) wb) wt) wr)
    · intro Δ'' lift2 liftWF2 hX wX hb wb ht wt hr wr hlc wlc
      exact leafNotPandZ_WF D (.var _) Pauli.X rfl wX (liftWF2 wLA)

/-! ## The remaining 8 non-adjacent pins (each `comm_deriv_wf`) -/

theorem brnaPinAt_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)}
    {hW : SFormula.Deriv Δ (brnaPinF D).weaken}
    {hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken)}
    {hBulkK1 : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b true))}
    {hKindK1 : SFormula.Deriv Δ (.eqBool (SC.closed (baseKindGuardTA (dP3 D) k1P3)) (SC.b false))}
    {hBulkF : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b false))}
    {hTopF : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA (dP3 D) k2P3)) (SC.b false))}
    {hRightC : SFormula.Deriv Δ (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k2P3)) (SC.b true))}
    {hBandK1 : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true))}
    {hRightB : SFormula.Deriv Δ (.eqBool (SC.closed (rightBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))}
    {hNonAdj : SFormula.Deriv Δ (.eqBool (SC.closed (brnaNonAdjTA D)) (SC.b true))}
    {rho : Env 3} {E : PartialStabilizer}
    (wW : DerivWF hW Surface.code.body (D.distance + 2) rho E)
    (wq : DerivWF hq Surface.code.body (D.distance + 2) rho E)
    (wBulkK1 : DerivWF hBulkK1 Surface.code.body (D.distance + 2) rho E)
    (wKindK1 : DerivWF hKindK1 Surface.code.body (D.distance + 2) rho E)
    (wBulkF : DerivWF hBulkF Surface.code.body (D.distance + 2) rho E)
    (wTopF : DerivWF hTopF Surface.code.body (D.distance + 2) rho E)
    (wRightC : DerivWF hRightC Surface.code.body (D.distance + 2) rho E)
    (wBandK1 : DerivWF hBandK1 Surface.code.body (D.distance + 2) rho E)
    (wRightB : DerivWF hRightB Surface.code.body (D.distance + 2) rho E)
    (wNonAdj : DerivWF hNonAdj Surface.code.body (D.distance + 2) rho E) :
    DerivWF (brnaPinAt D hW hq hBulkK1 hKindK1 hBulkF hTopF hRightC hBandK1 hRightB hNonAdj)
      Surface.code.body (D.distance + 2) rho E := by
  unfold brnaPinAt
  comm_deriv_wf

theorem blnaPinAt_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)}
    {hW : SFormula.Deriv Δ (blnaPinF D).weaken}
    {hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken)}
    {hBulkK1 : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b true))}
    {hKindK1 : SFormula.Deriv Δ (.eqBool (SC.closed (baseKindGuardTA (dP3 D) k1P3)) (SC.b false))}
    {hBulkF : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b false))}
    {hTopF : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA (dP3 D) k2P3)) (SC.b false))}
    {hRightF : SFormula.Deriv Δ (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k2P3)) (SC.b false))}
    {hLeftC : SFormula.Deriv Δ (.eqBool (SC.closed (leftClassGuardTA (dP3 D) k2P3)) (SC.b true))}
    {hBandK1 : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true))}
    {hLeftB : SFormula.Deriv Δ (.eqBool (SC.closed (leftBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))}
    {hNonAdj : SFormula.Deriv Δ (.eqBool (SC.closed (blnaNonAdjTA D)) (SC.b true))}
    {rho : Env 3} {E : PartialStabilizer}
    (wW : DerivWF hW Surface.code.body (D.distance + 2) rho E)
    (wq : DerivWF hq Surface.code.body (D.distance + 2) rho E)
    (wBulkK1 : DerivWF hBulkK1 Surface.code.body (D.distance + 2) rho E)
    (wKindK1 : DerivWF hKindK1 Surface.code.body (D.distance + 2) rho E)
    (wBulkF : DerivWF hBulkF Surface.code.body (D.distance + 2) rho E)
    (wTopF : DerivWF hTopF Surface.code.body (D.distance + 2) rho E)
    (wRightF : DerivWF hRightF Surface.code.body (D.distance + 2) rho E)
    (wLeftC : DerivWF hLeftC Surface.code.body (D.distance + 2) rho E)
    (wBandK1 : DerivWF hBandK1 Surface.code.body (D.distance + 2) rho E)
    (wLeftB : DerivWF hLeftB Surface.code.body (D.distance + 2) rho E)
    (wNonAdj : DerivWF hNonAdj Surface.code.body (D.distance + 2) rho E) :
    DerivWF (blnaPinAt D hW hq hBulkK1 hKindK1 hBulkF hTopF hRightF hLeftC hBandK1 hLeftB hNonAdj)
      Surface.code.body (D.distance + 2) rho E := by
  unfold blnaPinAt
  comm_deriv_wf

theorem tbnaPinAt_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)}
    {hW : SFormula.Deriv Δ (tbnaPinF D).weaken}
    {hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken)}
    {hBulkF : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b false))}
    {hTopC : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA (dP3 D) k1P3)) (SC.b true))}
    {hBulkK2 : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b true))}
    {hKindK2 : SFormula.Deriv Δ (.eqBool (SC.closed (baseKindGuardTA (dP3 D) k2P3)) (SC.b true))}
    {hTopB : SFormula.Deriv Δ (.eqBool (SC.closed (topBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true))}
    {hBulkB : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))}
    {hNonAdj : SFormula.Deriv Δ (.eqBool (SC.closed (tbnaNonAdjTA D)) (SC.b true))}
    {rho : Env 3} {E : PartialStabilizer}
    (wW : DerivWF hW Surface.code.body (D.distance + 2) rho E)
    (wq : DerivWF hq Surface.code.body (D.distance + 2) rho E)
    (wBulkF : DerivWF hBulkF Surface.code.body (D.distance + 2) rho E)
    (wTopC : DerivWF hTopC Surface.code.body (D.distance + 2) rho E)
    (wBulkK2 : DerivWF hBulkK2 Surface.code.body (D.distance + 2) rho E)
    (wKindK2 : DerivWF hKindK2 Surface.code.body (D.distance + 2) rho E)
    (wTopB : DerivWF hTopB Surface.code.body (D.distance + 2) rho E)
    (wBulkB : DerivWF hBulkB Surface.code.body (D.distance + 2) rho E)
    (wNonAdj : DerivWF hNonAdj Surface.code.body (D.distance + 2) rho E) :
    DerivWF (tbnaPinAt D hW hq hBulkF hTopC hBulkK2 hKindK2 hTopB hBulkB hNonAdj)
      Surface.code.body (D.distance + 2) rho E := by
  unfold tbnaPinAt
  comm_deriv_wf

theorem btbnaPinAt_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)}
    {hW : SFormula.Deriv Δ (btbnaPinF D).weaken}
    {hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken)}
    {hBulkF : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b false))}
    {hTopF : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA (dP3 D) k1P3)) (SC.b false))}
    {hRightF : SFormula.Deriv Δ (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k1P3)) (SC.b false))}
    {hLeftF : SFormula.Deriv Δ (.eqBool (SC.closed (leftClassGuardTA (dP3 D) k1P3)) (SC.b false))}
    {hBulkK2 : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b true))}
    {hKindK2 : SFormula.Deriv Δ (.eqBool (SC.closed (baseKindGuardTA (dP3 D) k2P3)) (SC.b true))}
    {hBotB : SFormula.Deriv Δ (.eqBool (SC.closed (bottomBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true))}
    {hBulkB : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))}
    {hNonAdj : SFormula.Deriv Δ (.eqBool (SC.closed (btbnaNonAdjTA D)) (SC.b true))}
    {rho : Env 3} {E : PartialStabilizer}
    (wW : DerivWF hW Surface.code.body (D.distance + 2) rho E)
    (wq : DerivWF hq Surface.code.body (D.distance + 2) rho E)
    (wBulkF : DerivWF hBulkF Surface.code.body (D.distance + 2) rho E)
    (wTopF : DerivWF hTopF Surface.code.body (D.distance + 2) rho E)
    (wRightF : DerivWF hRightF Surface.code.body (D.distance + 2) rho E)
    (wLeftF : DerivWF hLeftF Surface.code.body (D.distance + 2) rho E)
    (wBulkK2 : DerivWF hBulkK2 Surface.code.body (D.distance + 2) rho E)
    (wKindK2 : DerivWF hKindK2 Surface.code.body (D.distance + 2) rho E)
    (wBotB : DerivWF hBotB Surface.code.body (D.distance + 2) rho E)
    (wBulkB : DerivWF hBulkB Surface.code.body (D.distance + 2) rho E)
    (wNonAdj : DerivWF hNonAdj Surface.code.body (D.distance + 2) rho E) :
    DerivWF (btbnaPinAt D hW hq hBulkF hTopF hRightF hLeftF hBulkK2 hKindK2 hBotB hBulkB hNonAdj)
      Surface.code.body (D.distance + 2) rho E := by
  unfold btbnaPinAt
  comm_deriv_wf

theorem trnaPinAt_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)}
    {hW : SFormula.Deriv Δ (trnaPinF D).weaken}
    {hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken)}
    {hBulkFk1 : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b false))}
    {hTopCk1 : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA (dP3 D) k1P3)) (SC.b true))}
    {hBulkFk2 : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b false))}
    {hTopFk2 : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA (dP3 D) k2P3)) (SC.b false))}
    {hRightCk2 : SFormula.Deriv Δ (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k2P3)) (SC.b true))}
    {hTopB : SFormula.Deriv Δ (.eqBool (SC.closed (topBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true))}
    {hRightB : SFormula.Deriv Δ (.eqBool (SC.closed (rightBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))}
    {rho : Env 3} {E : PartialStabilizer}
    (wW : DerivWF hW Surface.code.body (D.distance + 2) rho E)
    (wq : DerivWF hq Surface.code.body (D.distance + 2) rho E)
    (wBulkFk1 : DerivWF hBulkFk1 Surface.code.body (D.distance + 2) rho E)
    (wTopCk1 : DerivWF hTopCk1 Surface.code.body (D.distance + 2) rho E)
    (wBulkFk2 : DerivWF hBulkFk2 Surface.code.body (D.distance + 2) rho E)
    (wTopFk2 : DerivWF hTopFk2 Surface.code.body (D.distance + 2) rho E)
    (wRightCk2 : DerivWF hRightCk2 Surface.code.body (D.distance + 2) rho E)
    (wTopB : DerivWF hTopB Surface.code.body (D.distance + 2) rho E)
    (wRightB : DerivWF hRightB Surface.code.body (D.distance + 2) rho E) :
    DerivWF (trnaPinAt D hW hq hBulkFk1 hTopCk1 hBulkFk2 hTopFk2 hRightCk2 hTopB hRightB)
      Surface.code.body (D.distance + 2) rho E := by
  unfold trnaPinAt
  comm_deriv_wf

theorem tlnaPinAt_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)}
    {hW : SFormula.Deriv Δ (tlnaPinF D).weaken}
    {hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken)}
    {hBulkFk1 : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b false))}
    {hTopCk1 : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA (dP3 D) k1P3)) (SC.b true))}
    {hBulkFk2 : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b false))}
    {hTopFk2 : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA (dP3 D) k2P3)) (SC.b false))}
    {hRightFk2 : SFormula.Deriv Δ (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k2P3)) (SC.b false))}
    {hLeftCk2 : SFormula.Deriv Δ (.eqBool (SC.closed (leftClassGuardTA (dP3 D) k2P3)) (SC.b true))}
    {hTopB : SFormula.Deriv Δ (.eqBool (SC.closed (topBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true))}
    {hLeftB : SFormula.Deriv Δ (.eqBool (SC.closed (leftBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))}
    {rho : Env 3} {E : PartialStabilizer}
    (wW : DerivWF hW Surface.code.body (D.distance + 2) rho E)
    (wq : DerivWF hq Surface.code.body (D.distance + 2) rho E)
    (wBulkFk1 : DerivWF hBulkFk1 Surface.code.body (D.distance + 2) rho E)
    (wTopCk1 : DerivWF hTopCk1 Surface.code.body (D.distance + 2) rho E)
    (wBulkFk2 : DerivWF hBulkFk2 Surface.code.body (D.distance + 2) rho E)
    (wTopFk2 : DerivWF hTopFk2 Surface.code.body (D.distance + 2) rho E)
    (wRightFk2 : DerivWF hRightFk2 Surface.code.body (D.distance + 2) rho E)
    (wLeftCk2 : DerivWF hLeftCk2 Surface.code.body (D.distance + 2) rho E)
    (wTopB : DerivWF hTopB Surface.code.body (D.distance + 2) rho E)
    (wLeftB : DerivWF hLeftB Surface.code.body (D.distance + 2) rho E) :
    DerivWF (tlnaPinAt D hW hq hBulkFk1 hTopCk1 hBulkFk2 hTopFk2 hRightFk2 hLeftCk2 hTopB hLeftB)
      Surface.code.body (D.distance + 2) rho E := by
  unfold tlnaPinAt
  comm_deriv_wf

theorem brbnaPinAt_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)}
    {hW : SFormula.Deriv Δ (brbnaPinF D).weaken}
    {hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken)}
    {hBulkFk1 : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b false))}
    {hTopFk1 : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA (dP3 D) k1P3)) (SC.b false))}
    {hRightFk1 : SFormula.Deriv Δ (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k1P3)) (SC.b false))}
    {hLeftFk1 : SFormula.Deriv Δ (.eqBool (SC.closed (leftClassGuardTA (dP3 D) k1P3)) (SC.b false))}
    {hBulkFk2 : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b false))}
    {hTopFk2 : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA (dP3 D) k2P3)) (SC.b false))}
    {hRightCk2 : SFormula.Deriv Δ (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k2P3)) (SC.b true))}
    {hBotB : SFormula.Deriv Δ (.eqBool (SC.closed (bottomBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true))}
    {hRightB : SFormula.Deriv Δ (.eqBool (SC.closed (rightBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))}
    {rho : Env 3} {E : PartialStabilizer}
    (wW : DerivWF hW Surface.code.body (D.distance + 2) rho E)
    (wq : DerivWF hq Surface.code.body (D.distance + 2) rho E)
    (wBulkFk1 : DerivWF hBulkFk1 Surface.code.body (D.distance + 2) rho E)
    (wTopFk1 : DerivWF hTopFk1 Surface.code.body (D.distance + 2) rho E)
    (wRightFk1 : DerivWF hRightFk1 Surface.code.body (D.distance + 2) rho E)
    (wLeftFk1 : DerivWF hLeftFk1 Surface.code.body (D.distance + 2) rho E)
    (wBulkFk2 : DerivWF hBulkFk2 Surface.code.body (D.distance + 2) rho E)
    (wTopFk2 : DerivWF hTopFk2 Surface.code.body (D.distance + 2) rho E)
    (wRightCk2 : DerivWF hRightCk2 Surface.code.body (D.distance + 2) rho E)
    (wBotB : DerivWF hBotB Surface.code.body (D.distance + 2) rho E)
    (wRightB : DerivWF hRightB Surface.code.body (D.distance + 2) rho E) :
    DerivWF (brbnaPinAt D hW hq hBulkFk1 hTopFk1 hRightFk1 hLeftFk1 hBulkFk2 hTopFk2 hRightCk2 hBotB hRightB)
      Surface.code.body (D.distance + 2) rho E := by
  unfold brbnaPinAt
  comm_deriv_wf

theorem blbnaPinAt_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)}
    {hW : SFormula.Deriv Δ (blbnaPinF D).weaken}
    {hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken)}
    {hBulkFk1 : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b false))}
    {hTopFk1 : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA (dP3 D) k1P3)) (SC.b false))}
    {hRightFk1 : SFormula.Deriv Δ (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k1P3)) (SC.b false))}
    {hLeftFk1 : SFormula.Deriv Δ (.eqBool (SC.closed (leftClassGuardTA (dP3 D) k1P3)) (SC.b false))}
    {hBulkFk2 : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b false))}
    {hTopFk2 : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA (dP3 D) k2P3)) (SC.b false))}
    {hRightFk2 : SFormula.Deriv Δ (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k2P3)) (SC.b false))}
    {hLeftCk2 : SFormula.Deriv Δ (.eqBool (SC.closed (leftClassGuardTA (dP3 D) k2P3)) (SC.b true))}
    {hBotB : SFormula.Deriv Δ (.eqBool (SC.closed (bottomBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true))}
    {hLeftB : SFormula.Deriv Δ (.eqBool (SC.closed (leftBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))}
    {rho : Env 3} {E : PartialStabilizer}
    (wW : DerivWF hW Surface.code.body (D.distance + 2) rho E)
    (wq : DerivWF hq Surface.code.body (D.distance + 2) rho E)
    (wBulkFk1 : DerivWF hBulkFk1 Surface.code.body (D.distance + 2) rho E)
    (wTopFk1 : DerivWF hTopFk1 Surface.code.body (D.distance + 2) rho E)
    (wRightFk1 : DerivWF hRightFk1 Surface.code.body (D.distance + 2) rho E)
    (wLeftFk1 : DerivWF hLeftFk1 Surface.code.body (D.distance + 2) rho E)
    (wBulkFk2 : DerivWF hBulkFk2 Surface.code.body (D.distance + 2) rho E)
    (wTopFk2 : DerivWF hTopFk2 Surface.code.body (D.distance + 2) rho E)
    (wRightFk2 : DerivWF hRightFk2 Surface.code.body (D.distance + 2) rho E)
    (wLeftCk2 : DerivWF hLeftCk2 Surface.code.body (D.distance + 2) rho E)
    (wBotB : DerivWF hBotB Surface.code.body (D.distance + 2) rho E)
    (wLeftB : DerivWF hLeftB Surface.code.body (D.distance + 2) rho E) :
    DerivWF (blbnaPinAt D hW hq hBulkFk1 hTopFk1 hRightFk1 hLeftFk1 hBulkFk2 hTopFk2 hRightFk2 hLeftCk2 hBotB hLeftB)
      Surface.code.body (D.distance + 2) rho E := by
  unfold blbnaPinAt
  comm_deriv_wf

end QHL.CodeLang.Surface.Verify
