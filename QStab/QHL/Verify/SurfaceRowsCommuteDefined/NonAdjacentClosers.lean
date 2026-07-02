import QStab.QHL.Verify.SurfaceRowsCommuteDefined.NonAdjacentPins

/-!
# Rows-commute definedness — NonAdjacentClosers

The 8 non-adjacent closers (each `pairCommutePointwise_WF` + pin → ⊥ + type-exclusion block).
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

set_option maxHeartbeats 1600000

/-! ## The 8 non-adjacent closers (each `pairCommutePointwise_WF` + pin → ⊥ + type-excl block).
The (Z,X) block is the identical X-type exclusion proven in `pairCommuteBulkBulkNonAdj_WF`. -/

theorem pairCommuteBulkRightNonAdj_WF (D : OddSurfaceDistance) {Γ : List (SFormula 2)}
    {hEntryA : SFormula.Deriv Γ (entryAQuant D)} {hEntryB : SFormula.Deriv Γ (entryBQuant D)}
    {hk1X : SFormula.Deriv Γ (k1IsX D true)} {hExcl1 : SFormula.Deriv Γ (typeExclF D k1P)}
    {hBulkK1 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true))}
    {hKindK1 : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k1P)) (SC.b false))}
    {hbulkFk2 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false))}
    {htopFk2 : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false))}
    {hrightCk2 : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b true))}
    {hNonAdj : SFormula.Deriv Γ (.eqBool (SC.closed (brnaNonAdjTA2 D)) (SC.b true))}
    {hPin : SFormula.Deriv Γ (brnaPinF D)}
    {rho : Env 2} {E : PartialStabilizer}
    (wEntryA : DerivWF hEntryA Surface.code.body (D.distance + 2) rho E)
    (wEntryB : DerivWF hEntryB Surface.code.body (D.distance + 2) rho E)
    (wHk1X : DerivWF hk1X Surface.code.body (D.distance + 2) rho E)
    (wHExcl1 : DerivWF hExcl1 Surface.code.body (D.distance + 2) rho E)
    (wHBulkK1 : DerivWF hBulkK1 Surface.code.body (D.distance + 2) rho E)
    (wHKindK1 : DerivWF hKindK1 Surface.code.body (D.distance + 2) rho E)
    (wHbulkFk2 : DerivWF hbulkFk2 Surface.code.body (D.distance + 2) rho E)
    (wHtopFk2 : DerivWF htopFk2 Surface.code.body (D.distance + 2) rho E)
    (wHrightCk2 : DerivWF hrightCk2 Surface.code.body (D.distance + 2) rho E)
    (wHNonAdj : DerivWF hNonAdj Surface.code.body (D.distance + 2) rho E)
    (wHPin : DerivWF hPin Surface.code.body (D.distance + 2) rho E)
    (hCtx : SFormula.ContextHolds Surface.code.body (D.distance + 2) rho E Γ) :
    DerivWF (pairCommuteBulkRightNonAdj D hEntryA hEntryB hk1X hExcl1 hBulkK1 hKindK1 hbulkFk2
        htopFk2 hrightCk2 hNonAdj hPin) Surface.code.body (D.distance + 2) rho E := by
  unfold pairCommuteBulkRightNonAdj
  refine pairCommutePointwise_WF D wEntryA wEntryB ?wAntiXZ ?wAntiZX hCtx
  case wAntiXZ =>
    intro x Δ' lift liftWF hLA wLA hLB wLB
    have wBulkK1Δ := liftWF (cw1_WF (derivWF_weakenFresh wHBulkK1))
    have wKindK1Δ := liftWF (cw1_WF (derivWF_weakenFresh wHKindK1))
    have wbulkFk2Δ := liftWF (cw1_WF (derivWF_weakenFresh wHbulkFk2))
    have wtopFk2Δ := liftWF (cw1_WF (derivWF_weakenFresh wHtopFk2))
    have wrightCk2Δ := liftWF (cw1_WF (derivWF_weakenFresh wHrightCk2))
    have wNonAdjΔ := liftWF (cw1_WF (derivWF_weakenFresh wHNonAdj))
    have wPinΔ := liftWF (cw1_WF (derivWF_weakenFresh wHPin))
    have wBandK1 := bhBandK1FromX_WF D wBulkK1Δ wLA
    have wRightB := brRightBandFromZ_WF D wbulkFk2Δ wtopFk2Δ wrightCk2Δ wLB
    exact derivWF_botElim (brnaPinAt_WF D wPinΔ (liftWF (derivWF_hyp _))
      wBulkK1Δ wKindK1Δ wbulkFk2Δ wtopFk2Δ wrightCk2Δ wBandK1 wRightB wNonAdjΔ)
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

theorem pairCommuteBulkLeftNonAdj_WF (D : OddSurfaceDistance) {Γ : List (SFormula 2)}
    {hEntryA : SFormula.Deriv Γ (entryAQuant D)} {hEntryB : SFormula.Deriv Γ (entryBQuant D)}
    {hk1X : SFormula.Deriv Γ (k1IsX D true)} {hExcl1 : SFormula.Deriv Γ (typeExclF D k1P)}
    {hBulkK1 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true))}
    {hKindK1 : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k1P)) (SC.b false))}
    {hbulkFk2 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false))}
    {htopFk2 : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false))}
    {hrightFk2 : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false))}
    {hleftCk2 : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b true))}
    {hNonAdj : SFormula.Deriv Γ (.eqBool (SC.closed (blnaNonAdjTA2 D)) (SC.b true))}
    {hPin : SFormula.Deriv Γ (blnaPinF D)}
    {rho : Env 2} {E : PartialStabilizer}
    (wEntryA : DerivWF hEntryA Surface.code.body (D.distance + 2) rho E)
    (wEntryB : DerivWF hEntryB Surface.code.body (D.distance + 2) rho E)
    (wHk1X : DerivWF hk1X Surface.code.body (D.distance + 2) rho E)
    (wHExcl1 : DerivWF hExcl1 Surface.code.body (D.distance + 2) rho E)
    (wHBulkK1 : DerivWF hBulkK1 Surface.code.body (D.distance + 2) rho E)
    (wHKindK1 : DerivWF hKindK1 Surface.code.body (D.distance + 2) rho E)
    (wHbulkFk2 : DerivWF hbulkFk2 Surface.code.body (D.distance + 2) rho E)
    (wHtopFk2 : DerivWF htopFk2 Surface.code.body (D.distance + 2) rho E)
    (wHrightFk2 : DerivWF hrightFk2 Surface.code.body (D.distance + 2) rho E)
    (wHleftCk2 : DerivWF hleftCk2 Surface.code.body (D.distance + 2) rho E)
    (wHNonAdj : DerivWF hNonAdj Surface.code.body (D.distance + 2) rho E)
    (wHPin : DerivWF hPin Surface.code.body (D.distance + 2) rho E)
    (hCtx : SFormula.ContextHolds Surface.code.body (D.distance + 2) rho E Γ) :
    DerivWF (pairCommuteBulkLeftNonAdj D hEntryA hEntryB hk1X hExcl1 hBulkK1 hKindK1 hbulkFk2
        htopFk2 hrightFk2 hleftCk2 hNonAdj hPin) Surface.code.body (D.distance + 2) rho E := by
  unfold pairCommuteBulkLeftNonAdj
  refine pairCommutePointwise_WF D wEntryA wEntryB ?wAntiXZ ?wAntiZX hCtx
  case wAntiXZ =>
    intro x Δ' lift liftWF hLA wLA hLB wLB
    have wBulkK1Δ := liftWF (cw1_WF (derivWF_weakenFresh wHBulkK1))
    have wKindK1Δ := liftWF (cw1_WF (derivWF_weakenFresh wHKindK1))
    have wbulkFk2Δ := liftWF (cw1_WF (derivWF_weakenFresh wHbulkFk2))
    have wtopFk2Δ := liftWF (cw1_WF (derivWF_weakenFresh wHtopFk2))
    have wrightFk2Δ := liftWF (cw1_WF (derivWF_weakenFresh wHrightFk2))
    have wleftCk2Δ := liftWF (cw1_WF (derivWF_weakenFresh wHleftCk2))
    have wNonAdjΔ := liftWF (cw1_WF (derivWF_weakenFresh wHNonAdj))
    have wPinΔ := liftWF (cw1_WF (derivWF_weakenFresh wHPin))
    have wBandK1 := bhBandK1FromX_WF D wBulkK1Δ wLA
    have wLeftB := blLeftBandFromZ_WF D wbulkFk2Δ wtopFk2Δ wrightFk2Δ wleftCk2Δ wLB
    exact derivWF_botElim (blnaPinAt_WF D wPinΔ (liftWF (derivWF_hyp _))
      wBulkK1Δ wKindK1Δ wbulkFk2Δ wtopFk2Δ wrightFk2Δ wleftCk2Δ wBandK1 wLeftB wNonAdjΔ)
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

theorem pairCommuteTopBulkNonAdj_WF (D : OddSurfaceDistance) {Γ : List (SFormula 2)}
    {hEntryA : SFormula.Deriv Γ (entryAQuant D)} {hEntryB : SFormula.Deriv Γ (entryBQuant D)}
    {hk1X : SFormula.Deriv Γ (k1IsX D true)} {hExcl1 : SFormula.Deriv Γ (typeExclF D k1P)}
    {hbulkFk1 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false))}
    {htopCk1 : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b true))}
    {hBulkK2 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true))}
    {hKindK2 : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k2P)) (SC.b true))}
    {hNonAdj : SFormula.Deriv Γ (.eqBool (SC.closed (tbnaNonAdjTA2 D)) (SC.b true))}
    {hPin : SFormula.Deriv Γ (tbnaPinF D)}
    {rho : Env 2} {E : PartialStabilizer}
    (wEntryA : DerivWF hEntryA Surface.code.body (D.distance + 2) rho E)
    (wEntryB : DerivWF hEntryB Surface.code.body (D.distance + 2) rho E)
    (wHk1X : DerivWF hk1X Surface.code.body (D.distance + 2) rho E)
    (wHExcl1 : DerivWF hExcl1 Surface.code.body (D.distance + 2) rho E)
    (wHbulkFk1 : DerivWF hbulkFk1 Surface.code.body (D.distance + 2) rho E)
    (wHtopCk1 : DerivWF htopCk1 Surface.code.body (D.distance + 2) rho E)
    (wHBulkK2 : DerivWF hBulkK2 Surface.code.body (D.distance + 2) rho E)
    (wHKindK2 : DerivWF hKindK2 Surface.code.body (D.distance + 2) rho E)
    (wHNonAdj : DerivWF hNonAdj Surface.code.body (D.distance + 2) rho E)
    (wHPin : DerivWF hPin Surface.code.body (D.distance + 2) rho E)
    (hCtx : SFormula.ContextHolds Surface.code.body (D.distance + 2) rho E Γ) :
    DerivWF (pairCommuteTopBulkNonAdj D hEntryA hEntryB hk1X hExcl1 hbulkFk1 htopCk1 hBulkK2
        hKindK2 hNonAdj hPin) Surface.code.body (D.distance + 2) rho E := by
  unfold pairCommuteTopBulkNonAdj
  refine pairCommutePointwise_WF D wEntryA wEntryB ?wAntiXZ ?wAntiZX hCtx
  case wAntiXZ =>
    intro x Δ' lift liftWF hLA wLA hLB wLB
    have wbulkFk1Δ := liftWF (cw1_WF (derivWF_weakenFresh wHbulkFk1))
    have wtopCk1Δ := liftWF (cw1_WF (derivWF_weakenFresh wHtopCk1))
    have wBulkK2Δ := liftWF (cw1_WF (derivWF_weakenFresh wHBulkK2))
    have wKindK2Δ := liftWF (cw1_WF (derivWF_weakenFresh wHKindK2))
    have wNonAdjΔ := liftWF (cw1_WF (derivWF_weakenFresh wHNonAdj))
    have wPinΔ := liftWF (cw1_WF (derivWF_weakenFresh wHPin))
    have wTopB := btTopBandFromX_WF D wbulkFk1Δ wtopCk1Δ wLA
    have wBulkB := bbBulkBandFromZ_WF D wBulkK2Δ wLB
    exact derivWF_botElim (tbnaPinAt_WF D wPinΔ (liftWF (derivWF_hyp _))
      wbulkFk1Δ wtopCk1Δ wBulkK2Δ wKindK2Δ wTopB wBulkB wNonAdjΔ)
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

theorem pairCommuteBottomBulkNonAdj_WF (D : OddSurfaceDistance) {Γ : List (SFormula 2)}
    {hEntryA : SFormula.Deriv Γ (entryAQuant D)} {hEntryB : SFormula.Deriv Γ (entryBQuant D)}
    {hk1X : SFormula.Deriv Γ (k1IsX D true)} {hExcl1 : SFormula.Deriv Γ (typeExclF D k1P)}
    {hbulkFk1 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false))}
    {htopFk1 : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false))}
    {hrightFk1 : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k1P)) (SC.b false))}
    {hleftFk1 : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k1P)) (SC.b false))}
    {hBulkK2 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true))}
    {hKindK2 : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k2P)) (SC.b true))}
    {hNonAdj : SFormula.Deriv Γ (.eqBool (SC.closed (btbnaNonAdjTA2 D)) (SC.b true))}
    {hPin : SFormula.Deriv Γ (btbnaPinF D)}
    {rho : Env 2} {E : PartialStabilizer}
    (wEntryA : DerivWF hEntryA Surface.code.body (D.distance + 2) rho E)
    (wEntryB : DerivWF hEntryB Surface.code.body (D.distance + 2) rho E)
    (wHk1X : DerivWF hk1X Surface.code.body (D.distance + 2) rho E)
    (wHExcl1 : DerivWF hExcl1 Surface.code.body (D.distance + 2) rho E)
    (wHbulkFk1 : DerivWF hbulkFk1 Surface.code.body (D.distance + 2) rho E)
    (wHtopFk1 : DerivWF htopFk1 Surface.code.body (D.distance + 2) rho E)
    (wHrightFk1 : DerivWF hrightFk1 Surface.code.body (D.distance + 2) rho E)
    (wHleftFk1 : DerivWF hleftFk1 Surface.code.body (D.distance + 2) rho E)
    (wHBulkK2 : DerivWF hBulkK2 Surface.code.body (D.distance + 2) rho E)
    (wHKindK2 : DerivWF hKindK2 Surface.code.body (D.distance + 2) rho E)
    (wHNonAdj : DerivWF hNonAdj Surface.code.body (D.distance + 2) rho E)
    (wHPin : DerivWF hPin Surface.code.body (D.distance + 2) rho E)
    (hCtx : SFormula.ContextHolds Surface.code.body (D.distance + 2) rho E Γ) :
    DerivWF (pairCommuteBottomBulkNonAdj D hEntryA hEntryB hk1X hExcl1 hbulkFk1 htopFk1 hrightFk1
        hleftFk1 hBulkK2 hKindK2 hNonAdj hPin) Surface.code.body (D.distance + 2) rho E := by
  unfold pairCommuteBottomBulkNonAdj
  refine pairCommutePointwise_WF D wEntryA wEntryB ?wAntiXZ ?wAntiZX hCtx
  case wAntiXZ =>
    intro x Δ' lift liftWF hLA wLA hLB wLB
    have wbulkFk1Δ := liftWF (cw1_WF (derivWF_weakenFresh wHbulkFk1))
    have wtopFk1Δ := liftWF (cw1_WF (derivWF_weakenFresh wHtopFk1))
    have wrightFk1Δ := liftWF (cw1_WF (derivWF_weakenFresh wHrightFk1))
    have wleftFk1Δ := liftWF (cw1_WF (derivWF_weakenFresh wHleftFk1))
    have wBulkK2Δ := liftWF (cw1_WF (derivWF_weakenFresh wHBulkK2))
    have wKindK2Δ := liftWF (cw1_WF (derivWF_weakenFresh wHKindK2))
    have wNonAdjΔ := liftWF (cw1_WF (derivWF_weakenFresh wHNonAdj))
    have wPinΔ := liftWF (cw1_WF (derivWF_weakenFresh wHPin))
    have wBotB := bbBottomBandFromX_WF D wbulkFk1Δ wtopFk1Δ wrightFk1Δ wleftFk1Δ wLA
    have wBulkB := bbBulkBandFromZ_WF D wBulkK2Δ wLB
    exact derivWF_botElim (btbnaPinAt_WF D wPinΔ (liftWF (derivWF_hyp _))
      wbulkFk1Δ wtopFk1Δ wrightFk1Δ wleftFk1Δ wBulkK2Δ wKindK2Δ wBotB wBulkB wNonAdjΔ)
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

theorem pairCommuteTopRightNonAdj_WF (D : OddSurfaceDistance) {Γ : List (SFormula 2)}
    {hEntryA : SFormula.Deriv Γ (entryAQuant D)} {hEntryB : SFormula.Deriv Γ (entryBQuant D)}
    {hk1X : SFormula.Deriv Γ (k1IsX D true)} {hExcl1 : SFormula.Deriv Γ (typeExclF D k1P)}
    {hbulkFk1 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false))}
    {htopCk1 : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b true))}
    {hbulkFk2 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false))}
    {htopFk2 : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false))}
    {hrightCk2 : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b true))}
    {hPin : SFormula.Deriv Γ (trnaPinF D)}
    {rho : Env 2} {E : PartialStabilizer}
    (wEntryA : DerivWF hEntryA Surface.code.body (D.distance + 2) rho E)
    (wEntryB : DerivWF hEntryB Surface.code.body (D.distance + 2) rho E)
    (wHk1X : DerivWF hk1X Surface.code.body (D.distance + 2) rho E)
    (wHExcl1 : DerivWF hExcl1 Surface.code.body (D.distance + 2) rho E)
    (wHbulkFk1 : DerivWF hbulkFk1 Surface.code.body (D.distance + 2) rho E)
    (wHtopCk1 : DerivWF htopCk1 Surface.code.body (D.distance + 2) rho E)
    (wHbulkFk2 : DerivWF hbulkFk2 Surface.code.body (D.distance + 2) rho E)
    (wHtopFk2 : DerivWF htopFk2 Surface.code.body (D.distance + 2) rho E)
    (wHrightCk2 : DerivWF hrightCk2 Surface.code.body (D.distance + 2) rho E)
    (wHPin : DerivWF hPin Surface.code.body (D.distance + 2) rho E)
    (hCtx : SFormula.ContextHolds Surface.code.body (D.distance + 2) rho E Γ) :
    DerivWF (pairCommuteTopRightNonAdj D hEntryA hEntryB hk1X hExcl1 hbulkFk1 htopCk1 hbulkFk2
        htopFk2 hrightCk2 hPin) Surface.code.body (D.distance + 2) rho E := by
  unfold pairCommuteTopRightNonAdj
  refine pairCommutePointwise_WF D wEntryA wEntryB ?wAntiXZ ?wAntiZX hCtx
  case wAntiXZ =>
    intro x Δ' lift liftWF hLA wLA hLB wLB
    have wbulkFk1Δ := liftWF (cw1_WF (derivWF_weakenFresh wHbulkFk1))
    have wtopCk1Δ := liftWF (cw1_WF (derivWF_weakenFresh wHtopCk1))
    have wbulkFk2Δ := liftWF (cw1_WF (derivWF_weakenFresh wHbulkFk2))
    have wtopFk2Δ := liftWF (cw1_WF (derivWF_weakenFresh wHtopFk2))
    have wrightCk2Δ := liftWF (cw1_WF (derivWF_weakenFresh wHrightCk2))
    have wPinΔ := liftWF (cw1_WF (derivWF_weakenFresh wHPin))
    have wTopB := btTopBandFromX_WF D wbulkFk1Δ wtopCk1Δ wLA
    have wRightB := brRightBandFromZ_WF D wbulkFk2Δ wtopFk2Δ wrightCk2Δ wLB
    exact derivWF_botElim (trnaPinAt_WF D wPinΔ (liftWF (derivWF_hyp _))
      wbulkFk1Δ wtopCk1Δ wbulkFk2Δ wtopFk2Δ wrightCk2Δ wTopB wRightB)
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

theorem pairCommuteTopLeftNonAdj_WF (D : OddSurfaceDistance) {Γ : List (SFormula 2)}
    {hEntryA : SFormula.Deriv Γ (entryAQuant D)} {hEntryB : SFormula.Deriv Γ (entryBQuant D)}
    {hk1X : SFormula.Deriv Γ (k1IsX D true)} {hExcl1 : SFormula.Deriv Γ (typeExclF D k1P)}
    {hbulkFk1 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false))}
    {htopCk1 : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b true))}
    {hbulkFk2 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false))}
    {htopFk2 : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false))}
    {hrightFk2 : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false))}
    {hleftCk2 : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b true))}
    {hPin : SFormula.Deriv Γ (tlnaPinF D)}
    {rho : Env 2} {E : PartialStabilizer}
    (wEntryA : DerivWF hEntryA Surface.code.body (D.distance + 2) rho E)
    (wEntryB : DerivWF hEntryB Surface.code.body (D.distance + 2) rho E)
    (wHk1X : DerivWF hk1X Surface.code.body (D.distance + 2) rho E)
    (wHExcl1 : DerivWF hExcl1 Surface.code.body (D.distance + 2) rho E)
    (wHbulkFk1 : DerivWF hbulkFk1 Surface.code.body (D.distance + 2) rho E)
    (wHtopCk1 : DerivWF htopCk1 Surface.code.body (D.distance + 2) rho E)
    (wHbulkFk2 : DerivWF hbulkFk2 Surface.code.body (D.distance + 2) rho E)
    (wHtopFk2 : DerivWF htopFk2 Surface.code.body (D.distance + 2) rho E)
    (wHrightFk2 : DerivWF hrightFk2 Surface.code.body (D.distance + 2) rho E)
    (wHleftCk2 : DerivWF hleftCk2 Surface.code.body (D.distance + 2) rho E)
    (wHPin : DerivWF hPin Surface.code.body (D.distance + 2) rho E)
    (hCtx : SFormula.ContextHolds Surface.code.body (D.distance + 2) rho E Γ) :
    DerivWF (pairCommuteTopLeftNonAdj D hEntryA hEntryB hk1X hExcl1 hbulkFk1 htopCk1 hbulkFk2
        htopFk2 hrightFk2 hleftCk2 hPin) Surface.code.body (D.distance + 2) rho E := by
  unfold pairCommuteTopLeftNonAdj
  refine pairCommutePointwise_WF D wEntryA wEntryB ?wAntiXZ ?wAntiZX hCtx
  case wAntiXZ =>
    intro x Δ' lift liftWF hLA wLA hLB wLB
    have wbulkFk1Δ := liftWF (cw1_WF (derivWF_weakenFresh wHbulkFk1))
    have wtopCk1Δ := liftWF (cw1_WF (derivWF_weakenFresh wHtopCk1))
    have wbulkFk2Δ := liftWF (cw1_WF (derivWF_weakenFresh wHbulkFk2))
    have wtopFk2Δ := liftWF (cw1_WF (derivWF_weakenFresh wHtopFk2))
    have wrightFk2Δ := liftWF (cw1_WF (derivWF_weakenFresh wHrightFk2))
    have wleftCk2Δ := liftWF (cw1_WF (derivWF_weakenFresh wHleftCk2))
    have wPinΔ := liftWF (cw1_WF (derivWF_weakenFresh wHPin))
    have wTopB := btTopBandFromX_WF D wbulkFk1Δ wtopCk1Δ wLA
    have wLeftB := blLeftBandFromZ_WF D wbulkFk2Δ wtopFk2Δ wrightFk2Δ wleftCk2Δ wLB
    exact derivWF_botElim (tlnaPinAt_WF D wPinΔ (liftWF (derivWF_hyp _))
      wbulkFk1Δ wtopCk1Δ wbulkFk2Δ wtopFk2Δ wrightFk2Δ wleftCk2Δ wTopB wLeftB)
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

theorem pairCommuteBottomRightNonAdj_WF (D : OddSurfaceDistance) {Γ : List (SFormula 2)}
    {hEntryA : SFormula.Deriv Γ (entryAQuant D)} {hEntryB : SFormula.Deriv Γ (entryBQuant D)}
    {hk1X : SFormula.Deriv Γ (k1IsX D true)} {hExcl1 : SFormula.Deriv Γ (typeExclF D k1P)}
    {hbulkFk1 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false))}
    {htopFk1 : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false))}
    {hrightFk1 : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k1P)) (SC.b false))}
    {hleftFk1 : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k1P)) (SC.b false))}
    {hbulkFk2 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false))}
    {htopFk2 : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false))}
    {hrightCk2 : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b true))}
    {hPin : SFormula.Deriv Γ (brbnaPinF D)}
    {rho : Env 2} {E : PartialStabilizer}
    (wEntryA : DerivWF hEntryA Surface.code.body (D.distance + 2) rho E)
    (wEntryB : DerivWF hEntryB Surface.code.body (D.distance + 2) rho E)
    (wHk1X : DerivWF hk1X Surface.code.body (D.distance + 2) rho E)
    (wHExcl1 : DerivWF hExcl1 Surface.code.body (D.distance + 2) rho E)
    (wHbulkFk1 : DerivWF hbulkFk1 Surface.code.body (D.distance + 2) rho E)
    (wHtopFk1 : DerivWF htopFk1 Surface.code.body (D.distance + 2) rho E)
    (wHrightFk1 : DerivWF hrightFk1 Surface.code.body (D.distance + 2) rho E)
    (wHleftFk1 : DerivWF hleftFk1 Surface.code.body (D.distance + 2) rho E)
    (wHbulkFk2 : DerivWF hbulkFk2 Surface.code.body (D.distance + 2) rho E)
    (wHtopFk2 : DerivWF htopFk2 Surface.code.body (D.distance + 2) rho E)
    (wHrightCk2 : DerivWF hrightCk2 Surface.code.body (D.distance + 2) rho E)
    (wHPin : DerivWF hPin Surface.code.body (D.distance + 2) rho E)
    (hCtx : SFormula.ContextHolds Surface.code.body (D.distance + 2) rho E Γ) :
    DerivWF (pairCommuteBottomRightNonAdj D hEntryA hEntryB hk1X hExcl1 hbulkFk1 htopFk1 hrightFk1
        hleftFk1 hbulkFk2 htopFk2 hrightCk2 hPin) Surface.code.body (D.distance + 2) rho E := by
  unfold pairCommuteBottomRightNonAdj
  refine pairCommutePointwise_WF D wEntryA wEntryB ?wAntiXZ ?wAntiZX hCtx
  case wAntiXZ =>
    intro x Δ' lift liftWF hLA wLA hLB wLB
    have wbulkFk1Δ := liftWF (cw1_WF (derivWF_weakenFresh wHbulkFk1))
    have wtopFk1Δ := liftWF (cw1_WF (derivWF_weakenFresh wHtopFk1))
    have wrightFk1Δ := liftWF (cw1_WF (derivWF_weakenFresh wHrightFk1))
    have wleftFk1Δ := liftWF (cw1_WF (derivWF_weakenFresh wHleftFk1))
    have wbulkFk2Δ := liftWF (cw1_WF (derivWF_weakenFresh wHbulkFk2))
    have wtopFk2Δ := liftWF (cw1_WF (derivWF_weakenFresh wHtopFk2))
    have wrightCk2Δ := liftWF (cw1_WF (derivWF_weakenFresh wHrightCk2))
    have wPinΔ := liftWF (cw1_WF (derivWF_weakenFresh wHPin))
    have wBotB := bbBottomBandFromX_WF D wbulkFk1Δ wtopFk1Δ wrightFk1Δ wleftFk1Δ wLA
    have wRightB := brRightBandFromZ_WF D wbulkFk2Δ wtopFk2Δ wrightCk2Δ wLB
    exact derivWF_botElim (brbnaPinAt_WF D wPinΔ (liftWF (derivWF_hyp _))
      wbulkFk1Δ wtopFk1Δ wrightFk1Δ wleftFk1Δ wbulkFk2Δ wtopFk2Δ wrightCk2Δ wBotB wRightB)
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

theorem pairCommuteBottomLeftNonAdj_WF (D : OddSurfaceDistance) {Γ : List (SFormula 2)}
    {hEntryA : SFormula.Deriv Γ (entryAQuant D)} {hEntryB : SFormula.Deriv Γ (entryBQuant D)}
    {hk1X : SFormula.Deriv Γ (k1IsX D true)} {hExcl1 : SFormula.Deriv Γ (typeExclF D k1P)}
    {hbulkFk1 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false))}
    {htopFk1 : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false))}
    {hrightFk1 : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k1P)) (SC.b false))}
    {hleftFk1 : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k1P)) (SC.b false))}
    {hbulkFk2 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false))}
    {htopFk2 : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false))}
    {hrightFk2 : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false))}
    {hleftCk2 : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b true))}
    {hPin : SFormula.Deriv Γ (blbnaPinF D)}
    {rho : Env 2} {E : PartialStabilizer}
    (wEntryA : DerivWF hEntryA Surface.code.body (D.distance + 2) rho E)
    (wEntryB : DerivWF hEntryB Surface.code.body (D.distance + 2) rho E)
    (wHk1X : DerivWF hk1X Surface.code.body (D.distance + 2) rho E)
    (wHExcl1 : DerivWF hExcl1 Surface.code.body (D.distance + 2) rho E)
    (wHbulkFk1 : DerivWF hbulkFk1 Surface.code.body (D.distance + 2) rho E)
    (wHtopFk1 : DerivWF htopFk1 Surface.code.body (D.distance + 2) rho E)
    (wHrightFk1 : DerivWF hrightFk1 Surface.code.body (D.distance + 2) rho E)
    (wHleftFk1 : DerivWF hleftFk1 Surface.code.body (D.distance + 2) rho E)
    (wHbulkFk2 : DerivWF hbulkFk2 Surface.code.body (D.distance + 2) rho E)
    (wHtopFk2 : DerivWF htopFk2 Surface.code.body (D.distance + 2) rho E)
    (wHrightFk2 : DerivWF hrightFk2 Surface.code.body (D.distance + 2) rho E)
    (wHleftCk2 : DerivWF hleftCk2 Surface.code.body (D.distance + 2) rho E)
    (wHPin : DerivWF hPin Surface.code.body (D.distance + 2) rho E)
    (hCtx : SFormula.ContextHolds Surface.code.body (D.distance + 2) rho E Γ) :
    DerivWF (pairCommuteBottomLeftNonAdj D hEntryA hEntryB hk1X hExcl1 hbulkFk1 htopFk1 hrightFk1
        hleftFk1 hbulkFk2 htopFk2 hrightFk2 hleftCk2 hPin) Surface.code.body (D.distance + 2) rho E := by
  unfold pairCommuteBottomLeftNonAdj
  refine pairCommutePointwise_WF D wEntryA wEntryB ?wAntiXZ ?wAntiZX hCtx
  case wAntiXZ =>
    intro x Δ' lift liftWF hLA wLA hLB wLB
    have wbulkFk1Δ := liftWF (cw1_WF (derivWF_weakenFresh wHbulkFk1))
    have wtopFk1Δ := liftWF (cw1_WF (derivWF_weakenFresh wHtopFk1))
    have wrightFk1Δ := liftWF (cw1_WF (derivWF_weakenFresh wHrightFk1))
    have wleftFk1Δ := liftWF (cw1_WF (derivWF_weakenFresh wHleftFk1))
    have wbulkFk2Δ := liftWF (cw1_WF (derivWF_weakenFresh wHbulkFk2))
    have wtopFk2Δ := liftWF (cw1_WF (derivWF_weakenFresh wHtopFk2))
    have wrightFk2Δ := liftWF (cw1_WF (derivWF_weakenFresh wHrightFk2))
    have wleftCk2Δ := liftWF (cw1_WF (derivWF_weakenFresh wHleftCk2))
    have wPinΔ := liftWF (cw1_WF (derivWF_weakenFresh wHPin))
    have wBotB := bbBottomBandFromX_WF D wbulkFk1Δ wtopFk1Δ wrightFk1Δ wleftFk1Δ wLA
    have wLeftB := blLeftBandFromZ_WF D wbulkFk2Δ wtopFk2Δ wrightFk2Δ wleftCk2Δ wLB
    exact derivWF_botElim (blbnaPinAt_WF D wPinΔ (liftWF (derivWF_hyp _))
      wbulkFk1Δ wtopFk1Δ wrightFk1Δ wleftFk1Δ wbulkFk2Δ wtopFk2Δ wrightFk2Δ wleftCk2Δ wBotB wLeftB)
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

end QHL.CodeLang.Surface.Verify
