import QStab.QHL.Verify.SurfaceRowsCommuteDefined.BulkBulkCombos

/-!
# Rows-commute definedness — BulkBoundaryCombos

The four bulk–boundary overlap closer WFs: top, bottom, right (role-swapped), and left.
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

set_option maxHeartbeats 1600000

/-! ## Bulk–boundary: BULK-TOP combo (rowA = top boundary X-leaf, rowB = bulk Z-leaf) -/

theorem btPinAt_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)}
    {hW : SFormula.Deriv Δ (btPinF D).weaken}
    {hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken)}
    {hBulkF : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b false))}
    {hTopC : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA (dP3 D) k1P3)) (SC.b true))}
    {hAdj : SFormula.Deriv Δ (.eqBool (SC.closed (.eqNat k2P3 (.mul (.natLit 2) (btB3 D)))) (SC.b true))}
    {hTopB : SFormula.Deriv Δ (.eqBool (SC.closed (topBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true))}
    {hBulkB : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))}
    {rho : Env 3} {E : PartialStabilizer}
    (wW : DerivWF hW Surface.code.body (D.distance + 2) rho E)
    (wq : DerivWF hq Surface.code.body (D.distance + 2) rho E)
    (wBulkF : DerivWF hBulkF Surface.code.body (D.distance + 2) rho E)
    (wTopC : DerivWF hTopC Surface.code.body (D.distance + 2) rho E)
    (wAdj : DerivWF hAdj Surface.code.body (D.distance + 2) rho E)
    (wTopB : DerivWF hTopB Surface.code.body (D.distance + 2) rho E)
    (wBulkB : DerivWF hBulkB Surface.code.body (D.distance + 2) rho E) :
    DerivWF (btPinAt D hW hq hBulkF hTopC hAdj hTopB hBulkB)
      Surface.code.body (D.distance + 2) rho E := by
  unfold btPinAt
  comm_deriv_wf

theorem btTopBandFromX_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)}
    {hBulkF : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b false))}
    {hTopC : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA (dP3 D) k1P3)) (SC.b true))}
    {hLeafX : SFormula.Deriv Δ (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3)) (SC.p Pauli.X))}
    {rho : Env 3} {E : PartialStabilizer}
    (wBulkF : DerivWF hBulkF Surface.code.body (D.distance + 2) rho E)
    (wTopC : DerivWF hTopC Surface.code.body (D.distance + 2) rho E)
    (wLeafX : DerivWF hLeafX Surface.code.body (D.distance + 2) rho E) :
    DerivWF (btTopBandFromX D hBulkF hTopC hLeafX) Surface.code.body (D.distance + 2) rho E := by
  unfold btTopBandFromX
  refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor)))
    (derivWF_hyp _) ?_
  refine derivWF_botElim (derivWF_notElim ?_ (derivWF_pauliNeqLit _ _ (by decide)))
  exact derivWF_eqPauliTrans' (derivWF_eqPauliSymm' (cw1_WF wLeafX))
    (baseLeafTopIS_WF _ (dP3 D) k1P3 qP3 (dP3_pure D) (.var _) (.var _)
      (cw1_WF wBulkF) (cw1_WF wTopC) (derivWF_hyp _))

theorem btBulkBandFromZ_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)}
    {hBulkT : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b true))}
    {hLeafZ : SFormula.Deriv Δ (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p Pauli.Z))}
    {rho : Env 3} {E : PartialStabilizer}
    (wBulkT : DerivWF hBulkT Surface.code.body (D.distance + 2) rho E)
    (wLeafZ : DerivWF hLeafZ Surface.code.body (D.distance + 2) rho E) :
    DerivWF (btBulkBandFromZ D hBulkT hLeafZ) Surface.code.body (D.distance + 2) rho E := by
  unfold btBulkBandFromZ
  refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor)))
    (derivWF_hyp _) ?_
  refine derivWF_botElim (derivWF_notElim ?_ (derivWF_pauliNeqLit _ _ (by decide)))
  exact derivWF_eqPauliTrans' (derivWF_eqPauliSymm' (cw1_WF wLeafZ))
    (baseLeafBulkIS_WF _ (dP3 D) k2P3 qP3 (dP3_pure D) (.var _) (.var _) (cw1_WF wBulkT) (derivWF_hyp _))

theorem commBulkTop_WF (D : OddSurfaceDistance) {Γ : List (SFormula 2)}
    {hEntryA : SFormula.Deriv Γ (entryAQuant D)} {hEntryB : SFormula.Deriv Γ (entryBQuant D)}
    {hk1X : SFormula.Deriv Γ (k1IsX D true)} {hExcl1 : SFormula.Deriv Γ (typeExclF D k1P)}
    {hbulkF : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false))}
    {htopC : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b true))}
    {hadj : SFormula.Deriv Γ (btAdjF D)} {hRange : SFormula.Deriv Γ (btRangePackF D)}
    {hTopBand : SFormula.Deriv Γ (btTopBandPackF D)} {hBulkBand : SFormula.Deriv Γ (btBulkBandPackF D)}
    {hPin : SFormula.Deriv Γ (btPinF D)}
    {hEA0 : SFormula.Deriv Γ (entryAAtQF D (btQ0 D))} {hEA1 : SFormula.Deriv Γ (entryAAtQF D (btQ1 D))}
    {hEB0 : SFormula.Deriv Γ (entryBAtQF D (btQ0 D))} {hEB1 : SFormula.Deriv Γ (entryBAtQF D (btQ1 D))}
    {rho : Env 2} {E : PartialStabilizer}
    (wEntryA : DerivWF hEntryA Surface.code.body (D.distance + 2) rho E)
    (wEntryB : DerivWF hEntryB Surface.code.body (D.distance + 2) rho E)
    (wHk1X : DerivWF hk1X Surface.code.body (D.distance + 2) rho E)
    (wHExcl1 : DerivWF hExcl1 Surface.code.body (D.distance + 2) rho E)
    (wHbulkF : DerivWF hbulkF Surface.code.body (D.distance + 2) rho E)
    (wHtopC : DerivWF htopC Surface.code.body (D.distance + 2) rho E)
    (wHadj : DerivWF hadj Surface.code.body (D.distance + 2) rho E)
    (wHRange : DerivWF hRange Surface.code.body (D.distance + 2) rho E)
    (wHTopBand : DerivWF hTopBand Surface.code.body (D.distance + 2) rho E)
    (wHBulkBand : DerivWF hBulkBand Surface.code.body (D.distance + 2) rho E)
    (wHPin : DerivWF hPin Surface.code.body (D.distance + 2) rho E)
    (wHEA0 : DerivWF hEA0 Surface.code.body (D.distance + 2) rho E)
    (wHEA1 : DerivWF hEA1 Surface.code.body (D.distance + 2) rho E)
    (wHEB0 : DerivWF hEB0 Surface.code.body (D.distance + 2) rho E)
    (wHEB1 : DerivWF hEB1 Surface.code.body (D.distance + 2) rho E)
    (hCtx : SFormula.ContextHolds Surface.code.body (D.distance + 2) rho E Γ) :
    DerivWF (commBulkTop D hEntryA hEntryB hk1X hExcl1 hbulkF htopC hadj hRange hTopBand
        hBulkBand hPin hEA0 hEA1 hEB0 hEB1) Surface.code.body (D.distance + 2) rho E := by
  unfold commBulkTop
  have wRangeP := derivWF_mp (derivWF_mp wHRange wHbulkF) wHtopC
  have wTBP := derivWF_mp (derivWF_mp wHTopBand wHbulkF) wHtopC
  have wBBP := derivWF_mp (derivWF_mp (derivWF_mp wHBulkBand wHbulkF) wHtopC) wHadj
  refine commBulkTopXZ_WF D (btQ0 D) (btQ1 D)
    (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
    (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
    wEntryA wEntryB wHk1X wHExcl1
    (derivWF_andElimLeft' wRangeP)
    (derivWF_andElimLeft' (derivWF_andElimRight' wRangeP))
    (derivWF_andElimRight' (derivWF_andElimRight' wRangeP))
    (derivWF_eqPauliTrans' wHEA0 (baseLeafTopXS_WF _ (dP2 D) k1P (btQ0 D) (dP2_pure D) (.var _)
      (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
      wHbulkF wHtopC (derivWF_andElimLeft' wTBP)))
    (derivWF_eqPauliTrans' wHEA1 (baseLeafTopXS_WF _ (dP2 D) k1P (btQ1 D) (dP2_pure D) (.var _)
      (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
      wHbulkF wHtopC (derivWF_andElimRight' wTBP)))
    (derivWF_eqPauliTrans' wHEB0 (baseLeafZS_WF _ (dP2 D) k2P (btQ0 D) (dP2_pure D) (.var _)
      (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
      (derivWF_andElimLeft' wBBP)
      (derivWF_andElimLeft' (derivWF_andElimRight' (derivWF_andElimRight' wBBP)))
      (derivWF_andElimLeft' (derivWF_andElimRight' wBBP))))
    (derivWF_eqPauliTrans' wHEB1 (baseLeafZS_WF _ (dP2 D) k2P (btQ1 D) (dP2_pure D) (.var _)
      (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
      (derivWF_andElimLeft' wBBP)
      (derivWF_andElimRight' (derivWF_andElimRight' (derivWF_andElimRight' wBBP)))
      (derivWF_andElimLeft' (derivWF_andElimRight' wBBP))))
    ?wHXZpin hCtx
  intro x Δ' lift liftWF hX wX hZ wZ
  have wbulkFΔ := liftWF (cw3_WF (derivWF_weakenFresh wHbulkF))
  have wtopCΔ := liftWF (cw3_WF (derivWF_weakenFresh wHtopC))
  have wadjΔ := liftWF (cw3_WF (derivWF_weakenFresh wHadj))
  have wBulkK2Δ := liftWF (cw3_WF (derivWF_weakenFresh (derivWF_andElimLeft' wBBP)))
  have wPinΔ := liftWF (cw3_WF (derivWF_weakenFresh wHPin))
  have wTopB := btTopBandFromX_WF D wbulkFΔ wtopCΔ wX
  have wBulkB := btBulkBandFromZ_WF D wBulkK2Δ wZ
  refine derivWF_orElim
    (btPinAt_WF D wPinΔ (liftWF (derivWF_hyp _)) wbulkFΔ wtopCΔ wadjΔ wTopB wBulkB) ?_ ?_
  · exact derivWF_botElim (derivWF_notElim (derivWF_hyp _) (cw1_WF (liftWF (derivWF_hyp _))))
  · exact derivWF_botElim (derivWF_notElim (derivWF_hyp _) (cw1_WF (liftWF (derivWF_hyp _))))

/-! ## Bulk–boundary: BULK-BOTTOM combo (bottom "else" leaf: 4 class-false + strip) -/

theorem bbPinAt_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)}
    {hW : SFormula.Deriv Δ (bbPinF D).weaken}
    {hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken)}
    {hBulkF : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b false))}
    {hTopF : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA (dP3 D) k1P3)) (SC.b false))}
    {hRightF : SFormula.Deriv Δ (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k1P3)) (SC.b false))}
    {hLeftF : SFormula.Deriv Δ (.eqBool (SC.closed (leftClassGuardTA (dP3 D) k1P3)) (SC.b false))}
    {hStrip : SFormula.Deriv Δ (.eqBool (SC.closed (.ltNat (baseBTA (dP3 D) k1P3)
      (.mul (.natLit 4) (baseHalfTA (dP3 D))))) (SC.b true))}
    {hAdj : SFormula.Deriv Δ (.eqBool (SC.closed (.eqNat k2P3
      (.add (.mul (.sub (dm1TA (dP3 D)) (.natLit 1)) (dm1TA (dP3 D)))
        (.add (.mul (.natLit 2) (bbB3 D)) (.natLit 1))))) (SC.b true))}
    {hBotB : SFormula.Deriv Δ (.eqBool (SC.closed (bottomBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true))}
    {hBulkB : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))}
    {rho : Env 3} {E : PartialStabilizer}
    (wW : DerivWF hW Surface.code.body (D.distance + 2) rho E)
    (wq : DerivWF hq Surface.code.body (D.distance + 2) rho E)
    (wBulkF : DerivWF hBulkF Surface.code.body (D.distance + 2) rho E)
    (wTopF : DerivWF hTopF Surface.code.body (D.distance + 2) rho E)
    (wRightF : DerivWF hRightF Surface.code.body (D.distance + 2) rho E)
    (wLeftF : DerivWF hLeftF Surface.code.body (D.distance + 2) rho E)
    (wStrip : DerivWF hStrip Surface.code.body (D.distance + 2) rho E)
    (wAdj : DerivWF hAdj Surface.code.body (D.distance + 2) rho E)
    (wBotB : DerivWF hBotB Surface.code.body (D.distance + 2) rho E)
    (wBulkB : DerivWF hBulkB Surface.code.body (D.distance + 2) rho E) :
    DerivWF (bbPinAt D hW hq hBulkF hTopF hRightF hLeftF hStrip hAdj hBotB hBulkB)
      Surface.code.body (D.distance + 2) rho E := by
  unfold bbPinAt
  comm_deriv_wf

theorem bbBottomBandFromX_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)}
    {hBulkF : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b false))}
    {hTopF : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA (dP3 D) k1P3)) (SC.b false))}
    {hRightF : SFormula.Deriv Δ (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k1P3)) (SC.b false))}
    {hLeftF : SFormula.Deriv Δ (.eqBool (SC.closed (leftClassGuardTA (dP3 D) k1P3)) (SC.b false))}
    {hLeafX : SFormula.Deriv Δ (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3)) (SC.p Pauli.X))}
    {rho : Env 3} {E : PartialStabilizer}
    (wBulkF : DerivWF hBulkF Surface.code.body (D.distance + 2) rho E)
    (wTopF : DerivWF hTopF Surface.code.body (D.distance + 2) rho E)
    (wRightF : DerivWF hRightF Surface.code.body (D.distance + 2) rho E)
    (wLeftF : DerivWF hLeftF Surface.code.body (D.distance + 2) rho E)
    (wLeafX : DerivWF hLeafX Surface.code.body (D.distance + 2) rho E) :
    DerivWF (bbBottomBandFromX D hBulkF hTopF hRightF hLeftF hLeafX)
      Surface.code.body (D.distance + 2) rho E := by
  unfold bbBottomBandFromX
  refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor)))
    (derivWF_hyp _) ?_
  refine derivWF_botElim (derivWF_notElim ?_ (derivWF_pauliNeqLit _ _ (by decide)))
  exact derivWF_eqPauliTrans' (derivWF_eqPauliSymm' (cw1_WF wLeafX))
    (baseLeafBottomIS_WF _ (dP3 D) k1P3 qP3 (dP3_pure D) (.var _) (.var _)
      (cw1_WF wBulkF) (cw1_WF wTopF) (cw1_WF wRightF) (cw1_WF wLeftF) (derivWF_hyp _))

theorem bbBulkBandFromZ_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)}
    {hBulkT : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b true))}
    {hLeafZ : SFormula.Deriv Δ (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p Pauli.Z))}
    {rho : Env 3} {E : PartialStabilizer}
    (wBulkT : DerivWF hBulkT Surface.code.body (D.distance + 2) rho E)
    (wLeafZ : DerivWF hLeafZ Surface.code.body (D.distance + 2) rho E) :
    DerivWF (bbBulkBandFromZ D hBulkT hLeafZ) Surface.code.body (D.distance + 2) rho E := by
  unfold bbBulkBandFromZ
  exact btBulkBandFromZ_WF D wBulkT wLeafZ

theorem commBottomBulk_WF (D : OddSurfaceDistance) {Γ : List (SFormula 2)}
    {hEntryA : SFormula.Deriv Γ (entryAQuant D)} {hEntryB : SFormula.Deriv Γ (entryBQuant D)}
    {hk1X : SFormula.Deriv Γ (k1IsX D true)} {hExcl1 : SFormula.Deriv Γ (typeExclF D k1P)}
    {hbulkF : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false))}
    {htopF : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false))}
    {hrightF : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k1P)) (SC.b false))}
    {hleftF : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k1P)) (SC.b false))}
    {hstrip : SFormula.Deriv Γ (bbStripF D)} {hadj : SFormula.Deriv Γ (bbAdjF D)}
    {hRange : SFormula.Deriv Γ (bbRangePackF D)}
    {hBottomBand : SFormula.Deriv Γ (bbBottomBandPackF D)} {hBulkBand : SFormula.Deriv Γ (bbBulkBandPackF D)}
    {hPin : SFormula.Deriv Γ (bbPinF D)}
    {hEA0 : SFormula.Deriv Γ (entryAAtQF D (bbQ0 D))} {hEA1 : SFormula.Deriv Γ (entryAAtQF D (bbQ1 D))}
    {hEB0 : SFormula.Deriv Γ (entryBAtQF D (bbQ0 D))} {hEB1 : SFormula.Deriv Γ (entryBAtQF D (bbQ1 D))}
    {rho : Env 2} {E : PartialStabilizer}
    (wEntryA : DerivWF hEntryA Surface.code.body (D.distance + 2) rho E)
    (wEntryB : DerivWF hEntryB Surface.code.body (D.distance + 2) rho E)
    (wHk1X : DerivWF hk1X Surface.code.body (D.distance + 2) rho E)
    (wHExcl1 : DerivWF hExcl1 Surface.code.body (D.distance + 2) rho E)
    (wHbulkF : DerivWF hbulkF Surface.code.body (D.distance + 2) rho E)
    (wHtopF : DerivWF htopF Surface.code.body (D.distance + 2) rho E)
    (wHrightF : DerivWF hrightF Surface.code.body (D.distance + 2) rho E)
    (wHleftF : DerivWF hleftF Surface.code.body (D.distance + 2) rho E)
    (wHstrip : DerivWF hstrip Surface.code.body (D.distance + 2) rho E)
    (wHadj : DerivWF hadj Surface.code.body (D.distance + 2) rho E)
    (wHRange : DerivWF hRange Surface.code.body (D.distance + 2) rho E)
    (wHBottomBand : DerivWF hBottomBand Surface.code.body (D.distance + 2) rho E)
    (wHBulkBand : DerivWF hBulkBand Surface.code.body (D.distance + 2) rho E)
    (wHPin : DerivWF hPin Surface.code.body (D.distance + 2) rho E)
    (wHEA0 : DerivWF hEA0 Surface.code.body (D.distance + 2) rho E)
    (wHEA1 : DerivWF hEA1 Surface.code.body (D.distance + 2) rho E)
    (wHEB0 : DerivWF hEB0 Surface.code.body (D.distance + 2) rho E)
    (wHEB1 : DerivWF hEB1 Surface.code.body (D.distance + 2) rho E)
    (hCtx : SFormula.ContextHolds Surface.code.body (D.distance + 2) rho E Γ) :
    DerivWF (commBottomBulk D hEntryA hEntryB hk1X hExcl1 hbulkF htopF hrightF hleftF hstrip
        hadj hRange hBottomBand hBulkBand hPin hEA0 hEA1 hEB0 hEB1)
      Surface.code.body (D.distance + 2) rho E := by
  unfold commBottomBulk
  have wRangeP := derivWF_mp (derivWF_mp (derivWF_mp (derivWF_mp (derivWF_mp wHRange wHbulkF) wHtopF) wHrightF) wHleftF) wHstrip
  have wBBP := derivWF_mp (derivWF_mp (derivWF_mp (derivWF_mp (derivWF_mp wHBottomBand wHbulkF) wHtopF) wHrightF) wHleftF) wHstrip
  have wKBP := derivWF_mp (derivWF_mp (derivWF_mp (derivWF_mp (derivWF_mp (derivWF_mp wHBulkBand wHbulkF) wHtopF) wHrightF) wHleftF) wHstrip) wHadj
  refine commBulkTopXZ_WF D (bbQ0 D) (bbQ1 D)
    (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
    (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
    wEntryA wEntryB wHk1X wHExcl1
    (derivWF_andElimLeft' wRangeP)
    (derivWF_andElimLeft' (derivWF_andElimRight' wRangeP))
    (derivWF_andElimRight' (derivWF_andElimRight' wRangeP))
    (derivWF_eqPauliTrans' wHEA0 (baseLeafBottomXS_WF _ (dP2 D) k1P (bbQ0 D) (dP2_pure D) (.var _)
      (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
      wHbulkF wHtopF wHrightF wHleftF (derivWF_andElimLeft' wBBP)))
    (derivWF_eqPauliTrans' wHEA1 (baseLeafBottomXS_WF _ (dP2 D) k1P (bbQ1 D) (dP2_pure D) (.var _)
      (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
      wHbulkF wHtopF wHrightF wHleftF (derivWF_andElimRight' wBBP)))
    (derivWF_eqPauliTrans' wHEB0 (baseLeafZS_WF _ (dP2 D) k2P (bbQ0 D) (dP2_pure D) (.var _)
      (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
      (derivWF_andElimLeft' wKBP)
      (derivWF_andElimLeft' (derivWF_andElimRight' (derivWF_andElimRight' wKBP)))
      (derivWF_andElimLeft' (derivWF_andElimRight' wKBP))))
    (derivWF_eqPauliTrans' wHEB1 (baseLeafZS_WF _ (dP2 D) k2P (bbQ1 D) (dP2_pure D) (.var _)
      (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
      (derivWF_andElimLeft' wKBP)
      (derivWF_andElimRight' (derivWF_andElimRight' (derivWF_andElimRight' wKBP)))
      (derivWF_andElimLeft' (derivWF_andElimRight' wKBP))))
    ?wHXZpin hCtx
  intro x Δ' lift liftWF hX wX hZ wZ
  have wbulkFΔ := liftWF (cw3_WF (derivWF_weakenFresh wHbulkF))
  have wtopFΔ := liftWF (cw3_WF (derivWF_weakenFresh wHtopF))
  have wrightFΔ := liftWF (cw3_WF (derivWF_weakenFresh wHrightF))
  have wleftFΔ := liftWF (cw3_WF (derivWF_weakenFresh wHleftF))
  have wstripΔ := liftWF (cw3_WF (derivWF_weakenFresh wHstrip))
  have wadjΔ := liftWF (cw3_WF (derivWF_weakenFresh wHadj))
  have wBulkK2Δ := liftWF (cw3_WF (derivWF_weakenFresh (derivWF_andElimLeft' wKBP)))
  have wPinΔ := liftWF (cw3_WF (derivWF_weakenFresh wHPin))
  have wBotB := bbBottomBandFromX_WF D wbulkFΔ wtopFΔ wrightFΔ wleftFΔ wX
  have wBulkB := bbBulkBandFromZ_WF D wBulkK2Δ wZ
  refine derivWF_orElim
    (bbPinAt_WF D wPinΔ (liftWF (derivWF_hyp _)) wbulkFΔ wtopFΔ wrightFΔ wleftFΔ wstripΔ wadjΔ wBotB wBulkB) ?_ ?_
  · exact derivWF_botElim (derivWF_notElim (derivWF_hyp _) (cw1_WF (liftWF (derivWF_hyp _))))
  · exact derivWF_botElim (derivWF_notElim (derivWF_hyp _) (cw1_WF (liftWF (derivWF_hyp _))))

/-! ## Bulk–boundary: BULK-RIGHT combo (ROLE-SWAPPED: rowA=bulk X, rowB=right boundary Z) -/

theorem brPinAt_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)}
    {hW : SFormula.Deriv Δ (brPinF D).weaken}
    {hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken)}
    {hBulkF : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b false))}
    {hTopF : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA (dP3 D) k2P3)) (SC.b false))}
    {hRightC : SFormula.Deriv Δ (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k2P3)) (SC.b true))}
    {hAdj : SFormula.Deriv Δ (.eqBool (SC.closed (.eqNat k1P3
      (.add (.mul (.mul (.natLit 2) (brR3 D)) (dm1TA (dP3 D)))
        (.sub (dm1TA (dP3 D)) (.natLit 1))))) (SC.b true))}
    {hBulkB : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true))}
    {hRightB : SFormula.Deriv Δ (.eqBool (SC.closed (rightBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))}
    {rho : Env 3} {E : PartialStabilizer}
    (wW : DerivWF hW Surface.code.body (D.distance + 2) rho E)
    (wq : DerivWF hq Surface.code.body (D.distance + 2) rho E)
    (wBulkF : DerivWF hBulkF Surface.code.body (D.distance + 2) rho E)
    (wTopF : DerivWF hTopF Surface.code.body (D.distance + 2) rho E)
    (wRightC : DerivWF hRightC Surface.code.body (D.distance + 2) rho E)
    (wAdj : DerivWF hAdj Surface.code.body (D.distance + 2) rho E)
    (wBulkB : DerivWF hBulkB Surface.code.body (D.distance + 2) rho E)
    (wRightB : DerivWF hRightB Surface.code.body (D.distance + 2) rho E) :
    DerivWF (brPinAt D hW hq hBulkF hTopF hRightC hAdj hBulkB hRightB)
      Surface.code.body (D.distance + 2) rho E := by
  unfold brPinAt
  comm_deriv_wf

theorem brBulkBandFromX_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)}
    {hBulkT : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b true))}
    {hLeafX : SFormula.Deriv Δ (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3)) (SC.p Pauli.X))}
    {rho : Env 3} {E : PartialStabilizer}
    (wBulkT : DerivWF hBulkT Surface.code.body (D.distance + 2) rho E)
    (wLeafX : DerivWF hLeafX Surface.code.body (D.distance + 2) rho E) :
    DerivWF (brBulkBandFromX D hBulkT hLeafX) Surface.code.body (D.distance + 2) rho E := by
  unfold brBulkBandFromX
  refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor)))
    (derivWF_hyp _) ?_
  refine derivWF_botElim (derivWF_notElim ?_ (derivWF_pauliNeqLit _ _ (by decide)))
  exact derivWF_eqPauliTrans' (derivWF_eqPauliSymm' (cw1_WF wLeafX))
    (baseLeafBulkIS_WF _ (dP3 D) k1P3 qP3 (dP3_pure D) (.var _) (.var _) (cw1_WF wBulkT) (derivWF_hyp _))

theorem brRightBandFromZ_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)}
    {hBulkF : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b false))}
    {hTopF : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA (dP3 D) k2P3)) (SC.b false))}
    {hRightC : SFormula.Deriv Δ (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k2P3)) (SC.b true))}
    {hLeafZ : SFormula.Deriv Δ (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p Pauli.Z))}
    {rho : Env 3} {E : PartialStabilizer}
    (wBulkF : DerivWF hBulkF Surface.code.body (D.distance + 2) rho E)
    (wTopF : DerivWF hTopF Surface.code.body (D.distance + 2) rho E)
    (wRightC : DerivWF hRightC Surface.code.body (D.distance + 2) rho E)
    (wLeafZ : DerivWF hLeafZ Surface.code.body (D.distance + 2) rho E) :
    DerivWF (brRightBandFromZ D hBulkF hTopF hRightC hLeafZ) Surface.code.body (D.distance + 2) rho E := by
  unfold brRightBandFromZ
  refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor)))
    (derivWF_hyp _) ?_
  refine derivWF_botElim (derivWF_notElim ?_ (derivWF_pauliNeqLit _ _ (by decide)))
  exact derivWF_eqPauliTrans' (derivWF_eqPauliSymm' (cw1_WF wLeafZ))
    (baseLeafRightIS_WF _ (dP3 D) k2P3 qP3 (dP3_pure D) (.var _) (.var _)
      (cw1_WF wBulkF) (cw1_WF wTopF) (cw1_WF wRightC) (derivWF_hyp _))

theorem commRightBulk_WF (D : OddSurfaceDistance) {Γ : List (SFormula 2)}
    {hEntryA : SFormula.Deriv Γ (entryAQuant D)} {hEntryB : SFormula.Deriv Γ (entryBQuant D)}
    {hk1X : SFormula.Deriv Γ (k1IsX D true)} {hExcl1 : SFormula.Deriv Γ (typeExclF D k1P)}
    {hbulkFk2 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false))}
    {htopFk2 : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false))}
    {hrightCk2 : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b true))}
    {hadj : SFormula.Deriv Γ (brAdjF D)} {hRange : SFormula.Deriv Γ (brRangePackF D)}
    {hRightBand : SFormula.Deriv Γ (brRightBandPackF D)} {hBulkBand : SFormula.Deriv Γ (brBulkBandPackF D)}
    {hPin : SFormula.Deriv Γ (brPinF D)}
    {hEA0 : SFormula.Deriv Γ (entryAAtQF D (brQ0 D))} {hEA1 : SFormula.Deriv Γ (entryAAtQF D (brQ1 D))}
    {hEB0 : SFormula.Deriv Γ (entryBAtQF D (brQ0 D))} {hEB1 : SFormula.Deriv Γ (entryBAtQF D (brQ1 D))}
    {rho : Env 2} {E : PartialStabilizer}
    (wEntryA : DerivWF hEntryA Surface.code.body (D.distance + 2) rho E)
    (wEntryB : DerivWF hEntryB Surface.code.body (D.distance + 2) rho E)
    (wHk1X : DerivWF hk1X Surface.code.body (D.distance + 2) rho E)
    (wHExcl1 : DerivWF hExcl1 Surface.code.body (D.distance + 2) rho E)
    (wHbulkFk2 : DerivWF hbulkFk2 Surface.code.body (D.distance + 2) rho E)
    (wHtopFk2 : DerivWF htopFk2 Surface.code.body (D.distance + 2) rho E)
    (wHrightCk2 : DerivWF hrightCk2 Surface.code.body (D.distance + 2) rho E)
    (wHadj : DerivWF hadj Surface.code.body (D.distance + 2) rho E)
    (wHRange : DerivWF hRange Surface.code.body (D.distance + 2) rho E)
    (wHRightBand : DerivWF hRightBand Surface.code.body (D.distance + 2) rho E)
    (wHBulkBand : DerivWF hBulkBand Surface.code.body (D.distance + 2) rho E)
    (wHPin : DerivWF hPin Surface.code.body (D.distance + 2) rho E)
    (wHEA0 : DerivWF hEA0 Surface.code.body (D.distance + 2) rho E)
    (wHEA1 : DerivWF hEA1 Surface.code.body (D.distance + 2) rho E)
    (wHEB0 : DerivWF hEB0 Surface.code.body (D.distance + 2) rho E)
    (wHEB1 : DerivWF hEB1 Surface.code.body (D.distance + 2) rho E)
    (hCtx : SFormula.ContextHolds Surface.code.body (D.distance + 2) rho E Γ) :
    DerivWF (commRightBulk D hEntryA hEntryB hk1X hExcl1 hbulkFk2 htopFk2 hrightCk2 hadj
        hRange hRightBand hBulkBand hPin hEA0 hEA1 hEB0 hEB1)
      Surface.code.body (D.distance + 2) rho E := by
  unfold commRightBulk
  have wRangeP := derivWF_mp (derivWF_mp (derivWF_mp wHRange wHbulkFk2) wHtopFk2) wHrightCk2
  have wRBP := derivWF_mp (derivWF_mp (derivWF_mp wHRightBand wHbulkFk2) wHtopFk2) wHrightCk2
  have wKBP := derivWF_mp (derivWF_mp (derivWF_mp (derivWF_mp wHBulkBand wHbulkFk2) wHtopFk2) wHrightCk2) wHadj
  refine commBulkTopXZ_WF D (brQ0 D) (brQ1 D)
    (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
    (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
    wEntryA wEntryB wHk1X wHExcl1
    (derivWF_andElimLeft' wRangeP)
    (derivWF_andElimLeft' (derivWF_andElimRight' wRangeP))
    (derivWF_andElimRight' (derivWF_andElimRight' wRangeP))
    (derivWF_eqPauliTrans' wHEA0 (baseLeafXS_WF _ (dP2 D) k1P (brQ0 D) (dP2_pure D) (.var _)
      (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
      (derivWF_andElimLeft' wKBP)
      (derivWF_andElimLeft' (derivWF_andElimRight' (derivWF_andElimRight' wKBP)))
      (derivWF_andElimLeft' (derivWF_andElimRight' wKBP))))
    (derivWF_eqPauliTrans' wHEA1 (baseLeafXS_WF _ (dP2 D) k1P (brQ1 D) (dP2_pure D) (.var _)
      (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
      (derivWF_andElimLeft' wKBP)
      (derivWF_andElimRight' (derivWF_andElimRight' (derivWF_andElimRight' wKBP)))
      (derivWF_andElimLeft' (derivWF_andElimRight' wKBP))))
    (derivWF_eqPauliTrans' wHEB0 (baseLeafRightZS_WF _ (dP2 D) k2P (brQ0 D) (dP2_pure D) (.var _)
      (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
      wHbulkFk2 wHtopFk2 wHrightCk2 (derivWF_andElimLeft' wRBP)))
    (derivWF_eqPauliTrans' wHEB1 (baseLeafRightZS_WF _ (dP2 D) k2P (brQ1 D) (dP2_pure D) (.var _)
      (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
      wHbulkFk2 wHtopFk2 wHrightCk2 (derivWF_andElimRight' wRBP)))
    ?wHXZpin hCtx
  intro x Δ' lift liftWF hX wX hZ wZ
  have wbulkFk2Δ := liftWF (cw3_WF (derivWF_weakenFresh wHbulkFk2))
  have wtopFk2Δ := liftWF (cw3_WF (derivWF_weakenFresh wHtopFk2))
  have wrightCk2Δ := liftWF (cw3_WF (derivWF_weakenFresh wHrightCk2))
  have wadjΔ := liftWF (cw3_WF (derivWF_weakenFresh wHadj))
  have wBulkK1Δ := liftWF (cw3_WF (derivWF_weakenFresh (derivWF_andElimLeft' wKBP)))
  have wPinΔ := liftWF (cw3_WF (derivWF_weakenFresh wHPin))
  have wBulkB := brBulkBandFromX_WF D wBulkK1Δ wX
  have wRightB := brRightBandFromZ_WF D wbulkFk2Δ wtopFk2Δ wrightCk2Δ wZ
  refine derivWF_orElim
    (brPinAt_WF D wPinΔ (liftWF (derivWF_hyp _)) wbulkFk2Δ wtopFk2Δ wrightCk2Δ wadjΔ wBulkB wRightB) ?_ ?_
  · exact derivWF_botElim (derivWF_notElim (derivWF_hyp _) (cw1_WF (liftWF (derivWF_hyp _))))
  · exact derivWF_botElim (derivWF_notElim (derivWF_hyp _) (cw1_WF (liftWF (derivWF_hyp _))))

/-! ## Bulk–boundary: BULK-LEFT combo (twin of right + extra ¬rightClass; baseLeafLeftZS) -/

theorem blPinAt_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)}
    {hW : SFormula.Deriv Δ (blPinF D).weaken}
    {hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken)}
    {hBulkF : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b false))}
    {hTopF : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA (dP3 D) k2P3)) (SC.b false))}
    {hRightF : SFormula.Deriv Δ (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k2P3)) (SC.b false))}
    {hLeftC : SFormula.Deriv Δ (.eqBool (SC.closed (leftClassGuardTA (dP3 D) k2P3)) (SC.b true))}
    {hAdj : SFormula.Deriv Δ (.eqBool (SC.closed (.eqNat k1P3
      (.mul (.add (.mul (.natLit 2) (blL3 D)) (.natLit 1)) (dm1TA (dP3 D))))) (SC.b true))}
    {hLeftB : SFormula.Deriv Δ (.eqBool (SC.closed (leftBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))}
    {hBulkB : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true))}
    {rho : Env 3} {E : PartialStabilizer}
    (wW : DerivWF hW Surface.code.body (D.distance + 2) rho E)
    (wq : DerivWF hq Surface.code.body (D.distance + 2) rho E)
    (wBulkF : DerivWF hBulkF Surface.code.body (D.distance + 2) rho E)
    (wTopF : DerivWF hTopF Surface.code.body (D.distance + 2) rho E)
    (wRightF : DerivWF hRightF Surface.code.body (D.distance + 2) rho E)
    (wLeftC : DerivWF hLeftC Surface.code.body (D.distance + 2) rho E)
    (wAdj : DerivWF hAdj Surface.code.body (D.distance + 2) rho E)
    (wLeftB : DerivWF hLeftB Surface.code.body (D.distance + 2) rho E)
    (wBulkB : DerivWF hBulkB Surface.code.body (D.distance + 2) rho E) :
    DerivWF (blPinAt D hW hq hBulkF hTopF hRightF hLeftC hAdj hLeftB hBulkB)
      Surface.code.body (D.distance + 2) rho E := by
  unfold blPinAt
  comm_deriv_wf

theorem blBulkBandFromX_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)}
    {hBulkT : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b true))}
    {hLeafX : SFormula.Deriv Δ (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3)) (SC.p Pauli.X))}
    {rho : Env 3} {E : PartialStabilizer}
    (wBulkT : DerivWF hBulkT Surface.code.body (D.distance + 2) rho E)
    (wLeafX : DerivWF hLeafX Surface.code.body (D.distance + 2) rho E) :
    DerivWF (blBulkBandFromX D hBulkT hLeafX) Surface.code.body (D.distance + 2) rho E := by
  unfold blBulkBandFromX
  refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor)))
    (derivWF_hyp _) ?_
  refine derivWF_botElim (derivWF_notElim ?_ (derivWF_pauliNeqLit _ _ (by decide)))
  exact derivWF_eqPauliTrans' (derivWF_eqPauliSymm' (cw1_WF wLeafX))
    (baseLeafBulkIS_WF _ (dP3 D) k1P3 qP3 (dP3_pure D) (.var _) (.var _) (cw1_WF wBulkT) (derivWF_hyp _))

theorem blLeftBandFromZ_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)}
    {hBulkF : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b false))}
    {hTopF : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA (dP3 D) k2P3)) (SC.b false))}
    {hRightF : SFormula.Deriv Δ (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k2P3)) (SC.b false))}
    {hLeftC : SFormula.Deriv Δ (.eqBool (SC.closed (leftClassGuardTA (dP3 D) k2P3)) (SC.b true))}
    {hLeafZ : SFormula.Deriv Δ (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p Pauli.Z))}
    {rho : Env 3} {E : PartialStabilizer}
    (wBulkF : DerivWF hBulkF Surface.code.body (D.distance + 2) rho E)
    (wTopF : DerivWF hTopF Surface.code.body (D.distance + 2) rho E)
    (wRightF : DerivWF hRightF Surface.code.body (D.distance + 2) rho E)
    (wLeftC : DerivWF hLeftC Surface.code.body (D.distance + 2) rho E)
    (wLeafZ : DerivWF hLeafZ Surface.code.body (D.distance + 2) rho E) :
    DerivWF (blLeftBandFromZ D hBulkF hTopF hRightF hLeftC hLeafZ) Surface.code.body (D.distance + 2) rho E := by
  unfold blLeftBandFromZ
  refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor)))
    (derivWF_hyp _) ?_
  refine derivWF_botElim (derivWF_notElim ?_ (derivWF_pauliNeqLit _ _ (by decide)))
  exact derivWF_eqPauliTrans' (derivWF_eqPauliSymm' (cw1_WF wLeafZ))
    (baseLeafLeftIS_WF _ (dP3 D) k2P3 qP3 (dP3_pure D) (.var _) (.var _)
      (cw1_WF wBulkF) (cw1_WF wTopF) (cw1_WF wRightF) (cw1_WF wLeftC) (derivWF_hyp _))

theorem commLeftBulk_WF (D : OddSurfaceDistance) {Γ : List (SFormula 2)}
    {hEntryA : SFormula.Deriv Γ (entryAQuant D)} {hEntryB : SFormula.Deriv Γ (entryBQuant D)}
    {hk1X : SFormula.Deriv Γ (k1IsX D true)} {hExcl1 : SFormula.Deriv Γ (typeExclF D k1P)}
    {hbulkFk2 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false))}
    {htopFk2 : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false))}
    {hrightFk2 : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false))}
    {hleftCk2 : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b true))}
    {hadj : SFormula.Deriv Γ (blAdjF D)} {hRange : SFormula.Deriv Γ (blRangePackF D)}
    {hLeftBand : SFormula.Deriv Γ (blLeftBandPackF D)} {hBulkBand : SFormula.Deriv Γ (blBulkBandPackF D)}
    {hPin : SFormula.Deriv Γ (blPinF D)}
    {hEA0 : SFormula.Deriv Γ (entryAAtQF D (blQ0 D))} {hEA1 : SFormula.Deriv Γ (entryAAtQF D (blQ1 D))}
    {hEB0 : SFormula.Deriv Γ (entryBAtQF D (blQ0 D))} {hEB1 : SFormula.Deriv Γ (entryBAtQF D (blQ1 D))}
    {rho : Env 2} {E : PartialStabilizer}
    (wEntryA : DerivWF hEntryA Surface.code.body (D.distance + 2) rho E)
    (wEntryB : DerivWF hEntryB Surface.code.body (D.distance + 2) rho E)
    (wHk1X : DerivWF hk1X Surface.code.body (D.distance + 2) rho E)
    (wHExcl1 : DerivWF hExcl1 Surface.code.body (D.distance + 2) rho E)
    (wHbulkFk2 : DerivWF hbulkFk2 Surface.code.body (D.distance + 2) rho E)
    (wHtopFk2 : DerivWF htopFk2 Surface.code.body (D.distance + 2) rho E)
    (wHrightFk2 : DerivWF hrightFk2 Surface.code.body (D.distance + 2) rho E)
    (wHleftCk2 : DerivWF hleftCk2 Surface.code.body (D.distance + 2) rho E)
    (wHadj : DerivWF hadj Surface.code.body (D.distance + 2) rho E)
    (wHRange : DerivWF hRange Surface.code.body (D.distance + 2) rho E)
    (wHLeftBand : DerivWF hLeftBand Surface.code.body (D.distance + 2) rho E)
    (wHBulkBand : DerivWF hBulkBand Surface.code.body (D.distance + 2) rho E)
    (wHPin : DerivWF hPin Surface.code.body (D.distance + 2) rho E)
    (wHEA0 : DerivWF hEA0 Surface.code.body (D.distance + 2) rho E)
    (wHEA1 : DerivWF hEA1 Surface.code.body (D.distance + 2) rho E)
    (wHEB0 : DerivWF hEB0 Surface.code.body (D.distance + 2) rho E)
    (wHEB1 : DerivWF hEB1 Surface.code.body (D.distance + 2) rho E)
    (hCtx : SFormula.ContextHolds Surface.code.body (D.distance + 2) rho E Γ) :
    DerivWF (commLeftBulk D hEntryA hEntryB hk1X hExcl1 hbulkFk2 htopFk2 hrightFk2 hleftCk2 hadj
        hRange hLeftBand hBulkBand hPin hEA0 hEA1 hEB0 hEB1)
      Surface.code.body (D.distance + 2) rho E := by
  unfold commLeftBulk
  have wRangeP := derivWF_mp (derivWF_mp (derivWF_mp (derivWF_mp wHRange wHbulkFk2) wHtopFk2) wHrightFk2) wHleftCk2
  have wLBP := derivWF_mp (derivWF_mp (derivWF_mp (derivWF_mp wHLeftBand wHbulkFk2) wHtopFk2) wHrightFk2) wHleftCk2
  have wKBP := derivWF_mp (derivWF_mp (derivWF_mp (derivWF_mp (derivWF_mp wHBulkBand wHbulkFk2) wHtopFk2) wHrightFk2) wHleftCk2) wHadj
  refine commBulkTopXZ_WF D (blQ0 D) (blQ1 D)
    (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
    (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
    wEntryA wEntryB wHk1X wHExcl1
    (derivWF_andElimLeft' wRangeP)
    (derivWF_andElimLeft' (derivWF_andElimRight' wRangeP))
    (derivWF_andElimRight' (derivWF_andElimRight' wRangeP))
    (derivWF_eqPauliTrans' wHEA0 (baseLeafXS_WF _ (dP2 D) k1P (blQ0 D) (dP2_pure D) (.var _)
      (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
      (derivWF_andElimLeft' wKBP)
      (derivWF_andElimLeft' (derivWF_andElimRight' (derivWF_andElimRight' wKBP)))
      (derivWF_andElimLeft' (derivWF_andElimRight' wKBP))))
    (derivWF_eqPauliTrans' wHEA1 (baseLeafXS_WF _ (dP2 D) k1P (blQ1 D) (dP2_pure D) (.var _)
      (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
      (derivWF_andElimLeft' wKBP)
      (derivWF_andElimRight' (derivWF_andElimRight' (derivWF_andElimRight' wKBP)))
      (derivWF_andElimLeft' (derivWF_andElimRight' wKBP))))
    (derivWF_eqPauliTrans' wHEB0 (baseLeafLeftZS_WF _ (dP2 D) k2P (blQ0 D) (dP2_pure D) (.var _)
      (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
      wHbulkFk2 wHtopFk2 wHrightFk2 wHleftCk2 (derivWF_andElimLeft' wLBP)))
    (derivWF_eqPauliTrans' wHEB1 (baseLeafLeftZS_WF _ (dP2 D) k2P (blQ1 D) (dP2_pure D) (.var _)
      (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
      wHbulkFk2 wHtopFk2 wHrightFk2 wHleftCk2 (derivWF_andElimRight' wLBP)))
    ?wHXZpin hCtx
  intro x Δ' lift liftWF hX wX hZ wZ
  have wbulkFk2Δ := liftWF (cw3_WF (derivWF_weakenFresh wHbulkFk2))
  have wtopFk2Δ := liftWF (cw3_WF (derivWF_weakenFresh wHtopFk2))
  have wrightFk2Δ := liftWF (cw3_WF (derivWF_weakenFresh wHrightFk2))
  have wleftCk2Δ := liftWF (cw3_WF (derivWF_weakenFresh wHleftCk2))
  have wadjΔ := liftWF (cw3_WF (derivWF_weakenFresh wHadj))
  have wBulkK1Δ := liftWF (cw3_WF (derivWF_weakenFresh (derivWF_andElimLeft' wKBP)))
  have wPinΔ := liftWF (cw3_WF (derivWF_weakenFresh wHPin))
  have wBulkB := blBulkBandFromX_WF D wBulkK1Δ wX
  have wLeftB := blLeftBandFromZ_WF D wbulkFk2Δ wtopFk2Δ wrightFk2Δ wleftCk2Δ wZ
  refine derivWF_orElim
    (blPinAt_WF D wPinΔ (liftWF (derivWF_hyp _)) wbulkFk2Δ wtopFk2Δ wrightFk2Δ wleftCk2Δ wadjΔ wLeftB wBulkB) ?_ ?_
  · exact derivWF_botElim (derivWF_notElim (derivWF_hyp _) (cw1_WF (liftWF (derivWF_hyp _))))
  · exact derivWF_botElim (derivWF_notElim (derivWF_hyp _) (cw1_WF (liftWF (derivWF_hyp _))))

end QHL.CodeLang.Surface.Verify
