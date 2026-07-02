import QStab.QHL.Verify.SurfaceRowsCommuteDefined.TypeClosers

/-!
# Rows-commute definedness — BulkBulkCombos

The bulk–bulk overlap closer WFs: horizontal, and its row-transpose vertical combo.
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

set_option maxHeartbeats 1600000

/-! ## Bulk–Bulk-horiz per-combo combinator WFs (reuse: comm_deriv_wf + baseLeafBulkIS_WF) -/

theorem bhPinAt_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)}
    {hW : SFormula.Deriv Δ (bhPinF D).weaken}
    {hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken)}
    {hBulkK1 : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b true))}
    {hRow : SFormula.Deriv Δ (.eqBool (SC.closed (.ltNat
      (.add (.mod k1P3 (dm1TA (dP3 D))) (.natLit 1)) (dm1TA (dP3 D)))) (SC.b true))}
    {hAdj : SFormula.Deriv Δ (.eqBool (SC.closed (.eqNat k2P3 (.add k1P3 (.natLit 1)))) (SC.b true))}
    {hBandK1 : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true))}
    {hBandK2 : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))}
    {rho : Env 3} {E : PartialStabilizer}
    (wW : DerivWF hW Surface.code.body (D.distance + 2) rho E)
    (wq : DerivWF hq Surface.code.body (D.distance + 2) rho E)
    (wBulkK1 : DerivWF hBulkK1 Surface.code.body (D.distance + 2) rho E)
    (wRow : DerivWF hRow Surface.code.body (D.distance + 2) rho E)
    (wAdj : DerivWF hAdj Surface.code.body (D.distance + 2) rho E)
    (wBandK1 : DerivWF hBandK1 Surface.code.body (D.distance + 2) rho E)
    (wBandK2 : DerivWF hBandK2 Surface.code.body (D.distance + 2) rho E) :
    DerivWF (bhPinAt D hW hq hBulkK1 hRow hAdj hBandK1 hBandK2)
      Surface.code.body (D.distance + 2) rho E := by
  unfold bhPinAt
  comm_deriv_wf

theorem bhBandK1FromX_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)}
    {hBulkT : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b true))}
    {hLeafX : SFormula.Deriv Δ (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3)) (SC.p Pauli.X))}
    {rho : Env 3} {E : PartialStabilizer}
    (wBulkT : DerivWF hBulkT Surface.code.body (D.distance + 2) rho E)
    (wLeafX : DerivWF hLeafX Surface.code.body (D.distance + 2) rho E) :
    DerivWF (bhBandK1FromX D hBulkT hLeafX) Surface.code.body (D.distance + 2) rho E := by
  unfold bhBandK1FromX
  refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor)))
    (derivWF_hyp _) ?_
  refine derivWF_botElim (derivWF_notElim ?_ (derivWF_pauliNeqLit _ _ (by decide)))
  exact derivWF_eqPauliTrans' (derivWF_eqPauliSymm' (cw1_WF wLeafX))
    (baseLeafBulkIS_WF _ (dP3 D) k1P3 qP3 (dP3_pure D) (.var _) (.var _) (cw1_WF wBulkT) (derivWF_hyp _))

theorem bhBandK2FromZ_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)}
    {hBulkT : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b true))}
    {hLeafZ : SFormula.Deriv Δ (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p Pauli.Z))}
    {rho : Env 3} {E : PartialStabilizer}
    (wBulkT : DerivWF hBulkT Surface.code.body (D.distance + 2) rho E)
    (wLeafZ : DerivWF hLeafZ Surface.code.body (D.distance + 2) rho E) :
    DerivWF (bhBandK2FromZ D hBulkT hLeafZ) Surface.code.body (D.distance + 2) rho E := by
  unfold bhBandK2FromZ
  refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor)))
    (derivWF_hyp _) ?_
  refine derivWF_botElim (derivWF_notElim ?_ (derivWF_pauliNeqLit _ _ (by decide)))
  exact derivWF_eqPauliTrans' (derivWF_eqPauliSymm' (cw1_WF wLeafZ))
    (baseLeafBulkIS_WF _ (dP3 D) k2P3 qP3 (dP3_pure D) (.var _) (.var _) (cw1_WF wBulkT) (derivWF_hyp _))

/-- Purity of the arity-2 distance term `dP2 D`. -/
def dP2_pure (D : OddSurfaceDistance) : SFormula.PureNatTerm (dP2 D) := by
  unfold dP2
  repeat (first | exact SFormula.PureNatTerm.lift _ | exact SFormula.PureNatTerm.natLit _ | constructor)

/-- WF of the bulk–bulk-horizontal combo closer.  `commBulkTopXZ_WF` + per-q leaf facts
(`baseLeafXS_WF`/`baseLeafZS_WF`) + the pin (`bhPinAt_WF`/`bhBandK1FromX_WF`/`bhBandK2FromZ_WF`). -/
theorem commBulkBulkHoriz_WF (D : OddSurfaceDistance) {Γ : List (SFormula 2)}
    {hEntryA : SFormula.Deriv Γ (entryAQuant D)} {hEntryB : SFormula.Deriv Γ (entryBQuant D)}
    {hk1X : SFormula.Deriv Γ (k1IsX D true)} {hExcl1 : SFormula.Deriv Γ (typeExclF D k1P)}
    {hBulkK1 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true))}
    {hKindK1 : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k1P)) (SC.b false))}
    {hBulkK2 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true))}
    {hKindK2 : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k2P)) (SC.b true))}
    {hadj : SFormula.Deriv Γ (bhAdjF D)} {hrow : SFormula.Deriv Γ (bhRowF D)}
    {hRange : SFormula.Deriv Γ (bhRangePackF D)}
    {hBandK1 : SFormula.Deriv Γ (bhBandK1PackF D)} {hBandK2 : SFormula.Deriv Γ (bhBandK2PackF D)}
    {hPin : SFormula.Deriv Γ (bhPinF D)}
    {hEA0 : SFormula.Deriv Γ (entryAAtQF D (bhQ0 D))} {hEA1 : SFormula.Deriv Γ (entryAAtQF D (bhQ1 D))}
    {hEB0 : SFormula.Deriv Γ (entryBAtQF D (bhQ0 D))} {hEB1 : SFormula.Deriv Γ (entryBAtQF D (bhQ1 D))}
    {rho : Env 2} {E : PartialStabilizer}
    (wEntryA : DerivWF hEntryA Surface.code.body (D.distance + 2) rho E)
    (wEntryB : DerivWF hEntryB Surface.code.body (D.distance + 2) rho E)
    (wHk1X : DerivWF hk1X Surface.code.body (D.distance + 2) rho E)
    (wHExcl1 : DerivWF hExcl1 Surface.code.body (D.distance + 2) rho E)
    (wHBulkK1 : DerivWF hBulkK1 Surface.code.body (D.distance + 2) rho E)
    (wHKindK1 : DerivWF hKindK1 Surface.code.body (D.distance + 2) rho E)
    (wHBulkK2 : DerivWF hBulkK2 Surface.code.body (D.distance + 2) rho E)
    (wHKindK2 : DerivWF hKindK2 Surface.code.body (D.distance + 2) rho E)
    (wHadj : DerivWF hadj Surface.code.body (D.distance + 2) rho E)
    (wHrow : DerivWF hrow Surface.code.body (D.distance + 2) rho E)
    (wHRange : DerivWF hRange Surface.code.body (D.distance + 2) rho E)
    (wHBandK1 : DerivWF hBandK1 Surface.code.body (D.distance + 2) rho E)
    (wHBandK2 : DerivWF hBandK2 Surface.code.body (D.distance + 2) rho E)
    (wHPin : DerivWF hPin Surface.code.body (D.distance + 2) rho E)
    (wHEA0 : DerivWF hEA0 Surface.code.body (D.distance + 2) rho E)
    (wHEA1 : DerivWF hEA1 Surface.code.body (D.distance + 2) rho E)
    (wHEB0 : DerivWF hEB0 Surface.code.body (D.distance + 2) rho E)
    (wHEB1 : DerivWF hEB1 Surface.code.body (D.distance + 2) rho E)
    (hCtx : SFormula.ContextHolds Surface.code.body (D.distance + 2) rho E Γ) :
    DerivWF (commBulkBulkHoriz D hEntryA hEntryB hk1X hExcl1 hBulkK1 hKindK1 hBulkK2 hKindK2
        hadj hrow hRange hBandK1 hBandK2 hPin hEA0 hEA1 hEB0 hEB1)
      Surface.code.body (D.distance + 2) rho E := by
  unfold commBulkBulkHoriz
  have wRangeP := derivWF_mp (derivWF_mp wHRange wHBulkK1) wHrow
  have wK1BP := derivWF_mp (derivWF_mp wHBandK1 wHBulkK1) wHrow
  have wK2BP := derivWF_mp (derivWF_mp (derivWF_mp wHBandK2 wHBulkK1) wHrow) wHadj
  refine commBulkTopXZ_WF D (bhQ0 D) (bhQ1 D)
    (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
    (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
    wEntryA wEntryB wHk1X wHExcl1
    (derivWF_andElimLeft' wRangeP)
    (derivWF_andElimLeft' (derivWF_andElimRight' wRangeP))
    (derivWF_andElimRight' (derivWF_andElimRight' wRangeP))
    (derivWF_eqPauliTrans' wHEA0 (baseLeafXS_WF _ (dP2 D) k1P (bhQ0 D) (dP2_pure D) (.var _)
      (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
      wHBulkK1 (derivWF_andElimLeft' wK1BP) wHKindK1))
    (derivWF_eqPauliTrans' wHEA1 (baseLeafXS_WF _ (dP2 D) k1P (bhQ1 D) (dP2_pure D) (.var _)
      (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
      wHBulkK1 (derivWF_andElimRight' wK1BP) wHKindK1))
    (derivWF_eqPauliTrans' wHEB0 (baseLeafZS_WF _ (dP2 D) k2P (bhQ0 D) (dP2_pure D) (.var _)
      (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
      wHBulkK2 (derivWF_andElimLeft' wK2BP) wHKindK2))
    (derivWF_eqPauliTrans' wHEB1 (baseLeafZS_WF _ (dP2 D) k2P (bhQ1 D) (dP2_pure D) (.var _)
      (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
      wHBulkK2 (derivWF_andElimRight' wK2BP) wHKindK2))
    ?wHXZpin hCtx
  intro x Δ' lift liftWF hX wX hZ wZ
  have wBulkK1Δ := liftWF (cw3_WF (derivWF_weakenFresh wHBulkK1))
  have wBulkK2Δ := liftWF (cw3_WF (derivWF_weakenFresh wHBulkK2))
  have wrowΔ := liftWF (cw3_WF (derivWF_weakenFresh wHrow))
  have wadjΔ := liftWF (cw3_WF (derivWF_weakenFresh wHadj))
  have wPinΔ := liftWF (cw3_WF (derivWF_weakenFresh wHPin))
  have wBandK1B := bhBandK1FromX_WF D wBulkK1Δ wX
  have wBandK2B := bhBandK2FromZ_WF D wBulkK2Δ wZ
  refine derivWF_orElim
    (bhPinAt_WF D wPinΔ (liftWF (derivWF_hyp _)) wBulkK1Δ wrowΔ wadjΔ wBandK1B wBandK2B) ?_ ?_
  · exact derivWF_botElim (derivWF_notElim (derivWF_hyp _) (cw1_WF (liftWF (derivWF_hyp _))))
  · exact derivWF_botElim (derivWF_notElim (derivWF_hyp _) (cw1_WF (liftWF (derivWF_hyp _))))


/-! ## Bulk–Bulk-VERT combo (row-transpose of Horiz: bh→bv, mod→div, +1→+(d-1)) -/

theorem bvPinAt_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)}
    {hW : SFormula.Deriv Δ (bvPinF D).weaken}
    {hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken)}
    {hBulkK1 : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b true))}
    {hRow : SFormula.Deriv Δ (.eqBool (SC.closed (.ltNat
      (.add (.div k1P3 (dm1TA (dP3 D))) (.natLit 1)) (dm1TA (dP3 D)))) (SC.b true))}
    {hAdj : SFormula.Deriv Δ (.eqBool (SC.closed (.eqNat k2P3 (.add k1P3 (dm1TA (dP3 D))))) (SC.b true))}
    {hBandK1 : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true))}
    {hBandK2 : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))}
    {rho : Env 3} {E : PartialStabilizer}
    (wW : DerivWF hW Surface.code.body (D.distance + 2) rho E)
    (wq : DerivWF hq Surface.code.body (D.distance + 2) rho E)
    (wBulkK1 : DerivWF hBulkK1 Surface.code.body (D.distance + 2) rho E)
    (wRow : DerivWF hRow Surface.code.body (D.distance + 2) rho E)
    (wAdj : DerivWF hAdj Surface.code.body (D.distance + 2) rho E)
    (wBandK1 : DerivWF hBandK1 Surface.code.body (D.distance + 2) rho E)
    (wBandK2 : DerivWF hBandK2 Surface.code.body (D.distance + 2) rho E) :
    DerivWF (bvPinAt D hW hq hBulkK1 hRow hAdj hBandK1 hBandK2)
      Surface.code.body (D.distance + 2) rho E := by
  unfold bvPinAt
  comm_deriv_wf

theorem bvBandK1FromX_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)}
    {hBulkT : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b true))}
    {hLeafX : SFormula.Deriv Δ (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3)) (SC.p Pauli.X))}
    {rho : Env 3} {E : PartialStabilizer}
    (wBulkT : DerivWF hBulkT Surface.code.body (D.distance + 2) rho E)
    (wLeafX : DerivWF hLeafX Surface.code.body (D.distance + 2) rho E) :
    DerivWF (bvBandK1FromX D hBulkT hLeafX) Surface.code.body (D.distance + 2) rho E := by
  unfold bvBandK1FromX
  refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor)))
    (derivWF_hyp _) ?_
  refine derivWF_botElim (derivWF_notElim ?_ (derivWF_pauliNeqLit _ _ (by decide)))
  exact derivWF_eqPauliTrans' (derivWF_eqPauliSymm' (cw1_WF wLeafX))
    (baseLeafBulkIS_WF _ (dP3 D) k1P3 qP3 (dP3_pure D) (.var _) (.var _) (cw1_WF wBulkT) (derivWF_hyp _))

theorem bvBandK2FromZ_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)}
    {hBulkT : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b true))}
    {hLeafZ : SFormula.Deriv Δ (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p Pauli.Z))}
    {rho : Env 3} {E : PartialStabilizer}
    (wBulkT : DerivWF hBulkT Surface.code.body (D.distance + 2) rho E)
    (wLeafZ : DerivWF hLeafZ Surface.code.body (D.distance + 2) rho E) :
    DerivWF (bvBandK2FromZ D hBulkT hLeafZ) Surface.code.body (D.distance + 2) rho E := by
  unfold bvBandK2FromZ
  refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor)))
    (derivWF_hyp _) ?_
  refine derivWF_botElim (derivWF_notElim ?_ (derivWF_pauliNeqLit _ _ (by decide)))
  exact derivWF_eqPauliTrans' (derivWF_eqPauliSymm' (cw1_WF wLeafZ))
    (baseLeafBulkIS_WF _ (dP3 D) k2P3 qP3 (dP3_pure D) (.var _) (.var _) (cw1_WF wBulkT) (derivWF_hyp _))

theorem commBulkBulkVert_WF (D : OddSurfaceDistance) {Γ : List (SFormula 2)}
    {hEntryA : SFormula.Deriv Γ (entryAQuant D)} {hEntryB : SFormula.Deriv Γ (entryBQuant D)}
    {hk1X : SFormula.Deriv Γ (k1IsX D true)} {hExcl1 : SFormula.Deriv Γ (typeExclF D k1P)}
    {hBulkK1 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true))}
    {hKindK1 : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k1P)) (SC.b false))}
    {hBulkK2 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true))}
    {hKindK2 : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k2P)) (SC.b true))}
    {hadj : SFormula.Deriv Γ (bvAdjF D)} {hrow : SFormula.Deriv Γ (bvRowF D)}
    {hRange : SFormula.Deriv Γ (bvRangePackF D)}
    {hBandK1 : SFormula.Deriv Γ (bvBandK1PackF D)} {hBandK2 : SFormula.Deriv Γ (bvBandK2PackF D)}
    {hPin : SFormula.Deriv Γ (bvPinF D)}
    {hEA0 : SFormula.Deriv Γ (entryAAtQF D (bvQ0 D))} {hEA1 : SFormula.Deriv Γ (entryAAtQF D (bvQ1 D))}
    {hEB0 : SFormula.Deriv Γ (entryBAtQF D (bvQ0 D))} {hEB1 : SFormula.Deriv Γ (entryBAtQF D (bvQ1 D))}
    {rho : Env 2} {E : PartialStabilizer}
    (wEntryA : DerivWF hEntryA Surface.code.body (D.distance + 2) rho E)
    (wEntryB : DerivWF hEntryB Surface.code.body (D.distance + 2) rho E)
    (wHk1X : DerivWF hk1X Surface.code.body (D.distance + 2) rho E)
    (wHExcl1 : DerivWF hExcl1 Surface.code.body (D.distance + 2) rho E)
    (wHBulkK1 : DerivWF hBulkK1 Surface.code.body (D.distance + 2) rho E)
    (wHKindK1 : DerivWF hKindK1 Surface.code.body (D.distance + 2) rho E)
    (wHBulkK2 : DerivWF hBulkK2 Surface.code.body (D.distance + 2) rho E)
    (wHKindK2 : DerivWF hKindK2 Surface.code.body (D.distance + 2) rho E)
    (wHadj : DerivWF hadj Surface.code.body (D.distance + 2) rho E)
    (wHrow : DerivWF hrow Surface.code.body (D.distance + 2) rho E)
    (wHRange : DerivWF hRange Surface.code.body (D.distance + 2) rho E)
    (wHBandK1 : DerivWF hBandK1 Surface.code.body (D.distance + 2) rho E)
    (wHBandK2 : DerivWF hBandK2 Surface.code.body (D.distance + 2) rho E)
    (wHPin : DerivWF hPin Surface.code.body (D.distance + 2) rho E)
    (wHEA0 : DerivWF hEA0 Surface.code.body (D.distance + 2) rho E)
    (wHEA1 : DerivWF hEA1 Surface.code.body (D.distance + 2) rho E)
    (wHEB0 : DerivWF hEB0 Surface.code.body (D.distance + 2) rho E)
    (wHEB1 : DerivWF hEB1 Surface.code.body (D.distance + 2) rho E)
    (hCtx : SFormula.ContextHolds Surface.code.body (D.distance + 2) rho E Γ) :
    DerivWF (commBulkBulkVert D hEntryA hEntryB hk1X hExcl1 hBulkK1 hKindK1 hBulkK2 hKindK2
        hadj hrow hRange hBandK1 hBandK2 hPin hEA0 hEA1 hEB0 hEB1)
      Surface.code.body (D.distance + 2) rho E := by
  unfold commBulkBulkVert
  have wRangeP := derivWF_mp (derivWF_mp wHRange wHBulkK1) wHrow
  have wK1BP := derivWF_mp (derivWF_mp wHBandK1 wHBulkK1) wHrow
  have wK2BP := derivWF_mp (derivWF_mp (derivWF_mp wHBandK2 wHBulkK1) wHrow) wHadj
  refine commBulkTopXZ_WF D (bvQ0 D) (bvQ1 D)
    (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
    (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
    wEntryA wEntryB wHk1X wHExcl1
    (derivWF_andElimLeft' wRangeP)
    (derivWF_andElimLeft' (derivWF_andElimRight' wRangeP))
    (derivWF_andElimRight' (derivWF_andElimRight' wRangeP))
    (derivWF_eqPauliTrans' wHEA0 (baseLeafXS_WF _ (dP2 D) k1P (bvQ0 D) (dP2_pure D) (.var _)
      (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
      wHBulkK1 (derivWF_andElimLeft' wK1BP) wHKindK1))
    (derivWF_eqPauliTrans' wHEA1 (baseLeafXS_WF _ (dP2 D) k1P (bvQ1 D) (dP2_pure D) (.var _)
      (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
      wHBulkK1 (derivWF_andElimRight' wK1BP) wHKindK1))
    (derivWF_eqPauliTrans' wHEB0 (baseLeafZS_WF _ (dP2 D) k2P (bvQ0 D) (dP2_pure D) (.var _)
      (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
      wHBulkK2 (derivWF_andElimLeft' wK2BP) wHKindK2))
    (derivWF_eqPauliTrans' wHEB1 (baseLeafZS_WF _ (dP2 D) k2P (bvQ1 D) (dP2_pure D) (.var _)
      (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
      wHBulkK2 (derivWF_andElimRight' wK2BP) wHKindK2))
    ?wHXZpin hCtx
  intro x Δ' lift liftWF hX wX hZ wZ
  have wBulkK1Δ := liftWF (cw3_WF (derivWF_weakenFresh wHBulkK1))
  have wBulkK2Δ := liftWF (cw3_WF (derivWF_weakenFresh wHBulkK2))
  have wrowΔ := liftWF (cw3_WF (derivWF_weakenFresh wHrow))
  have wadjΔ := liftWF (cw3_WF (derivWF_weakenFresh wHadj))
  have wPinΔ := liftWF (cw3_WF (derivWF_weakenFresh wHPin))
  have wBandK1B := bvBandK1FromX_WF D wBulkK1Δ wX
  have wBandK2B := bvBandK2FromZ_WF D wBulkK2Δ wZ
  refine derivWF_orElim
    (bvPinAt_WF D wPinΔ (liftWF (derivWF_hyp _)) wBulkK1Δ wrowΔ wadjΔ wBandK1B wBandK2B) ?_ ?_
  · exact derivWF_botElim (derivWF_notElim (derivWF_hyp _) (cw1_WF (liftWF (derivWF_hyp _))))
  · exact derivWF_botElim (derivWF_notElim (derivWF_hyp _) (cw1_WF (liftWF (derivWF_hyp _))))

end QHL.CodeLang.Surface.Verify
