import QStab.QHL.Verify.SurfaceRowsCommuteDefined.NonAdjacentClosers

/-!
# Rows-commute definedness — DispatcherPrereqs

Dispatcher prerequisites (kind WFs + `ContextHolds` boolCases extension) and the missing
bulk-bulk twins (HorizL column-twin, VertU row-twin).
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

set_option maxHeartbeats 1600000

/-! ## Dispatcher prerequisites: kind WFs + ContextHolds boolCases extension -/

theorem dbbKindK1OfIsX_WF (D : OddSurfaceDistance) {Γ : List (SFormula 2)}
    {hExcl1 : SFormula.Deriv Γ (typeExclF D k1P)} {hk1X : SFormula.Deriv Γ (k1IsX D true)}
    {hBulkK1 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true))}
    {rho : Env 2} {E : PartialStabilizer}
    (wExcl1 : DerivWF hExcl1 Surface.code.body (D.distance + 2) rho E)
    (wk1X : DerivWF hk1X Surface.code.body (D.distance + 2) rho E)
    (wBulkK1 : DerivWF hBulkK1 Surface.code.body (D.distance + 2) rho E) :
    DerivWF (dbbKindK1OfIsX D hExcl1 hk1X hBulkK1) Surface.code.body (D.distance + 2) rho E := by
  unfold dbbKindK1OfIsX
  exact derivWF_mp (derivWF_mp (derivWF_andElimLeft' wExcl1) wk1X) wBulkK1

theorem dbbKindK2OfNotIsX_WF (D : OddSurfaceDistance) {Γ : List (SFormula 2)}
    {hExcl2 : SFormula.Deriv Γ (typeExclF D k2P)} {hk2Z : SFormula.Deriv Γ (k2IsX D false)}
    {hBulkK2 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true))}
    {rho : Env 2} {E : PartialStabilizer}
    (wExcl2 : DerivWF hExcl2 Surface.code.body (D.distance + 2) rho E)
    (wk2Z : DerivWF hk2Z Surface.code.body (D.distance + 2) rho E)
    (wBulkK2 : DerivWF hBulkK2 Surface.code.body (D.distance + 2) rho E) :
    DerivWF (dbbKindK2OfNotIsX D hExcl2 hk2Z hBulkK2) Surface.code.body (D.distance + 2) rho E := by
  unfold dbbKindK2OfNotIsX
  exact derivWF_mp (derivWF_mp (derivWF_andElimLeft'
    (derivWF_andElimRight' (derivWF_andElimRight' (derivWF_andElimRight' wExcl2)))) wk2Z) wBulkK2

theorem contextHolds_cons_eqBoolTrue {arity : Nat} {b : STerm arity .bool} {Γ : List (SFormula arity)}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (hCtx : SFormula.ContextHolds cb fuel rho E Γ) (hb : b.eval cb fuel rho E = some true) :
    SFormula.ContextHolds cb fuel rho E (SFormula.eqBool b (SC.b true) :: Γ) := by
  intro A hA
  rcases List.mem_cons.mp hA with rfl | hA'
  · simp [SFormula.eval, hb, SC.b, STerm.eval, Term.eval]
  · exact hCtx A hA'

theorem contextHolds_cons_eqBoolFalse {arity : Nat} {b : STerm arity .bool} {Γ : List (SFormula arity)}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (hCtx : SFormula.ContextHolds cb fuel rho E Γ) (hb : b.eval cb fuel rho E = some false) :
    SFormula.ContextHolds cb fuel rho E (SFormula.eqBool b (SC.b false) :: Γ) := by
  intro A hA
  rcases List.mem_cons.mp hA with rfl | hA'
  · simp [SFormula.eval, hb, SC.b, STerm.eval, Term.eval]
  · exact hCtx A hA'

/-! ## Missing bulk-bulk twins: HorizL (column-twin of Horiz) + VertU (row-twin of Vert) -/

theorem bhlPinAt_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)}
    {hW : SFormula.Deriv Δ (bhlPinF D).weaken}
    {hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken)}
    {hBulkK1 : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b true))}
    {hCol : SFormula.Deriv Δ (.eqBool (SC.closed (.ltNat (.natLit 0) (.mod k1P3 (dm1TA (dP3 D))))) (SC.b true))}
    {hAdj : SFormula.Deriv Δ (.eqBool (SC.closed (.eqNat k2P3 (.sub k1P3 (.natLit 1)))) (SC.b true))}
    {hBandK1 : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true))}
    {hBandK2 : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))}
    {rho : Env 3} {E : PartialStabilizer}
    (wW : DerivWF hW Surface.code.body (D.distance + 2) rho E)
    (wq : DerivWF hq Surface.code.body (D.distance + 2) rho E)
    (wBulkK1 : DerivWF hBulkK1 Surface.code.body (D.distance + 2) rho E)
    (wCol : DerivWF hCol Surface.code.body (D.distance + 2) rho E)
    (wAdj : DerivWF hAdj Surface.code.body (D.distance + 2) rho E)
    (wBandK1 : DerivWF hBandK1 Surface.code.body (D.distance + 2) rho E)
    (wBandK2 : DerivWF hBandK2 Surface.code.body (D.distance + 2) rho E) :
    DerivWF (bhlPinAt D hW hq hBulkK1 hCol hAdj hBandK1 hBandK2)
      Surface.code.body (D.distance + 2) rho E := by
  unfold bhlPinAt
  comm_deriv_wf

theorem bhlBandK1FromX_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)}
    {hBulkT : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b true))}
    {hLeafX : SFormula.Deriv Δ (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3)) (SC.p Pauli.X))}
    {rho : Env 3} {E : PartialStabilizer}
    (wBulkT : DerivWF hBulkT Surface.code.body (D.distance + 2) rho E)
    (wLeafX : DerivWF hLeafX Surface.code.body (D.distance + 2) rho E) :
    DerivWF (bhlBandK1FromX D hBulkT hLeafX) Surface.code.body (D.distance + 2) rho E := by
  unfold bhlBandK1FromX
  refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor)))
    (derivWF_hyp _) ?_
  refine derivWF_botElim (derivWF_notElim ?_ (derivWF_pauliNeqLit _ _ (by decide)))
  exact derivWF_eqPauliTrans' (derivWF_eqPauliSymm' (cw1_WF wLeafX))
    (baseLeafBulkIS_WF _ (dP3 D) k1P3 qP3 (dP3_pure D) (.var _) (.var _) (cw1_WF wBulkT) (derivWF_hyp _))

theorem bhlBandK2FromZ_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)}
    {hBulkT : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b true))}
    {hLeafZ : SFormula.Deriv Δ (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p Pauli.Z))}
    {rho : Env 3} {E : PartialStabilizer}
    (wBulkT : DerivWF hBulkT Surface.code.body (D.distance + 2) rho E)
    (wLeafZ : DerivWF hLeafZ Surface.code.body (D.distance + 2) rho E) :
    DerivWF (bhlBandK2FromZ D hBulkT hLeafZ) Surface.code.body (D.distance + 2) rho E := by
  unfold bhlBandK2FromZ
  refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor)))
    (derivWF_hyp _) ?_
  refine derivWF_botElim (derivWF_notElim ?_ (derivWF_pauliNeqLit _ _ (by decide)))
  exact derivWF_eqPauliTrans' (derivWF_eqPauliSymm' (cw1_WF wLeafZ))
    (baseLeafBulkIS_WF _ (dP3 D) k2P3 qP3 (dP3_pure D) (.var _) (.var _) (cw1_WF wBulkT) (derivWF_hyp _))

theorem commBulkBulkHorizL_WF (D : OddSurfaceDistance) {Γ : List (SFormula 2)}
    {hEntryA : SFormula.Deriv Γ (entryAQuant D)} {hEntryB : SFormula.Deriv Γ (entryBQuant D)}
    {hk1X : SFormula.Deriv Γ (k1IsX D true)} {hExcl1 : SFormula.Deriv Γ (typeExclF D k1P)}
    {hBulkK1 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true))}
    {hKindK1 : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k1P)) (SC.b false))}
    {hBulkK2 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true))}
    {hKindK2 : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k2P)) (SC.b true))}
    {hadj : SFormula.Deriv Γ (bhlAdjF D)} {hcol : SFormula.Deriv Γ (bhlColF D)}
    {hRange : SFormula.Deriv Γ (bhlRangePackF D)}
    {hBandK1 : SFormula.Deriv Γ (bhlBandK1PackF D)} {hBandK2 : SFormula.Deriv Γ (bhlBandK2PackF D)}
    {hPin : SFormula.Deriv Γ (bhlPinF D)}
    {hEA0 : SFormula.Deriv Γ (entryAAtQF D (bhlQ0 D))} {hEA1 : SFormula.Deriv Γ (entryAAtQF D (bhlQ1 D))}
    {hEB0 : SFormula.Deriv Γ (entryBAtQF D (bhlQ0 D))} {hEB1 : SFormula.Deriv Γ (entryBAtQF D (bhlQ1 D))}
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
    (wHcol : DerivWF hcol Surface.code.body (D.distance + 2) rho E)
    (wHRange : DerivWF hRange Surface.code.body (D.distance + 2) rho E)
    (wHBandK1 : DerivWF hBandK1 Surface.code.body (D.distance + 2) rho E)
    (wHBandK2 : DerivWF hBandK2 Surface.code.body (D.distance + 2) rho E)
    (wHPin : DerivWF hPin Surface.code.body (D.distance + 2) rho E)
    (wHEA0 : DerivWF hEA0 Surface.code.body (D.distance + 2) rho E)
    (wHEA1 : DerivWF hEA1 Surface.code.body (D.distance + 2) rho E)
    (wHEB0 : DerivWF hEB0 Surface.code.body (D.distance + 2) rho E)
    (wHEB1 : DerivWF hEB1 Surface.code.body (D.distance + 2) rho E)
    (hCtx : SFormula.ContextHolds Surface.code.body (D.distance + 2) rho E Γ) :
    DerivWF (commBulkBulkHorizL D hEntryA hEntryB hk1X hExcl1 hBulkK1 hKindK1 hBulkK2 hKindK2
        hadj hcol hRange hBandK1 hBandK2 hPin hEA0 hEA1 hEB0 hEB1)
      Surface.code.body (D.distance + 2) rho E := by
  unfold commBulkBulkHorizL
  have wRangeP := derivWF_mp (derivWF_mp wHRange wHBulkK1) wHcol
  have wK1BP := derivWF_mp (derivWF_mp wHBandK1 wHBulkK1) wHcol
  have wK2BP := derivWF_mp (derivWF_mp (derivWF_mp wHBandK2 wHBulkK1) wHcol) wHadj
  refine commBulkTopXZ_WF D (bhlQ0 D) (bhlQ1 D)
    (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
    (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
    wEntryA wEntryB wHk1X wHExcl1
    (derivWF_andElimLeft' wRangeP)
    (derivWF_andElimLeft' (derivWF_andElimRight' wRangeP))
    (derivWF_andElimRight' (derivWF_andElimRight' wRangeP))
    (derivWF_eqPauliTrans' wHEA0 (baseLeafXS_WF _ (dP2 D) k1P (bhlQ0 D) (dP2_pure D) (.var _)
      (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
      wHBulkK1 (derivWF_andElimLeft' wK1BP) wHKindK1))
    (derivWF_eqPauliTrans' wHEA1 (baseLeafXS_WF _ (dP2 D) k1P (bhlQ1 D) (dP2_pure D) (.var _)
      (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
      wHBulkK1 (derivWF_andElimRight' wK1BP) wHKindK1))
    (derivWF_eqPauliTrans' wHEB0 (baseLeafZS_WF _ (dP2 D) k2P (bhlQ0 D) (dP2_pure D) (.var _)
      (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
      wHBulkK2 (derivWF_andElimLeft' wK2BP) wHKindK2))
    (derivWF_eqPauliTrans' wHEB1 (baseLeafZS_WF _ (dP2 D) k2P (bhlQ1 D) (dP2_pure D) (.var _)
      (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
      wHBulkK2 (derivWF_andElimRight' wK2BP) wHKindK2))
    ?wHXZpin hCtx
  intro x Δ' lift liftWF hX wX hZ wZ
  have wBulkK1Δ := liftWF (cw3_WF (derivWF_weakenFresh wHBulkK1))
  have wBulkK2Δ := liftWF (cw3_WF (derivWF_weakenFresh wHBulkK2))
  have wcolΔ := liftWF (cw3_WF (derivWF_weakenFresh wHcol))
  have wadjΔ := liftWF (cw3_WF (derivWF_weakenFresh wHadj))
  have wPinΔ := liftWF (cw3_WF (derivWF_weakenFresh wHPin))
  have wBandK1B := bhlBandK1FromX_WF D wBulkK1Δ wX
  have wBandK2B := bhlBandK2FromZ_WF D wBulkK2Δ wZ
  refine derivWF_orElim
    (bhlPinAt_WF D wPinΔ (liftWF (derivWF_hyp _)) wBulkK1Δ wcolΔ wadjΔ wBandK1B wBandK2B) ?_ ?_
  · exact derivWF_botElim (derivWF_notElim (derivWF_hyp _) (cw1_WF (liftWF (derivWF_hyp _))))
  · exact derivWF_botElim (derivWF_notElim (derivWF_hyp _) (cw1_WF (liftWF (derivWF_hyp _))))

theorem bvuPinAt_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)}
    {hW : SFormula.Deriv Δ (bvuPinF D).weaken}
    {hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken)}
    {hBulkK1 : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b true))}
    {hRow : SFormula.Deriv Δ (.eqBool (SC.closed (.ltNat (.natLit 0) (.div k1P3 (dm1TA (dP3 D))))) (SC.b true))}
    {hAdj : SFormula.Deriv Δ (.eqBool (SC.closed (.eqNat k2P3 (.sub k1P3 (dm1TA (dP3 D))))) (SC.b true))}
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
    DerivWF (bvuPinAt D hW hq hBulkK1 hRow hAdj hBandK1 hBandK2)
      Surface.code.body (D.distance + 2) rho E := by
  unfold bvuPinAt
  comm_deriv_wf

theorem bvuBandK1FromX_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)}
    {hBulkT : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b true))}
    {hLeafX : SFormula.Deriv Δ (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3)) (SC.p Pauli.X))}
    {rho : Env 3} {E : PartialStabilizer}
    (wBulkT : DerivWF hBulkT Surface.code.body (D.distance + 2) rho E)
    (wLeafX : DerivWF hLeafX Surface.code.body (D.distance + 2) rho E) :
    DerivWF (bvuBandK1FromX D hBulkT hLeafX) Surface.code.body (D.distance + 2) rho E := by
  unfold bvuBandK1FromX
  refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor)))
    (derivWF_hyp _) ?_
  refine derivWF_botElim (derivWF_notElim ?_ (derivWF_pauliNeqLit _ _ (by decide)))
  exact derivWF_eqPauliTrans' (derivWF_eqPauliSymm' (cw1_WF wLeafX))
    (baseLeafBulkIS_WF _ (dP3 D) k1P3 qP3 (dP3_pure D) (.var _) (.var _) (cw1_WF wBulkT) (derivWF_hyp _))

theorem bvuBandK2FromZ_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)}
    {hBulkT : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b true))}
    {hLeafZ : SFormula.Deriv Δ (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p Pauli.Z))}
    {rho : Env 3} {E : PartialStabilizer}
    (wBulkT : DerivWF hBulkT Surface.code.body (D.distance + 2) rho E)
    (wLeafZ : DerivWF hLeafZ Surface.code.body (D.distance + 2) rho E) :
    DerivWF (bvuBandK2FromZ D hBulkT hLeafZ) Surface.code.body (D.distance + 2) rho E := by
  unfold bvuBandK2FromZ
  refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor)))
    (derivWF_hyp _) ?_
  refine derivWF_botElim (derivWF_notElim ?_ (derivWF_pauliNeqLit _ _ (by decide)))
  exact derivWF_eqPauliTrans' (derivWF_eqPauliSymm' (cw1_WF wLeafZ))
    (baseLeafBulkIS_WF _ (dP3 D) k2P3 qP3 (dP3_pure D) (.var _) (.var _) (cw1_WF wBulkT) (derivWF_hyp _))

theorem commBulkBulkVertU_WF (D : OddSurfaceDistance) {Γ : List (SFormula 2)}
    {hEntryA : SFormula.Deriv Γ (entryAQuant D)} {hEntryB : SFormula.Deriv Γ (entryBQuant D)}
    {hk1X : SFormula.Deriv Γ (k1IsX D true)} {hExcl1 : SFormula.Deriv Γ (typeExclF D k1P)}
    {hBulkK1 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true))}
    {hKindK1 : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k1P)) (SC.b false))}
    {hBulkK2 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true))}
    {hKindK2 : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k2P)) (SC.b true))}
    {hadj : SFormula.Deriv Γ (bvuAdjF D)} {hrow : SFormula.Deriv Γ (bvuRowF D)}
    {hRange : SFormula.Deriv Γ (bvuRangePackF D)}
    {hBandK1 : SFormula.Deriv Γ (bvuBandK1PackF D)} {hBandK2 : SFormula.Deriv Γ (bvuBandK2PackF D)}
    {hPin : SFormula.Deriv Γ (bvuPinF D)}
    {hEA0 : SFormula.Deriv Γ (entryAAtQF D (bvuQ0 D))} {hEA1 : SFormula.Deriv Γ (entryAAtQF D (bvuQ1 D))}
    {hEB0 : SFormula.Deriv Γ (entryBAtQF D (bvuQ0 D))} {hEB1 : SFormula.Deriv Γ (entryBAtQF D (bvuQ1 D))}
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
    DerivWF (commBulkBulkVertU D hEntryA hEntryB hk1X hExcl1 hBulkK1 hKindK1 hBulkK2 hKindK2
        hadj hrow hRange hBandK1 hBandK2 hPin hEA0 hEA1 hEB0 hEB1)
      Surface.code.body (D.distance + 2) rho E := by
  unfold commBulkBulkVertU
  have wRangeP := derivWF_mp (derivWF_mp wHRange wHBulkK1) wHrow
  have wK1BP := derivWF_mp (derivWF_mp wHBandK1 wHBulkK1) wHrow
  have wK2BP := derivWF_mp (derivWF_mp (derivWF_mp wHBandK2 wHBulkK1) wHrow) wHadj
  refine commBulkTopXZ_WF D (bvuQ0 D) (bvuQ1 D)
    (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
    (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
    wEntryA wEntryB wHk1X wHExcl1
    (derivWF_andElimLeft' wRangeP)
    (derivWF_andElimLeft' (derivWF_andElimRight' wRangeP))
    (derivWF_andElimRight' (derivWF_andElimRight' wRangeP))
    (derivWF_eqPauliTrans' wHEA0 (baseLeafXS_WF _ (dP2 D) k1P (bvuQ0 D) (dP2_pure D) (.var _)
      (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
      wHBulkK1 (derivWF_andElimLeft' wK1BP) wHKindK1))
    (derivWF_eqPauliTrans' wHEA1 (baseLeafXS_WF _ (dP2 D) k1P (bvuQ1 D) (dP2_pure D) (.var _)
      (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
      wHBulkK1 (derivWF_andElimRight' wK1BP) wHKindK1))
    (derivWF_eqPauliTrans' wHEB0 (baseLeafZS_WF _ (dP2 D) k2P (bvuQ0 D) (dP2_pure D) (.var _)
      (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
      wHBulkK2 (derivWF_andElimLeft' wK2BP) wHKindK2))
    (derivWF_eqPauliTrans' wHEB1 (baseLeafZS_WF _ (dP2 D) k2P (bvuQ1 D) (dP2_pure D) (.var _)
      (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))
      wHBulkK2 (derivWF_andElimRight' wK2BP) wHKindK2))
    ?wHXZpin hCtx
  intro x Δ' lift liftWF hX wX hZ wZ
  have wBulkK1Δ := liftWF (cw3_WF (derivWF_weakenFresh wHBulkK1))
  have wBulkK2Δ := liftWF (cw3_WF (derivWF_weakenFresh wHBulkK2))
  have wrowΔ := liftWF (cw3_WF (derivWF_weakenFresh wHrow))
  have wadjΔ := liftWF (cw3_WF (derivWF_weakenFresh wHadj))
  have wPinΔ := liftWF (cw3_WF (derivWF_weakenFresh wHPin))
  have wBandK1B := bvuBandK1FromX_WF D wBulkK1Δ wX
  have wBandK2B := bvuBandK2FromZ_WF D wBulkK2Δ wZ
  refine derivWF_orElim
    (bvuPinAt_WF D wPinΔ (liftWF (derivWF_hyp _)) wBulkK1Δ wrowΔ wadjΔ wBandK1B wBandK2B) ?_ ?_
  · exact derivWF_botElim (derivWF_notElim (derivWF_hyp _) (cw1_WF (liftWF (derivWF_hyp _))))
  · exact derivWF_botElim (derivWF_notElim (derivWF_hyp _) (cw1_WF (liftWF (derivWF_hyp _))))

end QHL.CodeLang.Surface.Verify
