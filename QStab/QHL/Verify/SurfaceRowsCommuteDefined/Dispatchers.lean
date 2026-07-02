import QStab.QHL.Verify.SurfaceRowsCommuteDefined.DispatcherPrereqs

/-!
# Rows-commute definedness — Dispatchers

Dispatchers 1-9/9 (bulk–bulk, bulk–boundary, boundary–boundary boolCases trees) plus the
megaPacks pin-pack support.
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

set_option maxHeartbeats 1600000

/-! ## Dispatcher 1/9: dispatchBulkBulk (boolCases tree → 4 bulk-bulk overlap closers + non-adj) -/

theorem dispatchBulkBulk_WF (D : OddSurfaceDistance) {Γ : List (SFormula 2)}
    {hbundle : SFormula.Deriv Γ (pairBundleF D)} {hpacks : SFormula.Deriv Γ (dbbPacksF D)}
    {hkAX : SFormula.Deriv Γ (k1IsX D true)} {hkBZ : SFormula.Deriv Γ (k2IsX D false)}
    {hbulkA : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true))}
    {hbulkB : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true))}
    {rho : Env 2} {E : PartialStabilizer}
    (wbundle : DerivWF hbundle Surface.code.body (D.distance + 2) rho E)
    (wpacks : DerivWF hpacks Surface.code.body (D.distance + 2) rho E)
    (wkAX : DerivWF hkAX Surface.code.body (D.distance + 2) rho E)
    (wkBZ : DerivWF hkBZ Surface.code.body (D.distance + 2) rho E)
    (wbulkA : DerivWF hbulkA Surface.code.body (D.distance + 2) rho E)
    (wbulkB : DerivWF hbulkB Surface.code.body (D.distance + 2) rho E)
    (hCtx : SFormula.ContextHolds Surface.code.body (D.distance + 2) rho E Γ) :
    DerivWF (dispatchBulkBulk D hbundle hpacks hkAX hkBZ hbulkA hbulkB)
      Surface.code.body (D.distance + 2) rho E := by
  unfold dispatchBulkBulk
  -- Base facts.
  have wEntryA := derivWF_andElimLeft' wbundle
  have wEntryB := derivWF_andElimLeft' (derivWF_andElimRight' wbundle)
  have wExcl1 := derivWF_andElimLeft' (derivWF_andElimRight' (derivWF_andElimRight' wbundle))
  have wExcl2 := derivWF_andElimRight' (derivWF_andElimRight' (derivWF_andElimRight' wbundle))
  have wKindK1 := dbbKindK1OfIsX_WF D wExcl1 wkAX wbulkA
  have wKindK2 := dbbKindK2OfNotIsX_WF D wExcl2 wkBZ wbulkB
  -- Route bundles + imp facts.
  have wHoriz := derivWF_andElimLeft' wpacks
  have wVert := derivWF_andElimLeft' (derivWF_andElimRight' wpacks)
  have wHorizL := derivWF_andElimLeft' (derivWF_andElimRight' (derivWF_andElimRight' wpacks))
  have wVertU := derivWF_andElimLeft' (derivWF_andElimRight' (derivWF_andElimRight'
    (derivWF_andElimRight' wpacks)))
  have wBbna := derivWF_andElimLeft' (derivWF_andElimRight' (derivWF_andElimRight'
    (derivWF_andElimRight' (derivWF_andElimRight' wpacks))))
  have wImpRest := derivWF_andElimRight' (derivWF_andElimRight' (derivWF_andElimRight'
    (derivWF_andElimRight' (derivWF_andElimRight' wpacks))))
  have wBhRowImp := derivWF_andElimLeft' wImpRest
  have wBvRowImp := derivWF_andElimLeft' (derivWF_andElimRight' wImpRest)
  have wBhlColImp := derivWF_andElimLeft' (derivWF_andElimRight' (derivWF_andElimRight' wImpRest))
  have wNonAdjAll := derivWF_andElimLeft' (derivWF_andElimRight' (derivWF_andElimRight'
    (derivWF_andElimRight' wImpRest)))
  have wNonAdjVu := derivWF_andElimRight' (derivWF_andElimRight' (derivWF_andElimRight'
    (derivWF_andElimRight' wImpRest)))
  -- Per-route closer inputs.
  have wHR := derivWF_andElimLeft' wHoriz
  have wHB1 := derivWF_andElimLeft' (derivWF_andElimRight' wHoriz)
  have wHB2 := derivWF_andElimLeft' (derivWF_andElimRight' (derivWF_andElimRight' wHoriz))
  have wHP := derivWF_andElimLeft' (derivWF_andElimRight' (derivWF_andElimRight'
    (derivWF_andElimRight' wHoriz)))
  have wHe := derivWF_andElimRight' (derivWF_andElimRight' (derivWF_andElimRight'
    (derivWF_andElimRight' wHoriz)))
  have wHEA0 := derivWF_andElimLeft' (derivWF_andElimLeft' wHe)
  have wHEB0 := derivWF_andElimRight' (derivWF_andElimLeft' wHe)
  have wHEA1 := derivWF_andElimLeft' (derivWF_andElimRight' wHe)
  have wHEB1 := derivWF_andElimRight' (derivWF_andElimRight' wHe)
  have wVR := derivWF_andElimLeft' wVert
  have wVB1 := derivWF_andElimLeft' (derivWF_andElimRight' wVert)
  have wVB2 := derivWF_andElimLeft' (derivWF_andElimRight' (derivWF_andElimRight' wVert))
  have wVP := derivWF_andElimLeft' (derivWF_andElimRight' (derivWF_andElimRight'
    (derivWF_andElimRight' wVert)))
  have wVe := derivWF_andElimRight' (derivWF_andElimRight' (derivWF_andElimRight'
    (derivWF_andElimRight' wVert)))
  have wVEA0 := derivWF_andElimLeft' (derivWF_andElimLeft' wVe)
  have wVEB0 := derivWF_andElimRight' (derivWF_andElimLeft' wVe)
  have wVEA1 := derivWF_andElimLeft' (derivWF_andElimRight' wVe)
  have wVEB1 := derivWF_andElimRight' (derivWF_andElimRight' wVe)
  have wLR := derivWF_andElimLeft' wHorizL
  have wLB1 := derivWF_andElimLeft' (derivWF_andElimRight' wHorizL)
  have wLB2 := derivWF_andElimLeft' (derivWF_andElimRight' (derivWF_andElimRight' wHorizL))
  have wLP := derivWF_andElimLeft' (derivWF_andElimRight' (derivWF_andElimRight'
    (derivWF_andElimRight' wHorizL)))
  have wLe := derivWF_andElimRight' (derivWF_andElimRight' (derivWF_andElimRight'
    (derivWF_andElimRight' wHorizL)))
  have wLEA0 := derivWF_andElimLeft' (derivWF_andElimLeft' wLe)
  have wLEB0 := derivWF_andElimRight' (derivWF_andElimLeft' wLe)
  have wLEA1 := derivWF_andElimLeft' (derivWF_andElimRight' wLe)
  have wLEB1 := derivWF_andElimRight' (derivWF_andElimRight' wLe)
  have wUR := derivWF_andElimLeft' wVertU
  have wUB1 := derivWF_andElimLeft' (derivWF_andElimRight' wVertU)
  have wUB2 := derivWF_andElimLeft' (derivWF_andElimRight' (derivWF_andElimRight' wVertU))
  have wUP := derivWF_andElimLeft' (derivWF_andElimRight' (derivWF_andElimRight'
    (derivWF_andElimRight' wVertU)))
  have wUe := derivWF_andElimRight' (derivWF_andElimRight' (derivWF_andElimRight'
    (derivWF_andElimRight' wVertU)))
  have wUEA0 := derivWF_andElimLeft' (derivWF_andElimLeft' wUe)
  have wUEB0 := derivWF_andElimRight' (derivWF_andElimLeft' wUe)
  have wUEA1 := derivWF_andElimLeft' (derivWF_andElimRight' wUe)
  have wUEB1 := derivWF_andElimRight' (derivWF_andElimRight' wUe)
  -- ROUTE 1: horizontal-right.
  refine derivWF_boolCases_cond _ _
    (sterm_eval_closedPure (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor)))
    (fun hc1T => ?_) (fun hc1F => ?_)
  · -- horiz
    have h1T := contextHolds_cons_eqBoolTrue hCtx hc1T
    exact commBulkBulkHoriz_WF D (cw1_WF wEntryA) (cw1_WF wEntryB) (cw1_WF wkAX) (cw1_WF wExcl1)
      (cw1_WF wbulkA) (cw1_WF wKindK1) (cw1_WF wbulkB) (cw1_WF wKindK2) (derivWF_hyp _)
      (derivWF_mp (derivWF_mp (derivWF_mp (derivWF_mp
        (cw1_WF wBhRowImp) (cw1_WF wKindK1)) (cw1_WF wKindK2)) (cw1_WF wbulkA)) (derivWF_hyp _))
      (cw1_WF wHR) (cw1_WF wHB1) (cw1_WF wHB2) (cw1_WF wHP)
      (cw1_WF wHEA0) (cw1_WF wHEA1) (cw1_WF wHEB0) (cw1_WF wHEB1) h1T
  · -- rest1: ROUTE 2 vertical-down.
    have h1F := contextHolds_cons_eqBoolFalse hCtx hc1F
    refine derivWF_boolCases_cond _ _
      (sterm_eval_closedPure (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor)))
      (fun hc2T => ?_) (fun hc2F => ?_)
    · -- vert
      have h2T := contextHolds_cons_eqBoolTrue h1F hc2T
      exact commBulkBulkVert_WF D (cw2_WF wEntryA) (cw2_WF wEntryB) (cw2_WF wkAX) (cw2_WF wExcl1)
        (cw2_WF wbulkA) (cw2_WF wKindK1) (cw2_WF wbulkB) (cw2_WF wKindK2) (derivWF_hyp _)
        (derivWF_mp (derivWF_mp (cw2_WF wBvRowImp) (cw2_WF wbulkB)) (derivWF_hyp _))
        (cw2_WF wVR) (cw2_WF wVB1) (cw2_WF wVB2) (cw2_WF wVP)
        (cw2_WF wVEA0) (cw2_WF wVEA1) (cw2_WF wVEB0) (cw2_WF wVEB1) h2T
    · -- rest2: ROUTE 3 horizontal-left.
      have h2F := contextHolds_cons_eqBoolFalse h1F hc2F
      refine derivWF_boolCases_cond _ _
        (sterm_eval_closedPure (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor)))
        (fun hc3T => ?_) (fun hc3F => ?_)
      · -- horizL
        have h3T := contextHolds_cons_eqBoolTrue h2F hc3T
        exact commBulkBulkHorizL_WF D (cw3_WF wEntryA) (cw3_WF wEntryB) (cw3_WF wkAX) (cw3_WF wExcl1)
          (cw3_WF wbulkA) (cw3_WF wKindK1) (cw3_WF wbulkB) (cw3_WF wKindK2) (derivWF_hyp _)
          (derivWF_mp (derivWF_mp (derivWF_mp (derivWF_mp
            (cw3_WF wBhlColImp) (cw3_WF wKindK1)) (cw3_WF wKindK2)) (cw3_WF wbulkA)) (derivWF_hyp _))
          (cw3_WF wLR) (cw3_WF wLB1) (cw3_WF wLB2) (cw3_WF wLP)
          (cw3_WF wLEA0) (cw3_WF wLEA1) (cw3_WF wLEB0) (cw3_WF wLEB1) h3T
      · -- rest3: ROUTE 4 vertical-up.
        have h3F := contextHolds_cons_eqBoolFalse h2F hc3F
        refine derivWF_boolCases_cond _ _
          (sterm_eval_closedPure (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor)))
          (fun hc4T => ?_) (fun hc4F => ?_)
        · -- vertU outer: guard on 0 < cellR.
          have h4T := contextHolds_cons_eqBoolTrue h3F hc4T
          refine derivWF_boolCases_cond _ _
            (sterm_eval_closedPure (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor)))
            (fun hc5T => ?_) (fun hc5F => ?_)
          · -- vu
            have h5T := contextHolds_cons_eqBoolTrue h4T hc5T
            exact commBulkBulkVertU_WF D (cw5_WF wEntryA) (cw5_WF wEntryB) (cw5_WF wkAX) (cw5_WF wExcl1)
              (cw5_WF wbulkA) (cw5_WF wKindK1) (cw5_WF wbulkB) (cw5_WF wKindK2)
              (derivWF_hyp _) (derivWF_hyp _)
              (cw5_WF wUR) (cw5_WF wUB1) (cw5_WF wUB2) (cw5_WF wUP)
              (cw5_WF wUEA0) (cw5_WF wUEA1) (cw5_WF wUEB0) (cw5_WF wUEB1) h5T
          · -- vuFail: non-overlap via dbbNonAdjVu.
            have h5F := contextHolds_cons_eqBoolFalse h4T hc5F
            refine pairCommuteBulkBulkNonAdj_WF D (cw5_WF wEntryA) (cw5_WF wEntryB) (cw5_WF wkAX)
              (cw5_WF wExcl1) (cw5_WF wbulkA) (cw5_WF wKindK1) (cw5_WF wbulkB) (cw5_WF wKindK2)
              ?_ (cw5_WF wBbna) h5F
            exact derivWF_mp (derivWF_mp (derivWF_mp (derivWF_mp
              (cw5_WF wNonAdjVu) (cw5_WF wbulkA)) (cw2_WF (derivWF_hyp _)))
              (derivWF_hyp _)) (derivWF_hyp _)
        · -- rest4: all four index conditions fail, non-overlap via dbbNonAdjAll.
          have h4F := contextHolds_cons_eqBoolFalse h3F hc4F
          refine pairCommuteBulkBulkNonAdj_WF D (cw4_WF wEntryA) (cw4_WF wEntryB) (cw4_WF wkAX)
            (cw4_WF wExcl1) (cw4_WF wbulkA) (cw4_WF wKindK1) (cw4_WF wbulkB) (cw4_WF wKindK2)
            ?_ (cw4_WF wBbna) h4F
          exact derivWF_mp (derivWF_mp (derivWF_mp (derivWF_mp (derivWF_mp (derivWF_mp
            (cw4_WF wNonAdjAll) (cw4_WF wbulkA)) (cw4_WF wbulkB)) (cw3_WF (derivWF_hyp _)))
            (cw2_WF (derivWF_hyp _))) (cw1_WF (derivWF_hyp _)))
            (derivWF_hyp _)

/-! ## Dispatchers 2-5/9: bulk↔boundary (single boolCases → overlap closer / non-adj) -/

theorem dispatchBulkRight_WF (D : OddSurfaceDistance) {Γ : List (SFormula 2)}
    {hbundle : SFormula.Deriv Γ (pairBundleF D)} {hpacks : SFormula.Deriv Γ (dbrPacksF D)}
    {hkAX : SFormula.Deriv Γ (k1IsX D true)} {hkBZ : SFormula.Deriv Γ (k2IsX D false)}
    {hbulkA : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true))}
    {hnbulkB : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false))}
    {hntopB : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false))}
    {hrightB : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b true))}
    {rho : Env 2} {E : PartialStabilizer}
    (wbundle : DerivWF hbundle Surface.code.body (D.distance + 2) rho E)
    (wpacks : DerivWF hpacks Surface.code.body (D.distance + 2) rho E)
    (wkAX : DerivWF hkAX Surface.code.body (D.distance + 2) rho E)
    (wkBZ : DerivWF hkBZ Surface.code.body (D.distance + 2) rho E)
    (wbulkA : DerivWF hbulkA Surface.code.body (D.distance + 2) rho E)
    (wnbulkB : DerivWF hnbulkB Surface.code.body (D.distance + 2) rho E)
    (wntopB : DerivWF hntopB Surface.code.body (D.distance + 2) rho E)
    (wrightB : DerivWF hrightB Surface.code.body (D.distance + 2) rho E)
    (hCtx : SFormula.ContextHolds Surface.code.body (D.distance + 2) rho E Γ) :
    DerivWF (dispatchBulkRight D hbundle hpacks hkAX hkBZ hbulkA hnbulkB hntopB hrightB)
      Surface.code.body (D.distance + 2) rho E := by
  unfold dispatchBulkRight
  have wEntryA := derivWF_andElimLeft' wbundle
  have wEntryB := derivWF_andElimLeft' (derivWF_andElimRight' wbundle)
  have wExcl1 := derivWF_andElimLeft' (derivWF_andElimRight' (derivWF_andElimRight' wbundle))
  have wKindK1 := dbbKindK1OfIsX_WF D wExcl1 wkAX wbulkA
  have wRange := derivWF_andElimLeft' wpacks
  have wRest1 := derivWF_andElimRight' wpacks
  have wRightBand := derivWF_andElimLeft' wRest1
  have wRest2 := derivWF_andElimRight' wRest1
  have wBulkBand := derivWF_andElimLeft' wRest2
  have wRest3 := derivWF_andElimRight' wRest2
  have wPin := derivWF_andElimLeft' wRest3
  have wRest4 := derivWF_andElimRight' wRest3
  have wE0 := derivWF_andElimLeft' wRest4
  have wEA0 := derivWF_andElimLeft' wE0
  have wEB0 := derivWF_andElimRight' wE0
  have wRest5 := derivWF_andElimRight' wRest4
  have wE1 := derivWF_andElimLeft' wRest5
  have wEA1 := derivWF_andElimLeft' wE1
  have wEB1 := derivWF_andElimRight' wE1
  have wRest6 := derivWF_andElimRight' wRest5
  have wBrnaPin := derivWF_andElimLeft' wRest6
  have wNonAdjImp := derivWF_andElimRight' wRest6
  refine derivWF_boolCases_cond _ _
    (sterm_eval_closedPure (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor)))
    (fun hcT => ?_) (fun hcF => ?_)
  · have hCtxA := contextHolds_cons_eqBoolTrue hCtx hcT
    exact commRightBulk_WF D (cw1_WF wEntryA) (cw1_WF wEntryB) (cw1_WF wkAX) (cw1_WF wExcl1)
      (cw1_WF wnbulkB) (cw1_WF wntopB) (cw1_WF wrightB) (derivWF_hyp _)
      (cw1_WF wRange) (cw1_WF wRightBand) (cw1_WF wBulkBand) (cw1_WF wPin)
      (cw1_WF wEA0) (cw1_WF wEA1) (cw1_WF wEB0) (cw1_WF wEB1) hCtxA
  · have hCtxF := contextHolds_cons_eqBoolFalse hCtx hcF
    refine pairCommuteBulkRightNonAdj_WF D (cw1_WF wEntryA) (cw1_WF wEntryB) (cw1_WF wkAX)
      (cw1_WF wExcl1) (cw1_WF wbulkA) (cw1_WF wKindK1) (cw1_WF wnbulkB) (cw1_WF wntopB)
      (cw1_WF wrightB) ?_ (cw1_WF wBrnaPin) hCtxF
    exact derivWF_mp (derivWF_mp (cw1_WF wNonAdjImp) (cw1_WF wKindK1)) (derivWF_hyp _)

theorem dispatchBulkLeft_WF (D : OddSurfaceDistance) {Γ : List (SFormula 2)}
    {hbundle : SFormula.Deriv Γ (pairBundleF D)} {hpacks : SFormula.Deriv Γ (dblPacksF D)}
    {hkAX : SFormula.Deriv Γ (k1IsX D true)} {hkBZ : SFormula.Deriv Γ (k2IsX D false)}
    {hbulkA : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true))}
    {hnbulkB : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false))}
    {hntopB : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false))}
    {hnrightB : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false))}
    {hleftB : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b true))}
    {rho : Env 2} {E : PartialStabilizer}
    (wbundle : DerivWF hbundle Surface.code.body (D.distance + 2) rho E)
    (wpacks : DerivWF hpacks Surface.code.body (D.distance + 2) rho E)
    (wkAX : DerivWF hkAX Surface.code.body (D.distance + 2) rho E)
    (wkBZ : DerivWF hkBZ Surface.code.body (D.distance + 2) rho E)
    (wbulkA : DerivWF hbulkA Surface.code.body (D.distance + 2) rho E)
    (wnbulkB : DerivWF hnbulkB Surface.code.body (D.distance + 2) rho E)
    (wntopB : DerivWF hntopB Surface.code.body (D.distance + 2) rho E)
    (wnrightB : DerivWF hnrightB Surface.code.body (D.distance + 2) rho E)
    (wleftB : DerivWF hleftB Surface.code.body (D.distance + 2) rho E)
    (hCtx : SFormula.ContextHolds Surface.code.body (D.distance + 2) rho E Γ) :
    DerivWF (dispatchBulkLeft D hbundle hpacks hkAX hkBZ hbulkA hnbulkB hntopB hnrightB hleftB)
      Surface.code.body (D.distance + 2) rho E := by
  unfold dispatchBulkLeft
  have wEntryA := derivWF_andElimLeft' wbundle
  have wEntryB := derivWF_andElimLeft' (derivWF_andElimRight' wbundle)
  have wExcl1 := derivWF_andElimLeft' (derivWF_andElimRight' (derivWF_andElimRight' wbundle))
  have wKindK1 := dbbKindK1OfIsX_WF D wExcl1 wkAX wbulkA
  have wRange := derivWF_andElimLeft' wpacks
  have wRest1 := derivWF_andElimRight' wpacks
  have wLeftBand := derivWF_andElimLeft' wRest1
  have wRest2 := derivWF_andElimRight' wRest1
  have wBulkBand := derivWF_andElimLeft' wRest2
  have wRest3 := derivWF_andElimRight' wRest2
  have wPin := derivWF_andElimLeft' wRest3
  have wRest4 := derivWF_andElimRight' wRest3
  have wE0 := derivWF_andElimLeft' wRest4
  have wEA0 := derivWF_andElimLeft' wE0
  have wEB0 := derivWF_andElimRight' wE0
  have wRest5 := derivWF_andElimRight' wRest4
  have wE1 := derivWF_andElimLeft' wRest5
  have wEA1 := derivWF_andElimLeft' wE1
  have wEB1 := derivWF_andElimRight' wE1
  have wRest6 := derivWF_andElimRight' wRest5
  have wBlnaPin := derivWF_andElimLeft' wRest6
  have wNonAdjImp := derivWF_andElimRight' wRest6
  refine derivWF_boolCases_cond _ _
    (sterm_eval_closedPure (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor)))
    (fun hcT => ?_) (fun hcF => ?_)
  · have hCtxA := contextHolds_cons_eqBoolTrue hCtx hcT
    exact commLeftBulk_WF D (cw1_WF wEntryA) (cw1_WF wEntryB) (cw1_WF wkAX) (cw1_WF wExcl1)
      (cw1_WF wnbulkB) (cw1_WF wntopB) (cw1_WF wnrightB) (cw1_WF wleftB) (derivWF_hyp _)
      (cw1_WF wRange) (cw1_WF wLeftBand) (cw1_WF wBulkBand) (cw1_WF wPin)
      (cw1_WF wEA0) (cw1_WF wEA1) (cw1_WF wEB0) (cw1_WF wEB1) hCtxA
  · have hCtxF := contextHolds_cons_eqBoolFalse hCtx hcF
    refine pairCommuteBulkLeftNonAdj_WF D (cw1_WF wEntryA) (cw1_WF wEntryB) (cw1_WF wkAX)
      (cw1_WF wExcl1) (cw1_WF wbulkA) (cw1_WF wKindK1) (cw1_WF wnbulkB) (cw1_WF wntopB)
      (cw1_WF wnrightB) (cw1_WF wleftB) ?_ (cw1_WF wBlnaPin) hCtxF
    exact derivWF_mp (derivWF_mp (cw1_WF wNonAdjImp) (cw1_WF wKindK1)) (derivWF_hyp _)

theorem dispatchTopBulk_WF (D : OddSurfaceDistance) {Γ : List (SFormula 2)}
    {hbundle : SFormula.Deriv Γ (pairBundleF D)} {hpacks : SFormula.Deriv Γ (dtbPacksF D)}
    {hkAX : SFormula.Deriv Γ (k1IsX D true)} {hkBZ : SFormula.Deriv Γ (k2IsX D false)}
    {hnbulkA : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false))}
    {htopA : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b true))}
    {hbulkB : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true))}
    {rho : Env 2} {E : PartialStabilizer}
    (wbundle : DerivWF hbundle Surface.code.body (D.distance + 2) rho E)
    (wpacks : DerivWF hpacks Surface.code.body (D.distance + 2) rho E)
    (wkAX : DerivWF hkAX Surface.code.body (D.distance + 2) rho E)
    (wkBZ : DerivWF hkBZ Surface.code.body (D.distance + 2) rho E)
    (wnbulkA : DerivWF hnbulkA Surface.code.body (D.distance + 2) rho E)
    (wtopA : DerivWF htopA Surface.code.body (D.distance + 2) rho E)
    (wbulkB : DerivWF hbulkB Surface.code.body (D.distance + 2) rho E)
    (hCtx : SFormula.ContextHolds Surface.code.body (D.distance + 2) rho E Γ) :
    DerivWF (dispatchTopBulk D hbundle hpacks hkAX hkBZ hnbulkA htopA hbulkB)
      Surface.code.body (D.distance + 2) rho E := by
  unfold dispatchTopBulk
  have wEntryA := derivWF_andElimLeft' wbundle
  have wEntryB := derivWF_andElimLeft' (derivWF_andElimRight' wbundle)
  have wExcl1 := derivWF_andElimLeft' (derivWF_andElimRight' (derivWF_andElimRight' wbundle))
  have wExcl2 := derivWF_andElimRight' (derivWF_andElimRight' (derivWF_andElimRight' wbundle))
  have wKindK2 := dbbKindK2OfNotIsX_WF D wExcl2 wkBZ wbulkB
  have wRange := derivWF_andElimLeft' wpacks
  have wRest1 := derivWF_andElimRight' wpacks
  have wTopBand := derivWF_andElimLeft' wRest1
  have wRest2 := derivWF_andElimRight' wRest1
  have wBulkBand := derivWF_andElimLeft' wRest2
  have wRest3 := derivWF_andElimRight' wRest2
  have wPin := derivWF_andElimLeft' wRest3
  have wRest4 := derivWF_andElimRight' wRest3
  have wE0 := derivWF_andElimLeft' wRest4
  have wEA0 := derivWF_andElimLeft' wE0
  have wEB0 := derivWF_andElimRight' wE0
  have wRest5 := derivWF_andElimRight' wRest4
  have wE1 := derivWF_andElimLeft' wRest5
  have wEA1 := derivWF_andElimLeft' wE1
  have wEB1 := derivWF_andElimRight' wE1
  have wRest6 := derivWF_andElimRight' wRest5
  have wTbnaPin := derivWF_andElimLeft' wRest6
  have wNonAdjImp := derivWF_andElimRight' wRest6
  refine derivWF_boolCases_cond _ _
    (sterm_eval_closedPure (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor)))
    (fun hcT => ?_) (fun hcF => ?_)
  · have hCtxA := contextHolds_cons_eqBoolTrue hCtx hcT
    exact commBulkTop_WF D (cw1_WF wEntryA) (cw1_WF wEntryB) (cw1_WF wkAX) (cw1_WF wExcl1)
      (cw1_WF wnbulkA) (cw1_WF wtopA) (derivWF_hyp _)
      (cw1_WF wRange) (cw1_WF wTopBand) (cw1_WF wBulkBand) (cw1_WF wPin)
      (cw1_WF wEA0) (cw1_WF wEA1) (cw1_WF wEB0) (cw1_WF wEB1) hCtxA
  · have hCtxF := contextHolds_cons_eqBoolFalse hCtx hcF
    refine pairCommuteTopBulkNonAdj_WF D (cw1_WF wEntryA) (cw1_WF wEntryB) (cw1_WF wkAX)
      (cw1_WF wExcl1) (cw1_WF wnbulkA) (cw1_WF wtopA) (cw1_WF wbulkB) (cw1_WF wKindK2)
      ?_ (cw1_WF wTbnaPin) hCtxF
    exact derivWF_mp (derivWF_mp (cw1_WF wNonAdjImp) (cw1_WF wKindK2)) (derivWF_hyp _)

theorem dispatchBottomBulk_WF (D : OddSurfaceDistance) {Γ : List (SFormula 2)}
    {hbundle : SFormula.Deriv Γ (pairBundleF D)} {hpacks : SFormula.Deriv Γ (dbtbPacksF D)}
    {hkAX : SFormula.Deriv Γ (k1IsX D true)} {hkBZ : SFormula.Deriv Γ (k2IsX D false)}
    {hnbulkA : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false))}
    {hntopA : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false))}
    {hnrightA : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k1P)) (SC.b false))}
    {hnleftA : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k1P)) (SC.b false))}
    {hbulkB : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true))}
    {rho : Env 2} {E : PartialStabilizer}
    (wbundle : DerivWF hbundle Surface.code.body (D.distance + 2) rho E)
    (wpacks : DerivWF hpacks Surface.code.body (D.distance + 2) rho E)
    (wkAX : DerivWF hkAX Surface.code.body (D.distance + 2) rho E)
    (wkBZ : DerivWF hkBZ Surface.code.body (D.distance + 2) rho E)
    (wnbulkA : DerivWF hnbulkA Surface.code.body (D.distance + 2) rho E)
    (wntopA : DerivWF hntopA Surface.code.body (D.distance + 2) rho E)
    (wnrightA : DerivWF hnrightA Surface.code.body (D.distance + 2) rho E)
    (wnleftA : DerivWF hnleftA Surface.code.body (D.distance + 2) rho E)
    (wbulkB : DerivWF hbulkB Surface.code.body (D.distance + 2) rho E)
    (hCtx : SFormula.ContextHolds Surface.code.body (D.distance + 2) rho E Γ) :
    DerivWF (dispatchBottomBulk D hbundle hpacks hkAX hkBZ hnbulkA hntopA hnrightA hnleftA hbulkB)
      Surface.code.body (D.distance + 2) rho E := by
  unfold dispatchBottomBulk
  have wEntryA := derivWF_andElimLeft' wbundle
  have wEntryB := derivWF_andElimLeft' (derivWF_andElimRight' wbundle)
  have wExcl1 := derivWF_andElimLeft' (derivWF_andElimRight' (derivWF_andElimRight' wbundle))
  have wExcl2 := derivWF_andElimRight' (derivWF_andElimRight' (derivWF_andElimRight' wbundle))
  have wKindK2 := dbbKindK2OfNotIsX_WF D wExcl2 wkBZ wbulkB
  have wRange := derivWF_andElimLeft' wpacks
  have wRest1 := derivWF_andElimRight' wpacks
  have wBotBand := derivWF_andElimLeft' wRest1
  have wRest2 := derivWF_andElimRight' wRest1
  have wBulkBand := derivWF_andElimLeft' wRest2
  have wRest3 := derivWF_andElimRight' wRest2
  have wPin := derivWF_andElimLeft' wRest3
  have wRest4 := derivWF_andElimRight' wRest3
  have wE0 := derivWF_andElimLeft' wRest4
  have wEA0 := derivWF_andElimLeft' wE0
  have wEB0 := derivWF_andElimRight' wE0
  have wRest5 := derivWF_andElimRight' wRest4
  have wE1 := derivWF_andElimLeft' wRest5
  have wEA1 := derivWF_andElimLeft' wE1
  have wEB1 := derivWF_andElimRight' wE1
  have wRest6 := derivWF_andElimRight' wRest5
  have wBtbnaPin := derivWF_andElimLeft' wRest6
  have wRest7 := derivWF_andElimRight' wRest6
  have wNonAdjImp := derivWF_andElimLeft' wRest7
  have wStripImp := derivWF_andElimRight' wRest7
  refine derivWF_boolCases_cond _ _
    (sterm_eval_closedPure (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor)))
    (fun hcT => ?_) (fun hcF => ?_)
  · have hCtxA := contextHolds_cons_eqBoolTrue hCtx hcT
    exact commBottomBulk_WF D (cw1_WF wEntryA) (cw1_WF wEntryB) (cw1_WF wkAX) (cw1_WF wExcl1)
      (cw1_WF wnbulkA) (cw1_WF wntopA) (cw1_WF wnrightA) (cw1_WF wnleftA)
      (derivWF_mp (derivWF_mp (cw1_WF wStripImp) (cw1_WF wbulkB)) (derivWF_hyp _)) (derivWF_hyp _)
      (cw1_WF wRange) (cw1_WF wBotBand) (cw1_WF wBulkBand) (cw1_WF wPin)
      (cw1_WF wEA0) (cw1_WF wEA1) (cw1_WF wEB0) (cw1_WF wEB1) hCtxA
  · have hCtxF := contextHolds_cons_eqBoolFalse hCtx hcF
    refine pairCommuteBottomBulkNonAdj_WF D (cw1_WF wEntryA) (cw1_WF wEntryB) (cw1_WF wkAX)
      (cw1_WF wExcl1) (cw1_WF wnbulkA) (cw1_WF wntopA) (cw1_WF wnrightA) (cw1_WF wnleftA)
      (cw1_WF wbulkB) (cw1_WF wKindK2) ?_ (cw1_WF wBtbnaPin) hCtxF
    exact derivWF_mp (derivWF_mp (cw1_WF wNonAdjImp) (cw1_WF wKindK2)) (derivWF_hyp _)

/-! ## Dispatchers 6-9/9: boundary↔boundary (always non-adjacent → direct call, no boolCases) -/

theorem dispatchTopRight_WF (D : OddSurfaceDistance) {Γ : List (SFormula 2)}
    {hbundle : SFormula.Deriv Γ (pairBundleF D)} {hpacks : SFormula.Deriv Γ (dtrPacksF D)}
    {hkAX : SFormula.Deriv Γ (k1IsX D true)} {hkBZ : SFormula.Deriv Γ (k2IsX D false)}
    {hnbulkA : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false))}
    {htopA : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b true))}
    {hnbulkB : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false))}
    {hntopB : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false))}
    {hrightB : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b true))}
    {rho : Env 2} {E : PartialStabilizer}
    (wbundle : DerivWF hbundle Surface.code.body (D.distance + 2) rho E)
    (wpacks : DerivWF hpacks Surface.code.body (D.distance + 2) rho E)
    (wkAX : DerivWF hkAX Surface.code.body (D.distance + 2) rho E)
    (wkBZ : DerivWF hkBZ Surface.code.body (D.distance + 2) rho E)
    (wnbulkA : DerivWF hnbulkA Surface.code.body (D.distance + 2) rho E)
    (wtopA : DerivWF htopA Surface.code.body (D.distance + 2) rho E)
    (wnbulkB : DerivWF hnbulkB Surface.code.body (D.distance + 2) rho E)
    (wntopB : DerivWF hntopB Surface.code.body (D.distance + 2) rho E)
    (wrightB : DerivWF hrightB Surface.code.body (D.distance + 2) rho E)
    (hCtx : SFormula.ContextHolds Surface.code.body (D.distance + 2) rho E Γ) :
    DerivWF (dispatchTopRight D hbundle hpacks hkAX hkBZ hnbulkA htopA hnbulkB hntopB hrightB)
      Surface.code.body (D.distance + 2) rho E := by
  unfold dispatchTopRight
  exact pairCommuteTopRightNonAdj_WF D (derivWF_andElimLeft' wbundle)
    (derivWF_andElimLeft' (derivWF_andElimRight' wbundle)) wkAX
    (derivWF_andElimLeft' (derivWF_andElimRight' (derivWF_andElimRight' wbundle)))
    wnbulkA wtopA wnbulkB wntopB wrightB wpacks hCtx

theorem dispatchTopLeft_WF (D : OddSurfaceDistance) {Γ : List (SFormula 2)}
    {hbundle : SFormula.Deriv Γ (pairBundleF D)} {hpacks : SFormula.Deriv Γ (dtlPacksF D)}
    {hkAX : SFormula.Deriv Γ (k1IsX D true)} {hkBZ : SFormula.Deriv Γ (k2IsX D false)}
    {hnbulkA : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false))}
    {htopA : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b true))}
    {hnbulkB : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false))}
    {hntopB : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false))}
    {hnrightB : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false))}
    {hleftB : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b true))}
    {rho : Env 2} {E : PartialStabilizer}
    (wbundle : DerivWF hbundle Surface.code.body (D.distance + 2) rho E)
    (wpacks : DerivWF hpacks Surface.code.body (D.distance + 2) rho E)
    (wkAX : DerivWF hkAX Surface.code.body (D.distance + 2) rho E)
    (wkBZ : DerivWF hkBZ Surface.code.body (D.distance + 2) rho E)
    (wnbulkA : DerivWF hnbulkA Surface.code.body (D.distance + 2) rho E)
    (wtopA : DerivWF htopA Surface.code.body (D.distance + 2) rho E)
    (wnbulkB : DerivWF hnbulkB Surface.code.body (D.distance + 2) rho E)
    (wntopB : DerivWF hntopB Surface.code.body (D.distance + 2) rho E)
    (wnrightB : DerivWF hnrightB Surface.code.body (D.distance + 2) rho E)
    (wleftB : DerivWF hleftB Surface.code.body (D.distance + 2) rho E)
    (hCtx : SFormula.ContextHolds Surface.code.body (D.distance + 2) rho E Γ) :
    DerivWF (dispatchTopLeft D hbundle hpacks hkAX hkBZ hnbulkA htopA hnbulkB hntopB hnrightB hleftB)
      Surface.code.body (D.distance + 2) rho E := by
  unfold dispatchTopLeft
  exact pairCommuteTopLeftNonAdj_WF D (derivWF_andElimLeft' wbundle)
    (derivWF_andElimLeft' (derivWF_andElimRight' wbundle)) wkAX
    (derivWF_andElimLeft' (derivWF_andElimRight' (derivWF_andElimRight' wbundle)))
    wnbulkA wtopA wnbulkB wntopB wnrightB wleftB wpacks hCtx

theorem dispatchBottomRight_WF (D : OddSurfaceDistance) {Γ : List (SFormula 2)}
    {hbundle : SFormula.Deriv Γ (pairBundleF D)} {hpacks : SFormula.Deriv Γ (dbtrPacksF D)}
    {hkAX : SFormula.Deriv Γ (k1IsX D true)} {hkBZ : SFormula.Deriv Γ (k2IsX D false)}
    {hnbulkA : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false))}
    {hntopA : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false))}
    {hnrightA : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k1P)) (SC.b false))}
    {hnleftA : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k1P)) (SC.b false))}
    {hnbulkB : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false))}
    {hntopB : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false))}
    {hrightB : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b true))}
    {rho : Env 2} {E : PartialStabilizer}
    (wbundle : DerivWF hbundle Surface.code.body (D.distance + 2) rho E)
    (wpacks : DerivWF hpacks Surface.code.body (D.distance + 2) rho E)
    (wkAX : DerivWF hkAX Surface.code.body (D.distance + 2) rho E)
    (wkBZ : DerivWF hkBZ Surface.code.body (D.distance + 2) rho E)
    (wnbulkA : DerivWF hnbulkA Surface.code.body (D.distance + 2) rho E)
    (wntopA : DerivWF hntopA Surface.code.body (D.distance + 2) rho E)
    (wnrightA : DerivWF hnrightA Surface.code.body (D.distance + 2) rho E)
    (wnleftA : DerivWF hnleftA Surface.code.body (D.distance + 2) rho E)
    (wnbulkB : DerivWF hnbulkB Surface.code.body (D.distance + 2) rho E)
    (wntopB : DerivWF hntopB Surface.code.body (D.distance + 2) rho E)
    (wrightB : DerivWF hrightB Surface.code.body (D.distance + 2) rho E)
    (hCtx : SFormula.ContextHolds Surface.code.body (D.distance + 2) rho E Γ) :
    DerivWF (dispatchBottomRight D hbundle hpacks hkAX hkBZ hnbulkA hntopA hnrightA hnleftA hnbulkB hntopB hrightB)
      Surface.code.body (D.distance + 2) rho E := by
  unfold dispatchBottomRight
  exact pairCommuteBottomRightNonAdj_WF D (derivWF_andElimLeft' wbundle)
    (derivWF_andElimLeft' (derivWF_andElimRight' wbundle)) wkAX
    (derivWF_andElimLeft' (derivWF_andElimRight' (derivWF_andElimRight' wbundle)))
    wnbulkA wntopA wnrightA wnleftA wnbulkB wntopB wrightB wpacks hCtx

theorem dispatchBottomLeft_WF (D : OddSurfaceDistance) {Γ : List (SFormula 2)}
    {hbundle : SFormula.Deriv Γ (pairBundleF D)} {hpacks : SFormula.Deriv Γ (dbtlPacksF D)}
    {hkAX : SFormula.Deriv Γ (k1IsX D true)} {hkBZ : SFormula.Deriv Γ (k2IsX D false)}
    {hnbulkA : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false))}
    {hntopA : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false))}
    {hnrightA : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k1P)) (SC.b false))}
    {hnleftA : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k1P)) (SC.b false))}
    {hnbulkB : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false))}
    {hntopB : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false))}
    {hnrightB : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false))}
    {hleftB : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b true))}
    {rho : Env 2} {E : PartialStabilizer}
    (wbundle : DerivWF hbundle Surface.code.body (D.distance + 2) rho E)
    (wpacks : DerivWF hpacks Surface.code.body (D.distance + 2) rho E)
    (wkAX : DerivWF hkAX Surface.code.body (D.distance + 2) rho E)
    (wkBZ : DerivWF hkBZ Surface.code.body (D.distance + 2) rho E)
    (wnbulkA : DerivWF hnbulkA Surface.code.body (D.distance + 2) rho E)
    (wntopA : DerivWF hntopA Surface.code.body (D.distance + 2) rho E)
    (wnrightA : DerivWF hnrightA Surface.code.body (D.distance + 2) rho E)
    (wnleftA : DerivWF hnleftA Surface.code.body (D.distance + 2) rho E)
    (wnbulkB : DerivWF hnbulkB Surface.code.body (D.distance + 2) rho E)
    (wntopB : DerivWF hntopB Surface.code.body (D.distance + 2) rho E)
    (wnrightB : DerivWF hnrightB Surface.code.body (D.distance + 2) rho E)
    (wleftB : DerivWF hleftB Surface.code.body (D.distance + 2) rho E)
    (hCtx : SFormula.ContextHolds Surface.code.body (D.distance + 2) rho E Γ) :
    DerivWF (dispatchBottomLeft D hbundle hpacks hkAX hkBZ hnbulkA hntopA hnrightA hnleftA hnbulkB hntopB hnrightB hleftB)
      Surface.code.body (D.distance + 2) rho E := by
  unfold dispatchBottomLeft
  exact pairCommuteBottomLeftNonAdj_WF D (derivWF_andElimLeft' wbundle)
    (derivWF_andElimLeft' (derivWF_andElimRight' wbundle)) wkAX
    (derivWF_andElimLeft' (derivWF_andElimRight' (derivWF_andElimRight' wbundle)))
    wnbulkA wntopA wnrightA wnleftA wnbulkB wntopB wnrightB wleftB wpacks hCtx

/-! ## megaPacks support: generic pin-pack WFA (allNatLtIntro over arithBool, bound `nP2`) -/

theorem nP2ArithBoolPack_WF {D : OddSurfaceDistance} {A : SFormula 3}
    {hfrag : arithBoolFragment A = true}
    {hvalid : ∀ (rho : Env 3) (E : PartialStabilizer),
      A.eval Surface.code.body (D.distance + 2) rho E = some true}
    {rho : Env 2} {E : PartialStabilizer} :
    DerivWFA (PureFamilyDerivA.allNatLtIntro (nP2 D)
      (PureFamilyDerivA.arithBool A hfrag hvalid)) rho E := by
  refine derivWFA_allNatLtIntro _ ⟨nQubits D.distance, ?_, fun y _ => True.intro⟩
  simp [nP2, SC.closed, STerm.eval, Term.eval, Term.lift, Term.weakenVar]

/-- Row-A flat-entry pack WFA (reuses the normalizer's `rowEntryFlatSym_WF`). -/
theorem entryAAtQ_WF (D : OddSurfaceDistance) (qT : Term 2 .nat) (hq : SFormula.PureNatTerm qT)
    {rho : Env 2} {E : PartialStabilizer} :
    DerivWFA (entryAAtQ D qT hq) rho E := by
  unfold entryAAtQ
  exact rowEntryFlatSym_WF D.index (distP2 D) k1P qT (SFormula.PureNatTerm.var ⟨1, by decide⟩) hq
    rho E (by have h : D.distance = 2 * D.index + 3 := rfl; omega)

/-- Row-B flat-entry pack WFA. -/
theorem entryBAtQ_WF (D : OddSurfaceDistance) (qT : Term 2 .nat) (hq : SFormula.PureNatTerm qT)
    {rho : Env 2} {E : PartialStabilizer} :
    DerivWFA (entryBAtQ D qT hq) rho E := by
  unfold entryBAtQ
  exact rowEntryFlatSym_WF D.index (distP2 D) k2P qT (SFormula.PureNatTerm.var ⟨0, by decide⟩) hq
    rho E (by have h : D.distance = 2 * D.index + 3 := rfl; omega)

/-- Recursively discharge `DerivWFA` for any pack built from `pfdaAnd2` / pin packs
(`allNatLtIntro` over `arithBool`) / flat-entry packs / `arithBool` leaves. -/
macro "pack_wfa" : tactic => `(tactic|
  repeat (first
    | exact nP2ArithBoolPack_WF
    | exact entryAAtQ_WF _ _ _
    | exact entryBAtQ_WF _ _ _
    | refine pfdaAnd2_WF ?_ ?_
    | exact True.intro))

theorem megaPacks_WF (D : OddSurfaceDistance) {rho : Env 2} {E : PartialStabilizer} :
    DerivWFA (megaPacks D) rho E := by
  unfold megaPacks
  pack_wfa

/-- `.and pairBundleF megaPacksF` evals `true` (soundness of `pfdaAnd2 pairBundle megaPacks`). -/
theorem pairAndMegaHolds (D : OddSurfaceDistance) (rho : Env 2) (E : PartialStabilizer) :
    (SFormula.and (pairBundleF D) (megaPacksF D)).eval Surface.code.body (D.distance + 2) rho E
      = some true :=
  PureFamilyDerivA.sound (pfdaAnd2 (pairBundle D) (megaPacks D)) rho E
    (pfda_defined (pfdaAnd2 (pairBundle D) (megaPacks D)) rho E
      (pfdaAnd2_WF (pairBundle_WF D) (megaPacks_WF D)))

end QHL.CodeLang.Surface.Verify
