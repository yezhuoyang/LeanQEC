import QStab.QHL.Verify.SurfaceRowsCommuteDefined.Dispatchers

/-!
# Rows-commute definedness — Router

The top-level (X,Z) router (boolCases tree on class guards → the 9 dispatchers), the
different-type ∀∀ family + combined dispatch family, and the `inst*` family-instantiation WFs.
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

set_option maxHeartbeats 1600000

/-! ## Top-level (X,Z) router: boolCases tree on class guards → the 9 dispatchers -/

theorem dispatchRouter_WF (D : OddSurfaceDistance) {Γ : List (SFormula 2)}
    {hbundle : SFormula.Deriv Γ (pairBundleF D)} {hmega : SFormula.Deriv Γ (megaPacksF D)}
    {hkAX : SFormula.Deriv Γ (k1IsX D true)} {hkBZ : SFormula.Deriv Γ (k2IsX D false)}
    {rho : Env 2} {E : PartialStabilizer}
    (wbundle : DerivWF hbundle Surface.code.body (D.distance + 2) rho E)
    (wmega : DerivWF hmega Surface.code.body (D.distance + 2) rho E)
    (wkAX : DerivWF hkAX Surface.code.body (D.distance + 2) rho E)
    (wkBZ : DerivWF hkBZ Surface.code.body (D.distance + 2) rho E)
    (hCtx : SFormula.ContextHolds Surface.code.body (D.distance + 2) rho E Γ) :
    DerivWF (dispatchRouter D hbundle hmega hkAX hkBZ) Surface.code.body (D.distance + 2) rho E := by
  unfold dispatchRouter
  have wExcl1 := derivWF_andElimLeft' (derivWF_andElimRight' (derivWF_andElimRight' wbundle))
  have wExcl2 := derivWF_andElimRight' (derivWF_andElimRight' (derivWF_andElimRight' wbundle))
  have wMdbb := derivWF_andElimLeft' wmega
  have wMr1 := derivWF_andElimRight' wmega
  have wMdbr := derivWF_andElimLeft' wMr1
  have wMr2 := derivWF_andElimRight' wMr1
  have wMdbl := derivWF_andElimLeft' wMr2
  have wMr3 := derivWF_andElimRight' wMr2
  have wMdtb := derivWF_andElimLeft' wMr3
  have wMr4 := derivWF_andElimRight' wMr3
  have wMdbtb := derivWF_andElimLeft' wMr4
  have wMr5 := derivWF_andElimRight' wMr4
  have wMdtr := derivWF_andElimLeft' wMr5
  have wMr6 := derivWF_andElimRight' wMr5
  have wMdtl := derivWF_andElimLeft' wMr6
  have wMr7 := derivWF_andElimRight' wMr6
  have wMdbtr := derivWF_andElimLeft' wMr7
  have wMdbtl := derivWF_andElimRight' wMr7
  have wXtNotRightZ := derivWF_andElimLeft' (derivWF_andElimRight' wExcl1)
  have wXtNotLeftZ := derivWF_andElimLeft' (derivWF_andElimRight' (derivWF_andElimRight' wExcl1))
  have wZtNotTopX := derivWF_andElimLeft' (derivWF_andElimRight' (derivWF_andElimRight'
    (derivWF_andElimRight' (derivWF_andElimRight' wExcl2))))
  have wZtNotBottomX := derivWF_andElimRight' (derivWF_andElimRight'
    (derivWF_andElimRight' (derivWF_andElimRight' (derivWF_andElimRight' wExcl2))))
  refine derivWF_boolCases_cond _ _
    (sterm_eval_closedPure (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor)))
    (fun hb1T => ?_) (fun hb1F => ?_)
  · -- k1bulk
    refine derivWF_boolCases_cond _ _
      (sterm_eval_closedPure (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor)))
      (fun hb2T => ?_) (fun hb2F => ?_)
    · -- k1b_k2bulk → dispatchBulkBulk
      exact dispatchBulkBulk_WF D (cw2_WF wbundle) (cw2_WF wMdbb) (cw2_WF wkAX) (cw2_WF wkBZ)
        (cw1_WF (derivWF_hyp _)) (derivWF_hyp _)
        (contextHolds_cons_eqBoolTrue (contextHolds_cons_eqBoolTrue hCtx hb1T) hb2T)
    · -- k1b_k2nbulk
      refine derivWF_boolCases_cond _ _
        (sterm_eval_closedPure (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor)))
        (fun hrT => ?_) (fun hrF => ?_)
      · -- rT → dispatchBulkRight
        exact dispatchBulkRight_WF D (cw3_WF wbundle) (cw3_WF wMdbr) (cw3_WF wkAX) (cw3_WF wkBZ)
          (cw2_WF (derivWF_hyp _)) (cw1_WF (derivWF_hyp _))
          (cw1_WF (derivWF_mp (derivWF_mp (cw2_WF wZtNotTopX) (cw2_WF wkBZ)) (derivWF_hyp _)))
          (derivWF_hyp _)
          (contextHolds_cons_eqBoolTrue (contextHolds_cons_eqBoolFalse
            (contextHolds_cons_eqBoolTrue hCtx hb1T) hb2F) hrT)
      · -- rF
        refine derivWF_boolCases_cond _ _
          (sterm_eval_closedPure (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor)))
          (fun hlT => ?_) (fun hlF => ?_)
        · -- lT → dispatchBulkLeft
          exact dispatchBulkLeft_WF D (cw4_WF wbundle) (cw4_WF wMdbl) (cw4_WF wkAX) (cw4_WF wkBZ)
            (cw3_WF (derivWF_hyp _)) (cw2_WF (derivWF_hyp _))
            (cw2_WF (derivWF_mp (derivWF_mp (cw2_WF wZtNotTopX) (cw2_WF wkBZ)) (derivWF_hyp _)))
            (cw1_WF (derivWF_hyp _)) (derivWF_hyp _)
            (contextHolds_cons_eqBoolTrue (contextHolds_cons_eqBoolFalse (contextHolds_cons_eqBoolFalse
              (contextHolds_cons_eqBoolTrue hCtx hb1T) hb2F) hrF) hlT)
        · -- lF: vacuous
          exact derivWF_botElim (derivWF_notElim
            (derivWF_mp (derivWF_mp (derivWF_mp (cw4_WF wZtNotBottomX) (cw4_WF wkBZ))
              (cw2_WF (derivWF_hyp _)))
              (cw2_WF (derivWF_mp (derivWF_mp (cw2_WF wZtNotTopX) (cw2_WF wkBZ)) (derivWF_hyp _))))
            (derivWF_eqBoolFalseNotTrue (derivWF_hyp _)))
  · -- k1nbulk
    refine derivWF_boolCases_cond _ _
      (sterm_eval_closedPure (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor)))
      (fun hb2T => ?_) (fun hb2F => ?_)
    · -- k1nb_k2bulk
      refine derivWF_boolCases_cond _ _
        (sterm_eval_closedPure (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor)))
        (fun htbT => ?_) (fun htbF => ?_)
      · -- tbT → dispatchTopBulk
        exact dispatchTopBulk_WF D (cw3_WF wbundle) (cw3_WF wMdtb) (cw3_WF wkAX) (cw3_WF wkBZ)
          (cw2_WF (derivWF_hyp _)) (derivWF_hyp _) (cw1_WF (derivWF_hyp _))
          (contextHolds_cons_eqBoolTrue (contextHolds_cons_eqBoolTrue
            (contextHolds_cons_eqBoolFalse hCtx hb1F) hb2T) htbT)
      · -- tbF → dispatchBottomBulk
        exact dispatchBottomBulk_WF D (cw3_WF wbundle) (cw3_WF wMdbtb) (cw3_WF wkAX) (cw3_WF wkBZ)
          (cw2_WF (derivWF_hyp _)) (derivWF_hyp _)
          (derivWF_mp (derivWF_mp (derivWF_mp (cw3_WF wXtNotRightZ) (cw3_WF wkAX))
            (cw2_WF (derivWF_hyp _))) (derivWF_hyp _))
          (derivWF_mp (derivWF_mp (derivWF_mp (derivWF_mp (cw3_WF wXtNotLeftZ) (cw3_WF wkAX))
            (cw2_WF (derivWF_hyp _))) (derivWF_hyp _))
            (derivWF_mp (derivWF_mp (derivWF_mp (cw3_WF wXtNotRightZ) (cw3_WF wkAX))
              (cw2_WF (derivWF_hyp _))) (derivWF_hyp _)))
          (cw1_WF (derivWF_hyp _))
          (contextHolds_cons_eqBoolFalse (contextHolds_cons_eqBoolTrue
            (contextHolds_cons_eqBoolFalse hCtx hb1F) hb2T) htbF)
    · -- k1nb_k2nbulk
      refine derivWF_boolCases_cond _ _
        (sterm_eval_closedPure (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor)))
        (fun htopT => ?_) (fun htopF => ?_)
      · -- topT
        refine derivWF_boolCases_cond _ _
          (sterm_eval_closedPure (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor)))
          (fun htrT => ?_) (fun htrF => ?_)
        · -- trT → dispatchTopRight
          exact dispatchTopRight_WF D (cw4_WF wbundle) (cw4_WF wMdtr) (cw4_WF wkAX) (cw4_WF wkBZ)
            (cw3_WF (derivWF_hyp _)) (cw1_WF (derivWF_hyp _)) (cw2_WF (derivWF_hyp _))
            (cw2_WF (derivWF_mp (derivWF_mp (cw2_WF wZtNotTopX) (cw2_WF wkBZ)) (derivWF_hyp _)))
            (derivWF_hyp _)
            (contextHolds_cons_eqBoolTrue (contextHolds_cons_eqBoolTrue (contextHolds_cons_eqBoolFalse
              (contextHolds_cons_eqBoolFalse hCtx hb1F) hb2F) htopT) htrT)
        · -- trF
          refine derivWF_boolCases_cond _ _
            (sterm_eval_closedPure (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor)))
            (fun htlT => ?_) (fun htlF => ?_)
          · -- tlT → dispatchTopLeft
            exact dispatchTopLeft_WF D (cw5_WF wbundle) (cw5_WF wMdtl) (cw5_WF wkAX) (cw5_WF wkBZ)
              (cw4_WF (derivWF_hyp _)) (cw2_WF (derivWF_hyp _)) (cw3_WF (derivWF_hyp _))
              (cw3_WF (derivWF_mp (derivWF_mp (cw2_WF wZtNotTopX) (cw2_WF wkBZ)) (derivWF_hyp _)))
              (cw1_WF (derivWF_hyp _)) (derivWF_hyp _)
              (contextHolds_cons_eqBoolTrue (contextHolds_cons_eqBoolFalse (contextHolds_cons_eqBoolTrue
                (contextHolds_cons_eqBoolFalse (contextHolds_cons_eqBoolFalse hCtx hb1F) hb2F) htopT) htrF) htlT)
          · -- tlF: vacuous
            exact derivWF_botElim (derivWF_notElim
              (derivWF_mp (derivWF_mp (derivWF_mp (cw5_WF wZtNotBottomX) (cw5_WF wkBZ))
                (cw3_WF (derivWF_hyp _)))
                (cw3_WF (derivWF_mp (derivWF_mp (cw2_WF wZtNotTopX) (cw2_WF wkBZ)) (derivWF_hyp _))))
              (derivWF_eqBoolFalseNotTrue (derivWF_hyp _)))
      · -- topF
        refine derivWF_boolCases_cond _ _
          (sterm_eval_closedPure (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor)))
          (fun hbrT => ?_) (fun hbrF => ?_)
        · -- brT → dispatchBottomRight
          exact dispatchBottomRight_WF D (cw4_WF wbundle) (cw4_WF wMdbtr) (cw4_WF wkAX) (cw4_WF wkBZ)
            (cw3_WF (derivWF_hyp _)) (cw1_WF (derivWF_hyp _))
            (cw1_WF (derivWF_mp (derivWF_mp (derivWF_mp (cw3_WF wXtNotRightZ) (cw3_WF wkAX))
              (cw2_WF (derivWF_hyp _))) (derivWF_hyp _)))
            (cw1_WF (derivWF_mp (derivWF_mp (derivWF_mp (derivWF_mp (cw3_WF wXtNotLeftZ) (cw3_WF wkAX))
              (cw2_WF (derivWF_hyp _))) (derivWF_hyp _))
              (derivWF_mp (derivWF_mp (derivWF_mp (cw3_WF wXtNotRightZ) (cw3_WF wkAX))
                (cw2_WF (derivWF_hyp _))) (derivWF_hyp _))))
            (cw2_WF (derivWF_hyp _))
            (cw2_WF (derivWF_mp (derivWF_mp (cw2_WF wZtNotTopX) (cw2_WF wkBZ)) (derivWF_hyp _)))
            (derivWF_hyp _)
            (contextHolds_cons_eqBoolTrue (contextHolds_cons_eqBoolFalse (contextHolds_cons_eqBoolFalse
              (contextHolds_cons_eqBoolFalse hCtx hb1F) hb2F) htopF) hbrT)
        · -- brF
          refine derivWF_boolCases_cond _ _
            (sterm_eval_closedPure (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor)))
            (fun hblT => ?_) (fun hblF => ?_)
          · -- blT → dispatchBottomLeft
            exact dispatchBottomLeft_WF D (cw5_WF wbundle) (cw5_WF wMdbtl) (cw5_WF wkAX) (cw5_WF wkBZ)
              (cw4_WF (derivWF_hyp _)) (cw2_WF (derivWF_hyp _))
              (cw2_WF (derivWF_mp (derivWF_mp (derivWF_mp (cw3_WF wXtNotRightZ) (cw3_WF wkAX))
                (cw2_WF (derivWF_hyp _))) (derivWF_hyp _)))
              (cw2_WF (derivWF_mp (derivWF_mp (derivWF_mp (derivWF_mp (cw3_WF wXtNotLeftZ) (cw3_WF wkAX))
                (cw2_WF (derivWF_hyp _))) (derivWF_hyp _))
                (derivWF_mp (derivWF_mp (derivWF_mp (cw3_WF wXtNotRightZ) (cw3_WF wkAX))
                  (cw2_WF (derivWF_hyp _))) (derivWF_hyp _))))
              (cw3_WF (derivWF_hyp _))
              (cw3_WF (derivWF_mp (derivWF_mp (cw2_WF wZtNotTopX) (cw2_WF wkBZ)) (derivWF_hyp _)))
              (cw1_WF (derivWF_hyp _)) (derivWF_hyp _)
              (contextHolds_cons_eqBoolTrue (contextHolds_cons_eqBoolFalse (contextHolds_cons_eqBoolFalse
                (contextHolds_cons_eqBoolFalse (contextHolds_cons_eqBoolFalse hCtx hb1F) hb2F) htopF) hbrF) hblT)
          · -- blF: vacuous
            exact derivWF_botElim (derivWF_notElim
              (derivWF_mp (derivWF_mp (derivWF_mp (cw5_WF wZtNotBottomX) (cw5_WF wkBZ))
                (cw3_WF (derivWF_hyp _)))
                (cw3_WF (derivWF_mp (derivWF_mp (cw2_WF wZtNotTopX) (cw2_WF wkBZ)) (derivWF_hyp _))))
              (derivWF_eqBoolFalseNotTrue (derivWF_hyp _)))

/-! ## Different-type ∀∀ family + combined dispatch family -/

theorem dispatchDiffType_WF (D : OddSurfaceDistance) {E : PartialStabilizer} :
    DerivWFA (dispatchDiffType D) Env.empty E := by
  unfold dispatchDiffType
  refine derivWFA_allNatLtIntro _ ⟨numStab D.distance,
    by simp [SC.closed, STerm.eval, Term.eval], fun k1 _ => ?_⟩
  refine derivWFA_allNatLtIntro _ ⟨numStab D.distance,
    by simp [SC.closed, STerm.eval, Term.eval, Term.lift], fun k2 _ => ?_⟩
  refine derivWFA_cut1 ?core (pfdaAnd2_WF (pairBundle_WF D) (megaPacks_WF D))
  refine derivWF_impIntro_cond ?fdA (fun hk1 => derivWF_impIntro_cond ?fdB (fun hk2 => ?inner))
  case fdA =>
    exact formulaDefined_eqBool (sterm_eval_closedPure (by repeat (first | assumption | constructor)))
      (sterm_eval_b _)
  case fdB =>
    exact formulaDefined_eqBool (sterm_eval_closedPure (by repeat (first | assumption | constructor)))
      (sterm_eval_b _)
  case inner =>
    refine dispatchRouter_WF D (by comm_deriv_wf) (by comm_deriv_wf) (by comm_deriv_wf)
      (by comm_deriv_wf) ?hCtx
    intro F hF
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with h | h | h <;> subst h
    · exact hk2
    · exact hk1
    · exact pairAndMegaHolds D _ E

theorem allDispatch_WF (D : OddSurfaceDistance) {E : PartialStabilizer} :
    DerivWFA (allDispatch D) Env.empty E := by
  unfold allDispatch
  exact pfdaAndG_WF (dispatchDiffType_WF D) (pfdaAndG_WF (sameTypeXFamily_WF D) (sameTypeZFamily_WF D))

/-- `allDispatchF` evals `true` at `Env.empty` (soundness of `allDispatch`). -/
theorem allDispatchHolds (D : OddSurfaceDistance) (E : PartialStabilizer) :
    (allDispatchF D).eval Surface.code.body (D.distance + 2) Env.empty E = some true :=
  PureFamilyDerivA.sound (allDispatch D) Env.empty E
    (pfda_defined (allDispatch D) Env.empty E (allDispatch_WF D))

/-! ## inst* family-instantiation WFs (probe) -/

theorem instDDFid_WF (D : OddSurfaceDistance) {Γ : List (SFormula 2)}
    {hF : SFormula.Deriv Γ ((SFormula.allNatLt (SC.closed (Term.natLit (numStab D.distance)))
        (SFormula.allNatLt (SC.closed (Term.lift 0 (Term.natLit (numStab D.distance))))
          (diffTypeBody D))).weaken.weaken)}
    {hk1Lt : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed k1P) (famN0 D))}
    {hk2Lt : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed k2P) (famN0 D))}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env 2} {E : PartialStabilizer}
    (wF : DerivWF hF cb fuel rho E) (wk1Lt : DerivWF hk1Lt cb fuel rho E)
    (wk2Lt : DerivWF hk2Lt cb fuel rho E) :
    DerivWF (instDDFid D hF hk1Lt hk2Lt) cb fuel rho E := by
  unfold instDDFid
  refine derivWF_cast_type rfl ?_ _ _ ?_
  · simp [diffTypeBody, k1IsX, k2IsX, pairGoal, nP2, rowA, rowB, dP2, k1P, k2P,
      isXTypeTA, bulkGuardTA, baseKindGuardTA, topClassGuardTA, rightClassGuardTA, leftClassGuardTA,
      bulkCountTA, dm1TA, baseBTA, baseHalfTA,
      SFormula.instantiateTopNat, SFormula.instantiateNatAt, SFormula.lift, SFormula.weaken,
      STerm.instantiateNatAt, STerm.lift, STerm.weaken, Term.instantiateNatAt, Term.lift,
      Term.weaken, Term.weakenVar, SC.n, SC.closed, SC.b]
  · refine derivWF_applyNatSubstitutionBetaElim ?_
    refine derivWF_allNatLtElim _ _ _ ?_ wk2Lt
    refine derivWF_cast_type rfl ?_ _ _ ?_
    · simp only [SFormula.instantiateTopNat, SFormula.instantiateNatAt, SFormula.lift,
        STerm.instantiateNatAt, STerm.lift, Term.instantiateNatAt, Term.lift,
        STerm.weaken, SFormula.weaken, Term.weaken, Term.weakenVar, SC.n, SC.closed]
    · refine derivWF_applyNatSubstitutionBetaElim ?_
      exact derivWF_allNatLtElim _ _ _ wF wk1Lt

theorem instDDFswap_WF (D : OddSurfaceDistance) {Γ : List (SFormula 2)}
    {hF : SFormula.Deriv Γ ((SFormula.allNatLt (SC.closed (Term.natLit (numStab D.distance)))
        (SFormula.allNatLt (SC.closed (Term.lift 0 (Term.natLit (numStab D.distance))))
          (diffTypeBody D))).weaken.weaken)}
    {hk1Lt : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed k1P) (famN0 D))}
    {hk2Lt : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed k2P) (famN0 D))}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env 2} {E : PartialStabilizer}
    (wF : DerivWF hF cb fuel rho E) (wk1Lt : DerivWF hk1Lt cb fuel rho E)
    (wk2Lt : DerivWF hk2Lt cb fuel rho E) :
    DerivWF (instDDFswap D hF hk1Lt hk2Lt) cb fuel rho E := by
  unfold instDDFswap
  refine derivWF_cast_type rfl ?_ _ _ ?_
  · simp [diffTypeBody, k1IsX, k2IsX, pairGoal, nP2, rowA, rowB, dP2, k1P, k2P,
      isXTypeTA, bulkGuardTA, baseKindGuardTA, topClassGuardTA, rightClassGuardTA, leftClassGuardTA,
      bulkCountTA, dm1TA, baseBTA, baseHalfTA,
      SFormula.instantiateTopNat, SFormula.instantiateNatAt, SFormula.lift, SFormula.weaken,
      STerm.instantiateNatAt, STerm.lift, STerm.weaken, Term.instantiateNatAt, Term.lift,
      Term.weaken, Term.weakenVar, SC.n, SC.closed, SC.b]
  · refine derivWF_applyNatSubstitutionBetaElim ?_
    refine derivWF_allNatLtElim _ _ _ ?_ wk1Lt
    refine derivWF_cast_type rfl ?_ _ _ ?_
    · simp only [SFormula.instantiateTopNat, SFormula.instantiateNatAt, SFormula.lift,
        STerm.instantiateNatAt, STerm.lift, Term.instantiateNatAt, Term.lift,
        STerm.weaken, SFormula.weaken, Term.weaken, Term.weakenVar, SC.n, SC.closed]
    · refine derivWF_applyNatSubstitutionBetaElim ?_
      exact derivWF_allNatLtElim _ _ _ wF wk2Lt

theorem instSDFXid_WF (D : OddSurfaceDistance) {Γ : List (SFormula 2)}
    {hF : SFormula.Deriv Γ ((SFormula.allNatLt (SC.closed (Term.natLit (numStab D.distance)))
        (SFormula.allNatLt (SC.closed (Term.lift 0 (Term.natLit (numStab D.distance))))
          (sameTypeXBody D))).weaken.weaken)}
    {hk1Lt : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed k1P) (famN0 D))}
    {hk2Lt : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed k2P) (famN0 D))}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env 2} {E : PartialStabilizer}
    (wF : DerivWF hF cb fuel rho E) (wk1Lt : DerivWF hk1Lt cb fuel rho E)
    (wk2Lt : DerivWF hk2Lt cb fuel rho E) :
    DerivWF (instSDFXid D hF hk1Lt hk2Lt) cb fuel rho E := by
  unfold instSDFXid
  refine derivWF_cast_type rfl ?_ _ _ ?_
  · simp [sameTypeXBody, k1IsX, k2IsX, pairGoal, nP2, rowA, rowB, dP2, k1P, k2P,
      isXTypeTA, bulkGuardTA, baseKindGuardTA, topClassGuardTA, rightClassGuardTA, leftClassGuardTA,
      bulkCountTA, dm1TA, baseBTA, baseHalfTA,
      SFormula.instantiateTopNat, SFormula.instantiateNatAt, SFormula.lift, SFormula.weaken,
      STerm.instantiateNatAt, STerm.lift, STerm.weaken, Term.instantiateNatAt, Term.lift,
      Term.weaken, Term.weakenVar, SC.n, SC.closed, SC.b]
  · refine derivWF_applyNatSubstitutionBetaElim ?_
    refine derivWF_allNatLtElim _ _ _ ?_ wk2Lt
    refine derivWF_cast_type rfl ?_ _ _ ?_
    · simp only [SFormula.instantiateTopNat, SFormula.instantiateNatAt, SFormula.lift,
        STerm.instantiateNatAt, STerm.lift, Term.instantiateNatAt, Term.lift,
        STerm.weaken, SFormula.weaken, Term.weaken, Term.weakenVar, SC.n, SC.closed]
    · refine derivWF_applyNatSubstitutionBetaElim ?_
      exact derivWF_allNatLtElim _ _ _ wF wk1Lt

theorem instSDFZid_WF (D : OddSurfaceDistance) {Γ : List (SFormula 2)}
    {hF : SFormula.Deriv Γ ((SFormula.allNatLt (SC.closed (Term.natLit (numStab D.distance)))
        (SFormula.allNatLt (SC.closed (Term.lift 0 (Term.natLit (numStab D.distance))))
          (sameTypeZBody D))).weaken.weaken)}
    {hk1Lt : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed k1P) (famN0 D))}
    {hk2Lt : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed k2P) (famN0 D))}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env 2} {E : PartialStabilizer}
    (wF : DerivWF hF cb fuel rho E) (wk1Lt : DerivWF hk1Lt cb fuel rho E)
    (wk2Lt : DerivWF hk2Lt cb fuel rho E) :
    DerivWF (instSDFZid D hF hk1Lt hk2Lt) cb fuel rho E := by
  unfold instSDFZid
  refine derivWF_cast_type rfl ?_ _ _ ?_
  · simp [sameTypeZBody, k1IsX, k2IsX, pairGoal, nP2, rowA, rowB, dP2, k1P, k2P,
      isXTypeTA, bulkGuardTA, baseKindGuardTA, topClassGuardTA, rightClassGuardTA, leftClassGuardTA,
      bulkCountTA, dm1TA, baseBTA, baseHalfTA,
      SFormula.instantiateTopNat, SFormula.instantiateNatAt, SFormula.lift, SFormula.weaken,
      STerm.instantiateNatAt, STerm.lift, STerm.weaken, Term.instantiateNatAt, Term.lift,
      Term.weaken, Term.weakenVar, SC.n, SC.closed, SC.b]
  · refine derivWF_applyNatSubstitutionBetaElim ?_
    refine derivWF_allNatLtElim _ _ _ ?_ wk2Lt
    refine derivWF_cast_type rfl ?_ _ _ ?_
    · simp only [SFormula.instantiateTopNat, SFormula.instantiateNatAt, SFormula.lift,
        STerm.instantiateNatAt, STerm.lift, Term.instantiateNatAt, Term.lift,
        STerm.weaken, SFormula.weaken, Term.weaken, Term.weakenVar, SC.n, SC.closed]
    · refine derivWF_applyNatSubstitutionBetaElim ?_
      exact derivWF_allNatLtElim _ _ _ wF wk1Lt

end QHL.CodeLang.Surface.Verify
