import QStab.QHL.Verify.SurfaceRowsCommuteDefined.Router

/-!
# Rows-commute definedness — Assembly

The top: `rowsCommuteSym_WF` (cut over allDispatch + per-type boolCases tree) and the
`codeLevelDefined` assembly (weights + pair-from-normalizers + the codeLevel tree).
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

set_option maxHeartbeats 1600000

/-! ## The top: rowsCommuteSym_WF (cut over allDispatch + per-(k1,k2)-type boolCases tree) -/

theorem rowsCommuteSym_WF (D : OddSurfaceDistance) {E : PartialStabilizer} :
    DerivWFA (rowsCommuteSym D) Env.empty E := by
  unfold rowsCommuteSym
  refine derivWFA_cut1 ?core (allDispatch_WF D)
  refine derivWF_allNatLtIntroBounded _ _ ⟨numStab D.distance, ?_, fun x1 hx1 => ⟨?_, ?_⟩⟩
  · simp [SC.closed, STerm.eval, Term.eval, Term.lift]
  · -- child: second bounded binder
    refine derivWF_allNatLtIntroBounded _ _ ⟨numStab D.distance, ?_, fun x2 hx2 => ⟨?_, ?_⟩⟩
    · simp [SC.closed, STerm.eval, Term.eval, Term.lift]
    · -- boolCases tree on isXTypeTA k1 / k2
      refine derivWF_boolCases _ _
        (sterm_eval_closedPure (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))) ?_ ?_
      · refine derivWF_boolCases _ _
          (sterm_eval_closedPure (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))) ?_ ?_
        · -- (X,X): instSDFXid
          exact derivWF_mp (derivWF_mp (instSDFXid_WF D
            (cw2_WF (derivWF_andElimLeft' (derivWF_andElimRight' (derivWF_hyp _))))
            (cw2_WF (derivWF_hyp _)) (cw2_WF (derivWF_hyp _))) (derivWF_hyp _)) (derivWF_hyp _)
        · -- (X,Z): instDDFid
          exact derivWF_mp (derivWF_mp (instDDFid_WF D
            (cw2_WF (derivWF_andElimLeft' (derivWF_hyp _)))
            (cw2_WF (derivWF_hyp _)) (cw2_WF (derivWF_hyp _))) (derivWF_hyp _)) (derivWF_hyp _)
      · refine derivWF_boolCases _ _
          (sterm_eval_closedPure (by repeat (first | exact dP2_pure D | exact SFormula.PureNatTerm.var _ | exact SFormula.PureNatTerm.natLit _ | constructor))) ?_ ?_
        · -- (Z,X): commutesSymm + instDDFswap
          exact derivWF_commutesSymm (derivWF_mp (derivWF_mp (instDDFswap_WF D
            (cw2_WF (derivWF_andElimLeft' (derivWF_hyp _)))
            (cw2_WF (derivWF_hyp _)) (cw2_WF (derivWF_hyp _))) (derivWF_hyp _)) (derivWF_hyp _))
        · -- (Z,Z): instSDFZid
          exact derivWF_mp (derivWF_mp (instSDFZid_WF D
            (cw2_WF (derivWF_andElimRight' (derivWF_andElimRight' (derivWF_hyp _))))
            (cw2_WF (derivWF_hyp _)) (cw2_WF (derivWF_hyp _))) (derivWF_hyp _)) (derivWF_hyp _)
    · -- ContextHolds (cons x1 empty) [boundNatLt n0, allDispatchF.weaken]
      exact contextHolds_boundNatLt_cons _ _ _ _ _ _ _ _
        (by simp [SC.closed, STerm.eval, Term.eval, Term.lift]) hx1
        (fun A hA => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
          subst hA; exact allDispatchHolds D E)
  · -- ContextHolds Env.empty [allDispatchF D]
    intro A hA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
    subst hA; exact allDispatchHolds D E

/-! ## codeLevelDefined assembly: weights + pair-from-normalizers + the codeLevel tree -/

theorem logicalWeightsPure_WF (D : OddSurfaceDistance) (E : PartialStabilizer) :
    DerivWFA (logicalWeightsPure D) Env.empty E := by
  unfold logicalWeightsPure
  exact derivWFA_cut2 (derivWF_andIntro (derivWF_hyp _) (derivWF_hyp _))
    (logicalXWeightExactPure_WF D E) (logicalZWeightExactPure_WF D E)

theorem logicalPairPureFromNormalizers_WF (D : OddSurfaceDistance) (E : PartialStabilizer) :
    DerivWFA (logicalPairPureFromNormalizers D (xNormScaffold D) (zNormScaffold D)) Env.empty E := by
  unfold logicalPairPureFromNormalizers
  exact derivWFA_cut2 (derivWF_andIntro (derivWF_hyp _) (derivWF_hyp _)) (xNormScaffold_WF D E)
    (derivWFA_cut2 (derivWF_andIntro (derivWF_hyp _) (derivWF_hyp _)) (zNormScaffold_WF D E)
      (logicalXZNoncommPure_WF D E))

theorem codeLevelDefinedAux (D : OddSurfaceDistance) (E : PartialStabilizer) :
    (codeLevelPureFromGeneratedRows D (rowsCommuteSym D) (xNormScaffold D)
      (zNormScaffold D)).DefinedObligations E := by
  refine pfd_defined _ E ?_
  unfold codeLevelPureFromGeneratedRows
  refine derivWFP_arity0 ?_
  exact derivWFA_cut2 (derivWF_andIntro (derivWF_hyp _) (derivWF_hyp _)) (rowsCommuteSym_WF D)
    (derivWFA_cut2 (derivWF_andIntro (derivWF_hyp _) (derivWF_hyp _))
      (logicalPairPureFromNormalizers_WF D E) (logicalWeightsPure_WF D E))

end QHL.CodeLang.Surface.Verify
