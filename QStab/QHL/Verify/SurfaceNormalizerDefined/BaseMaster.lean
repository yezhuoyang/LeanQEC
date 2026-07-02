import QStab.QHL.Verify.SurfaceNormalizerDefined.BaseLeaf

/-!
# Normalizer sub-tree definedness — BaseMaster

The base master `DerivWF`, assembled from the per-peel / per-leaf lemmas.
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

set_option maxHeartbeats 1600000

/-! ## Base master `DerivWF` — assembled from the per-peel/per-leaf lemmas

The master's 5-deep `boolCases` tree is wired explicitly (each guard bool-eval is total,
`sterm_eval_closedPure`); every leaf is `eqPauliTrans (peel) (eqPauliSymm (leaf))`, whose
`DerivWF` is `⟨peel_WF, leaf_WF⟩`.  The peels/leaves carry `.hyp` guard children, whose
`DerivWF` is `True.intro`.  Built from the isolated lemmas — NO global `peel_walk` over
the whole master (that re-runs the explicit-simp cast strip per node and blows up). -/
theorem baseEntryMasterD_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer} :
    DerivWF (baseEntryMasterD (Γ := Γ) dT kT qT hq) cb fuel rho E := by
  unfold baseEntryMasterD
  refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?bulkT ?bulkF
  case bulkT =>
    refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?bandT ?bandF
    case bandT =>
      refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?kindT ?kindF
      case kindT =>
        exact derivWF_eqPauliTrans' (recBasePeelD_Z_WF _ _ _ _ hd hk hq True.intro True.intro True.intro)
          (derivWF_eqPauliSymm' (leafZ_WF _ _ _ hd hk hq True.intro True.intro True.intro))
      case kindF =>
        exact derivWF_eqPauliTrans' (recBasePeelD_X_WF _ _ _ _ hd hk hq True.intro True.intro True.intro)
          (derivWF_eqPauliSymm' (leafBulkX_WF _ _ _ _ hd hk hq True.intro True.intro True.intro))
    case bandF =>
      exact derivWF_eqPauliTrans' (recBasePeelD_I_WF _ _ _ _ hd hk hq True.intro True.intro)
        (derivWF_eqPauliSymm' (leafBulkI_WF _ _ _ _ hd hk hq True.intro True.intro))
  case bulkF =>
    refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?tcT ?tcF
    case tcT =>
      refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?tbT ?tbF
      case tbT =>
        exact derivWF_eqPauliTrans' (recTopXPeelD_WF _ _ _ _ hd hk hq True.intro True.intro True.intro)
          (derivWF_eqPauliSymm' (leafTopX_WF _ _ _ _ hd hk hq True.intro True.intro True.intro))
      case tbF =>
        exact derivWF_eqPauliTrans' (recTopIPeelD_WF _ _ _ _ hd hk hq True.intro True.intro True.intro)
          (derivWF_eqPauliSymm' (leafTopI_WF _ _ _ _ hd hk hq True.intro True.intro True.intro))
    case tcF =>
      refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?rcT ?rcF
      case rcT =>
        refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?rbT ?rbF
        case rbT =>
          exact derivWF_eqPauliTrans'
            (recRightZPeelD_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro)
            (derivWF_eqPauliSymm'
              (leafRightZ_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro))
        case rbF =>
          exact derivWF_eqPauliTrans'
            (recRightIPeelD_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro)
            (derivWF_eqPauliSymm'
              (leafRightI_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro))
      case rcF =>
        refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?lcT ?lcF
        case lcT =>
          refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?lbT ?lbF
          case lbT =>
            exact derivWF_eqPauliTrans'
              (recLeftZPeelD_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro True.intro)
              (derivWF_eqPauliSymm'
                (leafLeftZ_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro True.intro))
          case lbF =>
            exact derivWF_eqPauliTrans'
              (recLeftIPeelD_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro True.intro)
              (derivWF_eqPauliSymm'
                (leafLeftI_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro True.intro))
        case lcF =>
          refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?bbT ?bbF
          case bbT =>
            exact derivWF_eqPauliTrans'
              (recBottomXPeelD_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro True.intro)
              (derivWF_eqPauliSymm'
                (leafBottomX_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro True.intro))
          case bbF =>
            exact derivWF_eqPauliTrans'
              (recBottomIPeelD_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro True.intro)
              (derivWF_eqPauliSymm'
                (leafBottomI_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro True.intro))

/-- `DerivWF` of `baseLeafSelfEq` (the roundabout reflexivity `baseLeafTreeTA = baseLeafTreeTA`):
same 7-level boolCases structure as `baseEntryMasterD_WF`, but each leaf is `leafX / leafX`
(no peel side).  Consumed by `recFallbackPeelD_WF` / `baseBoundaryStripD_WF`. -/
theorem baseLeafSelfEq_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer} :
    DerivWF (baseLeafSelfEq (Γ := Γ) dT kT qT) cb fuel rho E := by
  unfold baseLeafSelfEq
  refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?bulkT ?bulkF
  case bulkT =>
    refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?bandT ?bandF
    case bandT =>
      refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?kindT ?kindF
      case kindT =>
        exact derivWF_eqPauliTrans' (leafZ_WF _ _ _ hd hk hq True.intro True.intro True.intro)
          (derivWF_eqPauliSymm' (leafZ_WF _ _ _ hd hk hq True.intro True.intro True.intro))
      case kindF =>
        exact derivWF_eqPauliTrans' (leafBulkX_WF _ _ _ _ hd hk hq True.intro True.intro True.intro)
          (derivWF_eqPauliSymm' (leafBulkX_WF _ _ _ _ hd hk hq True.intro True.intro True.intro))
    case bandF =>
      exact derivWF_eqPauliTrans' (leafBulkI_WF _ _ _ _ hd hk hq True.intro True.intro)
        (derivWF_eqPauliSymm' (leafBulkI_WF _ _ _ _ hd hk hq True.intro True.intro))
  case bulkF =>
    refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?tcT ?tcF
    case tcT =>
      refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?tbT ?tbF
      case tbT =>
        exact derivWF_eqPauliTrans' (leafTopX_WF _ _ _ _ hd hk hq True.intro True.intro True.intro)
          (derivWF_eqPauliSymm' (leafTopX_WF _ _ _ _ hd hk hq True.intro True.intro True.intro))
      case tbF =>
        exact derivWF_eqPauliTrans' (leafTopI_WF _ _ _ _ hd hk hq True.intro True.intro True.intro)
          (derivWF_eqPauliSymm' (leafTopI_WF _ _ _ _ hd hk hq True.intro True.intro True.intro))
    case tcF =>
      refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?rcT ?rcF
      case rcT =>
        refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?rbT ?rbF
        case rbT =>
          exact derivWF_eqPauliTrans'
            (leafRightZ_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro)
            (derivWF_eqPauliSymm'
              (leafRightZ_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro))
        case rbF =>
          exact derivWF_eqPauliTrans'
            (leafRightI_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro)
            (derivWF_eqPauliSymm'
              (leafRightI_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro))
      case rcF =>
        refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?lcT ?lcF
        case lcT =>
          refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?lbT ?lbF
          case lbT =>
            exact derivWF_eqPauliTrans'
              (leafLeftZ_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro True.intro)
              (derivWF_eqPauliSymm'
                (leafLeftZ_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro True.intro))
          case lbF =>
            exact derivWF_eqPauliTrans'
              (leafLeftI_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro True.intro)
              (derivWF_eqPauliSymm'
                (leafLeftI_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro True.intro))
        case lcF =>
          refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?bbT ?bbF
          case bbT =>
            exact derivWF_eqPauliTrans'
              (leafBottomX_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro True.intro)
              (derivWF_eqPauliSymm'
                (leafBottomX_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro True.intro))
          case bbF =>
            exact derivWF_eqPauliTrans'
              (leafBottomI_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro True.intro)
              (derivWF_eqPauliSymm'
                (leafBottomI_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro True.intro))

set_option maxHeartbeats 400000

end QHL.CodeLang.Surface.Verify
