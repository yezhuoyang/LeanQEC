import QStab.QHL.Verify.SurfaceNormalizerDefined.RowSelect

/-!
# Normalizer sub-tree definedness — FlatBridge

Flat-bridge `DerivWF` infrastructure: the `baseLeaf*S` / `recLeaf*S` navigation lemmas and
the `flatStep*` inner↔outer flat-tree cell-equality lemmas.
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

set_option maxHeartbeats 1600000

/-! ## Flat-bridge `DerivWF` infrastructure

The flat bridge `rowSymTreeFlatBridgeSym` and its master `recFlatMasterD` are
**pure-formula** derivations (every node is `eqPauli`/`eqBool`/`imp`/`and`/`mp`/
`boolCases`/`pauliIteSelect`/`contextWeakening` over PurePauli/PureBool/PureNat
terms — NO `recCall`/`stabAt`/`recUnfold`).  So every `DerivWF` obligation is either
trivial (`hyp`/`assumption`/imp-arg → `True`) or `FormulaDefined` of a pure formula
(dischargeable by `formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)` /
`sterm_eval_closedPure`).  The uniform `flat_deriv_wf` tactic walks any such
derivation. -/

/-- `DerivWF (andElimLeft child) = DerivWF child` (definedness only recurses). -/
theorem derivWF_andElimLeft' {arity : Nat} {Γ : List (SFormula arity)} {A B : SFormula arity}
    {child : SFormula.Deriv Γ (.and A B)} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer} (h : DerivWF child cb fuel rho E) :
    DerivWF (SFormula.Deriv.andElimLeft child) cb fuel rho E := h

/-- `DerivWF (andElimRight child) = DerivWF child`. -/
theorem derivWF_andElimRight' {arity : Nat} {Γ : List (SFormula arity)} {A B : SFormula arity}
    {child : SFormula.Deriv Γ (.and A B)} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer} (h : DerivWF child cb fuel rho E) :
    DerivWF (SFormula.Deriv.andElimRight child) cb fuel rho E := h

/-- Uniform `DerivWF` discharger for a pure-formula derivation: applies the structural
`derivWF_*` combinators head-first, closes guard/imp child WFs by `assumption`/`True.intro`,
and every `FormulaDefined` leaf via the `PurePauli` route. -/
macro "flat_deriv_wf" : tactic =>
  `(tactic|
    repeat first
      | exact True.intro
      | assumption
      | refine derivWF_eqPauliTrans' ?_ ?_
      | refine derivWF_eqPauliSymm' ?_
      | refine derivWF_mp ?_ ?_
      | refine derivWF_andIntro ?_ ?_
      | refine derivWF_andElimLeft' ?_
      | refine derivWF_andElimRight' ?_
      | refine derivWF_contextWeakening' _ _ ?_
      | refine derivWF_pauliIteSelectThen' _ _ _ ?_ ?_
      | refine derivWF_pauliIteSelectElse' _ _ _ ?_ ?_
      | refine derivWF_boolCases _ _
          (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?_ ?_
      | apply formulaDefined_eqPauli_purePauli
      | leaf_pp)

/-! ### `baseLeaf*S` flat-leaf navigation `DerivWF` lemmas (resolve `baseLeafTreeTA` to the
selected `pauliLit` from the cell-class/band guards).  Proved once each, cited by the
`flatStep*` `DerivWF` proofs so the big leaf trees are never re-walked. -/

theorem baseLeafZS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hBand hKind} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wBand : DerivWF hBand cb fuel rho E)
    (wKind : DerivWF hKind cb fuel rho E) :
    DerivWF (baseLeafZS (Γ := Γ) dT kT qT hBulk hBand hKind) cb fuel rho E := by
  unfold baseLeafZS; flat_deriv_wf

theorem baseLeafXS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hBand hKind} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wBand : DerivWF hBand cb fuel rho E)
    (wKind : DerivWF hKind cb fuel rho E) :
    DerivWF (baseLeafXS (Γ := Γ) dT kT qT hBulk hBand hKind) cb fuel rho E := by
  unfold baseLeafXS; flat_deriv_wf

theorem baseLeafBulkIS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hBand} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wBand : DerivWF hBand cb fuel rho E) :
    DerivWF (baseLeafBulkIS (Γ := Γ) dT kT qT hBulk hBand) cb fuel rho E := by
  unfold baseLeafBulkIS; flat_deriv_wf

theorem baseLeafTopXS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hTopClass hTopBand} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wTopBand : DerivWF hTopBand cb fuel rho E) :
    DerivWF (baseLeafTopXS (Γ := Γ) dT kT qT hBulk hTopClass hTopBand) cb fuel rho E := by
  unfold baseLeafTopXS; flat_deriv_wf

theorem baseLeafTopIS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hTopClass hTopBand} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wTopBand : DerivWF hTopBand cb fuel rho E) :
    DerivWF (baseLeafTopIS (Γ := Γ) dT kT qT hBulk hTopClass hTopBand) cb fuel rho E := by
  unfold baseLeafTopIS; flat_deriv_wf

theorem baseLeafRightZS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hTopClass hRightClass hRightBand}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wRightBand : DerivWF hRightBand cb fuel rho E) :
    DerivWF (baseLeafRightZS (Γ := Γ) dT kT qT hBulk hTopClass hRightClass hRightBand) cb fuel rho E := by
  unfold baseLeafRightZS; flat_deriv_wf

theorem baseLeafRightIS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hTopClass hRightClass hRightBand}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wRightBand : DerivWF hRightBand cb fuel rho E) :
    DerivWF (baseLeafRightIS (Γ := Γ) dT kT qT hBulk hTopClass hRightClass hRightBand) cb fuel rho E := by
  unfold baseLeafRightIS; flat_deriv_wf

theorem baseLeafLeftZS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hTopClass hRightClass hLeftClass hLeftBand}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wLeftClass : DerivWF hLeftClass cb fuel rho E)
    (wLeftBand : DerivWF hLeftBand cb fuel rho E) :
    DerivWF (baseLeafLeftZS (Γ := Γ) dT kT qT hBulk hTopClass hRightClass hLeftClass hLeftBand) cb fuel rho E := by
  unfold baseLeafLeftZS; flat_deriv_wf

theorem baseLeafLeftIS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hTopClass hRightClass hLeftClass hLeftBand}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wLeftClass : DerivWF hLeftClass cb fuel rho E)
    (wLeftBand : DerivWF hLeftBand cb fuel rho E) :
    DerivWF (baseLeafLeftIS (Γ := Γ) dT kT qT hBulk hTopClass hRightClass hLeftClass hLeftBand) cb fuel rho E := by
  unfold baseLeafLeftIS; flat_deriv_wf

theorem baseLeafBottomXS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hTopClass hRightClass hLeftClass hBottomBand}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wLeftClass : DerivWF hLeftClass cb fuel rho E)
    (wBottomBand : DerivWF hBottomBand cb fuel rho E) :
    DerivWF (baseLeafBottomXS (Γ := Γ) dT kT qT hBulk hTopClass hRightClass hLeftClass hBottomBand) cb fuel rho E := by
  unfold baseLeafBottomXS; flat_deriv_wf

theorem baseLeafBottomIS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hTopClass hRightClass hLeftClass hBottomBand}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wLeftClass : DerivWF hLeftClass cb fuel rho E)
    (wBottomBand : DerivWF hBottomBand cb fuel rho E) :
    DerivWF (baseLeafBottomIS (Γ := Γ) dT kT qT hBulk hTopClass hRightClass hLeftClass hBottomBand) cb fuel rho E := by
  unfold baseLeafBottomIS; flat_deriv_wf

/-- `flat_step_wf`: like `flat_deriv_wf` but discharges `baseLeaf*S` leaves by CITING their
proved WF lemmas (no re-unfolding/re-walking of `baseLeafTreeTA`), keeping `flatStep*` terms
small. -/
macro "flat_step_wf" : tactic =>
  `(tactic|
    repeat first
      | exact True.intro
      | assumption
      | refine innerDTA_pure ?_
      | refine interiorKTA_pure ?_ ?_
      | refine topKTA_pure ?_ ?_
      | refine rightKTA_pure ?_ ?_
      | refine leftKTA_pure ?_ ?_
      | refine bottomKTA_pure ?_ ?_
      | refine innerQTA_pure ?_ ?_
      | refine baseLeafZS_WF _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
      | refine baseLeafXS_WF _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
      | refine baseLeafBulkIS_WF _ _ _ _ ?_ ?_ ?_ ?_ ?_
      | refine baseLeafTopXS_WF _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
      | refine baseLeafTopIS_WF _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
      | refine baseLeafRightZS_WF _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      | refine baseLeafRightIS_WF _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      | refine baseLeafLeftZS_WF _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      | refine baseLeafLeftIS_WF _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      | refine baseLeafBottomXS_WF _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      | refine baseLeafBottomIS_WF _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      | refine derivWF_eqPauliTrans' ?_ ?_
      | refine derivWF_eqPauliSymm' ?_
      | refine derivWF_mp ?_ ?_
      | refine derivWF_andIntro ?_ ?_
      | refine derivWF_andElimLeft' ?_
      | refine derivWF_andElimRight' ?_
      | refine derivWF_contextWeakening' _ _ ?_
      | refine derivWF_pauliIteSelectThen' _ _ _ ?_ ?_
      | refine derivWF_pauliIteSelectElse' _ _ _ ?_ ?_
      | refine derivWF_boolCases _ _
          (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?_ ?_
      | apply formulaDefined_eqPauli_purePauli
      | leaf_pp)

/-! ### `recLeaf*S` self-sim navigation `DerivWF` lemmas (resolve `recLeafTreeTA` to the
selected cell; need `PurePauli` of the five resolved cells for the `pauliIteSelect` leaves). -/

theorem recLeafIntS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpi : PurePauli pInt) (hpt : PurePauli pTop) (hpr : PurePauli pRight)
    (hpl : PurePauli pLeft) (hpb : PurePauli pBottom)
    {hBulk hInterior hInside} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wInside : DerivWF hInside cb fuel rho E) :
    DerivWF (recLeafIntS (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom hBulk hInterior hInside) cb fuel rho E := by
  unfold recLeafIntS; flat_deriv_wf

theorem recLeafIntIS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpi : PurePauli pInt) (hpt : PurePauli pTop) (hpr : PurePauli pRight)
    (hpl : PurePauli pLeft) (hpb : PurePauli pBottom)
    {hBulk hInterior hInside} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wInside : DerivWF hInside cb fuel rho E) :
    DerivWF (recLeafIntIS (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom hBulk hInterior hInside) cb fuel rho E := by
  unfold recLeafIntIS; flat_deriv_wf

theorem recLeafTopS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpi : PurePauli pInt) (hpt : PurePauli pTop) (hpr : PurePauli pRight)
    (hpl : PurePauli pLeft) (hpb : PurePauli pBottom)
    {hBulk hInterior hTop hInside} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wTop : DerivWF hTop cb fuel rho E) (wInside : DerivWF hInside cb fuel rho E) :
    DerivWF (recLeafTopS (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom hBulk hInterior hTop hInside) cb fuel rho E := by
  unfold recLeafTopS; flat_deriv_wf

theorem recLeafTopNIS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpi : PurePauli pInt) (hpt : PurePauli pTop) (hpr : PurePauli pRight)
    (hpl : PurePauli pLeft) (hpb : PurePauli pBottom)
    {hBulk hInterior hTop hInside} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wTop : DerivWF hTop cb fuel rho E) (wInside : DerivWF hInside cb fuel rho E) :
    DerivWF (recLeafTopNIS (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom hBulk hInterior hTop hInside) cb fuel rho E := by
  unfold recLeafTopNIS; flat_deriv_wf

theorem recLeafRightS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpi : PurePauli pInt) (hpt : PurePauli pTop) (hpr : PurePauli pRight)
    (hpl : PurePauli pLeft) (hpb : PurePauli pBottom)
    {hBulk hInterior hTop hRight hInside} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wTop : DerivWF hTop cb fuel rho E) (wRight : DerivWF hRight cb fuel rho E)
    (wInside : DerivWF hInside cb fuel rho E) :
    DerivWF (recLeafRightS (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom hBulk hInterior hTop hRight hInside) cb fuel rho E := by
  unfold recLeafRightS; flat_deriv_wf

theorem recLeafRightNIS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpi : PurePauli pInt) (hpt : PurePauli pTop) (hpr : PurePauli pRight)
    (hpl : PurePauli pLeft) (hpb : PurePauli pBottom)
    {hBulk hInterior hTop hRight hInside} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wTop : DerivWF hTop cb fuel rho E) (wRight : DerivWF hRight cb fuel rho E)
    (wInside : DerivWF hInside cb fuel rho E) :
    DerivWF (recLeafRightNIS (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom hBulk hInterior hTop hRight hInside) cb fuel rho E := by
  unfold recLeafRightNIS; flat_deriv_wf

theorem recLeafLeftS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpi : PurePauli pInt) (hpt : PurePauli pTop) (hpr : PurePauli pRight)
    (hpl : PurePauli pLeft) (hpb : PurePauli pBottom)
    {hBulk hInterior hTop hRight hLeft hInside} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wTop : DerivWF hTop cb fuel rho E) (wRight : DerivWF hRight cb fuel rho E)
    (wLeft : DerivWF hLeft cb fuel rho E) (wInside : DerivWF hInside cb fuel rho E) :
    DerivWF (recLeafLeftS (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom hBulk hInterior hTop hRight hLeft hInside) cb fuel rho E := by
  unfold recLeafLeftS; flat_deriv_wf

theorem recLeafLeftNIS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpi : PurePauli pInt) (hpt : PurePauli pTop) (hpr : PurePauli pRight)
    (hpl : PurePauli pLeft) (hpb : PurePauli pBottom)
    {hBulk hInterior hTop hRight hLeft hInside} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wTop : DerivWF hTop cb fuel rho E) (wRight : DerivWF hRight cb fuel rho E)
    (wLeft : DerivWF hLeft cb fuel rho E) (wInside : DerivWF hInside cb fuel rho E) :
    DerivWF (recLeafLeftNIS (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom hBulk hInterior hTop hRight hLeft hInside) cb fuel rho E := by
  unfold recLeafLeftNIS; flat_deriv_wf

theorem recLeafBottomS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpi : PurePauli pInt) (hpt : PurePauli pTop) (hpr : PurePauli pRight)
    (hpl : PurePauli pLeft) (hpb : PurePauli pBottom)
    {hBulk hInterior hTop hRight hLeft hBottom hInside} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wTop : DerivWF hTop cb fuel rho E) (wRight : DerivWF hRight cb fuel rho E)
    (wLeft : DerivWF hLeft cb fuel rho E) (wBottom : DerivWF hBottom cb fuel rho E)
    (wInside : DerivWF hInside cb fuel rho E) :
    DerivWF (recLeafBottomS (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom hBulk hInterior hTop hRight hLeft hBottom hInside) cb fuel rho E := by
  unfold recLeafBottomS; flat_deriv_wf

theorem recLeafBottomNIS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpi : PurePauli pInt) (hpt : PurePauli pTop) (hpr : PurePauli pRight)
    (hpl : PurePauli pLeft) (hpb : PurePauli pBottom)
    {hBulk hInterior hTop hRight hLeft hBottom hInside} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wTop : DerivWF hTop cb fuel rho E) (wRight : DerivWF hRight cb fuel rho E)
    (wLeft : DerivWF hLeft cb fuel rho E) (wBottom : DerivWF hBottom cb fuel rho E)
    (wInside : DerivWF hInside cb fuel rho E) :
    DerivWF (recLeafBottomNIS (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom hBulk hInterior hTop hRight hLeft hBottom hInside) cb fuel rho E := by
  unfold recLeafBottomNIS; flat_deriv_wf

theorem recLeafFallbackS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpi : PurePauli pInt) (hpt : PurePauli pTop) (hpr : PurePauli pRight)
    (hpl : PurePauli pLeft) (hpb : PurePauli pBottom)
    {hBulk hInterior hTop hRight hLeft hBottom} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wTop : DerivWF hTop cb fuel rho E) (wRight : DerivWF hRight cb fuel rho E)
    (wLeft : DerivWF hLeft cb fuel rho E) (wBottom : DerivWF hBottom cb fuel rho E) :
    DerivWF (recLeafFallbackS (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom hBulk hInterior hTop hRight hLeft hBottom) cb fuel rho E := by
  unfold recLeafFallbackS; flat_deriv_wf

theorem recLeafBoundaryS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpi : PurePauli pInt) (hpt : PurePauli pTop) (hpr : PurePauli pRight)
    (hpl : PurePauli pLeft) (hpb : PurePauli pBottom)
    {hBulk} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) :
    DerivWF (recLeafBoundaryS (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom hBulk) cb fuel rho E := by
  unfold recLeafBoundaryS; flat_deriv_wf

/-! ### `flatStep*` `DerivWF` lemmas (the inner↔outer flat-tree equality at each cell; pure
boolCases over outer band/kind, `mp` on the correspondence implications, `baseLeaf*S` leaves). -/

theorem flatStepInterior_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hInterior hInside hImpBulk hImpBandT hImpBandF hImpKindT hImpKindF}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wInside : DerivWF hInside cb fuel rho E)
    (wImpBulk : DerivWF hImpBulk cb fuel rho E) (wImpBandT : DerivWF hImpBandT cb fuel rho E)
    (wImpBandF : DerivWF hImpBandF cb fuel rho E) (wImpKindT : DerivWF hImpKindT cb fuel rho E)
    (wImpKindF : DerivWF hImpKindF cb fuel rho E) :
    DerivWF (flatStepInterior (Γ := Γ) dT kT qT hBulk hInterior hInside hImpBulk hImpBandT hImpBandF hImpKindT hImpKindF) cb fuel rho E := by
  unfold flatStepInterior; flat_step_wf

theorem flatStepInteriorNI_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hInterior hInside hImpBandF}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wInside : DerivWF hInside cb fuel rho E) (wImpBandF : DerivWF hImpBandF cb fuel rho E) :
    DerivWF (flatStepInteriorNI (Γ := Γ) dT kT qT hBulk hInterior hInside hImpBandF) cb fuel rho E := by
  unfold flatStepInteriorNI; flat_step_wf

theorem flatStepTop_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hInterior hTop hInside hImpCtx hImpBandT hImpBandF}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wTop : DerivWF hTop cb fuel rho E) (wInside : DerivWF hInside cb fuel rho E)
    (wImpCtx : DerivWF hImpCtx cb fuel rho E) (wImpBandT : DerivWF hImpBandT cb fuel rho E)
    (wImpBandF : DerivWF hImpBandF cb fuel rho E) :
    DerivWF (flatStepTop (Γ := Γ) dT kT qT hBulk hInterior hTop hInside hImpCtx hImpBandT hImpBandF) cb fuel rho E := by
  unfold flatStepTop; flat_step_wf

theorem flatStepTopNI_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hInterior hTop hInside hImpCtx hImpBandT hImpBandF}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wTop : DerivWF hTop cb fuel rho E) (wInside : DerivWF hInside cb fuel rho E)
    (wImpCtx : DerivWF hImpCtx cb fuel rho E) (wImpBandT : DerivWF hImpBandT cb fuel rho E)
    (wImpBandF : DerivWF hImpBandF cb fuel rho E) :
    DerivWF (flatStepTopNI (Γ := Γ) dT kT qT hBulk hInterior hTop hInside hImpCtx hImpBandT hImpBandF) cb fuel rho E := by
  unfold flatStepTopNI; flat_step_wf

theorem flatStepRight_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hInterior hTop hRight hInside hImpCtx hImpBandT hImpBandF}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wTop : DerivWF hTop cb fuel rho E) (wRight : DerivWF hRight cb fuel rho E)
    (wInside : DerivWF hInside cb fuel rho E) (wImpCtx : DerivWF hImpCtx cb fuel rho E)
    (wImpBandT : DerivWF hImpBandT cb fuel rho E) (wImpBandF : DerivWF hImpBandF cb fuel rho E) :
    DerivWF (flatStepRight (Γ := Γ) dT kT qT hBulk hInterior hTop hRight hInside hImpCtx hImpBandT hImpBandF) cb fuel rho E := by
  unfold flatStepRight; flat_step_wf

theorem flatStepRightNI_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hInterior hTop hRight hInside hImpCtx hImpBandT hImpBandF}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wTop : DerivWF hTop cb fuel rho E) (wRight : DerivWF hRight cb fuel rho E)
    (wInside : DerivWF hInside cb fuel rho E) (wImpCtx : DerivWF hImpCtx cb fuel rho E)
    (wImpBandT : DerivWF hImpBandT cb fuel rho E) (wImpBandF : DerivWF hImpBandF cb fuel rho E) :
    DerivWF (flatStepRightNI (Γ := Γ) dT kT qT hBulk hInterior hTop hRight hInside hImpCtx hImpBandT hImpBandF) cb fuel rho E := by
  unfold flatStepRightNI; flat_step_wf

theorem flatStepLeft_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hInterior hTop hRight hLeft hInside hImpCtx hImpBandT hImpBandF}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wTop : DerivWF hTop cb fuel rho E) (wRight : DerivWF hRight cb fuel rho E)
    (wLeft : DerivWF hLeft cb fuel rho E) (wInside : DerivWF hInside cb fuel rho E)
    (wImpCtx : DerivWF hImpCtx cb fuel rho E) (wImpBandT : DerivWF hImpBandT cb fuel rho E)
    (wImpBandF : DerivWF hImpBandF cb fuel rho E) :
    DerivWF (flatStepLeft (Γ := Γ) dT kT qT hBulk hInterior hTop hRight hLeft hInside hImpCtx hImpBandT hImpBandF) cb fuel rho E := by
  unfold flatStepLeft; flat_step_wf

theorem flatStepLeftNI_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hInterior hTop hRight hLeft hInside hImpCtx hImpBandT hImpBandF}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wTop : DerivWF hTop cb fuel rho E) (wRight : DerivWF hRight cb fuel rho E)
    (wLeft : DerivWF hLeft cb fuel rho E) (wInside : DerivWF hInside cb fuel rho E)
    (wImpCtx : DerivWF hImpCtx cb fuel rho E) (wImpBandT : DerivWF hImpBandT cb fuel rho E)
    (wImpBandF : DerivWF hImpBandF cb fuel rho E) :
    DerivWF (flatStepLeftNI (Γ := Γ) dT kT qT hBulk hInterior hTop hRight hLeft hInside hImpCtx hImpBandT hImpBandF) cb fuel rho E := by
  unfold flatStepLeftNI; flat_step_wf

theorem flatStepBottom_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hInterior hTop hRight hLeft hBottom hInside hImpCtx hImpBandT hImpBandF}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wTop : DerivWF hTop cb fuel rho E) (wRight : DerivWF hRight cb fuel rho E)
    (wLeft : DerivWF hLeft cb fuel rho E) (wBottom : DerivWF hBottom cb fuel rho E)
    (wInside : DerivWF hInside cb fuel rho E) (wImpCtx : DerivWF hImpCtx cb fuel rho E)
    (wImpBandT : DerivWF hImpBandT cb fuel rho E) (wImpBandF : DerivWF hImpBandF cb fuel rho E) :
    DerivWF (flatStepBottom (Γ := Γ) dT kT qT hBulk hInterior hTop hRight hLeft hBottom hInside hImpCtx hImpBandT hImpBandF) cb fuel rho E := by
  unfold flatStepBottom; flat_step_wf

theorem flatStepBottomNI_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hInterior hTop hRight hLeft hBottom hInside hImpCtx hImpBandT hImpBandF}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wTop : DerivWF hTop cb fuel rho E) (wRight : DerivWF hRight cb fuel rho E)
    (wLeft : DerivWF hLeft cb fuel rho E) (wBottom : DerivWF hBottom cb fuel rho E)
    (wInside : DerivWF hInside cb fuel rho E) (wImpCtx : DerivWF hImpCtx cb fuel rho E)
    (wImpBandT : DerivWF hImpBandT cb fuel rho E) (wImpBandF : DerivWF hImpBandF cb fuel rho E) :
    DerivWF (flatStepBottomNI (Γ := Γ) dT kT qT hBulk hInterior hTop hRight hLeft hBottom hInside hImpCtx hImpBandT hImpBandF) cb fuel rho E := by
  unfold flatStepBottomNI; flat_step_wf

/-- `flat_master_wf`: the master discharger — `flat_step_wf` plus `apply`-citations of the
proved `recLeaf*S_WF` / `flatStep*_WF` / `baseLeaf*S_WF` (so each navigation/step is reused,
never re-walked).  `apply` infers the index/cell args from the goal, leaving `hd/hk/hq`,
`PurePauli` (hp), and guard/imp WF goals to `assumption`/`True.intro`/combinators. -/
macro "flat_master_wf" : tactic =>
  `(tactic|
    repeat first
      | exact True.intro
      | assumption
      | refine innerDTA_pure ?_
      | refine interiorKTA_pure ?_ ?_
      | refine topKTA_pure ?_ ?_
      | refine rightKTA_pure ?_ ?_
      | refine leftKTA_pure ?_ ?_
      | refine bottomKTA_pure ?_ ?_
      | refine innerQTA_pure ?_ ?_
      | apply recLeafIntS_WF
      | apply recLeafIntIS_WF
      | apply recLeafTopS_WF
      | apply recLeafTopNIS_WF
      | apply recLeafRightS_WF
      | apply recLeafRightNIS_WF
      | apply recLeafLeftS_WF
      | apply recLeafLeftNIS_WF
      | apply recLeafBottomS_WF
      | apply recLeafBottomNIS_WF
      | apply recLeafFallbackS_WF
      | apply recLeafBoundaryS_WF
      | apply flatStepInterior_WF
      | apply flatStepInteriorNI_WF
      | apply flatStepTop_WF
      | apply flatStepTopNI_WF
      | apply flatStepRight_WF
      | apply flatStepRightNI_WF
      | apply flatStepLeft_WF
      | apply flatStepLeftNI_WF
      | apply flatStepBottom_WF
      | apply flatStepBottomNI_WF
      | apply baseLeafZS_WF
      | apply baseLeafXS_WF
      | apply baseLeafBulkIS_WF
      | apply baseLeafTopXS_WF
      | apply baseLeafTopIS_WF
      | apply baseLeafRightZS_WF
      | apply baseLeafRightIS_WF
      | apply baseLeafLeftZS_WF
      | apply baseLeafLeftIS_WF
      | apply baseLeafBottomXS_WF
      | apply baseLeafBottomIS_WF
      | refine derivWF_eqPauliTrans' ?_ ?_
      | refine derivWF_eqPauliSymm' ?_
      | refine derivWF_mp ?_ ?_
      | refine derivWF_andIntro ?_ ?_
      | refine derivWF_andElimLeft' ?_
      | refine derivWF_andElimRight' ?_
      | refine derivWF_contextWeakening' _ _ ?_
      | refine derivWF_pauliIteSelectThen' _ _ _ ?_ ?_
      | refine derivWF_pauliIteSelectElse' _ _ _ ?_ ?_
      | refine derivWF_boolCases _ _
          (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?_ ?_
      | apply formulaDefined_eqPauli_purePauli
      | leaf_pp)

/-- **`recFlatMasterD_WF`** — `DerivWF` of the flat-bridge master boolCases tree.  Mirrors
`recFlatMasterD` (each leaf `eqPauliTrans (recLeaf*S) (eqPauliTrans (contextWeakening hLeq*)
(flatStep*))`); the five resolved cells need `PurePauli`, and the IH-leaf equalities + the
~30 correspondence implications enter as `DerivWF` hyps (all `True.intro` at the bridge call,
where they are `andElim` projections of the cut hypothesis). -/
theorem recFlatMasterD_WF {arity : Nat} {Γ : List (SFormula arity)}
    (dT kT qT : Term arity .nat) (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpi : PurePauli pInt) (hpt : PurePauli pTop) (hpr : PurePauli pRight)
    (hpl : PurePauli pLeft) (hpb : PurePauli pBottom)
    {hLeqInt hLeqTop hLeqRight hLeqLeft hLeqBottom
      hImpBulk hImpBandT hImpBandF hImpKindT hImpKindF hImpBandFNI
      hTopImpCtx hTopImpBandT hTopImpBandF hRightImpCtx hRightImpBandT hRightImpBandF
      hLeftImpCtx hLeftImpBandT hLeftImpBandF hBottomImpCtx hBottomImpBandT hBottomImpBandF
      hTopNIImpCtx hTopNIImpBandT hTopNIImpBandF hRightNIImpCtx hRightNIImpBandT hRightNIImpBandF
      hLeftNIImpCtx hLeftNIImpBandT hLeftNIImpBandF hBottomNIImpCtx hBottomNIImpBandT hBottomNIImpBandF}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wLeqInt : DerivWF hLeqInt cb fuel rho E) (wLeqTop : DerivWF hLeqTop cb fuel rho E)
    (wLeqRight : DerivWF hLeqRight cb fuel rho E) (wLeqLeft : DerivWF hLeqLeft cb fuel rho E)
    (wLeqBottom : DerivWF hLeqBottom cb fuel rho E) (wImpBulk : DerivWF hImpBulk cb fuel rho E)
    (wImpBandT : DerivWF hImpBandT cb fuel rho E) (wImpBandF : DerivWF hImpBandF cb fuel rho E)
    (wImpKindT : DerivWF hImpKindT cb fuel rho E) (wImpKindF : DerivWF hImpKindF cb fuel rho E)
    (wImpBandFNI : DerivWF hImpBandFNI cb fuel rho E) (wTopImpCtx : DerivWF hTopImpCtx cb fuel rho E)
    (wTopImpBandT : DerivWF hTopImpBandT cb fuel rho E) (wTopImpBandF : DerivWF hTopImpBandF cb fuel rho E)
    (wRightImpCtx : DerivWF hRightImpCtx cb fuel rho E) (wRightImpBandT : DerivWF hRightImpBandT cb fuel rho E)
    (wRightImpBandF : DerivWF hRightImpBandF cb fuel rho E) (wLeftImpCtx : DerivWF hLeftImpCtx cb fuel rho E)
    (wLeftImpBandT : DerivWF hLeftImpBandT cb fuel rho E) (wLeftImpBandF : DerivWF hLeftImpBandF cb fuel rho E)
    (wBottomImpCtx : DerivWF hBottomImpCtx cb fuel rho E) (wBottomImpBandT : DerivWF hBottomImpBandT cb fuel rho E)
    (wBottomImpBandF : DerivWF hBottomImpBandF cb fuel rho E) (wTopNIImpCtx : DerivWF hTopNIImpCtx cb fuel rho E)
    (wTopNIImpBandT : DerivWF hTopNIImpBandT cb fuel rho E) (wTopNIImpBandF : DerivWF hTopNIImpBandF cb fuel rho E)
    (wRightNIImpCtx : DerivWF hRightNIImpCtx cb fuel rho E) (wRightNIImpBandT : DerivWF hRightNIImpBandT cb fuel rho E)
    (wRightNIImpBandF : DerivWF hRightNIImpBandF cb fuel rho E) (wLeftNIImpCtx : DerivWF hLeftNIImpCtx cb fuel rho E)
    (wLeftNIImpBandT : DerivWF hLeftNIImpBandT cb fuel rho E) (wLeftNIImpBandF : DerivWF hLeftNIImpBandF cb fuel rho E)
    (wBottomNIImpCtx : DerivWF hBottomNIImpCtx cb fuel rho E) (wBottomNIImpBandT : DerivWF hBottomNIImpBandT cb fuel rho E)
    (wBottomNIImpBandF : DerivWF hBottomNIImpBandF cb fuel rho E) :
    DerivWF (recFlatMasterD (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom
        hLeqInt hLeqTop hLeqRight hLeqLeft hLeqBottom
        hImpBulk hImpBandT hImpBandF hImpKindT hImpKindF hImpBandFNI
        hTopImpCtx hTopImpBandT hTopImpBandF hRightImpCtx hRightImpBandT hRightImpBandF
        hLeftImpCtx hLeftImpBandT hLeftImpBandF hBottomImpCtx hBottomImpBandT hBottomImpBandF
        hTopNIImpCtx hTopNIImpBandT hTopNIImpBandF hRightNIImpCtx hRightNIImpBandT hRightNIImpBandF
        hLeftNIImpCtx hLeftNIImpBandT hLeftNIImpBandF hBottomNIImpCtx hBottomNIImpBandT hBottomNIImpBandF)
      cb fuel rho E := by
  unfold recFlatMasterD
  flat_master_wf

/-- The flat-bridge analogue of the descending witness for `rowSymTreeFlatBridgeSym`.
Placeholder name capturing the parallel `m`-induction's per-level eval side-data;
the bridge's `recFlatMasterD` boolCases tree consumes the same kind of inner-cell
witnesses as `recRowConvergeA`. -/
def RowFlatWitness {arity : Nat} (qT : Term arity .nat) (m : Nat)
    (rho : Env arity) (E : PartialStabilizer) : Prop := True

/-- **`rowSymTreeFlatBridgeSym_WF`** — `DerivWFA` of the symbolic flat bridge, by induction
on `m` (parallel to the bridge's own recursion).  Base: `core (baseLeafSelfEq)`.  Step:
`cut1 (recFlatMasterD …) hConj` — master via `recFlatMasterD_WF`, `hConj` cut2-chain relays
the five IH facts (induction IH) + the ~30 `arithBool` correspondence implications
(`DerivWFA = True`).  No row-projection witnesses needed (the bridge has no `recCall`). -/
theorem rowSymTreeFlatBridgeSym_WF {arity fuel : Nat} (m : Nat) (D : DistAtA arity m)
    (kT qT : Term arity .nat) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (rho : Env arity) (E : PartialStabilizer) :
    DerivWFA (rowSymTreeFlatBridgeSym (fuel := fuel) m D kT qT hk hq) rho E := by
  induction m generalizing kT qT hk hq with
  | zero =>
      exact baseLeafSelfEq_WF [] D.dT kT qT D.pure hk hq
  | succ m ih =>
      have hd : SFormula.PureNatTerm D.dT := D.pure
      have hpi : PurePauli (rowSymTreeA m (innerDTA D.dT) (interiorKTA D.dT kT) (innerQTA D.dT qT)) :=
        rowSymTreeA_purePauli m (innerDTA_pure D.pure) (interiorKTA_pure D.pure hk) (innerQTA_pure D.pure hq)
      have hpt : PurePauli (rowSymTreeA m (recInnerDTA D.dT) (topKTA D.dT kT) (innerQTA D.dT qT)) :=
        rowSymTreeA_purePauli m (innerDTA_pure D.pure) (topKTA_pure D.pure hk) (innerQTA_pure D.pure hq)
      have hpr : PurePauli (rowSymTreeA m (recInnerDTA D.dT) (rightKTA D.dT kT) (innerQTA D.dT qT)) :=
        rowSymTreeA_purePauli m (innerDTA_pure D.pure) (rightKTA_pure D.pure hk) (innerQTA_pure D.pure hq)
      have hpl : PurePauli (rowSymTreeA m (recInnerDTA D.dT) (leftKTA D.dT kT) (innerQTA D.dT qT)) :=
        rowSymTreeA_purePauli m (innerDTA_pure D.pure) (leftKTA_pure D.pure hk) (innerQTA_pure D.pure hq)
      have hpb : PurePauli (rowSymTreeA m (recInnerDTA D.dT) (bottomKTA D.dT kT) (innerQTA D.dT qT)) :=
        rowSymTreeA_purePauli m (innerDTA_pure D.pure) (bottomKTA_pure D.pure hk) (innerQTA_pure D.pure hq)
      unfold rowSymTreeFlatBridgeSym
      refine ⟨?_, ?_⟩
      · -- master core: `recFlatMasterD` over the resolved cells (`hpi…hpb`); andElim arg WFs auto.
        unfold recFlatMasterD
        flat_master_wf
      · -- `hConj`: the 34-deep cut2 chain — 5 IH facts (induction IH at the inner indices) +
        -- ~30 `arithBool` imps (`DerivWFA = True`); cores are `andIntro` of two `hyp`s.
        repeat first
          | exact True.intro
          | assumption
          | apply ih
          | refine interiorKTA_pure ?_ ?_
          | refine topKTA_pure ?_ ?_
          | refine rightKTA_pure ?_ ?_
          | refine leftKTA_pure ?_ ?_
          | refine bottomKTA_pure ?_ ?_
          | refine innerQTA_pure ?_ ?_
          | refine ⟨⟨True.intro, True.intro⟩, ?_, ?_⟩

/-- `DerivWFA` of the symbolic flat row entry — the KEYSTONE.  `rowEntryFlatSym =
eqPauliTrans (surfaceRowEntryCharSymbolicA …) (rowSymTreeFlatBridgeSym …)`, so its
`DerivWFA` is the pair of the two sub-derivations' `DerivWFA`.  The first conjunct is
exactly `surfaceRowEntryCharSymbolicA_WF` (the proven `m`-induction, depending only on
the two flat master helpers); the second is the parallel flat-bridge induction.

Requires the row-projection witnesses (`hproj` at this level, `hwit` descending) — the
qubit-in-range side-data the binder range supplies in the real consumers. -/
theorem rowEntryFlatSym_WF {arity fuel : Nat} (m : Nat) (DD : DistAtA arity m)
    (kT qT : Term arity .nat)
    (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (rho : Env arity) (E : PartialStabilizer)
    (hfuel : m + 2 ≤ fuel) :
    DerivWFA (rowEntryFlatSym (fuel := fuel) m DD kT qT hk hq) rho E := by
  -- `eqPauliTrans` splits into the two sub-derivations' `DerivWFA`.
  refine ⟨?_, ?_⟩
  · -- `surfaceRowEntryCharSymbolicA m DD kT qT` — now **witness-free** (local projection
    -- width `SC.succClosed qT`, so `qv < qv + 1` is trivial).
    exact surfaceRowEntryCharSymbolicA_WF m DD kT qT hk hq rho E hfuel
  · -- `rowSymTreeFlatBridgeSym m DD kT qT` — the flat bridge (parallel `m`-induction, STEP E).
    exact rowSymTreeFlatBridgeSym_WF m DD kT qT hk hq rho E

end QHL.CodeLang.Surface.Verify
