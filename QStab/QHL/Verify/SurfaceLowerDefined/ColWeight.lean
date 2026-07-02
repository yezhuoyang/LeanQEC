import QStab.QHL.Verify.SurfaceLowerDefined.RowWeight

/-!
# Lower bound — ColWeight

The Z / column weight-counting core (core 6', dual of `RowWeight`): `zColsWeight_WF`.
-/

namespace QHL.CodeLang.Surface.Verify

open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

set_option maxHeartbeats 1600000

/-- Z-dual of `xSupportWitnessToSurjectiveBodyDeriv_WF`. -/
theorem zSupportWitnessToSurjectiveBodyDeriv_WF (D : OddSurfaceDistance) {E : PartialStabilizer}
    (hTotal : TotalUpTo (nQubits D.distance) E) {rho : Env 2} :
    DerivWF (zSupportWitnessToSurjectiveBodyDeriv D) Surface.code.body
      (bridgeProofFuel D) rho E := by
  unfold zSupportWitnessToSurjectiveBodyDeriv
  refine derivWF_existsNatLtIntroTerm _ _ _ ?hlt ?hbody ?hrange
  case hlt =>
    exact derivWF_gridIdxLeftLtSquare _ _ _ (derivWF_hyp _) (derivWF_hyp _)
  case hbody =>
    refine derivWF_applyNatSubstitutionBeta ?_
    simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
    refine derivWF_cast_type rfl ?eq1 _ _ (derivWF_cast_type rfl ?eq2 _ _ ?inner)
    case eq1 =>
      simp [gridColOf, SFormula.instantiateTopNat, SFormula.instantiateNatAt, STerm.instantiateNatAt,
        SFormula.lift, SFormula.nonIAt, SFormula.boundNat, STerm.lift, STerm.weaken,
        Term.instantiateNatAt, Term.lift, Term.weaken, Term.weakenVar, SC.closed, SC.p, SC.bound,
        rowVar1, colVar, gridIdx, NatArithmetic.colOf]
    case eq2 =>
      simp [
        SFormula.nonIAt, STerm.lift, STerm.weaken,
        Term.lift, Term.weaken, Term.weakenVar, SC.closed, SC.p, SC.bound,
        rowVar1, colVar, gridIdx, NatArithmetic.colOf]
    case inner =>
      exact derivWF_andIntro True.intro
        (derivWF_gridIdxLeftModEq _ _ _ (derivWF_hyp _) (derivWF_hyp _))
  case hrange =>
    refine ⟨nQubits D.distance, by simp [STerm.lift, STerm.weaken, SC.n, 
        STerm.eval, Term.eval, Term.lift],
      fun y hy => ?_⟩
    refine formulaDefined_and ?_ ?_
    · refine formulaDefined_not (formulaDefined_eqPauli ?_ (sterm_eval_p _))
      obtain ⟨p, hp⟩ := hTotal y hy
      exact ⟨p, by simp [SC.bound, STerm.eval, STerm.weaken, STerm.lift,
        SC.closed, Term.eval, Term.lift, Term.weakenVar, SFormula.boundNat,
        Env.cons, hp]⟩
    · refine formulaDefined_eqNat ?_ ?_
      · exact ⟨y % D.distance, by simp [gridColOf, SC.closed, STerm.lift, STerm.eval,
          Term.lift, NatArithmetic.colOf, rowVar1, Term.eval, Term.weakenVar, Env.cons,
          bind, Option.bind]⟩
      · exact ⟨rho 1, by simp [SFormula.boundNat, SC.closed, STerm.weaken, STerm.lift,
          STerm.eval, Term.lift, Term.weakenVar, Term.eval, Env.cons]⟩

/-- Z-dual of `fd_xRowOccupiedAtF`: cell `d*inner + col`, `Pauli.X`. -/
theorem fd_zColOccupiedAtF (D : OddSurfaceDistance) {E : PartialStabilizer}
    (hTotal : TotalUpTo (nQubits D.distance) E) {col : Nat} (hcol : col < D.distance) :
    SFormula.Deriv.FormulaDefined Surface.code.body (bridgeProofFuel D) (Env.cons col Env.empty) E
      (OpenStab.zColOccupiedAtF D.distance SC.bound.weaken rowVar1) := by
  refine formulaDefined_not ?_
  refine formulaDefined_allNatLt _ _ (scn_eval _ _ _ _ _) (fun inner hinner => ?_)
  refine formulaDefined_not ?_
  exact formulaDefined_eqBool
    (sterm_eval_anticommutes (zCellReadDefined D hTotal hcol hinner) (sterm_eval_p Pauli.X))
    (sterm_eval_b true)

/-- Z-dual of `fd_xRowsOccupiedF`. -/
theorem fd_zColsOccupiedF (D : OddSurfaceDistance) {E : PartialStabilizer}
    (hTotal : TotalUpTo (nQubits D.distance) E) :
    SFormula.Deriv.FormulaDefined Surface.code.body (bridgeProofFuel D) Env.empty E
      (OpenStab.zColsOccupiedF D) :=
  formulaDefined_allNatLt _ _ (scn_eval _ _ _ _ _) (fun _col hcol => fd_zColOccupiedAtF D hTotal hcol)

/-- Z-dual of `fd_xRowsOccupiedAllRowsSupportF`: cell `d*inner + col`, `Pauli.X`. -/
theorem fd_zColsOccupiedAllColsSupportF (D : OddSurfaceDistance) {E : PartialStabilizer}
    (hTotal : TotalUpTo (nQubits D.distance) E) :
    SFormula.Deriv.FormulaDefined Surface.code.body (bridgeProofFuel D) Env.empty E
      (zColsOccupiedAllColsSupportF D) := by
  refine formulaDefined_allNatLt _ _ (scn_eval _ _ _ _ _) (fun col hcol => ?_)
  refine formulaDefined_existsNatLt _ _ (scn_eval _ _ _ _ _) (fun inner hinner => ?_)
  exact formulaDefined_eqBool
    (sterm_eval_anticommutes (zCellReadDefined D hTotal hcol hinner) (sterm_eval_p Pauli.X))
    (sterm_eval_b true)

/-- Z-dual of `xRowOccupiedDeMorganDeriv_WF`: cell `d*x + col`, `Pauli.X`. -/
theorem zColOccupiedDeMorganDeriv_WF (D : OddSurfaceDistance) {E : PartialStabilizer}
    (hTotal : TotalUpTo (nQubits D.distance) E) {col : Nat} (hcol : col < D.distance) :
    DerivWF (zColOccupiedDeMorganDeriv D) Surface.code.body
      (bridgeProofFuel D) (Env.cons col Env.empty) E := by
  unfold zColOccupiedDeMorganDeriv
  refine ⟨True.intro, D.distance, scn_eval _ _ _ _ _, fun x hx => ?_⟩
  exact formulaDefined_eqBool
    (sterm_eval_anticommutes (zCellReadDefined D hTotal hcol hx) (sterm_eval_p Pauli.X))
    (sterm_eval_b true)

/-- Z-dual of `xRowsOccupiedAllRowsSupportDeriv_WF`. -/
theorem zColsOccupiedAllColsSupportDeriv_WF (D : OddSurfaceDistance) {E : PartialStabilizer}
    (hTotal : TotalUpTo (nQubits D.distance) E) :
    DerivWF (zColsOccupiedAllColsSupportDeriv D) Surface.code.body
      (bridgeProofFuel D) Env.empty E := by
  unfold zColsOccupiedAllColsSupportDeriv
  refine derivWF_impIntro_cond (fd_zColsOccupiedF D hTotal) (fun hgOcc => ?_)
  refine derivWF_allNatLtIntroBounded _ _
    ⟨D.distance, scn_eval _ _ _ _ _, fun idx hidx => ⟨?body2, ?ctx2⟩⟩
  case body2 =>
    refine derivWF_mp ?hDem ?hOcc
    case hDem =>
      exact derivWF_impIntro_cond (fd_zColOccupiedAtF D hTotal hidx)
        (fun _ => zColOccupiedDeMorganDeriv_WF D hTotal hidx)
    case hOcc =>
      refine derivWF_applyNatBoundNatBeta _ ?_
      exact derivWF_allNatLtElim _ _ _ (derivWF_hyp _) True.intro
  case ctx2 =>
    intro A hA
    cases hA with
    | head => exact hgOcc
    | tail _ h => cases h

/-- Z-dual of `xRowsOccupiedSupportSurjectiveDeriv_WF`. -/
theorem zColsOccupiedSupportSurjectiveDeriv_WF (D : OddSurfaceDistance) {E : PartialStabilizer}
    (hTotal : TotalUpTo (nQubits D.distance) E) :
    DerivWF (zColsOccupiedSupportSurjectiveDeriv D) Surface.code.body
      (bridgeProofFuel D) Env.empty E := by
  unfold zColsOccupiedSupportSurjectiveDeriv
  refine derivWF_impIntro_cond (fd_zColsOccupiedF D hTotal) (fun hgOcc => ?_)
  refine derivWF_mp ?hAllImp ?hAll
  case hAllImp =>
    refine derivWF_impIntro_cond (fd_zColsOccupiedAllColsSupportF D hTotal) (fun hgAll => ?_)
    unfold zColsSupportSurjectiveFromAllColsSupportDeriv
    refine derivWF_allNatLtIntroBounded _ _
      ⟨D.distance, scn_eval _ _ _ _ _, fun idx hidx => ⟨?body, ?ctx⟩⟩
    case body =>
      refine ⟨?hExists, D.distance, scn_eval _ _ _ _ _,
        fun x hx hA => ⟨zSupportWitnessToSurjectiveBodyDeriv_WF D hTotal, ?ctxInner⟩⟩
      case hExists =>
        refine derivWF_applyNatBoundNatBeta _ ?_
        exact derivWF_allNatLtElim _ _ _ (derivWF_hyp _) True.intro
      case ctxInner =>
        exact contextHolds_boundNatLt_cons Surface.code.body (bridgeProofFuel D) (SC.n D.distance)
          Env.empty E [OpenStab.zColsOccupiedAllColsSupportF D] idx D.distance (scn_eval _ _ _ _ _)
          hidx (fun A hA => by cases hA with | head => exact hgAll | tail _ h => cases h)
    case ctx =>
      intro A hA
      cases hA with
      | head => exact hgAll
      | tail _ h => cases h
  case hAll =>
    refine derivWF_mp ?_ True.intro
    exact derivWF_weakenContext _ (zColsOccupiedAllColsSupportDeriv_WF D hTotal)

/-- Core 6 z-dual: `zColsWeightLowerByCountingDeriv` WF (mirror of `xRowsWeight_WF`). -/
theorem zColsWeight_WF (D : OddSurfaceDistance) {E : PartialStabilizer}
    (hTotal : TotalUpTo (nQubits D.distance) E) :
    DerivWF (zColsWeightLowerByCountingDeriv D) Surface.code.body
      (bridgeProofFuel D) Env.empty E := by
  have hFD : SFormula.Deriv.FormulaDefined Surface.code.body (bridgeProofFuel D) Env.empty E
      (OpenStab.zColsOccupiedF D) := fd_zColsOccupiedF D hTotal
  unfold zColsWeightLowerByCountingDeriv
  comm_deriv_wf
  refine ⟨?_, trivial,
    formulaDefined_weightLe (scn_eval _ _ _ _ _) (by simp [SC.bound, STerm.eval])
      (scn_eval _ _ _ _ _) (StabTotalUpTo_of_TotalUpTo hTotal)⟩
  refine derivWF_mp ?_ True.intro
  exact derivWF_weakenContext _ (zColsOccupiedSupportSurjectiveDeriv_WF D hTotal)

end QHL.CodeLang.Surface.Verify
