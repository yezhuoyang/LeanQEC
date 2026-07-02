import QStab.QHL.Verify.SurfaceLowerDefined.BridgeNorms

/-!
# Lower bound — RowWeight

The X / row weight-counting core (core 6): the occupancy `FormulaDefined`s and the
support-surjectivity derivation that give `xRowsWeight_WF`.
-/

namespace QHL.CodeLang.Surface.Verify

open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

set_option maxHeartbeats 1600000

/-- WF of the cover's witness body — exact analog of `logicalXSupportSurjectiveDeriv_WF`'s inner
`existsNatLtIntroTerm` (SurfaceCodeLevelDefined:603-662). `nonI = pauliAnticommutesNonI … (.hyp)` is
structural (DerivWF clause = `DerivWF child` = `True`); `rowEq = gridIdxLeftDivEq` over two hyps; the
only real work is the two-level `simpa`-cast strip and the range's `nonIAt`/`eqNat` E-evals via `hTotal`. -/
theorem xSupportWitnessToSurjectiveBodyDeriv_WF (D : OddSurfaceDistance) {E : PartialStabilizer}
    (hTotal : TotalUpTo (nQubits D.distance) E) {rho : Env 2} :
    DerivWF (xSupportWitnessToSurjectiveBodyDeriv D) Surface.code.body
      (bridgeProofFuel D) rho E := by
  unfold xSupportWitnessToSurjectiveBodyDeriv
  refine derivWF_existsNatLtIntroTerm _ _ _ ?hlt ?hbody ?hrange
  case hlt =>
    exact derivWF_gridIdxLeftLtSquare _ _ _ (derivWF_hyp _) (derivWF_hyp _)
  case hbody =>
    refine derivWF_applyNatSubstitutionBeta ?_
    simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
    refine derivWF_cast_type rfl ?eq1 _ _ (derivWF_cast_type rfl ?eq2 _ _ ?inner)
    case eq1 =>
      simp [gridRowOf, SFormula.instantiateTopNat, SFormula.instantiateNatAt,
        SFormula.lift, SFormula.nonIAt, SFormula.boundNat,
        STerm.instantiateNatAt, STerm.lift, STerm.weaken, Term.instantiateNatAt,
        Term.lift, Term.weaken, Term.weakenVar, SC.closed, SC.p, SC.bound,
        rowVar1, colVar, gridIdx, NatArithmetic.rowOf]
    case eq2 =>
      simp [
        SFormula.nonIAt, 
        STerm.lift, STerm.weaken, 
        Term.lift, Term.weaken, Term.weakenVar, SC.closed, SC.p, SC.bound,
        rowVar1, colVar, gridIdx, NatArithmetic.rowOf]
    case inner =>
      exact derivWF_andIntro True.intro
        (derivWF_gridIdxLeftDivEq _ _ _ (derivWF_hyp _) (derivWF_hyp _))
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
      · exact ⟨y / D.distance, by simp [gridRowOf, SC.closed, STerm.lift, STerm.eval,
          Term.lift, NatArithmetic.rowOf, rowVar1, Term.eval, Term.weakenVar, Env.cons,
          bind, Option.bind]⟩
      · exact ⟨rho 1, by simp [SFormula.boundNat, SC.closed, STerm.weaken, STerm.lift,
          STerm.eval, Term.lift, Term.weakenVar, Term.eval, Env.cons]⟩

/-- WF of `xRowOccupiedDeMorganDeriv` = `finiteDeMorgan (SC.n d) (xSupportAtF …) (.hyp …)`: child
is a hyp (`True`); the range is `∀ x < d, FD (xSupportAtF SC.bound (gridIdx d row x))`, the same
`anticommutes` E-eval as `hFD2`, with the cell qubit `d*row + x < nQubits` needing `row < d`. -/
theorem xRowOccupiedDeMorganDeriv_WF (D : OddSurfaceDistance) {E : PartialStabilizer}
    (hTotal : TotalUpTo (nQubits D.distance) E) {row : Nat} (hrow : row < D.distance) :
    DerivWF (xRowOccupiedDeMorganDeriv D) Surface.code.body
      (bridgeProofFuel D) (Env.cons row Env.empty) E := by
  unfold xRowOccupiedDeMorganDeriv
  refine ⟨True.intro, D.distance, scn_eval _ _ _ _ _, fun x hx => ?_⟩
  exact formulaDefined_eqBool
    (sterm_eval_anticommutes (xCellReadDefined D hTotal hrow hx) (sterm_eval_p Pauli.Z))
    (sterm_eval_b true)

/-- FD of `xRowOccupiedAtF d SC.bound rowVar1` = `not (allNatLt d (not (xSupportAtF …)))`: the
`gridIdx`-cell `anticommutes` E-eval (cell `d*row + col < nQubits` needs `row < d`). Reused by
`fd_xRowsOccupiedF` and the `hDem` branch of `xRowsOccupiedAllRowsSupportDeriv_WF`. -/
theorem fd_xRowOccupiedAtF (D : OddSurfaceDistance) {E : PartialStabilizer}
    (hTotal : TotalUpTo (nQubits D.distance) E) {row : Nat} (hrow : row < D.distance) :
    SFormula.Deriv.FormulaDefined Surface.code.body (bridgeProofFuel D) (Env.cons row Env.empty) E
      (OpenStab.xRowOccupiedAtF D.distance SC.bound.weaken rowVar1) := by
  refine formulaDefined_not ?_
  refine formulaDefined_allNatLt _ _ (scn_eval _ _ _ _ _) (fun col hcol => ?_)
  refine formulaDefined_not ?_
  exact formulaDefined_eqBool
    (sterm_eval_anticommutes (xCellReadDefined D hTotal hrow hcol) (sterm_eval_p Pauli.Z))
    (sterm_eval_b true)

/-- FD of `xRowsOccupiedF D` = `allNatLt d (xRowOccupiedAtF …)`, via `fd_xRowOccupiedAtF`. -/
theorem fd_xRowsOccupiedF (D : OddSurfaceDistance) {E : PartialStabilizer}
    (hTotal : TotalUpTo (nQubits D.distance) E) :
    SFormula.Deriv.FormulaDefined Surface.code.body (bridgeProofFuel D) Env.empty E
      (OpenStab.xRowsOccupiedF D) :=
  formulaDefined_allNatLt _ _ (scn_eval _ _ _ _ _) (fun _row hrow => fd_xRowOccupiedAtF D hTotal hrow)

/-- WF of `xRowsOccupiedAllRowsSupportDeriv` (the `hAll` branch of the cover). The `weakenBy` in
`hDemorgan` reduces under `derivWF_impIntro_cond`, exposing the original `xRowOccupiedDeMorganDeriv`. -/
theorem xRowsOccupiedAllRowsSupportDeriv_WF (D : OddSurfaceDistance) {E : PartialStabilizer}
    (hTotal : TotalUpTo (nQubits D.distance) E) :
    DerivWF (xRowsOccupiedAllRowsSupportDeriv D) Surface.code.body
      (bridgeProofFuel D) Env.empty E := by
  unfold xRowsOccupiedAllRowsSupportDeriv
  refine derivWF_impIntro_cond (fd_xRowsOccupiedF D hTotal) (fun hgOcc => ?_)
  refine derivWF_allNatLtIntroBounded _ _
    ⟨D.distance, scn_eval _ _ _ _ _, fun idx hidx => ⟨?body2, ?ctx2⟩⟩
  case body2 =>
    refine derivWF_mp ?hDem ?hOcc
    case hDem =>
      exact derivWF_impIntro_cond (fd_xRowOccupiedAtF D hTotal hidx)
        (fun _ => xRowOccupiedDeMorganDeriv_WF D hTotal hidx)
    case hOcc =>
      refine derivWF_applyNatBoundNatBeta _ ?_
      exact derivWF_allNatLtElim _ _ _ (derivWF_hyp _) True.intro
  case ctx2 =>
    -- allNatLtIntroBounded ctx is at the BASE env with Γ = [xRowsOccupiedF D]: just the guard.
    intro A hA
    cases hA with
    | head => exact hgOcc
    | tail _ h => cases h

/-- FD of `xRowsOccupiedAllRowsSupportF D` = `allNatLt d (existsNatLt d (xSupportAtF …))`: same
`gridIdx` `anticommutes` E-eval as `fd_xRowOccupiedAtF`, one `existsNatLt` instead of `not allNatLt not`. -/
theorem fd_xRowsOccupiedAllRowsSupportF (D : OddSurfaceDistance) {E : PartialStabilizer}
    (hTotal : TotalUpTo (nQubits D.distance) E) :
    SFormula.Deriv.FormulaDefined Surface.code.body (bridgeProofFuel D) Env.empty E
      (xRowsOccupiedAllRowsSupportF D) := by
  refine formulaDefined_allNatLt _ _ (scn_eval _ _ _ _ _) (fun row hrow => ?_)
  refine formulaDefined_existsNatLt _ _ (scn_eval _ _ _ _ _) (fun col hcol => ?_)
  exact formulaDefined_eqBool
    (sterm_eval_anticommutes (xCellReadDefined D hTotal hrow hcol) (sterm_eval_p Pauli.Z))
    (sterm_eval_b true)

/-- WF of `xRowsOccupiedSupportSurjectiveDeriv` — the cover's core sub-tree. Empty top-level context
(no ctx obstacle); the inner impIntros supply the `xRowsOccupiedF`/`xRowsOccupiedAllRowsSupportF` guards;
`fromAllRows`'s `existsNatLtElim` body is the proven witness WF, its ctx the `boundNatLt::guard.weaken`
form via `contextHolds_boundNatLt_cons`; `hAll` reuses `xRowsOccupiedAllRowsSupportDeriv_WF`. -/
theorem xRowsOccupiedSupportSurjectiveDeriv_WF (D : OddSurfaceDistance) {E : PartialStabilizer}
    (hTotal : TotalUpTo (nQubits D.distance) E) :
    DerivWF (xRowsOccupiedSupportSurjectiveDeriv D) Surface.code.body
      (bridgeProofFuel D) Env.empty E := by
  unfold xRowsOccupiedSupportSurjectiveDeriv
  refine derivWF_impIntro_cond (fd_xRowsOccupiedF D hTotal) (fun hgOcc => ?_)
  refine derivWF_mp ?hAllImp ?hAll
  case hAllImp =>
    refine derivWF_impIntro_cond (fd_xRowsOccupiedAllRowsSupportF D hTotal) (fun hgAll => ?_)
    unfold xRowsSupportSurjectiveFromAllRowsSupportDeriv
    refine derivWF_allNatLtIntroBounded _ _
      ⟨D.distance, scn_eval _ _ _ _ _, fun idx hidx => ⟨?body, ?ctx⟩⟩
    case body =>
      refine ⟨?hExists, D.distance, scn_eval _ _ _ _ _,
        fun x hx hA => ⟨xSupportWitnessToSurjectiveBodyDeriv_WF D hTotal, ?ctxInner⟩⟩
      case hExists =>
        refine derivWF_applyNatBoundNatBeta _ ?_
        exact derivWF_allNatLtElim _ _ _ (derivWF_hyp _) True.intro
      case ctxInner =>
        exact contextHolds_boundNatLt_cons Surface.code.body (bridgeProofFuel D) (SC.n D.distance)
          Env.empty E [OpenStab.xRowsOccupiedAllRowsSupportF D] idx D.distance (scn_eval _ _ _ _ _)
          hidx (fun A hA => by cases hA with | head => exact hgAll | tail _ h => cases h)
    case ctx =>
      intro A hA
      cases hA with
      | head => exact hgAll
      | tail _ h => cases h
  case hAll =>
    refine derivWF_mp ?_ True.intro
    exact derivWF_weakenContext _ (xRowsOccupiedAllRowsSupportDeriv_WF D hTotal)

/-- Core 6: `xRowsWeightLowerByCountingDeriv` WF (empty context → no ContextHolds obstacle).
`comm_deriv_wf` leaves the FD of `xRowsOccupiedF` (nested `allNatLt` + the `gridIdx` E-eval pattern)
and the `finiteSurjectiveWeightLower` node (cover walk + `weightLe` FD). -/
theorem xRowsWeight_WF (D : OddSurfaceDistance) {E : PartialStabilizer}
    (hTotal : TotalUpTo (nQubits D.distance) E) :
    DerivWF (xRowsWeightLowerByCountingDeriv D) Surface.code.body
      (bridgeProofFuel D) Env.empty E := by
  -- `FD xRowsOccupiedF` recurs (main + inside the cover); reuse the atomic FD lemma (dual of the
  -- Z side's `fd_zColsOccupiedF` reuse in `zColsWeight_WF`).
  have hFD : SFormula.Deriv.FormulaDefined Surface.code.body (bridgeProofFuel D) Env.empty E
      (OpenStab.xRowsOccupiedF D) := fd_xRowsOccupiedF D hTotal
  -- `FD xRowsOccupiedAllRowsSupportF` (= allNatLt (existsNatLt (xSupportAtF))): same atomic leaf.
  have hFD2 : SFormula.Deriv.FormulaDefined Surface.code.body (bridgeProofFuel D) Env.empty E
      (xRowsOccupiedAllRowsSupportF D) := fd_xRowsOccupiedAllRowsSupportF D hTotal
  unfold xRowsWeightLowerByCountingDeriv
  -- comm_deriv_wf auto-discharges FD `xRowsOccupiedF` leaves via `hFD`; the `finiteSurjectiveWeightLower`
  -- node is the only thing left (its `weightLe` FD supplied inline, cover walked by a second comm_deriv_wf).
  comm_deriv_wf
  refine ⟨?_, trivial,
    formulaDefined_weightLe (scn_eval _ _ _ _ _) (by simp [SC.bound, STerm.eval])
      (scn_eval _ _ _ _ _) (StabTotalUpTo_of_TotalUpTo hTotal)⟩
  -- cover: `mp (xRowsOccupiedSupportSurjectiveDeriv).weakenContext assumption`, closed by the proven
  -- whole-sub-tree WF (witness body + DeMorgan + allRowsSupport + surjective assembly).
  refine derivWF_mp ?_ True.intro
  exact derivWF_weakenContext _ (xRowsOccupiedSupportSurjectiveDeriv_WF D hTotal)

/-! ### Z-dual chain (mirror of the x-chain above): col↔row, Pauli.X, gridColOf, gridIdxLeftModEq. -/

end QHL.CodeLang.Surface.Verify
