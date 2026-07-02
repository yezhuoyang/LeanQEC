import QStab.QHL.Verify.SurfaceLowerDefined.RowColCut

/-!
# Lower bound — LogicalOp

The logical-operator layer: `FormulaDefined` of the normaliser / anticommutation /
bridge-factor formulas, plus the rule-truth `…_holds` lemmas (each rule's `eval = true`,
obtained from its own derivation via `Deriv.sound`) that discharge the family contexts.
-/

namespace QHL.CodeLang.Surface.Verify

open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

set_option maxHeartbeats 1600000

/-- FD of `normalizesOddF` = `allNatLt (commutesUpTo (codeRow s) E)`: each code row
`codeRow d s = recCall d s` evaluates to a stabilizer total up to `nQubits`
(`recCall_total_at_bridgeFuel`), `E` is total by `hTotal`. -/
theorem formulaDefined_normalizesOdd (D : OddSurfaceDistance) {E : PartialStabilizer}
    (hTotal : TotalUpTo (nQubits D.distance) E) :
    SFormula.Deriv.FormulaDefined Surface.code.body (bridgeProofFuel D) Env.empty E
      (OpenStab.normalizesOddF D) := by
  unfold OpenStab.normalizesOddF
  refine formulaDefined_allNatLt _ _ (scn_eval _ _ _ _ _) (fun s hs => ?_)
  obtain ⟨sa, hsa, hsaT⟩ := recCall_total_symbolicK D.index (bridgeProofFuel D)
    (by have : D.distance = 2 * D.index + 3 := rfl; simp only [bridgeProofFuel]; omega)
    (kT := rowVar1) (by constructor) (Env.cons s Env.empty)
  refine formulaDefined_commutesUpTo (Av := sa) (Bv := E) (scn_eval _ _ _ _ _) ?hA
    (by simp [SC.bound, STerm.eval, STerm.weaken, STerm.lift]) hsaT
    (StabTotalUpTo_of_TotalUpTo hTotal)
  case hA =>
    simpa [SC.closed, STerm.eval, Formula.codeRow] using hsa

/-- FD of `anticommutesLogicalZF` = `not (commutesUpTo E (logicalZOdd))`: `E` total by `hTotal`,
the logical `Z` operator evaluates to an everywhere-total stabilizer (`logicalZ_eval_total`). -/
theorem formulaDefined_anticommutesLogicalZ (D : OddSurfaceDistance) {E : PartialStabilizer}
    (hTotal : TotalUpTo (nQubits D.distance) E) :
    SFormula.Deriv.FormulaDefined Surface.code.body (bridgeProofFuel D) Env.empty E
      (OpenStab.anticommutesLogicalZF D) := by
  unfold OpenStab.anticommutesLogicalZF
  obtain ⟨g, hg⟩ := logicalZ_eval_total Surface.code.body (D.distance + 1) D.distance Env.empty
  refine formulaDefined_not (formulaDefined_commutesUpTo (Av := E) (Bv := fun q => some (g q))
    (scn_eval _ _ _ _ _) (by simp [SC.bound, STerm.eval]) ?hB
    (StabTotalUpTo_of_TotalUpTo hTotal) StabTotalUpTo.ofTotal)
  case hB => simpa [SC.closed, STerm.eval, logicalZOdd, bridgeProofFuel] using hg

/-- FD of `anticommutesLogicalXF` (dual): the logical `X` operator is everywhere-total. -/
theorem formulaDefined_anticommutesLogicalX (D : OddSurfaceDistance) {E : PartialStabilizer}
    (hTotal : TotalUpTo (nQubits D.distance) E) :
    SFormula.Deriv.FormulaDefined Surface.code.body (bridgeProofFuel D) Env.empty E
      (OpenStab.anticommutesLogicalXF D) := by
  unfold OpenStab.anticommutesLogicalXF
  obtain ⟨g, hg⟩ := logicalX_eval_total Surface.code.body (D.distance + 1) D.distance Env.empty
  refine formulaDefined_not (formulaDefined_commutesUpTo (Av := E) (Bv := fun q => some (g q))
    (scn_eval _ _ _ _ _) (by simp [SC.bound, STerm.eval]) ?hB
    (StabTotalUpTo_of_TotalUpTo hTotal) StabTotalUpTo.ofTotal)
  case hB => simpa [SC.closed, STerm.eval, logicalXOdd, bridgeProofFuel] using hg

/-- FD of `rowBridgeFactorsCommuteF` = `allNatLt (commutesUpTo (rowBridge row) E)`: each row
bridge evaluates to an everywhere-total stabilizer (`rowBridge_eval`), `E` total by `hTotal`. -/
theorem formulaDefined_rowBridgeFactorsCommute (D : OddSurfaceDistance) {E : PartialStabilizer}
    (hTotal : TotalUpTo (nQubits D.distance) E) :
    SFormula.Deriv.FormulaDefined Surface.code.body (bridgeProofFuel D) Env.empty E
      (OpenStab.rowBridgeFactorsCommuteF D) := by
  unfold OpenStab.rowBridgeFactorsCommuteF
  refine formulaDefined_allNatLt _ _ (scn_eval _ _ _ _ _) (fun row hrow => ?_)
  exact formulaDefined_commutesUpTo (Av := fun q => some (tRow D.distance row q)) (Bv := E)
    (by simp [SC.n, STerm.weaken, STerm.lift, STerm.eval, Term.eval, Term.lift]) (rowBridge_eval D E row)
    (by simp [SC.bound, STerm.eval, STerm.weaken, STerm.lift]) StabTotalUpTo.ofTotal
    (StabTotalUpTo_of_TotalUpTo hTotal)

/-- FD of `colBridgeFactorsCommuteF` (dual): each column bridge is everywhere-total. -/
theorem formulaDefined_colBridgeFactorsCommute (D : OddSurfaceDistance) {E : PartialStabilizer}
    (hTotal : TotalUpTo (nQubits D.distance) E) :
    SFormula.Deriv.FormulaDefined Surface.code.body (bridgeProofFuel D) Env.empty E
      (OpenStab.colBridgeFactorsCommuteF D) := by
  unfold OpenStab.colBridgeFactorsCommuteF
  refine formulaDefined_allNatLt _ _ (scn_eval _ _ _ _ _) (fun col hcol => ?_)
  exact formulaDefined_commutesUpTo (Av := fun q => some (tCol D.distance col q)) (Bv := E)
    (by simp [SC.n, STerm.weaken, STerm.lift, STerm.eval, Term.eval, Term.lift]) (colBridge_eval D E col)
    (by simp [SC.bound, STerm.eval, STerm.weaken, STerm.lift]) StabTotalUpTo.ofTotal
    (StabTotalUpTo_of_TotalUpTo hTotal)

/-- The cut-commutation rule is semantically TRUE for every `E` — via `Deriv.sound` of its own
derivation, whose `DefinedObligations` come from `rowCutNoX_WF` (core 1) through `deriv_defined`.
This is the `ContextHolds` ingredient for cores 4-6 (no new geometric proof, no kernel change). -/
theorem rowCutNoXImpliesCommutes_holds (D : OddSurfaceDistance) {E : PartialStabilizer}
    (hTotal : TotalUpTo (nQubits D.distance) E) :
    (rowCutNoXImpliesCommutesF D).eval Surface.code.body (bridgeProofFuel D) Env.empty E
      = some true :=
  SFormula.Deriv.sound (rowCutNoXImpliesCommutesDeriv D)
    (deriv_defined (rowCutNoXImpliesCommutesDeriv D) Surface.code.body (bridgeProofFuel D)
      Env.empty E (rowCutNoX_WF D hTotal))
    (fun A hA => by cases hA)

/-- Dual: the column cut-commutation rule is true for every `E` (via `colCutNoZ_WF`, core 2). -/
theorem colCutNoZImpliesCommutes_holds (D : OddSurfaceDistance) {E : PartialStabilizer}
    (hTotal : TotalUpTo (nQubits D.distance) E) :
    (colCutNoZImpliesCommutesF D).eval Surface.code.body (bridgeProofFuel D) Env.empty E
      = some true :=
  SFormula.Deriv.sound (colCutNoZImpliesCommutesDeriv D)
    (deriv_defined (colCutNoZImpliesCommutesDeriv D) Surface.code.body (bridgeProofFuel D)
      Env.empty E (colCutNoZ_WF D hTotal))
    (fun A hA => by cases hA)

/-- The row-cut telescoping identity is true for every `E` — `PureFamilyDeriv.sound` of the closed
leaf `rowCutTelescopingPure` (whose `DefinedObligations` are already proved). -/
theorem rowCutTelescoping_holds (D : OddSurfaceDistance) (E : PartialStabilizer) :
    (rowCutTelescopingF D).eval Surface.code.body (bridgeProofFuel D) Env.empty E = some true :=
  (rowCutTelescopingPure D).sound E (rowCutTelescopingPure_defined D E)

/-- Dual: the column-cut telescoping identity is true for every `E`. -/
theorem colCutTelescoping_holds (D : OddSurfaceDistance) (E : PartialStabilizer) :
    (colCutTelescopingF D).eval Surface.code.body (bridgeProofFuel D) Env.empty E = some true :=
  (colCutTelescopingPure D).sound E (colCutTelescopingPure_defined D E)




/-! ### Ctx truths for the bridge norms (via the closed pure family leaves + `PureFamilyDeriv.sound`). -/
theorem rowBridgeGeneratedEqF_holds (D : OddSurfaceDistance) (E : PartialStabilizer) :
    (rowBridgeGeneratedEqF D).eval Surface.code.body (bridgeProofFuel D) Env.empty E = some true :=
  (rowBridgeGeneratedPure D).sound E (rowBridgeGeneratedPure_defined D E)
theorem rowZStripIndexInRange_holds (D : OddSurfaceDistance) (E : PartialStabilizer) :
    (rowZStripIndexInRangeF D).eval Surface.code.body (bridgeProofFuel D) Env.empty E = some true :=
  (rowStripRangePure D).sound E (by trivial)
theorem colBridgeGeneratedEqF_holds (D : OddSurfaceDistance) (E : PartialStabilizer) :
    (colBridgeGeneratedEqF D).eval Surface.code.body (bridgeProofFuel D) Env.empty E = some true :=
  (colBridgeGeneratedPure D).sound E (colBridgeGeneratedPure_defined D E)
theorem colXStripIndexInRange_holds (D : OddSurfaceDistance) (E : PartialStabilizer) :
    (colXStripIndexInRangeF D).eval Surface.code.body (bridgeProofFuel D) Env.empty E = some true :=
  (colStripRangePure D).sound E (by trivial)

end QHL.CodeLang.Surface.Verify
