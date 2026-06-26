import QStab.QHL.Verify.SurfaceDistanceContract

/-!
# Pure assembly for the Surface distance contract

This module contains only object-logic assembly.  It does not run
`Formula.check`, does not use `Formula.eval` as a proof of distance, and does
not introduce any closed Surface fact by assertion.  The six closed geometric
facts that used to be `checkedBoundFree` leaves are explicit inputs.
-/

namespace QHL.CodeLang.Surface.Verify

open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

/-! ## Surface index-range leaves via the generic grid rule

The Surface index-range leaves `rowZStripIndexInRangeF`/`colXStripIndexInRangeF`
(`CodeSurface`) are *definitionally* the generic kernel grid-range formulas at
`D.distance`: the Surface aliases `numStab`/`stripWidth`/`rowZStripIndex`/
`colXStripIndex` are pure unfoldings of the kernel `gridNumStab`/`gridStripWidth`/
`gridRowZStripIndex`/`gridColXStripIndex`, and the witness/binder wrapping matches
exactly.  Hence each leaf is produced by the corresponding generic constructor
through a `rfl`-level type defeq, with **no** evaluator at proof time.  (These two
definitions used to live in `PureDeriv.lean`; they reference Surface names and so
belong here, keeping the generic pure-logic layer Surface-decoupled.) -/

/-- The row index-range leaf is closed as a pure derivation tree. -/
def rowStripRangePure (D : OddSurfaceDistance) :
    PureFamilyDeriv Surface.code.body (bridgeProofFuel D) (rowZStripIndexInRangeF D) :=
  .gridRowStripRange D.distance

/-- The column index-range leaf is closed as a pure derivation tree. -/
def colStripRangePure (D : OddSurfaceDistance) :
    PureFamilyDeriv Surface.code.body (bridgeProofFuel D) (colXStripIndexInRangeF D) :=
  .gridColStripRange D.distance

/-! ## Surface cut families and telescoping leaves via the generic fold rule

The generic `PureFamilyDeriv.foldTelescope` rule closes a fold-telescoping leaf
`foldTelescopeF cut outerBound N` for any *closed, total* cut family.  The Surface
row/column telescoping leaves `rowCutTelescopingF`/`colCutTelescopingF` are
exactly such leaves: their cut family is the inner of `rowCut`/`colCut`
(a `stabLam` returning `Z`/`X` on the matching grid line, `I` elsewhere), which is
closed and everywhere-defined.  We expose that inner family, prove its totality
(four `Term.eval` facts), and discharge the leaves through the generic rule. -/

/-- The closed inner of the Surface **row** cut family: `λ q. if q / dist = row
    then Z else I`, as a closed `Term`.  Wrapping it in `SC.closed` recovers
    `Surface.rowCut dist row`; so `telBridge`/`telPrefix` over this family are
    *definitionally* the Surface `rowBridge`/`rowCutTelescopedPrefix`. -/
def rowCutInner (dist : Nat) {a : Nat} (row : Term a .nat) : Term a .stab :=
  .stabLam <|
    .ite (.eqNat (.div Formula.qVar (.natLit dist)) row.weaken)
      (.pauliLit Pauli.Z)
      (.pauliLit Pauli.I)

/-- The closed inner of the Surface **column** cut family: `λ q. if q % dist = col
    then X else I`. -/
def colCutInner (dist : Nat) {a : Nat} (col : Term a .nat) : Term a .stab :=
  .stabLam <|
    .ite (.eqNat (.mod Formula.qVar (.natLit dist)) col.weaken)
      (.pauliLit Pauli.X)
      (.pauliLit Pauli.I)

/-- The six closed Surface facts needed by the lower-bound proof, now as pure
derivation-tree inputs rather than evaluator-checked leaves. -/
structure PureLowerClosedLeaves (D : OddSurfaceDistance) where
  rowBridgeGenerated :
    PureFamilyDeriv Surface.code.body (bridgeProofFuel D) (rowBridgeGeneratedEqF D)
  rowStripIndexInRange :
    PureFamilyDeriv Surface.code.body (bridgeProofFuel D) (rowZStripIndexInRangeF D)
  rowCutTelescoping :
    PureFamilyDeriv Surface.code.body (bridgeProofFuel D) (rowCutTelescopingF D)
  colBridgeGenerated :
    PureFamilyDeriv Surface.code.body (bridgeProofFuel D) (colBridgeGeneratedEqF D)
  colStripIndexInRange :
    PureFamilyDeriv Surface.code.body (bridgeProofFuel D) (colXStripIndexInRangeF D)
  colCutTelescoping :
    PureFamilyDeriv Surface.code.body (bridgeProofFuel D) (colCutTelescopingF D)

namespace PureLowerClosedLeaves

/-- Row bridge factors from a generated bridge equality and strip-index range
fact, using only the generic symbolic derivation already present in
`CodeSurface`. -/
def rowBridgeFactorsFromNormalizer {D : OddSurfaceDistance}
    (L : PureLowerClosedLeaves D) :
    PureFamilyDeriv Surface.code.body (bridgeProofFuel D)
      (rowBridgeFactorsFromNormalizerF D) :=
  .cut2 (rowBridgeFactorsFromGeneratedNormalizerDeriv D)
    L.rowBridgeGenerated
    L.rowStripIndexInRange

/-- Column bridge factors, dual to `rowBridgeFactorsFromNormalizer`. -/
def colBridgeFactorsFromNormalizer {D : OddSurfaceDistance}
    (L : PureLowerClosedLeaves D) :
    PureFamilyDeriv Surface.code.body (bridgeProofFuel D)
      (colBridgeFactorsFromNormalizerF D) :=
  .cut2 (colBridgeFactorsFromGeneratedNormalizerDeriv D)
    L.colBridgeGenerated
    L.colStripIndexInRange

/-- X-side parity propagation from the closed row facts and the generic local
cut-commutation derivation. -/
def xParityPropagationRows {D : OddSurfaceDistance}
    (L : PureLowerClosedLeaves D) :
    PureFamilyDeriv Surface.code.body (bridgeProofFuel D)
      (OpenStab.xParityPropagationRowsF D) :=
  .cut3 (OpenStab.xParityPropagationRowsFromBridgeFactorsDeriv D)
    (.core (rowCutNoXImpliesCommutesDeriv D))
    L.rowCutTelescoping
    L.rowBridgeFactorsFromNormalizer

/-- Z-side parity propagation, dual to `xParityPropagationRows`. -/
def zParityPropagationCols {D : OddSurfaceDistance}
    (L : PureLowerClosedLeaves D) :
    PureFamilyDeriv Surface.code.body (bridgeProofFuel D)
      (OpenStab.zParityPropagationColsF D) :=
  .cut3 (OpenStab.zParityPropagationColsFromBridgeFactorsDeriv D)
    (.core (colCutNoZImpliesCommutesDeriv D))
    L.colCutTelescoping
    L.colBridgeFactorsFromNormalizer

/-- Full pure lower-bound derivation, assuming only the six closed Surface
leaves above.  The parity, support, counting, and final implication steps are
all generic `SFormula.Deriv` trees wrapped through `PureFamilyDeriv.core`/cuts. -/
def lowerBound {D : OddSurfaceDistance}
    (L : PureLowerClosedLeaves D) :
    PureForallStabDeriv Surface.code.body (bridgeProofFuel D)
      (distanceLowerBoundForallStabF D) :=
  .intro <|
    .cut4 (distanceLowerBoundBodyFromFamilyLemmasDeriv D)
      L.xParityPropagationRows
      (.core (xRowsWeightLowerByCountingDeriv D))
      L.zParityPropagationCols
      (.core (zColsWeightLowerByCountingDeriv D))

end PureLowerClosedLeaves

/-! ### Totality of the Surface cut families, and the telescoping leaves

`rowCutInner`/`colCutInner` are *total* closed cut families: at any index value
they evaluate to an everywhere-defined stabilizer.  The four `Term.eval` facts the
generic `foldTelescope` obligation demands are all instances of a single
single-binder evaluation, with the index argument computed in the supplied
environment.  The Pauli interpretation is `gRow dist iv q = if q / dist = iv then
Z else I` (and `gCol` with `%`). -/

/-- Pauli interpretation realised by the row cut family. -/
def gRow (dist iv q : Nat) : Pauli := if q / dist = iv then Pauli.Z else Pauli.I

/-- Pauli interpretation realised by the column cut family. -/
def gCol (dist iv q : Nat) : Pauli := if q % dist = iv then Pauli.X else Pauli.I

/-- The row cut at a nat-term index `idx` (evaluating to `iv` in `rho`) is the
    everywhere-defined stabilizer `fun q => some (gRow dist iv q)`. -/
theorem rowCutInner_eval {a : Nat} (dist : Nat) (cb : Term 2 .stab) (fuel iv : Nat)
    (idx : Term a .nat) (rho : Env a) (hidx : Term.eval cb fuel idx rho = some iv) :
    Term.eval cb fuel (rowCutInner dist idx) rho =
      some (fun q => some (gRow dist iv q)) := by
  simp only [rowCutInner, Term.eval]
  congr 1
  funext q
  have hidxW : Term.eval cb fuel idx.weaken (Env.cons q rho) = some iv := by
    rw [Term.weaken, Term.eval_weaken_top]; exact hidx
  simp only [Formula.qVar, Term.eval, Env.cons, hidxW, gRow]
  by_cases h : q / dist = iv <;> simp [h]

/-- The column cut at a nat-term index `idx` (evaluating to `iv` in `rho`) is the
    everywhere-defined stabilizer `fun q => some (gCol dist iv q)`. -/
theorem colCutInner_eval {a : Nat} (dist : Nat) (cb : Term 2 .stab) (fuel iv : Nat)
    (idx : Term a .nat) (rho : Env a) (hidx : Term.eval cb fuel idx rho = some iv) :
    Term.eval cb fuel (colCutInner dist idx) rho =
      some (fun q => some (gCol dist iv q)) := by
  simp only [colCutInner, Term.eval]
  congr 1
  funext q
  have hidxW : Term.eval cb fuel idx.weaken (Env.cons q rho) = some iv := by
    rw [Term.weaken, Term.eval_weaken_top]; exact hidx
  simp only [Formula.qVar, Term.eval, Env.cons, hidxW, gCol]
  by_cases h : q % dist = iv <;> simp [h]

/-- **Row telescoping leaf** as a pure derivation, via the generic `foldTelescope`
    rule.  `rowCutTelescopingF D` is *definitionally* `foldTelescopeF
    (rowCutInner D.distance) D.distance (nQubits D.distance)`. -/
def rowCutTelescopingPure (D : OddSurfaceDistance) :
    PureFamilyDeriv Surface.code.body (bridgeProofFuel D) (rowCutTelescopingF D) :=
  .foldTelescope (rowCutInner D.distance) D.distance (nQubits D.distance)

/-- **Column telescoping leaf** as a pure derivation, dual to the row one. -/
def colCutTelescopingPure (D : OddSurfaceDistance) :
    PureFamilyDeriv Surface.code.body (bridgeProofFuel D) (colCutTelescopingF D) :=
  .foldTelescope (colCutInner D.distance) D.distance (nQubits D.distance)

/-- The row telescoping leaf's definedness obligation: totality of `rowCutInner`,
    witnessed by `gRow D.distance`.  All four facts follow from `rowCutInner_eval`
    with the index argument evaluated in its environment. -/
theorem rowCutTelescopingPure_defined (D : OddSurfaceDistance) (E : PartialStabilizer) :
    (rowCutTelescopingPure D).DefinedObligations E := by
  refine ⟨gRow D.distance, ?_, ?_, ?_, ?_⟩
  · intro row iv
    exact rowCutInner_eval D.distance _ _ iv telFoldVar _ (by simp [telFoldVar, Term.eval, Env.cons])
  · intro row iv
    refine rowCutInner_eval D.distance _ _ (iv + 1) (.add telFoldVar (.natLit 1)) _ ?_
    simp [telFoldVar, Term.eval, Env.cons]
  · intro row
    exact rowCutInner_eval D.distance _ _ 0 (.natLit 0) _ (by simp [Term.eval])
  · intro row
    exact rowCutInner_eval D.distance _ _ row telRowVar _ (by simp [telRowVar, Term.eval, Env.cons])

/-- The column telescoping leaf's definedness obligation, dual to the row one. -/
theorem colCutTelescopingPure_defined (D : OddSurfaceDistance) (E : PartialStabilizer) :
    (colCutTelescopingPure D).DefinedObligations E := by
  refine ⟨gCol D.distance, ?_, ?_, ?_, ?_⟩
  · intro row iv
    exact colCutInner_eval D.distance _ _ iv telFoldVar _ (by simp [telFoldVar, Term.eval, Env.cons])
  · intro row iv
    refine colCutInner_eval D.distance _ _ (iv + 1) (.add telFoldVar (.natLit 1)) _ ?_
    simp [telFoldVar, Term.eval, Env.cons]
  · intro row
    exact colCutInner_eval D.distance _ _ 0 (.natLit 0) _ (by simp [Term.eval])
  · intro row
    exact colCutInner_eval D.distance _ _ row telRowVar _ (by simp [telRowVar, Term.eval, Env.cons])

#print axioms rowStripRangePure
#print axioms colStripRangePure
#print axioms rowCutTelescopingPure
#print axioms colCutTelescopingPure
#print axioms rowCutTelescopingPure_defined
#print axioms colCutTelescopingPure_defined

end QHL.CodeLang.Surface.Verify
