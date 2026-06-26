import QStab.QHL.Verify.SurfacePureAssembly

/-!
# Surface bridge-generated equalities as pure derivation trees

The two OPEN lower-bound leaves `rowBridgeGenerated`/`colBridgeGenerated` of the
Surface distance prover are *bridge = strip-product* equalities

  `∀ row < d-1,  rowBridge d row  =_N  ∏_{slot < stripWidth d} codeRow(stripIdx row slot)`.

These are *definitionally* the generic `foldDisjointF` formula of `PureDeriv`, so
each is closed by the generic `PureFamilyDeriv.foldDisjoint` rule: the bridge LHS,
the strip body, the outer/strip bounds, and the qubit bound are read straight off
`rowBridgeGeneratedEqF`/`colBridgeGeneratedEqF`.

The rule's soundness side-condition (the *disjoint-tiling* fact: the strip's bulk
plaquettes and one boundary stabilizer tile the two-row band with no overlaps, so
their product collapses to the bridge) is its `DefinedObligations`, discharged in
the prover's `lowerDefined` field.
-/

namespace QHL.CodeLang.Surface.Verify

open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

/-- The closed strip body of the **row** strip product: the recursive surface
    stabilizer `codeRow d (rowZStripIndex d row slot)` at the fold slot. -/
def rowStripBody (D : OddSurfaceDistance) : STerm 2 .stab :=
  .closed (Formula.codeRow (.natLit D.distance)
    (rowZStripIndex D.distance rowVar1.weaken colVar))

/-- The closed strip body of the **column** strip product. -/
def colStripBody (D : OddSurfaceDistance) : STerm 2 .stab :=
  .closed (Formula.codeRow (.natLit D.distance)
    (colXStripIndex D.distance rowVar1.weaken colVar))

/-- `rowBridgeGeneratedEqF D` is definitionally the generic disjoint-fold formula. -/
theorem rowBridgeGeneratedEqF_eq (D : OddSurfaceDistance) :
    rowBridgeGeneratedEqF D =
      foldDisjointF (rowBridge D.distance rowVar1) (rowStripBody D)
        (D.distance - 1) (stripWidth D.distance) (nQubits D.distance) := rfl

/-- `colBridgeGeneratedEqF D` is definitionally the generic disjoint-fold formula. -/
theorem colBridgeGeneratedEqF_eq (D : OddSurfaceDistance) :
    colBridgeGeneratedEqF D =
      foldDisjointF (colBridge D.distance rowVar1) (colStripBody D)
        (D.distance - 1) (stripWidth D.distance) (nQubits D.distance) := rfl

/-- **Row bridge-generated equality** as a pure derivation tree, via the generic
    `foldDisjoint` rule. -/
def rowBridgeGeneratedPure (D : OddSurfaceDistance) :
    PureFamilyDeriv Surface.code.body (bridgeProofFuel D) (rowBridgeGeneratedEqF D) :=
  .foldDisjoint (rowBridge D.distance rowVar1) (rowStripBody D)
    (D.distance - 1) (stripWidth D.distance) (nQubits D.distance)

/-- **Column bridge-generated equality** as a pure derivation tree, dual to the row
    one. -/
def colBridgeGeneratedPure (D : OddSurfaceDistance) :
    PureFamilyDeriv Surface.code.body (bridgeProofFuel D) (colBridgeGeneratedEqF D) :=
  .foldDisjoint (colBridge D.distance rowVar1) (colStripBody D)
    (D.distance - 1) (stripWidth D.distance) (nQubits D.distance)

#print axioms rowBridgeGeneratedPure
#print axioms colBridgeGeneratedPure

end QHL.CodeLang.Surface.Verify
