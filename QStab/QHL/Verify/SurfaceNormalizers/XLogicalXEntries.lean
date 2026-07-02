import QStab.QHL.Verify.SurfaceNormalizers.XSetup

/-!
# Logical-normalizer consumers — XLogicalXEntries

The symbolic (∀ D) logicalX normaliser scaffolding: arity witnesses and flat row-entry
resolvers, the arity-general `baseLeafTreeTA` leaf peels, the `logicalX` entry lemmas, and the
per-`k` row stabiliser + arity-1 `arithBool` facts.
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface

set_option maxRecDepth 65536

/-! ## Symbolic (forall D) logicalX normalizer (geometric classification)

The definitions below implement the geometric classification of the bound
stabilizer index that closes the `sorry` in `xNormScaffold`.  They were developed
incrementally and are prover-side only (no `native_decide` / `Formula.check` /
`Formula.eval`-as-proof / `deriveTrue?` / `admit` / new `axiom` / `unsafe`). -/

/-! ## The arity-1 distance witness and flat row-entry resolver

`distAtBoundIdx D : DistAtA 1 D.index` has `dT = Term.lift 0 (.natLit D.distance)`,
exactly the distance term appearing in the per-`k` commutation goal of
`xNormScaffold` (after `allNatLtIntro`).  `rowEntryFlatSym` keyed to it resolves
the generated row entry at the symbolic stabilizer index `k = var 0` and any pure
qubit term `qT` directly to the flat classifier `baseLeafTreeTA`. -/

/-- The distance term shared by the goal and by `distAtBoundIdx`. -/
abbrev dX1 (D : OddSurfaceDistance) : Term 1 .nat := Term.lift 0 (Term.natLit D.distance)

/-- The bound stabilizer index `k = var 0` at arity 1. -/
abbrev kX1 : Term 1 .nat := Term.var ⟨0, by decide⟩

/-- **Flat row entry at a pure qubit term.**  For any pure qubit term `qT`, the
generated row entry of the bound stabilizer `k = var 0` at `qT` equals the flat
recursion-free classifier `baseLeafTreeTA (lift d) (var 0) qT`. -/
def xEntryFlat1 (D : OddSurfaceDistance) (qT : Term 1 .nat) (hq : SFormula.PureNatTerm qT) :
    PureFamilyDerivA Surface.code.body (D.distance + 2)
      (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed qT))
        (SC.closed (baseLeafTreeTA (dX1 D) kX1 qT))) :=
  rowEntryFlatSym (fuel := D.distance + 2) D.index (distAtBoundIdx D) kX1 qT
    (SFormula.PureNatTerm.var ⟨0, by decide⟩) hq

/-! ## Arity-general `baseLeafTreeTA` leaf peels (public, re-derived locally)

Mirrors of the `private baseLeaf*S` reducers in `SurfaceFlatBridge.lean`, reducing
`baseLeafTreeTA dT kT qT` to its selected leaf Pauli given the cell-class / band
guards as `SFormula.Deriv` premises.  Each is a transparent `eqPauliTrans` chain of
`pauliIteSelectThen/Else` over the `ite`-tree of `baseLeafTreeTA`.  Arity-general so
they apply at both arity 1 (literal qubit) and arity 2 (symbolic qubit binder). -/

def baseLeafZ {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hBand : SFormula.Deriv Γ (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)))
    (hKind : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b true))) :
    SFormula.Deriv Γ (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.p Pauli.Z)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hBand)
      (SFormula.Deriv.pauliIteSelectThen _ _ _ hKind))

def baseLeafBulkX {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hBand : SFormula.Deriv Γ (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)))
    (hKind : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b false))) :
    SFormula.Deriv Γ (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.p Pauli.X)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hBand)
      (SFormula.Deriv.pauliIteSelectElse _ _ _ hKind))

def baseLeafBulkI {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hBand : SFormula.Deriv Γ (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false))) :
    SFormula.Deriv Γ (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.p Pauli.I)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hBulk)
    (SFormula.Deriv.pauliIteSelectElse _ _ _ hBand)

def baseLeafTopX {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b true)))
    (hTopBand : SFormula.Deriv Γ (.eqBool (SC.closed (topBandGuardTA dT kT qT)) (SC.b true))) :
    SFormula.Deriv Γ (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.p Pauli.X)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hTopClass)
      (SFormula.Deriv.pauliIteSelectThen _ _ _ hTopBand))

def baseLeafTopI {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b true)))
    (hTopBand : SFormula.Deriv Γ (.eqBool (SC.closed (topBandGuardTA dT kT qT)) (SC.b false))) :
    SFormula.Deriv Γ (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.p Pauli.I)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hTopClass)
      (SFormula.Deriv.pauliIteSelectElse _ _ _ hTopBand))

def baseLeafRightZ {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false)))
    (hRightClass : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b true)))
    (hRightBand : SFormula.Deriv Γ (.eqBool (SC.closed (rightBandGuardTA dT kT qT)) (SC.b true))) :
    SFormula.Deriv Γ (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.p Pauli.Z)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hTopClass)
      (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hRightClass)
        (SFormula.Deriv.pauliIteSelectThen _ _ _ hRightBand)))

def baseLeafRightI {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false)))
    (hRightClass : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b true)))
    (hRightBand : SFormula.Deriv Γ (.eqBool (SC.closed (rightBandGuardTA dT kT qT)) (SC.b false))) :
    SFormula.Deriv Γ (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.p Pauli.I)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hTopClass)
      (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hRightClass)
        (SFormula.Deriv.pauliIteSelectElse _ _ _ hRightBand)))

def baseLeafLeftZ {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false)))
    (hRightClass : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b false)))
    (hLeftClass : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA dT kT)) (SC.b true)))
    (hLeftBand : SFormula.Deriv Γ (.eqBool (SC.closed (leftBandGuardTA dT kT qT)) (SC.b true))) :
    SFormula.Deriv Γ (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.p Pauli.Z)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hTopClass)
      (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hRightClass)
        (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hLeftClass)
          (SFormula.Deriv.pauliIteSelectThen _ _ _ hLeftBand))))

def baseLeafLeftI {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false)))
    (hRightClass : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b false)))
    (hLeftClass : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA dT kT)) (SC.b true)))
    (hLeftBand : SFormula.Deriv Γ (.eqBool (SC.closed (leftBandGuardTA dT kT qT)) (SC.b false))) :
    SFormula.Deriv Γ (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.p Pauli.I)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hTopClass)
      (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hRightClass)
        (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hLeftClass)
          (SFormula.Deriv.pauliIteSelectElse _ _ _ hLeftBand))))

def baseLeafBottomX {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false)))
    (hRightClass : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b false)))
    (hLeftClass : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA dT kT)) (SC.b false)))
    (hBottomBand : SFormula.Deriv Γ (.eqBool (SC.closed (bottomBandGuardTA dT kT qT)) (SC.b true))) :
    SFormula.Deriv Γ (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.p Pauli.X)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hTopClass)
      (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hRightClass)
        (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hLeftClass)
          (SFormula.Deriv.pauliIteSelectThen _ _ _ hBottomBand))))

def baseLeafBottomI {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false)))
    (hRightClass : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b false)))
    (hLeftClass : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA dT kT)) (SC.b false)))
    (hBottomBand : SFormula.Deriv Γ (.eqBool (SC.closed (bottomBandGuardTA dT kT qT)) (SC.b false))) :
    SFormula.Deriv Γ (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.p Pauli.I)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hTopClass)
      (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hRightClass)
        (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hLeftClass)
          (SFormula.Deriv.pauliIteSelectElse _ _ _ hBottomBand))))

/-! ## `logicalX` entry lemmas (∀ D)

The lifted `logicalX` operator and its column-0 / off-column entries, generalized
from the d=3 mirrors `logicalXOnColumnEntryX` / `logicalXLitEntryX`. -/

/-- The lifted `logicalX` operator at arity 2 (`(lift logicalXOdd D).weaken`). -/
abbrev liftedLX2 (D : OddSurfaceDistance) : STerm 2 .stab :=
  (SC.closed (Term.lift 0 (logicalXOdd D))).weaken

/-- The lifted `logicalX` operator at arity 1 (`lift logicalXOdd D`). -/
abbrev liftedLX1 (D : OddSurfaceDistance) : STerm 1 .stab :=
  SC.closed (Term.lift 0 (logicalXOdd D))

/-- On a column-0 qubit (column guard `q mod d = 0` TRUE), the `logicalX` entry at
the bound qubit is `X`.  ∀-D mirror of `logicalXOnColumnEntryX`. -/
def lxOnColEntryX {Δ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hTrue : SFormula.Deriv Δ (.eqBool (logicalXColGuardAt2 D) (SC.b true))) :
    SFormula.Deriv Δ (.eqPauli (.stabAt (liftedLX2 D) SFormula.boundNat) (SC.p Pauli.X)) := by
  have h := SFormula.Deriv.stabAtClosedIteLamEqThen (Γ := Δ)
    (.eqNat (.mod Formula.qVar (.natLit D.distance)) (.natLit 0))
    (.pauliLit Pauli.X) (.pauliLit Pauli.I)
    (Term.var ⟨0, by decide⟩)
    (SFormula.PureNatTerm.var ⟨0, by decide⟩)
    (by simpa [logicalXColGuardAt2] using hTrue)
  simpa [liftedLX2, logicalXOdd, logicalX, Formula.qVar, SFormula.boundNat, SC.closed, SC.p,
    OddSurfaceDistance.distance, oddDistance,
    STerm.weaken, STerm.lift, Term.instantiateTopNat, Term.instantiateNatAt, Term.lift,
    Term.weaken, Term.weakenVar] using h

/-- The closed `logicalX` column guard `q mod d = 0` at a PURE qubit term `qT`,
true form, at arity 1. -/
abbrev colGuardPure1 (D : OddSurfaceDistance) (qT : Term 1 .nat) : SFormula 1 :=
  .eqBool (SC.closed (.eqNat (.mod qT (.natLit D.distance)) (.natLit 0))) (SC.b true)

/-- At a PURE column-0 qubit `qT`, given the closed column guard `qT mod d = 0`,
the `logicalX` entry is `X`.  Arity-1 ∀-D mirror of `logicalXLitEntryX`. -/
def lxPureEntryX {Γ : List (SFormula 1)} (D : OddSurfaceDistance)
    (qT : Term 1 .nat) (hq : SFormula.PureNatTerm qT)
    (hguardq : SFormula.Deriv Γ (colGuardPure1 D qT)) :
    SFormula.Deriv Γ (.eqPauli (.stabAt (liftedLX1 D) (SC.closed qT)) (SC.p Pauli.X)) := by
  have hguard : SFormula.Deriv Γ
      (.eqBool (SC.closed (Term.instantiateTopNat qT
        (.eqNat (.mod Formula.qVar (.natLit D.distance)) (.natLit 0)))) (SC.b true)) := by
    simpa [colGuardPure1, Formula.qVar,
      Term.instantiateTopNat, Term.instantiateNatAt] using hguardq
  have h := SFormula.Deriv.stabAtClosedIteLamEqThen (Γ := Γ)
    (.eqNat (.mod Formula.qVar (.natLit D.distance)) (.natLit 0))
    (.pauliLit Pauli.X) (.pauliLit Pauli.I)
    qT hq hguard
  simpa [liftedLX1, logicalXOdd, logicalX, Formula.qVar, SC.closed, SC.p,
    Term.instantiateTopNat, Term.instantiateNatAt, Term.lift] using h

/-! ## Arity-2 distance witness and symbolic-qubit flat resolver

Inside the all-others / pointwise premises the row stabilizer is weakened to arity
2 and probed at the symbolic qubit binder `boundNat = SC.closed (var 0)`.  At arity
2 the once-weakened stabilizer index is `k = var 1` and the distance term is
`lift0 (lift0 (natLit d)) = (distAtBoundIdx2 D).dT`. -/

/-- Distance term at arity 2 (the weakening of `dX1`). -/
abbrev dX2 (D : OddSurfaceDistance) : Term 2 .nat := (distAtBoundIdx2 D).dT
/-- Once-weakened stabilizer index `k = var 1` at arity 2. -/
abbrev kX2 : Term 2 .nat := Term.var ⟨1, by decide⟩

/-- **Flat row entry at the symbolic qubit binder.**  At arity 2 the generated row
entry of the (once-weakened) bound stabilizer `k = var 1` at `boundNat = var 0`
equals the flat classifier `baseLeafTreeTA (dX2 D) (var 1) (var 0)`. -/
def xEntryFlat2Bound (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2)
      (.eqPauli (.stabAt (SC.closed (.recCall (dX2 D) kX2)) SFormula.boundNat)
        (SC.closed (baseLeafTreeTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩)))) :=
  rowEntryFlatSym (fuel := D.distance + 2) D.index (distAtBoundIdx2 D) kX2
    (Term.var ⟨0, by decide⟩)
    (SFormula.PureNatTerm.var ⟨1, by decide⟩)
    (SFormula.PureNatTerm.var ⟨0, by decide⟩)

/-! ## Per-`k` row stabilizer (arity 1) -/

/-- The frozen row stabilizer of the per-`k` goal at arity 1. -/
abbrev rowK1 (D : OddSurfaceDistance) : STerm 1 .stab :=
  SC.closed ((Term.lift 0 (Term.natLit D.distance)).recCall (Term.var ⟨0, Formula.normalizesCodeUpTo._proof_1⟩))

/-- The weakened (arity-2) row stabilizer, in the form that appears inside the
pointwise / all-others premises. -/
abbrev rowK2 (D : OddSurfaceDistance) : STerm 2 .stab :=
  (SC.closed ((Term.lift 0 (Term.natLit D.distance)).recCall (Term.var ⟨0, Formula.normalizesCodeUpTo._proof_1⟩))).weaken

/-- **The weakened row stabilizer is the arity-2 `recCall` at `k = var 1`.**
Definitional bridge: `(rowK1 D).weaken = SC.closed (recCall (dX2 D) (var 1))`. -/
theorem rowK2_eq (D : OddSurfaceDistance) :
    rowK2 D = SC.closed (.recCall (dX2 D) kX2) := rfl

/-- The flat row entry at the symbolic qubit binder, with the left stabilizer in
the `rowK2` (weakened) form used inside the premises. -/
def xEntryFlat2BoundW (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2)
      (.eqPauli (.stabAt (rowK2 D) SFormula.boundNat)
        (SC.closed (baseLeafTreeTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩)))) := by
  rw [rowK2_eq]; exact xEntryFlat2Bound D

/-- **Column-0 local commutation from a non-`Z` row entry.**  Given the column
guard true at `boundNat` (so `logicalX` entry is `X`) and the row entry at
`boundNat` equal to a Pauli `p` with `anticommutes p X = false`, the row locally
commutes with `logicalX` at `boundNat`. -/
def colCommFromEntry {Δ : List (SFormula 2)} (D : OddSurfaceDistance) (p : Pauli)
    (hEntry : SFormula.Deriv Δ (.eqPauli (.stabAt (rowK2 D) SFormula.boundNat) (SC.p p)))
    (hAnti : SFormula.Deriv Δ (.eqBool (.anticommutes (SC.p Pauli.X) (SC.p p)) (SC.b false)))
    (hcol : SFormula.Deriv Δ (.eqBool (logicalXColGuardAt2 D) (SC.b true))) :
    SFormula.Deriv Δ (SFormula.localCommutesAt (rowK2 D) (liftedLX2 D) SFormula.boundNat) := by
  refine SFormula.Deriv.localCommutesOfLeftEqNoAntiRight _ _ _ (SC.p p) hEntry ?_
  -- `¬ anticommutes (logicalX entry) p = true`; the logicalX entry is `X`.
  have hX := lxOnColEntryX (Δ := Δ) D hcol
  have hLitFalse : SFormula.Deriv Δ
      (.eqBool (.anticommutes (.stabAt (liftedLX2 D) SFormula.boundNat) (SC.p p)) (SC.b false)) :=
    SFormula.Deriv.anticommutesTransport _ (SC.p Pauli.X) _ (SC.p p) (SC.b false)
      hX (SFormula.Deriv.pauliEqLit p) hAnti
  exact SFormula.Deriv.eqBoolFalseNotTrue _ hLitFalse

/-- The closed column guard at `boundNat`, raw `var0 % d = 0` form, as it appears
after unfolding `logicalXColGuardAt2`. -/
abbrev colGuardRaw2 (D : OddSurfaceDistance) : SFormula 2 :=
  .eqBool (SC.closed (.eqNat (.mod (Term.var ⟨0, by decide⟩) (Term.natLit D.distance)) (Term.natLit 0)))
    (SC.b true)

/-- `logicalXColGuardAt2 D = colGuardRaw2 D` after the instantiation reduces. -/
theorem colGuard2_eq (D : OddSurfaceDistance) :
    (SFormula.eqBool (logicalXColGuardAt2 D) (SC.b true)) = colGuardRaw2 D := by
  simp [logicalXColGuardAt2, colGuardRaw2, Formula.qVar, OddSurfaceDistance.distance,
    Term.instantiateTopNat, Term.instantiateNatAt]

/-! ## Arity-1 quantified arithmetic facts (`arithBool`)

These are the universally-true (class-independent) cell-guard facts over the
qubit `q < nQubits`, with the stabilizer index `k = var 0` symbolic.  Each is in
the `arithBoolFragment` (closed Nat/Bool atoms only) and discharged in one
`arithBool`.  Weakened to arity 2 and eliminated at `boundNat`, they supply the
arity-2 guard facts the column-0 dispatcher needs. -/

/-- The distance term at arity 1, raw form `natLit d` after the lift cancels under
elimination.  (We work with `dX1 D = lift0 (natLit d)`; under the per-`q` body the
guards mention `lift0 (natLit d)` directly.) -/
abbrev dBody : OddSurfaceDistance → Term 2 .nat := fun D => Term.lift 0 (dX1 D)

/-- Body (arity 2, qubit binder `boundNat = var 0`, `k = var 1`): on column 0
(`q % d = 0`), the right-`Z` boundary band guard is `false`.  (Right-`Z` lives in
column `d-1 ≠ 0`.) -/
abbrev rightBandFalseBody (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (colGuardRaw2 D)
    (.eqBool (SC.closed (rightBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.b false))

/-- The qubit-quantifier bound as it appears in the per-`k` goal: the once-lifted
literal `lift0 (natLit nQubits)` (so its weakening matches the `boundNatLt`
introduced by `allNatLtIntroBounded` on the goal). -/
abbrev nQ1 (D : OddSurfaceDistance) : STerm 1 .nat :=
  SC.closed (Term.lift 0 (Term.natLit (nQubits D.distance)))

/-- Quantified right-band-false fact, arity 1. -/
abbrev rightBandFalseF (D : OddSurfaceDistance) : SFormula 1 :=
  .allNatLt (nQ1 D) (rightBandFalseBody D)

/-- The `c = k mod (d-1) = 0` guard at arity 1 (k-only). -/
abbrev cZero1 (D : OddSurfaceDistance) (v : Bool) : SFormula 1 :=
  .eqBool (SC.closed (.eqNat (.mod kX1 (dm1TA (dX1 D))) (.natLit 0))) (SC.b v)
/-- The `c = k mod (d-1) = 0` guard at arity 2 (`k = var 1`). -/
abbrev cZero2 (D : OddSurfaceDistance) (v : Bool) : SFormula 2 :=
  .eqBool (SC.closed (.eqNat (.mod kX2 (dm1TA (dX2 D))) (.natLit 0))) (SC.b v)

/-- Body (arity 2): on column 0, if the bulk band guard holds then `c = 0`. -/
abbrev bandImpCZeroBody (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (colGuardRaw2 D)
    (.imp (.eqBool (SC.closed (baseBulkBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.b true))
      (cZero2 D true))

abbrev bandImpCZeroF (D : OddSurfaceDistance) : SFormula 1 :=
  .allNatLt (nQ1 D) (bandImpCZeroBody D)

def bandImpCZeroPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (bandImpCZeroF D) := by
  refine PureFamilyDerivA.allNatLtIntro _ ?_
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [baseBulkBandGuardTA, cZero2, dX2, distAtBoundIdx2, kX2, dm1TA, orEqSucc, band3,
    bulkCountTA, SFormula.eval, SC.closed, SC.b, STerm.eval, Term.eval, Term.lift, bind, Option.bind]
  -- Abstract the opaque row-match and bulk-range decides; only the column (mod) part matters.
  by_cases hq : rho ⟨0, by decide⟩ % D.distance = 0
  · rw [hq]
    by_cases hc : rho ⟨1, by decide⟩ % (D.distance - 1) = 0
    · -- c = 0 → cZero holds, both branches give `some true`.
      rw [hc]
      generalize (decide (rho ⟨0, by decide⟩ / D.distance = rho ⟨1, by decide⟩ / (D.distance - 1))) = r0
      generalize (decide (rho ⟨0, by decide⟩ / D.distance = rho ⟨1, by decide⟩ / (D.distance - 1) + 1)) = r1
      generalize (decide (rho ⟨1, by decide⟩ < (D.distance - 1) * (D.distance - 1))) = bk
      cases r0 <;> cases r1 <;> cases bk <;> simp
    · -- c ≠ 0 → the column (mod) disjunct is false, so band is false.
      have hc1 : decide (0 = rho ⟨1, by decide⟩ % (D.distance - 1)) = false := by
        simp only [decide_eq_false_iff_not]; omega
      have hc2 : decide (0 = rho ⟨1, by decide⟩ % (D.distance - 1) + 1) = false := by
        simp only [decide_eq_false_iff_not]; omega
      rw [hc1, hc2]
      generalize (decide (rho ⟨0, by decide⟩ / D.distance = rho ⟨1, by decide⟩ / (D.distance - 1))) = r0
      generalize (decide (rho ⟨0, by decide⟩ / D.distance = rho ⟨1, by decide⟩ / (D.distance - 1) + 1)) = r1
      cases r0 <;> cases r1 <;> simp
  · simp only [hq, decide_false, Bool.false_eq_true, if_false, reduceIte]

def rightBandFalsePack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (rightBandFalseF D) := by
  refine PureFamilyDerivA.allNatLtIntro _ ?_
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  have hd0 : (0 : Nat) ≠ D.distance - 1 := by omega
  simp only [rightBandGuardTA, dX2, distAtBoundIdx2, kX2, dm1TA, orEqSucc,
    SFormula.eval, SC.closed, SC.b, STerm.eval, Term.eval, Term.lift, bind, Option.bind]
  by_cases hq : rho ⟨0, by decide⟩ % D.distance = 0
  · -- column 0: inner `if q%d = d-1` is false (0 ≠ d-1 since d ≥ 3).
    rw [hq]
    simp only [hd0, decide_true, decide_false, Bool.false_eq_true, if_false, if_true, reduceIte]
  · simp only [hq, decide_false, Bool.false_eq_true, if_false, reduceIte]

end QHL.CodeLang.Surface.Verify
