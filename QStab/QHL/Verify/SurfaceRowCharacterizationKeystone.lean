import QStab.QHL.Verify.SurfaceRowCharacterizationGrid

/-!
# Keystone: distance-uniform cell classifier + promoted-boundary peel

`SurfaceRowCharacterizationFull.lean` discharges the `OddSurfaceDistance.index`
induction for the **center** cell (`recCenterChar`), and
`SurfaceRowCharacterizationGrid.lean` provides parametric peels for every
*base-entry* cell kind (bulk `Z`/`X`, four boundary checks) plus the
arbitrary-interior-`k` recursive engine `recInteriorRow_withIH`.

This file adds the two pieces needed to generalise `recCenterChar` from the
center cell to *all* `k`:

1. A **distance-uniform cell classifier** `surfaceCellPauli d k q` (and the
   `surfaceCellGuard` band), parametric in `d`/`k`/`q`, giving the expected entry
   Pauli of stabilizer `k` at qubit `q` — the recursive geometry classified via
   the same `rowOf`/`colOf` arithmetic that `recursiveEntry`/`baseEntry` use.

2. A **promoted-boundary peel** (`recPromotedBoundaryPeel{Inner,Outer,I}`), the
   `recInteriorPeel`-analogue over `promotedBoundaryEntry`: when the `inside`
   guard holds the entry is the inner-code reference `recCall (d-2) oldK innerQ`
   (resolved by the IH one layer down), and when `inside` fails the entry is the
   closed `ite outer (kind) I` leaf.

Nothing here adds a trusted rule, uses `native_decide`, `Formula.check`,
`Formula.eval`-as-distance, `deriveTrue?`, `admit`, or a new axiom.  Everything
reuses the foundation peel infrastructure of `SurfaceRowCharacterization*`.
-/

namespace QHL.CodeLang.Surface.Verify

open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface

set_option maxRecDepth 65536

/-! ## Distance-uniform cell classifier

`surfaceCellPauli d k q` returns the expected Pauli entry of stabilizer `k` at
qubit `q` for distance `d`.  The classification mirrors `CodeSurface.baseEntry`
exactly at the *grid* level (it does NOT re-run the recursion; for an interior
bulk cell at `d ≥ 5` the recursive entry references the inner code, whose entry
is by construction equal to `surfaceCellPauli (d-2) interiorK innerQ` — the
self-similarity that the keystone induction establishes).  Concretely this is the
function the row-commutation / normalization consumers compare against.

The classification uses ordinary `Nat` arithmetic (decidable), so it is a total
computable function, validated below by `#eval` against `Surface.code.evalAt?`. -/

/-- Grid row of qubit `q` at distance `d`. -/
@[reducible] def cellRow (d q : Nat) : Nat := q / d
/-- Grid col of qubit `q` at distance `d`. -/
@[reducible] def cellCol (d q : Nat) : Nat := q % d
/-- Bulk plaquette grid row of stabilizer `k`. -/
@[reducible] def cellR (d k : Nat) : Nat := k / (d - 1)
/-- Bulk plaquette grid col of stabilizer `k`. -/
@[reducible] def cellC (d k : Nat) : Nat := k % (d - 1)

/-- Whether `(k, q)` is an in-band bulk plaquette cell at distance `d`. -/
def inBulkBand (d k q : Nat) : Bool :=
  let row := cellRow d q; let col := cellCol d q
  let r := cellR d k; let c := cellC d k
  (row = r || row = r + 1) && (col = c || col = c + 1) && (k < (d-1)*(d-1))

/-- The bulk plaquette kind: `Z` when `(r + c)` even, else `X`. -/
def bulkKind (d k : Nat) : Pauli :=
  if (cellR d k + cellC d k) % 2 = 0 then Pauli.Z else Pauli.X

/-- The distance-uniform expected Pauli of stabilizer `k` at qubit `q`.

This is the *base-entry geometry*, valid at every distance for boundary cells and
for in-band bulk cells; for an interior bulk cell at `d ≥ 5` the recursive entry
delegates to the inner code, and the keystone induction proves that delegated
entry equals this same classifier one layer down. -/
def surfaceCellPauli (d k q : Nat) : Pauli :=
  let row := cellRow d q; let col := cellCol d q
  let dm1 := d - 1
  let bulkCount := dm1 * dm1
  let b := k - bulkCount
  let half := dm1 / 2
  if k < bulkCount then
    -- bulk plaquette
    if inBulkBand d k q then bulkKind d k else Pauli.I
  else if b < half then
    -- top-X boundary
    if k < d*d - 1 && row = 0 && (col = 2*b || col = 2*b + 1) then Pauli.X else Pauli.I
  else if b < 2*half then
    -- right-Z boundary
    let bbR := b - half
    if col = dm1 && (row = 2*bbR || row = 2*bbR + 1) then Pauli.Z else Pauli.I
  else if b < 3*half then
    -- left-Z boundary
    let bbL := b - 2*half
    if col = 0 && (row = 2*bbL + 1 || row = 2*bbL + 2) then Pauli.Z else Pauli.I
  else
    -- bottom-X boundary
    let bbB := b - 3*half
    if row = dm1 && (col = 2*bbB + 1 || col = 2*bbB + 2) then Pauli.X else Pauli.I

/-! ### Cross-validation of the classifier against the trusted evaluator

For a literal `(d, k, q)` the trusted `Surface.code.evalAt?` computes the actual
generated entry.  These `#eval`s confirm `surfaceCellPauli` matches it on a
spread of base (`d = 3`) and recursive (`d = 5`) cells, including the interior
self-similar cell (`d = 5`, center) where the recursion delegates. -/

/-- Exhaustive agreement of the classifier with the trusted evaluator over all
`(k, q) < (numStab d, nQubits d)` at a fixed distance, as a single Bool. -/
def classifierAgrees (d : Nat) : Bool :=
  (List.range (numStab d)).all fun k =>
    (List.range (nQubits d)).all fun q =>
      Surface.code.evalAt? d k q = some (surfaceCellPauli d k q)

-- Exhaustive cross-validation: the classifier is byte-for-byte the evaluator at
-- d = 3 (base) and d = 5 (recursive, exercising interior + promoted-boundary).
#eval classifierAgrees 3     -- expect true
#eval classifierAgrees 5     -- expect true
#eval classifierAgrees 7     -- expect true

-- spot checks of individual cells (each kind):
#eval decide (surfaceCellPauli 3 3 4 = Pauli.Z)      -- center bulk Z
#eval decide (surfaceCellPauli 3 4 0 = Pauli.X)      -- top-X
#eval decide (surfaceCellPauli 5 10 12 = Pauli.Z)    -- d=5 interior center

/-! ## Recursive-entry classifier guard terms (top/right/left/bottom cells)

These mirror the `topCell` / `rightCell` / `leftCell` / `bottomCell` selectors of
`CodeSurface.recursiveEntry`, parameterised over symbolic pure terms `dT`/`kT`.
They are the *closed* classifier guards (no `q` dependence) the promoted-boundary
peel selects through.  Built on the `dm1T`/`rT`/`cT` helpers of
`SurfaceRowCharacterizationFull`. -/

/-- Inner code distance `d - 2`. -/
def recInnerDT (dT : Term 0 .nat) : Term 0 .nat := .sub dT (.natLit 2)
/-- Inner bulk side `(d-2) - 1`. -/
def recInnerDm1T (dT : Term 0 .nat) : Term 0 .nat := .sub (recInnerDT dT) (.natLit 1)
/-- Inner bulk count `((d-2)-1)^2`. -/
def recInnerBulkT (dT : Term 0 .nat) : Term 0 .nat :=
  .mul (recInnerDm1T dT) (recInnerDm1T dT)
/-- Inner half-width `((d-2)-1)/2`. -/
def recInnerHalfT (dT : Term 0 .nat) : Term 0 .nat := .div (recInnerDm1T dT) (.natLit 2)

/-- `topB = (c - 1) / 2`. -/
def topBT (dT kT : Term 0 .nat) : Term 0 .nat := .div (.sub (cT dT kT) (.natLit 1)) (.natLit 2)
/-- `topCell = (r = 0) ∧ (c = 2·topB + 1) ∧ (topB < innerHalf)`. -/
def topCellGuard (dT kT : Term 0 .nat) : Term 0 .bool :=
  band3 (.eqNat (rT dT kT) (.natLit 0))
    (.eqNat (cT dT kT) (.add (.mul (.natLit 2) (topBT dT kT)) (.natLit 1)))
    (.ltNat (topBT dT kT) (recInnerHalfT dT))

/-- `rightB = (r - 1) / 2`. -/
def rightBT (dT kT : Term 0 .nat) : Term 0 .nat := .div (.sub (rT dT kT) (.natLit 1)) (.natLit 2)
/-- `rightCell = (c = lastCell) ∧ (r = 2·rightB + 1) ∧ (rightB < innerHalf)`. -/
def rightCellGuard (dT kT : Term 0 .nat) : Term 0 .bool :=
  band3 (.eqNat (cT dT kT) (lastCellT dT))
    (.eqNat (rT dT kT) (.add (.mul (.natLit 2) (rightBT dT kT)) (.natLit 1)))
    (.ltNat (rightBT dT kT) (recInnerHalfT dT))

/-- `leftB = (r - 2) / 2`. -/
def leftBT (dT kT : Term 0 .nat) : Term 0 .nat := .div (.sub (rT dT kT) (.natLit 2)) (.natLit 2)
/-- `leftCell = (c = 0) ∧ (r = 2·leftB + 2) ∧ (leftB < innerHalf)`. -/
def leftCellGuard (dT kT : Term 0 .nat) : Term 0 .bool :=
  band3 (.eqNat (cT dT kT) (.natLit 0))
    (.eqNat (rT dT kT) (.add (.mul (.natLit 2) (leftBT dT kT)) (.natLit 2)))
    (.ltNat (leftBT dT kT) (recInnerHalfT dT))

/-- `bottomB = (c - 2) / 2`. -/
def bottomBT (dT kT : Term 0 .nat) : Term 0 .nat := .div (.sub (cT dT kT) (.natLit 2)) (.natLit 2)
/-- `bottomCell = (r = lastCell) ∧ (c = 2·bottomB + 2) ∧ (bottomB < innerHalf)`. -/
def bottomCellGuard (dT kT : Term 0 .nat) : Term 0 .bool :=
  band3 (.eqNat (rT dT kT) (lastCellT dT))
    (.eqNat (cT dT kT) (.add (.mul (.natLit 2) (bottomBT dT kT)) (.natLit 2)))
    (.ltNat (bottomBT dT kT) (recInnerHalfT dT))

/-! ### Promoted inner stabilizer indices (`oldK`)

These are the `topK` / `rightK` / `leftK` / `bottomK` inner stabilizer indices the
promoted boundary routes to in the `d-2` code. -/

def topKT (dT kT : Term 0 .nat) : Term 0 .nat := .add (recInnerBulkT dT) (topBT dT kT)
def rightKT (dT kT : Term 0 .nat) : Term 0 .nat :=
  .add (recInnerBulkT dT) (.add (recInnerHalfT dT) (rightBT dT kT))
def leftKT (dT kT : Term 0 .nat) : Term 0 .nat :=
  .add (recInnerBulkT dT) (.add (.mul (.natLit 2) (recInnerHalfT dT)) (leftBT dT kT))
def bottomKT (dT kT : Term 0 .nat) : Term 0 .nat :=
  .add (recInnerBulkT dT) (.add (.mul (.natLit 3) (recInnerHalfT dT)) (bottomBT dT kT))

/-! ### The promoted-boundary `inside` guard and inner-`q`

`promotedBoundaryEntry` uses the SAME `inside`/`innerQ` as the interior cell:
`inside = band4 (1 ≤ row) (row < dm1) (1 ≤ col) (col < dm1)` and
`innerQ = (row-1)·innerD + (col-1)`.  These are exactly `insideGuardT` and
`innerQT` from `SurfaceRowCharacterizationFull`. -/

/-- The inner-code reference produced by a promoted-boundary cell with inner
stabilizer index `oldKT`: `stabAt (recCall (d-2) oldK) innerQ`. -/
def promotedInnerRef (dT qT oldKT : Term 0 .nat) : Term 0 .pauli :=
  .stabAt (.recCall (recInnerDT dT) oldKT) (innerQT dT qT)

/-! ## Shared guard-rewrite lemmas for the promoted-boundary peels

The four classifier guards and the `inside` guard, in their post-`simp` forms, are
shared between the inner-reference and the outer-leaf peels.  Factoring them keeps
each peel small. -/

private theorem interiorCellGuardT_simp (dT kT : Term 0 .nat) :
    interiorCellGuardT dT kT
      = ((Term.natLit 1).leNat (kT.div (dT.sub (Term.natLit 1)))).and
          (((kT.div (dT.sub (Term.natLit 1))).ltNat ((dT.sub (Term.natLit 1)).sub (Term.natLit 1))).and
            (((Term.natLit 1).leNat (kT.mod (dT.sub (Term.natLit 1)))).and
              ((kT.mod (dT.sub (Term.natLit 1))).ltNat ((dT.sub (Term.natLit 1)).sub (Term.natLit 1))))) := by
  simp only [interiorCellGuardT, band4, band3, le, rT, cT, lastCellT, dm1T]

private theorem insideGuardT_simp (dT qT : Term 0 .nat) :
    insideGuardT dT qT
      = ((Term.natLit 1).leNat (qT.div dT)).and
          (((qT.div dT).ltNat (dT.sub (Term.natLit 1))).and
            (((Term.natLit 1).leNat (qT.mod dT)).and
              ((qT.mod dT).ltNat (dT.sub (Term.natLit 1))))) := by
  simp only [insideGuardT, band4, band3, le, rowT, colT, dm1T]

private theorem topCellGuard_simp (dT kT : Term 0 .nat) :
    topCellGuard dT kT
      = (((kT.div (dT.sub (Term.natLit 1))).eqNat (Term.natLit 0)).and
          ((((kT.mod (dT.sub (Term.natLit 1))).eqNat
                (((Term.natLit 2).mul
                      (((kT.mod (dT.sub (Term.natLit 1))).sub (Term.natLit 1)).div (Term.natLit 2))).add
                  (Term.natLit 1)))).and
            ((((kT.mod (dT.sub (Term.natLit 1))).sub (Term.natLit 1)).div (Term.natLit 2)).ltNat
              (((dT.sub (Term.natLit 2)).sub (Term.natLit 1)).div (Term.natLit 2))))) := by
  simp only [topCellGuard, band3, topBT, rT, cT, recInnerHalfT, recInnerDm1T, recInnerDT, dm1T]

private theorem rightCellGuard_simp (dT kT : Term 0 .nat) :
    rightCellGuard dT kT
      = (((kT.mod (dT.sub (Term.natLit 1))).eqNat ((dT.sub (Term.natLit 1)).sub (Term.natLit 1))).and
          ((((kT.div (dT.sub (Term.natLit 1))).eqNat
                (((Term.natLit 2).mul
                      (((kT.div (dT.sub (Term.natLit 1))).sub (Term.natLit 1)).div (Term.natLit 2))).add
                  (Term.natLit 1)))).and
            ((((kT.div (dT.sub (Term.natLit 1))).sub (Term.natLit 1)).div (Term.natLit 2)).ltNat
              (((dT.sub (Term.natLit 2)).sub (Term.natLit 1)).div (Term.natLit 2))))) := by
  simp only [rightCellGuard, band3, rightBT, rT, cT, lastCellT, recInnerHalfT, recInnerDm1T,
    recInnerDT, dm1T]

private theorem leftCellGuard_simp (dT kT : Term 0 .nat) :
    leftCellGuard dT kT
      = (((kT.mod (dT.sub (Term.natLit 1))).eqNat (Term.natLit 0)).and
          ((((kT.div (dT.sub (Term.natLit 1))).eqNat
                (((Term.natLit 2).mul
                      (((kT.div (dT.sub (Term.natLit 1))).sub (Term.natLit 2)).div (Term.natLit 2))).add
                  (Term.natLit 2)))).and
            ((((kT.div (dT.sub (Term.natLit 1))).sub (Term.natLit 2)).div (Term.natLit 2)).ltNat
              (((dT.sub (Term.natLit 2)).sub (Term.natLit 1)).div (Term.natLit 2))))) := by
  simp only [leftCellGuard, band3, leftBT, rT, cT, recInnerHalfT, recInnerDm1T, recInnerDT, dm1T]

private theorem bottomCellGuard_simp (dT kT : Term 0 .nat) :
    bottomCellGuard dT kT
      = (((kT.div (dT.sub (Term.natLit 1))).eqNat ((dT.sub (Term.natLit 1)).sub (Term.natLit 1))).and
          ((((kT.mod (dT.sub (Term.natLit 1))).eqNat
                (((Term.natLit 2).mul
                      (((kT.mod (dT.sub (Term.natLit 1))).sub (Term.natLit 2)).div (Term.natLit 2))).add
                  (Term.natLit 2)))).and
            ((((kT.mod (dT.sub (Term.natLit 1))).sub (Term.natLit 2)).div (Term.natLit 2)).ltNat
              (((dT.sub (Term.natLit 2)).sub (Term.natLit 1)).div (Term.natLit 2))))) := by
  simp only [bottomCellGuard, band3, bottomBT, rT, cT, lastCellT, recInnerHalfT, recInnerDm1T,
    recInnerDT, dm1T]

/-! ## Promoted-boundary peels, inner-reference case (`inside` holds)

Each peel selects: outer `bulk` (TRUE), `interiorCell` (FALSE), then the
appropriate sequence of `*Cell` selections to reach the cell's
`promotedBoundaryEntry`, then `inside` (TRUE), landing on the inner-code reference
`stabAt (recCall (d-2) {top,right,left,bottom}K) innerQ`.

These are the cells where the keystone induction's IH (the `d-2` row
characterization at the projected inner stabilizer index) plugs in. -/

/-- Shared step 1+2: strip `stabLam`, select `bulk` (TRUE), push the qubit
instantiation through the residual `ite` tree. -/
private def promotedBulkSelect {fuel : Nat} (dT kT qT : Term 0 .nat)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardT dT kT)) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool
        (SC.closed (Term.instantiateTopNat qT
          (.ltNat (Term.lift 0 kT)
            (.mul (.sub (Term.lift 0 dT) (.natLit 1)) (.sub (Term.lift 0 dT) (.natLit 1))))))
        (SC.b true)) := by
  have heq : Term.instantiateTopNat qT
      (Term.ltNat (Term.lift 0 kT)
        (.mul (.sub (Term.lift 0 dT) (.natLit 1)) (.sub (Term.lift 0 dT) (.natLit 1))))
      = bulkGuardT dT kT := by
    simp only [bulkGuardT, bulkCountT, dm1T, Term.instantiateTopNat, Term.instantiateNatAt,
      instTop_lift]
  rw [heq]; exact hBulk

/-- **Top-cell promoted-boundary inner peel.** -/
def recTopPromotedInnerPeel {fuel : Nat} (dT kT qT : Term 0 .nat)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardT dT kT)) (SC.b true)))
    (hInterior : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (interiorCellGuardT dT kT)) (SC.b false)))
    (hTop : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topCellGuard dT kT)) (SC.b true)))
    (hInside : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (insideGuardT dT qT)) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt
          (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed qT))
        (SC.closed (promotedInnerRef dT qT (topKT dT kT)))) := by
  simp only [SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
    SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q,
    codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4, orEqSucc, le]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (pureStabAtClosedIteLamThen (fuel := fuel) _ _ _ qT hq
      (promotedBulkSelect dT kT qT hq hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← interiorCellGuardT_simp]; exact hInterior))
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← topCellGuard_simp]; exact hTop))
      (PureFamilyDerivA.eqPauliTrans _ _ _
        (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← insideGuardT_simp]; exact hInside))
        (PureFamilyDerivA.eqPauliRefl _)))

/-- **Right-cell promoted-boundary inner peel.** -/
def recRightPromotedInnerPeel {fuel : Nat} (dT kT qT : Term 0 .nat)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardT dT kT)) (SC.b true)))
    (hInterior : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (interiorCellGuardT dT kT)) (SC.b false)))
    (hTop : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topCellGuard dT kT)) (SC.b false)))
    (hRight : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (rightCellGuard dT kT)) (SC.b true)))
    (hInside : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (insideGuardT dT qT)) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt
          (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed qT))
        (SC.closed (promotedInnerRef dT qT (rightKT dT kT)))) := by
  simp only [SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
    SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q,
    codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4, orEqSucc, le]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (pureStabAtClosedIteLamThen (fuel := fuel) _ _ _ qT hq
      (promotedBulkSelect dT kT qT hq hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← interiorCellGuardT_simp]; exact hInterior))
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← topCellGuard_simp]; exact hTop))
      (PureFamilyDerivA.eqPauliTrans _ _ _
        (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← rightCellGuard_simp]; exact hRight))
        (PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← insideGuardT_simp]; exact hInside))
          (PureFamilyDerivA.eqPauliRefl _))))

/-- **Left-cell promoted-boundary inner peel.** -/
def recLeftPromotedInnerPeel {fuel : Nat} (dT kT qT : Term 0 .nat)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardT dT kT)) (SC.b true)))
    (hInterior : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (interiorCellGuardT dT kT)) (SC.b false)))
    (hTop : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topCellGuard dT kT)) (SC.b false)))
    (hRight : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (rightCellGuard dT kT)) (SC.b false)))
    (hLeft : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (leftCellGuard dT kT)) (SC.b true)))
    (hInside : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (insideGuardT dT qT)) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt
          (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed qT))
        (SC.closed (promotedInnerRef dT qT (leftKT dT kT)))) := by
  simp only [SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
    SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q,
    codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4, orEqSucc, le]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (pureStabAtClosedIteLamThen (fuel := fuel) _ _ _ qT hq
      (promotedBulkSelect dT kT qT hq hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← interiorCellGuardT_simp]; exact hInterior))
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← topCellGuard_simp]; exact hTop))
      (PureFamilyDerivA.eqPauliTrans _ _ _
        (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← rightCellGuard_simp]; exact hRight))
        (PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← leftCellGuard_simp]; exact hLeft))
          (PureFamilyDerivA.eqPauliTrans _ _ _
            (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← insideGuardT_simp]; exact hInside))
            (PureFamilyDerivA.eqPauliRefl _)))))

/-- **Bottom-cell promoted-boundary inner peel.** -/
def recBottomPromotedInnerPeel {fuel : Nat} (dT kT qT : Term 0 .nat)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardT dT kT)) (SC.b true)))
    (hInterior : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (interiorCellGuardT dT kT)) (SC.b false)))
    (hTop : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topCellGuard dT kT)) (SC.b false)))
    (hRight : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (rightCellGuard dT kT)) (SC.b false)))
    (hLeft : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (leftCellGuard dT kT)) (SC.b false)))
    (hBottom : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bottomCellGuard dT kT)) (SC.b true)))
    (hInside : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (insideGuardT dT qT)) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt
          (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed qT))
        (SC.closed (promotedInnerRef dT qT (bottomKT dT kT)))) := by
  simp only [SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
    SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q,
    codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4, orEqSucc, le]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (pureStabAtClosedIteLamThen (fuel := fuel) _ _ _ qT hq
      (promotedBulkSelect dT kT qT hq hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← interiorCellGuardT_simp]; exact hInterior))
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← topCellGuard_simp]; exact hTop))
      (PureFamilyDerivA.eqPauliTrans _ _ _
        (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← rightCellGuard_simp]; exact hRight))
        (PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← leftCellGuard_simp]; exact hLeft))
          (PureFamilyDerivA.eqPauliTrans _ _ _
            (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← bottomCellGuard_simp]; exact hBottom))
            (PureFamilyDerivA.eqPauliTrans _ _ _
              (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← insideGuardT_simp]; exact hInside))
              (PureFamilyDerivA.eqPauliRefl _))))))

/-! ## The promoted-boundary leaf terms (outer-`ite` of the not-inside branch)

When the `inside` guard fails, `promotedBoundaryEntry oldK outer kind` reduces to
`ite outer (kind) I`.  The `outer` guard is the cell's `*Outer` predicate; the
closed-leaf result is `kind` (in band) or `I` (out of band). -/

/-- Top-cell `outer` guard: `row = 0 ∧ (col = 2·topB+1 ∨ col = 2·topB+2)`. -/
def topOuterGuard (dT kT qT : Term 0 .nat) : Term 0 .bool :=
  .and (.eqNat (rowT dT qT) (.natLit 0))
    (orEqSucc (colT dT qT) (.add (.mul (.natLit 2) (topBT dT kT)) (.natLit 1)))
/-- Right-cell `outer` guard: `col = dm1 ∧ (row = 2·rightB+1 ∨ row = 2·rightB+2)`. -/
def rightOuterGuard (dT kT qT : Term 0 .nat) : Term 0 .bool :=
  .and (.eqNat (colT dT qT) (dm1T dT))
    (orEqSucc (rowT dT qT) (.add (.mul (.natLit 2) (rightBT dT kT)) (.natLit 1)))
/-- Left-cell `outer` guard: `col = 0 ∧ (row = 2·leftB+2 ∨ row = 2·leftB+3)`. -/
def leftOuterGuard (dT kT qT : Term 0 .nat) : Term 0 .bool :=
  .and (.eqNat (colT dT qT) (.natLit 0))
    (orEqSucc (rowT dT qT) (.add (.mul (.natLit 2) (leftBT dT kT)) (.natLit 2)))
/-- Bottom-cell `outer` guard: `row = dm1 ∧ (col = 2·bottomB+2 ∨ col = 2·bottomB+3)`. -/
def bottomOuterGuard (dT kT qT : Term 0 .nat) : Term 0 .bool :=
  .and (.eqNat (rowT dT qT) (dm1T dT))
    (orEqSucc (colT dT qT) (.add (.mul (.natLit 2) (bottomBT dT kT)) (.natLit 2)))

/-! ## Row-level promoted-boundary steps with the inductive hypothesis applied

The shape an `OddSurfaceDistance.index` induction consumes for a promoted-boundary
interior cell: compose the recursive-branch row selection
(`surfaceCodeRecursiveEntryEq`, distance guard `dT < 5` FALSE) with the
promoted-boundary inner peel and a *supplied* resolution `ih` of the inner-code
reference `promotedInnerRef dT qT oldK` to a leaf Pauli `p` (the IH one layer
down).  Four kinds (top/right/left/bottom). -/

def recTopPromotedRow_withIH {fuel : Nat} (n : STerm 0 .nat)
    (dT kT qT : Term 0 .nat) (p : Term 0 .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hDist : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat dT (n5 : Term 0 .nat))) (SC.b false)))
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardT dT kT)) (SC.b true)))
    (hInterior : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (interiorCellGuardT dT kT)) (SC.b false)))
    (hTop : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topCellGuard dT kT)) (SC.b true)))
    (hInside : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (insideGuardT dT qT)) (SC.b true)))
    (ih : PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (SC.closed (promotedInnerRef dT qT (topKT dT kT))) (SC.closed p))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (.stabAt (SC.closed (.recCall dT kT)) (SC.closed qT)) (SC.closed p)) :=
  surfaceCodeRecursiveEntryEq n dT kT qT p hd hk hDist
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (recTopPromotedInnerPeel dT kT qT hq hBulk hInterior hTop hInside) ih)

def recRightPromotedRow_withIH {fuel : Nat} (n : STerm 0 .nat)
    (dT kT qT : Term 0 .nat) (p : Term 0 .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hDist : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat dT (n5 : Term 0 .nat))) (SC.b false)))
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardT dT kT)) (SC.b true)))
    (hInterior : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (interiorCellGuardT dT kT)) (SC.b false)))
    (hTop : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topCellGuard dT kT)) (SC.b false)))
    (hRight : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (rightCellGuard dT kT)) (SC.b true)))
    (hInside : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (insideGuardT dT qT)) (SC.b true)))
    (ih : PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (SC.closed (promotedInnerRef dT qT (rightKT dT kT))) (SC.closed p))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (.stabAt (SC.closed (.recCall dT kT)) (SC.closed qT)) (SC.closed p)) :=
  surfaceCodeRecursiveEntryEq n dT kT qT p hd hk hDist
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (recRightPromotedInnerPeel dT kT qT hq hBulk hInterior hTop hRight hInside) ih)

def recLeftPromotedRow_withIH {fuel : Nat} (n : STerm 0 .nat)
    (dT kT qT : Term 0 .nat) (p : Term 0 .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hDist : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat dT (n5 : Term 0 .nat))) (SC.b false)))
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardT dT kT)) (SC.b true)))
    (hInterior : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (interiorCellGuardT dT kT)) (SC.b false)))
    (hTop : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topCellGuard dT kT)) (SC.b false)))
    (hRight : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (rightCellGuard dT kT)) (SC.b false)))
    (hLeft : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (leftCellGuard dT kT)) (SC.b true)))
    (hInside : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (insideGuardT dT qT)) (SC.b true)))
    (ih : PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (SC.closed (promotedInnerRef dT qT (leftKT dT kT))) (SC.closed p))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (.stabAt (SC.closed (.recCall dT kT)) (SC.closed qT)) (SC.closed p)) :=
  surfaceCodeRecursiveEntryEq n dT kT qT p hd hk hDist
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (recLeftPromotedInnerPeel dT kT qT hq hBulk hInterior hTop hRight hLeft hInside) ih)

def recBottomPromotedRow_withIH {fuel : Nat} (n : STerm 0 .nat)
    (dT kT qT : Term 0 .nat) (p : Term 0 .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hDist : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat dT (n5 : Term 0 .nat))) (SC.b false)))
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardT dT kT)) (SC.b true)))
    (hInterior : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (interiorCellGuardT dT kT)) (SC.b false)))
    (hTop : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topCellGuard dT kT)) (SC.b false)))
    (hRight : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (rightCellGuard dT kT)) (SC.b false)))
    (hLeft : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (leftCellGuard dT kT)) (SC.b false)))
    (hBottom : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bottomCellGuard dT kT)) (SC.b true)))
    (hInside : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (insideGuardT dT qT)) (SC.b true)))
    (ih : PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (SC.closed (promotedInnerRef dT qT (bottomKT dT kT))) (SC.closed p))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (.stabAt (SC.closed (.recCall dT kT)) (SC.closed qT)) (SC.closed p)) :=
  surfaceCodeRecursiveEntryEq n dT kT qT p hd hk hDist
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (recBottomPromotedInnerPeel dT kT qT hq hBulk hInterior hTop hRight hLeft hBottom hInside) ih)

/-! ## Recursion-faithful leaf function `recLeaf`

`surfaceCellPauli` is the *base-entry* geometry.  At `d ≥ 5` a bulk-interior or
promoted cell delegates to the inner code, so the actual generated entry is the
*inner* leaf one layer down.  `recLeaf m k q` mirrors the real recursion exactly:
it returns `surfaceCellPauli (oddDistance m) k q` for boundary / base-fallback
cells, and recurses (`recLeaf (m-1) innerK innerQ`) for interior / promoted-inside
cells.  By construction `recLeaf` is *self-similar*, so the keystone induction can
discharge the recursing cells with NO extra hypothesis: the inner leaf the IH
returns is, definitionally, `recLeaf` one layer down.

The relationship `recLeaf m k q = Surface.code.evalAt? (oddDistance m) k q` (and
hence `= surfaceCellPauli` whenever the latter is computed self-similarly) is the
content the keystone establishes derivation-side; here `recLeaf` is the
classifier the keystone's conclusion compares against. -/

/-- Cell-kind dispatch indices computed from `(d, k)` as plain `Nat`. -/
@[reducible] def cellLastCell (d : Nat) : Nat := (d - 1) - 1
@[reducible] def cellInnerHalf (d : Nat) : Nat := ((d - 2) - 1) / 2

/-- `(k,q)` is an interior bulk cell.  Right-nested `&&` to match `band4`. -/
def isInteriorCell (d k : Nat) : Bool :=
  let r := cellR d k; let c := cellC d k
  decide (1 ≤ r) && (decide (r < cellLastCell d) &&
    (decide (1 ≤ c) && decide (c < cellLastCell d)))
/-- `(k,q)` is inside the interior block (qubit).  Right-nested `&&`. -/
def isInside (d q : Nat) : Bool :=
  let row := cellRow d q; let col := cellCol d q
  decide (1 ≤ row) && (decide (row < d - 1) &&
    (decide (1 ≤ col) && decide (col < d - 1)))
-- The four boundary-promotion cell selectors, right-nested `decide && (..)` to match
-- `band3` so the term-level guard evaluates to them definitionally.
def isTopCell (d k : Nat) : Bool :=
  let r := cellR d k; let c := cellC d k; let tb := (c - 1) / 2
  decide (r = 0) && (decide (c = 2*tb + 1) && decide (tb < cellInnerHalf d))
def isRightCell (d k : Nat) : Bool :=
  let r := cellR d k; let c := cellC d k; let rb := (r - 1) / 2
  decide (c = cellLastCell d) && (decide (r = 2*rb + 1) && decide (rb < cellInnerHalf d))
def isLeftCell (d k : Nat) : Bool :=
  let r := cellR d k; let c := cellC d k; let lb := (r - 2) / 2
  decide (c = 0) && (decide (r = 2*lb + 2) && decide (lb < cellInnerHalf d))
def isBottomCell (d k : Nat) : Bool :=
  let r := cellR d k; let c := cellC d k; let bb := (c - 2) / 2
  decide (r = cellLastCell d) && (decide (c = 2*bb + 2) && decide (bb < cellInnerHalf d))

/-- Inner stabilizer indices (`Nat` values). -/
def innerInteriorK (d k : Nat) : Nat :=
  (cellR d k - 1) * ((d - 2) - 1) + (cellC d k - 1)
def innerTopK (d k : Nat) : Nat := ((d-2)-1)*((d-2)-1) + (cellC d k - 1)/2
def innerRightK (d k : Nat) : Nat :=
  ((d-2)-1)*((d-2)-1) + (cellInnerHalf d + (cellR d k - 1)/2)
def innerLeftK (d k : Nat) : Nat :=
  ((d-2)-1)*((d-2)-1) + (2*cellInnerHalf d + (cellR d k - 2)/2)
def innerBottomK (d k : Nat) : Nat :=
  ((d-2)-1)*((d-2)-1) + (3*cellInnerHalf d + (cellC d k - 2)/2)
/-- Inner qubit (`Nat` value). -/
def innerQval (d q : Nat) : Nat := (cellRow d q - 1) * (d - 2) + (cellCol d q - 1)

/-- The recursion-faithful leaf of stabilizer `k` at qubit `q`, distance index `m`. -/
def recLeaf : (m : Nat) → (k q : Nat) → Pauli
  | 0, k, q => surfaceCellPauli (oddDistance 0) k q
  | m + 1, k, q =>
      let d := oddDistance (m + 1)
      if k < (d-1)*(d-1) then
        if isInteriorCell d k then
          if isInside d q then recLeaf m (innerInteriorK d k) (innerQval d q) else Pauli.I
        else if isTopCell d k then
          if isInside d q then recLeaf m (innerTopK d k) (innerQval d q)
          else surfaceCellPauli d k q
        else if isRightCell d k then
          if isInside d q then recLeaf m (innerRightK d k) (innerQval d q)
          else surfaceCellPauli d k q
        else if isLeftCell d k then
          if isInside d q then recLeaf m (innerLeftK d k) (innerQval d q)
          else surfaceCellPauli d k q
        else if isBottomCell d k then
          if isInside d q then recLeaf m (innerBottomK d k) (innerQval d q)
          else surfaceCellPauli d k q
        else surfaceCellPauli d k q
      else surfaceCellPauli d k q

/-! ### Cross-validation: `recLeaf` matches the trusted evaluator

For a literal `(m, k, q)`, `recLeaf m k q` should equal `Surface.code.evalAt?`
at `(oddDistance m, k, q)`.  Note: at interior/promoted-inside cells the
`surfaceCellPauli` of `surfaceCellPauli d k q` is NOT used — `recLeaf` recurses —
so these `#eval`s genuinely test the self-similar dispatch. -/

/-- `recLeaf` agrees with the evaluator over all `(k,q)` at distance index `m`. -/
def recLeafAgrees (m : Nat) : Bool :=
  let d := oddDistance m
  (List.range (numStab d)).all fun k =>
    (List.range (nQubits d)).all fun q =>
      Surface.code.evalAt? d k q = some (recLeaf m k q)

#eval recLeafAgrees 0    -- d = 3, expect true
#eval recLeafAgrees 1    -- d = 5, expect true (exercises interior + promoted recursion)
#eval recLeafAgrees 2    -- d = 7, expect true (two recursion layers)

/-! ## General inner-index/qubit evaluation certificates

`SurfaceRowCharacterizationFull` proves `interiorKT_evalsTo` / `innerQT_evalsTo`
only for the *center* values (`centerK`/`centerQ`).  The keystone needs them at an
*arbitrary* `(kv, qv)`: the inner interior index `interiorKT dT kT` evaluates to
`innerInteriorK d kv` and the inner qubit `innerQT dT qT` to `innerQval d qv`. -/

/-- Purity of the inner interior index term. -/
def interiorKT_pure {dT kT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureNatTerm (interiorKT dT kT) :=
  SFormula.PureNatTerm.add
    (SFormula.PureNatTerm.mul
      (SFormula.PureNatTerm.sub
        (SFormula.PureNatTerm.div hk (SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 1)))
        (SFormula.PureNatTerm.nat 1))
      (SFormula.PureNatTerm.sub
        (SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 2)) (SFormula.PureNatTerm.nat 1)))
    (SFormula.PureNatTerm.sub
      (SFormula.PureNatTerm.mod hk (SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 1)))
      (SFormula.PureNatTerm.nat 1))

/-- Purity of the inner qubit term. -/
def innerQT_pure {dT qT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hq : SFormula.PureNatTerm qT) :
    SFormula.PureNatTerm (innerQT dT qT) :=
  SFormula.PureNatTerm.add
    (SFormula.PureNatTerm.mul
      (SFormula.PureNatTerm.sub (SFormula.PureNatTerm.div hq hd) (SFormula.PureNatTerm.nat 1))
      (SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 2)))
    (SFormula.PureNatTerm.sub (SFormula.PureNatTerm.mod hq hd) (SFormula.PureNatTerm.nat 1))

theorem interiorKT_evalsTo_gen {dT kT : Term 0 .nat} {fuel d kv : Nat} (rho : Env 0)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv) :
    Term.eval Surface.code.body fuel (interiorKT dT kT) rho = some (innerInteriorK d kv) := by
  simp only [interiorKT, innerDm1T, innerDT, rT, cT, dm1T, Term.eval, hdv, hkv,
    Option.bind, Option.pure_def, Option.bind_eq_bind]
  rfl

theorem innerQT_evalsTo_gen {dT qT : Term 0 .nat} {fuel d qv : Nat} (rho : Env 0)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hqv : Term.eval Surface.code.body fuel qT rho = some qv) :
    Term.eval Surface.code.body fuel (innerQT dT qT) rho = some (innerQval d qv) := by
  simp only [innerQT, innerDT, rowT, colT, Term.eval, hdv, hqv,
    Option.bind, Option.pure_def, Option.bind_eq_bind]
  rfl

/-- Purity of the promoted inner stabilizer-index terms. -/
def recInnerBulkT_pure {dT : Term 0 .nat} (hd : SFormula.PureNatTerm dT) :
    SFormula.PureNatTerm (recInnerBulkT dT) :=
  SFormula.PureNatTerm.mul
    (SFormula.PureNatTerm.sub (SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 2))
      (SFormula.PureNatTerm.nat 1))
    (SFormula.PureNatTerm.sub (SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 2))
      (SFormula.PureNatTerm.nat 1))
def recInnerHalfT_pure {dT : Term 0 .nat} (hd : SFormula.PureNatTerm dT) :
    SFormula.PureNatTerm (recInnerHalfT dT) :=
  SFormula.PureNatTerm.div
    (SFormula.PureNatTerm.sub (SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 2))
      (SFormula.PureNatTerm.nat 1)) (SFormula.PureNatTerm.nat 2)
def topKT_pure {dT kT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureNatTerm (topKT dT kT) :=
  SFormula.PureNatTerm.add (recInnerBulkT_pure hd)
    (SFormula.PureNatTerm.div
      (SFormula.PureNatTerm.sub
        (SFormula.PureNatTerm.mod hk (SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 1)))
        (SFormula.PureNatTerm.nat 1)) (SFormula.PureNatTerm.nat 2))
def rightKT_pure {dT kT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureNatTerm (rightKT dT kT) :=
  SFormula.PureNatTerm.add (recInnerBulkT_pure hd)
    (SFormula.PureNatTerm.add (recInnerHalfT_pure hd)
      (SFormula.PureNatTerm.div
        (SFormula.PureNatTerm.sub
          (SFormula.PureNatTerm.div hk (SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 1)))
          (SFormula.PureNatTerm.nat 1)) (SFormula.PureNatTerm.nat 2)))
def leftKT_pure {dT kT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureNatTerm (leftKT dT kT) :=
  SFormula.PureNatTerm.add (recInnerBulkT_pure hd)
    (SFormula.PureNatTerm.add
      (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 2) (recInnerHalfT_pure hd))
      (SFormula.PureNatTerm.div
        (SFormula.PureNatTerm.sub
          (SFormula.PureNatTerm.div hk (SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 1)))
          (SFormula.PureNatTerm.nat 2)) (SFormula.PureNatTerm.nat 2)))
def bottomKT_pure {dT kT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureNatTerm (bottomKT dT kT) :=
  SFormula.PureNatTerm.add (recInnerBulkT_pure hd)
    (SFormula.PureNatTerm.add
      (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 3) (recInnerHalfT_pure hd))
      (SFormula.PureNatTerm.div
        (SFormula.PureNatTerm.sub
          (SFormula.PureNatTerm.mod hk (SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 1)))
          (SFormula.PureNatTerm.nat 2)) (SFormula.PureNatTerm.nat 2)))

theorem topKT_evalsTo_gen {dT kT : Term 0 .nat} {fuel d kv : Nat} (rho : Env 0)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv) :
    Term.eval Surface.code.body fuel (topKT dT kT) rho = some (innerTopK d kv) := by
  simp only [topKT, recInnerBulkT, recInnerDm1T, recInnerDT, topBT, cT, dm1T, Term.eval, hdv, hkv,
    Option.bind, Option.pure_def, Option.bind_eq_bind]
  rfl

theorem rightKT_evalsTo_gen {dT kT : Term 0 .nat} {fuel d kv : Nat} (rho : Env 0)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv) :
    Term.eval Surface.code.body fuel (rightKT dT kT) rho = some (innerRightK d kv) := by
  simp only [rightKT, recInnerBulkT, recInnerDm1T, recInnerDT, recInnerHalfT, rightBT, rT, dm1T,
    Term.eval, hdv, hkv, Option.bind, Option.pure_def, Option.bind_eq_bind]
  rfl

theorem leftKT_evalsTo_gen {dT kT : Term 0 .nat} {fuel d kv : Nat} (rho : Env 0)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv) :
    Term.eval Surface.code.body fuel (leftKT dT kT) rho = some (innerLeftK d kv) := by
  simp only [leftKT, recInnerBulkT, recInnerDm1T, recInnerDT, recInnerHalfT, leftBT, rT, dm1T,
    Term.eval, hdv, hkv, Option.bind, Option.pure_def, Option.bind_eq_bind]
  rfl

theorem bottomKT_evalsTo_gen {dT kT : Term 0 .nat} {fuel d kv : Nat} (rho : Env 0)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv) :
    Term.eval Surface.code.body fuel (bottomKT dT kT) rho = some (innerBottomK d kv) := by
  simp only [bottomKT, recInnerBulkT, recInnerDm1T, recInnerDT, recInnerHalfT, bottomBT, cT, dm1T,
    Term.eval, hdv, hkv, Option.bind, Option.pure_def, Option.bind_eq_bind]
  rfl

/-! ## General guard generators from Nat-level cell-kind facts

Each closed classifier/band guard, fed eval certificates `dT→d`, `kT→kv`,
`qT→qv`, evaluates to the matching decidable `Nat`-level Bool.  Combined with a
`Nat`-level fact (`isInteriorCell d kv = true`, etc.) this discharges the
term-level guard via `guardTrueEval` / `guardFalseEval`.  These generalise the
center-specific `centerBulkGuard` / `centerInteriorGuard` / `centerInsideGuard`
to an arbitrary `(kv, qv)`. -/

/-- `bulkGuardT` evaluates to `decide (kv < (d-1)*(d-1))`. -/
def bulkGuard_of {fuel d kv : Nat} {dT kT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT)
    (hdv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel kT rho = some kv)
    (hfact : decide (kv < (d-1)*(d-1)) = true) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardT dT kT)) (SC.b true)) :=
  guardTrueEval (bulkGuardT_pure hd hk) (by
    intro rho
    simp only [bulkGuardT, bulkCountT, dm1T, Term.eval, hdv rho, hkv rho,
      Option.bind, Option.pure_def, Option.bind_eq_bind, Option.some.injEq]
    exact hfact)

/-- `bulkGuardT` evaluates to `false` (boundary index). -/
def bulkGuardFalse_of {fuel d kv : Nat} {dT kT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT)
    (hdv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel kT rho = some kv)
    (hfact : decide (kv < (d-1)*(d-1)) = false) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardT dT kT)) (SC.b false)) :=
  guardFalseEval (bulkGuardT_pure hd hk) (by
    intro rho
    simp only [bulkGuardT, bulkCountT, dm1T, Term.eval, hdv rho, hkv rho,
      Option.bind, Option.pure_def, Option.bind_eq_bind, Option.some.injEq]
    exact hfact)

/-- `interiorCellGuardT` evaluates to `isInteriorCell d kv`. -/
theorem interiorCellGuardT_eval_gen {fuel d kv : Nat} {dT kT : Term 0 .nat} (rho : Env 0)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv) :
    Term.eval Surface.code.body fuel (interiorCellGuardT dT kT) rho
      = some (isInteriorCell d kv) := by
  simp only [interiorCellGuardT, band4, band3, le, rT, cT, lastCellT, dm1T, Term.eval,
    hdv, hkv, Option.bind, Option.pure_def, Option.bind_eq_bind, Option.some.injEq,
    isInteriorCell, cellR, cellC, cellLastCell]
  rcases Bool.eq_false_or_eq_true (decide (1 ≤ kv / (d-1))) with h|h <;>
    rcases Bool.eq_false_or_eq_true (decide (kv / (d-1) < d-1-1)) with h2|h2 <;>
    rcases Bool.eq_false_or_eq_true (decide (1 ≤ kv % (d-1))) with h3|h3 <;>
    simp [h, h2, h3]

/-- `insideGuardT` evaluates to `isInside d qv`. -/
theorem insideGuardT_eval_gen {fuel d qv : Nat} {dT qT : Term 0 .nat} (rho : Env 0)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hqv : Term.eval Surface.code.body fuel qT rho = some qv) :
    Term.eval Surface.code.body fuel (insideGuardT dT qT) rho
      = some (isInside d qv) := by
  simp only [insideGuardT, band4, band3, le, rowT, colT, dm1T, Term.eval,
    hdv, hqv, Option.bind, Option.pure_def, Option.bind_eq_bind, Option.some.injEq,
    isInside, cellRow, cellCol]
  rcases Bool.eq_false_or_eq_true (decide (1 ≤ qv / d)) with h|h <;>
    rcases Bool.eq_false_or_eq_true (decide (qv / d < d-1)) with h2|h2 <;>
    rcases Bool.eq_false_or_eq_true (decide (1 ≤ qv % d)) with h3|h3 <;>
    simp [h, h2, h3]

/-- `interiorCellGuardT` derivation from `isInteriorCell d kv = true`. -/
def interiorCellGuard_of {fuel d kv : Nat} {dT kT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT)
    (hdv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel kT rho = some kv)
    (hfact : isInteriorCell d kv = true) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (interiorCellGuardT dT kT)) (SC.b true)) :=
  guardTrueEval (interiorCellGuardT_pure hd hk) (by
    intro rho; rw [interiorCellGuardT_eval_gen rho (hdv rho) (hkv rho), hfact])

/-- `interiorCellGuardT` derivation from `isInteriorCell d kv = false`. -/
def interiorCellGuardFalse_of {fuel d kv : Nat} {dT kT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT)
    (hdv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel kT rho = some kv)
    (hfact : isInteriorCell d kv = false) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (interiorCellGuardT dT kT)) (SC.b false)) :=
  guardFalseEval (interiorCellGuardT_pure hd hk) (by
    intro rho; rw [interiorCellGuardT_eval_gen rho (hdv rho) (hkv rho), hfact])

/-- `insideGuardT` derivation from `isInside d qv = true`. -/
def insideGuard_of {fuel d qv : Nat} {dT qT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hq : SFormula.PureNatTerm qT)
    (hdv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel dT rho = some d)
    (hqv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel qT rho = some qv)
    (hfact : isInside d qv = true) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (insideGuardT dT qT)) (SC.b true)) :=
  guardTrueEval (insideGuardT_pure hd hq) (by
    intro rho; rw [insideGuardT_eval_gen rho (hdv rho) (hqv rho), hfact])

/-- `insideGuardT` derivation from `isInside d qv = false`. -/
def insideGuardFalse_of {fuel d qv : Nat} {dT qT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hq : SFormula.PureNatTerm qT)
    (hdv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel dT rho = some d)
    (hqv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel qT rho = some qv)
    (hfact : isInside d qv = false) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (insideGuardT dT qT)) (SC.b false)) :=
  guardFalseEval (insideGuardT_pure hd hq) (by
    intro rho; rw [insideGuardT_eval_gen rho (hdv rho) (hqv rho), hfact])

/-- The `Term.eval` of a `band3` of comparisons normalizes to the right-nested
`&&` of the three `decide`s. -/
private theorem band3_ite_form (a b c : Bool) :
    (if a = true then (if b = true then some c else some false) else some false)
      = some (a && (b && c)) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- `topCellGuard` evaluates to `isTopCell d kv`. -/
theorem topCellGuard_eval_gen {fuel d kv : Nat} {dT kT : Term 0 .nat} (rho : Env 0)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv) :
    Term.eval Surface.code.body fuel (topCellGuard dT kT) rho = some (isTopCell d kv) := by
  simp only [topCellGuard, band3, topBT, rT, cT, recInnerHalfT, recInnerDm1T, recInnerDT, dm1T,
    Term.eval, hdv, hkv, Option.bind, Option.pure_def, Option.bind_eq_bind,
    isTopCell, cellR, cellC, cellInnerHalf]
  exact band3_ite_form _ _ _

/-- `rightCellGuard` evaluates to `isRightCell d kv`. -/
theorem rightCellGuard_eval_gen {fuel d kv : Nat} {dT kT : Term 0 .nat} (rho : Env 0)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv) :
    Term.eval Surface.code.body fuel (rightCellGuard dT kT) rho = some (isRightCell d kv) := by
  simp only [rightCellGuard, band3, rightBT, rT, cT, lastCellT, recInnerHalfT, recInnerDm1T,
    recInnerDT, dm1T, Term.eval, hdv, hkv, Option.bind, Option.pure_def, Option.bind_eq_bind,
    isRightCell, cellR, cellC, cellLastCell, cellInnerHalf]
  exact band3_ite_form _ _ _

/-- `leftCellGuard` evaluates to `isLeftCell d kv`. -/
theorem leftCellGuard_eval_gen {fuel d kv : Nat} {dT kT : Term 0 .nat} (rho : Env 0)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv) :
    Term.eval Surface.code.body fuel (leftCellGuard dT kT) rho = some (isLeftCell d kv) := by
  simp only [leftCellGuard, band3, leftBT, rT, cT, recInnerHalfT, recInnerDm1T, recInnerDT, dm1T,
    Term.eval, hdv, hkv, Option.bind, Option.pure_def, Option.bind_eq_bind,
    isLeftCell, cellR, cellC, cellInnerHalf]
  exact band3_ite_form _ _ _

/-- `bottomCellGuard` evaluates to `isBottomCell d kv`. -/
theorem bottomCellGuard_eval_gen {fuel d kv : Nat} {dT kT : Term 0 .nat} (rho : Env 0)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv) :
    Term.eval Surface.code.body fuel (bottomCellGuard dT kT) rho = some (isBottomCell d kv) := by
  simp only [bottomCellGuard, band3, bottomBT, rT, cT, lastCellT, recInnerHalfT, recInnerDm1T,
    recInnerDT, dm1T, Term.eval, hdv, hkv, Option.bind, Option.pure_def, Option.bind_eq_bind,
    isBottomCell, cellR, cellC, cellLastCell, cellInnerHalf]
  exact band3_ite_form _ _ _

/-- Cell-guard derivation (TRUE/FALSE) from the matching Nat-level selector. -/
def cellGuard_of {fuel : Nat} {b : Bool} {g : Term 0 .bool}
    (gpure : SFormula.PureBoolTerm g)
    (geval : ∀ (rho : Env 0), Term.eval Surface.code.body fuel g rho = some b)
    : PureFamilyDerivA Surface.code.body fuel (.eqBool (SC.closed g) (SC.b b)) :=
  match b with
  | true => guardTrueEval gpure geval
  | false => guardFalseEval gpure geval

/-- Purity of the four cell guards. -/
def topCellGuard_pure {dT kT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureBoolTerm (topCellGuard dT kT) := by
  have hdm1 := SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 1)
  have hr := SFormula.PureNatTerm.div hk hdm1
  have hc := SFormula.PureNatTerm.mod hk hdm1
  have htb := SFormula.PureNatTerm.div (SFormula.PureNatTerm.sub hc (SFormula.PureNatTerm.nat 1))
    (SFormula.PureNatTerm.nat 2)
  have hih := SFormula.PureNatTerm.div
    (SFormula.PureNatTerm.sub (SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 2))
      (SFormula.PureNatTerm.nat 1)) (SFormula.PureNatTerm.nat 2)
  exact SFormula.PureBoolTerm.and (SFormula.PureBoolTerm.eqNat hr (SFormula.PureNatTerm.nat 0))
    (SFormula.PureBoolTerm.and
      (SFormula.PureBoolTerm.eqNat hc
        (SFormula.PureNatTerm.add (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 2) htb)
          (SFormula.PureNatTerm.nat 1)))
      (SFormula.PureBoolTerm.ltNat htb hih))

def rightCellGuard_pure {dT kT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureBoolTerm (rightCellGuard dT kT) := by
  have hdm1 := SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 1)
  have hr := SFormula.PureNatTerm.div hk hdm1
  have hc := SFormula.PureNatTerm.mod hk hdm1
  have hrb := SFormula.PureNatTerm.div (SFormula.PureNatTerm.sub hr (SFormula.PureNatTerm.nat 1))
    (SFormula.PureNatTerm.nat 2)
  have hlast := SFormula.PureNatTerm.sub hdm1 (SFormula.PureNatTerm.nat 1)
  have hih := SFormula.PureNatTerm.div
    (SFormula.PureNatTerm.sub (SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 2))
      (SFormula.PureNatTerm.nat 1)) (SFormula.PureNatTerm.nat 2)
  exact SFormula.PureBoolTerm.and (SFormula.PureBoolTerm.eqNat hc hlast)
    (SFormula.PureBoolTerm.and
      (SFormula.PureBoolTerm.eqNat hr
        (SFormula.PureNatTerm.add (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 2) hrb)
          (SFormula.PureNatTerm.nat 1)))
      (SFormula.PureBoolTerm.ltNat hrb hih))

def leftCellGuard_pure {dT kT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureBoolTerm (leftCellGuard dT kT) := by
  have hdm1 := SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 1)
  have hr := SFormula.PureNatTerm.div hk hdm1
  have hc := SFormula.PureNatTerm.mod hk hdm1
  have hlb := SFormula.PureNatTerm.div (SFormula.PureNatTerm.sub hr (SFormula.PureNatTerm.nat 2))
    (SFormula.PureNatTerm.nat 2)
  have hih := SFormula.PureNatTerm.div
    (SFormula.PureNatTerm.sub (SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 2))
      (SFormula.PureNatTerm.nat 1)) (SFormula.PureNatTerm.nat 2)
  exact SFormula.PureBoolTerm.and (SFormula.PureBoolTerm.eqNat hc (SFormula.PureNatTerm.nat 0))
    (SFormula.PureBoolTerm.and
      (SFormula.PureBoolTerm.eqNat hr
        (SFormula.PureNatTerm.add (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 2) hlb)
          (SFormula.PureNatTerm.nat 2)))
      (SFormula.PureBoolTerm.ltNat hlb hih))

def bottomCellGuard_pure {dT kT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureBoolTerm (bottomCellGuard dT kT) := by
  have hdm1 := SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 1)
  have hr := SFormula.PureNatTerm.div hk hdm1
  have hc := SFormula.PureNatTerm.mod hk hdm1
  have hbb := SFormula.PureNatTerm.div (SFormula.PureNatTerm.sub hc (SFormula.PureNatTerm.nat 2))
    (SFormula.PureNatTerm.nat 2)
  have hlast := SFormula.PureNatTerm.sub hdm1 (SFormula.PureNatTerm.nat 1)
  have hih := SFormula.PureNatTerm.div
    (SFormula.PureNatTerm.sub (SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 2))
      (SFormula.PureNatTerm.nat 1)) (SFormula.PureNatTerm.nat 2)
  exact SFormula.PureBoolTerm.and (SFormula.PureBoolTerm.eqNat hr hlast)
    (SFormula.PureBoolTerm.and
      (SFormula.PureBoolTerm.eqNat hc
        (SFormula.PureNatTerm.add (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 2) hbb)
          (SFormula.PureNatTerm.nat 2)))
      (SFormula.PureBoolTerm.ltNat hbb hih))

/-- Generic cell-guard derivation from the matching Nat selector value `b`. -/
def topCellGuard_of {fuel d kv : Nat} {dT kT : Term 0 .nat} {b : Bool}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT)
    (hdv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel kT rho = some kv)
    (hfact : isTopCell d kv = b) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topCellGuard dT kT)) (SC.b b)) :=
  cellGuard_of (topCellGuard_pure hd hk)
    (by intro rho; rw [topCellGuard_eval_gen rho (hdv rho) (hkv rho), hfact])

def rightCellGuard_of {fuel d kv : Nat} {dT kT : Term 0 .nat} {b : Bool}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT)
    (hdv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel kT rho = some kv)
    (hfact : isRightCell d kv = b) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (rightCellGuard dT kT)) (SC.b b)) :=
  cellGuard_of (rightCellGuard_pure hd hk)
    (by intro rho; rw [rightCellGuard_eval_gen rho (hdv rho) (hkv rho), hfact])

def leftCellGuard_of {fuel d kv : Nat} {dT kT : Term 0 .nat} {b : Bool}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT)
    (hdv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel kT rho = some kv)
    (hfact : isLeftCell d kv = b) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (leftCellGuard dT kT)) (SC.b b)) :=
  cellGuard_of (leftCellGuard_pure hd hk)
    (by intro rho; rw [leftCellGuard_eval_gen rho (hdv rho) (hkv rho), hfact])

def bottomCellGuard_of {fuel d kv : Nat} {dT kT : Term 0 .nat} {b : Bool}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT)
    (hdv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel kT rho = some kv)
    (hfact : isBottomCell d kv = b) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bottomCellGuard dT kT)) (SC.b b)) :=
  cellGuard_of (bottomCellGuard_pure hd hk)
    (by intro rho; rw [bottomCellGuard_eval_gen rho (hdv rho) (hkv rho), hfact])

/-- **Interior-cell, not-inside peel → `I`.**  Selects bulk (TRUE), interiorCell
(TRUE), inside (FALSE), landing on the closed `I` leaf. -/
def recInteriorPeelI {fuel : Nat} (dT kT qT : Term 0 .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardT dT kT)) (SC.b true)))
    (hInterior : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (interiorCellGuardT dT kT)) (SC.b true)))
    (hInside : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (insideGuardT dT qT)) (SC.b false))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt
          (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed qT))
        (SC.closed (.pauliLit Pauli.I))) := by
  simp only [SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
    SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q,
    codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4, orEqSucc, le]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (pureStabAtClosedIteLamThen (fuel := fuel) _ _ _ qT hq
      (promotedBulkSelect dT kT qT hq hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← interiorCellGuardT_simp]; exact hInterior))
    (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← insideGuardT_simp]; exact hInside))

/-- Row-level interior not-inside `→ I` step. -/
def recInteriorRow_I {fuel : Nat} (n : STerm 0 .nat)
    (dT kT qT : Term 0 .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hDist : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat dT (n5 : Term 0 .nat))) (SC.b false)))
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardT dT kT)) (SC.b true)))
    (hInterior : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (interiorCellGuardT dT kT)) (SC.b true)))
    (hInside : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (insideGuardT dT qT)) (SC.b false))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (.stabAt (SC.closed (.recCall dT kT)) (SC.closed qT))
        (SC.closed (.pauliLit Pauli.I))) :=
  surfaceCodeRecursiveEntryEq n dT kT qT (.pauliLit Pauli.I) hd hk hDist
    (recInteriorPeelI dT kT qT hd hk hq hBulk hInterior hInside)

/-! ## The keystone: full forall-`k` discharged induction (recursing cells)

`surfaceRowChar` generalises `recCenterChar` (which handles only the always-interior
center cell) to *every* `k`.  It is **structurally recursive on the index `m`** — the
inductive hypothesis comes from the recursive call, NOT a hypothesis argument — and
dispatches each `(kv, qv)` by cell kind:

* **interior-inside** and the four **promoted-{top,right,left,bottom}-inside** cells
  recurse: their inner-code reference is resolved by `surfaceRowChar m …` instantiated
  at the projected inner index/qubit, exactly the `O(d)`-deep recursion the distance
  proof consumes.  The leaf they produce is, *definitionally*, `recLeaf` one layer down
  (self-similarity is built into `recLeaf`), so no extra hypothesis is needed.

* every **non-recursing** cell (boundary index, bulk fallback, and the
  not-inside leaves) is resolved by the supplied `oracle` — a parametric base-entry
  resolver.  At those cells `recLeaf m kv qv = surfaceCellPauli (oddDistance m) kv qv`,
  the *base-entry geometry*, which `recBasePeel{,X,I}` / `recTopXPeel` / … (the Grid-file
  parametric peels) discharge from the band/kind/classifier guards.

This isolates the remaining work to the base-entry guard generators (the analogue of
`bulkGuard_of` for the base bulk-band / kind / boundary-classifier guards at general
`d`), behind the `oracle` interface — the recursing structure of the induction, the
genuinely hard part, is fully discharged here. -/

/-- Resolver for non-recursing cells: the generated row `recCall dT kT` at `qT`
carries the base-entry classifier Pauli.  Discharged per-`d` from the parametric
base peels; abstracted here so the keystone's recursing structure stands alone. -/
structure BaseOracle (fuel : Nat) where
  resolve : (m : Nat) → (D : DistAt m) → (kT qT : Term 0 .nat) → (kv qv : Nat) →
    SFormula.PureNatTerm kT → SFormula.PureNatTerm qT →
    (∀ (rho : Env 0), Term.eval Surface.code.body fuel kT rho = some kv) →
    (∀ (rho : Env 0), Term.eval Surface.code.body fuel qT rho = some qv) →
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (.stabAt (SC.closed (.recCall D.dT kT)) (SC.closed qT))
        (SC.closed (.pauliLit (surfaceCellPauli (oddDistance m) kv qv))))

/-- **The keystone forall-`k` induction.**  For every index `m`, every stabilizer
index `kv` and qubit `qv` (carried by pure terms `kT`/`qT` with eval certificates),
the generated code row `recCall D.dT kT` at `qT` carries `recLeaf m kv qv`.

Genuinely discharged by structural recursion on `m`: the recursing cells feed the IH
from the recursive call; the rest go through `oracle`. -/
def surfaceRowChar {fuel : Nat} (oracle : BaseOracle fuel) :
    (m : Nat) → (D : DistAt m) → (kT qT : Term 0 .nat) → (kv qv : Nat) →
    SFormula.PureNatTerm kT → SFormula.PureNatTerm qT →
    (∀ (rho : Env 0), Term.eval Surface.code.body fuel kT rho = some kv) →
    (∀ (rho : Env 0), Term.eval Surface.code.body fuel qT rho = some qv) →
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.recCall D.dT kT)) (SC.closed qT))
        (SC.closed (.pauliLit (recLeaf m kv qv))))
  | 0, D, kT, qT, kv, qv, hk, hq, hkv, hqv => by
      -- Base case d = 3: recLeaf 0 = surfaceCellPauli 3, resolved by the oracle.
      have h := oracle.resolve 0 D kT qT kv qv hk hq hkv hqv
      simpa only [recLeaf] using h
  | m + 1, D, kT, qT, kv, qv, hk, hq, hkv, hqv => by
      -- Recursive case d ≥ 5.  Dispatch on the Nat-level cell kind of (kv, qv).
      set d := oddDistance (m + 1) with hd_def
      by_cases hbulk : kv < (d - 1) * (d - 1)
      · -- bulk index
        by_cases hint : isInteriorCell d kv = true
        · -- interior cell
          by_cases hin : isInside d qv = true
          · -- interior-inside: recurse via the IH.
            have hleaf : recLeaf (m + 1) kv qv
                = recLeaf m (innerInteriorK d kv) (innerQval d qv) := by
              simp only [recLeaf, ← hd_def, if_pos hbulk, hint, hin, if_true]
            rw [hleaf]
            exact recInteriorRow_withIH (SC.n (nQubits d)) D.dT kT qT
              (.pauliLit (recLeaf m (innerInteriorK d kv) (innerQval d qv)))
              D.pure hk hq
              (distLtFiveFalse_of_DistAt D)
              (bulkGuard_of D.pure hk D.evalsTo hkv (decide_eq_true hbulk))
              (interiorCellGuard_of D.pure hk D.evalsTo hkv hint)
              (insideGuard_of D.pure hq D.evalsTo hqv hin)
              (PureFamilyDerivA.eqPauliTrans _ _ _
                (PureFamilyDerivA.closedStabAtSplit
                  (.recCall (innerDT D.dT) (interiorKT D.dT kT)) (innerQT D.dT qT))
                (surfaceRowChar oracle m D.pred (interiorKT D.dT kT) (innerQT D.dT qT)
                  (innerInteriorK d kv) (innerQval d qv)
                  (interiorKT_pure D.pure hk) (innerQT_pure D.pure hq)
                  (fun rho => interiorKT_evalsTo_gen rho (D.evalsTo rho) (hkv rho))
                  (fun rho => innerQT_evalsTo_gen rho (D.evalsTo rho) (hqv rho))))
          · -- interior-not-inside: leaf is I; resolved by the interior-I peel.
            have hinF : isInside d qv = false := by simpa using hin
            have hleaf : recLeaf (m + 1) kv qv = Pauli.I := by
              simp only [recLeaf, ← hd_def, if_pos hbulk, hint, if_true, hinF,
                Bool.false_eq_true, if_false]
            rw [hleaf]
            exact recInteriorRow_I (SC.n (nQubits d)) D.dT kT qT D.pure hk hq
              (distLtFiveFalse_of_DistAt D)
              (bulkGuard_of D.pure hk D.evalsTo hkv (decide_eq_true hbulk))
              (interiorCellGuard_of D.pure hk D.evalsTo hkv hint)
              (insideGuardFalse_of D.pure hq D.evalsTo hqv hinF)
        · -- non-interior bulk cell: promoted (top/right/left/bottom) or base fallback.
          have hintF : isInteriorCell d kv = false := by simpa using hint
          by_cases htop : isTopCell d kv = true
          · by_cases hin : isInside d qv = true
            · -- top-cell inside: recurse via the IH.
              have hleaf : recLeaf (m + 1) kv qv
                  = recLeaf m (innerTopK d kv) (innerQval d qv) := by
                simp only [recLeaf, ← hd_def, if_pos hbulk, hintF, htop, hin,
                  Bool.false_eq_true, if_false, if_true]
              rw [hleaf]
              exact recTopPromotedRow_withIH (SC.n (nQubits d)) D.dT kT qT
                (.pauliLit (recLeaf m (innerTopK d kv) (innerQval d qv)))
                D.pure hk hq (distLtFiveFalse_of_DistAt D)
                (bulkGuard_of D.pure hk D.evalsTo hkv (decide_eq_true hbulk))
                (interiorCellGuardFalse_of D.pure hk D.evalsTo hkv hintF)
                (topCellGuard_of D.pure hk D.evalsTo hkv htop)
                (insideGuard_of D.pure hq D.evalsTo hqv hin)
                (PureFamilyDerivA.eqPauliTrans _ _ _
                  (PureFamilyDerivA.closedStabAtSplit
                    (.recCall (recInnerDT D.dT) (topKT D.dT kT)) (innerQT D.dT qT))
                  (surfaceRowChar oracle m D.pred (topKT D.dT kT) (innerQT D.dT qT)
                    (innerTopK d kv) (innerQval d qv)
                    (topKT_pure D.pure hk) (innerQT_pure D.pure hq)
                    (fun rho => topKT_evalsTo_gen rho (D.evalsTo rho) (hkv rho))
                    (fun rho => innerQT_evalsTo_gen rho (D.evalsTo rho) (hqv rho))))
            · -- top-cell not-inside leaf: recLeaf = surfaceCellPauli, oracle resolves.
              have hinF : isInside d qv = false := by simpa using hin
              have hleaf : recLeaf (m + 1) kv qv = surfaceCellPauli d kv qv := by
                simp only [recLeaf, ← hd_def, if_pos hbulk, hintF, htop, hinF,
                  Bool.false_eq_true, if_false, if_true]
              rw [hleaf]; exact oracle.resolve (m + 1) D kT qT kv qv hk hq hkv hqv
          · by_cases hright : isRightCell d kv = true
            · by_cases hin : isInside d qv = true
              · -- right-cell inside: recurse via the IH.
                have htopF : isTopCell d kv = false := by simpa using htop
                have hleaf : recLeaf (m + 1) kv qv
                    = recLeaf m (innerRightK d kv) (innerQval d qv) := by
                  simp only [recLeaf, ← hd_def, if_pos hbulk, hintF, htopF, hright, hin,
                    Bool.false_eq_true, if_false, if_true]
                rw [hleaf]
                exact recRightPromotedRow_withIH (SC.n (nQubits d)) D.dT kT qT
                  (.pauliLit (recLeaf m (innerRightK d kv) (innerQval d qv)))
                  D.pure hk hq (distLtFiveFalse_of_DistAt D)
                  (bulkGuard_of D.pure hk D.evalsTo hkv (decide_eq_true hbulk))
                  (interiorCellGuardFalse_of D.pure hk D.evalsTo hkv hintF)
                  (topCellGuard_of D.pure hk D.evalsTo hkv htopF)
                  (rightCellGuard_of D.pure hk D.evalsTo hkv hright)
                  (insideGuard_of D.pure hq D.evalsTo hqv hin)
                  (PureFamilyDerivA.eqPauliTrans _ _ _
                    (PureFamilyDerivA.closedStabAtSplit
                      (.recCall (recInnerDT D.dT) (rightKT D.dT kT)) (innerQT D.dT qT))
                    (surfaceRowChar oracle m D.pred (rightKT D.dT kT) (innerQT D.dT qT)
                      (innerRightK d kv) (innerQval d qv)
                      (rightKT_pure D.pure hk) (innerQT_pure D.pure hq)
                      (fun rho => rightKT_evalsTo_gen rho (D.evalsTo rho) (hkv rho))
                      (fun rho => innerQT_evalsTo_gen rho (D.evalsTo rho) (hqv rho))))
              · -- right-cell not-inside leaf.
                have htopF : isTopCell d kv = false := by simpa using htop
                have hinF : isInside d qv = false := by simpa using hin
                have hleaf : recLeaf (m + 1) kv qv = surfaceCellPauli d kv qv := by
                  simp only [recLeaf, ← hd_def, if_pos hbulk, hintF, htopF, hright, hinF,
                    Bool.false_eq_true, if_false, if_true]
                rw [hleaf]; exact oracle.resolve (m + 1) D kT qT kv qv hk hq hkv hqv
            · by_cases hleft : isLeftCell d kv = true
              · by_cases hin : isInside d qv = true
                · -- left-cell inside: recurse via the IH.
                  have htopF : isTopCell d kv = false := by simpa using htop
                  have hrightF : isRightCell d kv = false := by simpa using hright
                  have hleaf : recLeaf (m + 1) kv qv
                      = recLeaf m (innerLeftK d kv) (innerQval d qv) := by
                    simp only [recLeaf, ← hd_def, if_pos hbulk, hintF, htopF, hrightF, hleft, hin,
                      Bool.false_eq_true, if_false, if_true]
                  rw [hleaf]
                  exact recLeftPromotedRow_withIH (SC.n (nQubits d)) D.dT kT qT
                    (.pauliLit (recLeaf m (innerLeftK d kv) (innerQval d qv)))
                    D.pure hk hq (distLtFiveFalse_of_DistAt D)
                    (bulkGuard_of D.pure hk D.evalsTo hkv (decide_eq_true hbulk))
                    (interiorCellGuardFalse_of D.pure hk D.evalsTo hkv hintF)
                    (topCellGuard_of D.pure hk D.evalsTo hkv htopF)
                    (rightCellGuard_of D.pure hk D.evalsTo hkv hrightF)
                    (leftCellGuard_of D.pure hk D.evalsTo hkv hleft)
                    (insideGuard_of D.pure hq D.evalsTo hqv hin)
                    (PureFamilyDerivA.eqPauliTrans _ _ _
                      (PureFamilyDerivA.closedStabAtSplit
                        (.recCall (recInnerDT D.dT) (leftKT D.dT kT)) (innerQT D.dT qT))
                      (surfaceRowChar oracle m D.pred (leftKT D.dT kT) (innerQT D.dT qT)
                        (innerLeftK d kv) (innerQval d qv)
                        (leftKT_pure D.pure hk) (innerQT_pure D.pure hq)
                        (fun rho => leftKT_evalsTo_gen rho (D.evalsTo rho) (hkv rho))
                        (fun rho => innerQT_evalsTo_gen rho (D.evalsTo rho) (hqv rho))))
                · -- left-cell not-inside leaf.
                  have htopF : isTopCell d kv = false := by simpa using htop
                  have hrightF : isRightCell d kv = false := by simpa using hright
                  have hinF : isInside d qv = false := by simpa using hin
                  have hleaf : recLeaf (m + 1) kv qv = surfaceCellPauli d kv qv := by
                    simp only [recLeaf, ← hd_def, if_pos hbulk, hintF, htopF, hrightF, hleft, hinF,
                      Bool.false_eq_true, if_false, if_true]
                  rw [hleaf]; exact oracle.resolve (m + 1) D kT qT kv qv hk hq hkv hqv
              · by_cases hbottom : isBottomCell d kv = true
                · by_cases hin : isInside d qv = true
                  · -- bottom-cell inside: recurse via the IH.
                    have htopF : isTopCell d kv = false := by simpa using htop
                    have hrightF : isRightCell d kv = false := by simpa using hright
                    have hleftF : isLeftCell d kv = false := by simpa using hleft
                    have hleaf : recLeaf (m + 1) kv qv
                        = recLeaf m (innerBottomK d kv) (innerQval d qv) := by
                      simp only [recLeaf, ← hd_def, if_pos hbulk, hintF, htopF, hrightF, hleftF,
                        hbottom, hin, Bool.false_eq_true, if_false, if_true]
                    rw [hleaf]
                    exact recBottomPromotedRow_withIH (SC.n (nQubits d)) D.dT kT qT
                      (.pauliLit (recLeaf m (innerBottomK d kv) (innerQval d qv)))
                      D.pure hk hq (distLtFiveFalse_of_DistAt D)
                      (bulkGuard_of D.pure hk D.evalsTo hkv (decide_eq_true hbulk))
                      (interiorCellGuardFalse_of D.pure hk D.evalsTo hkv hintF)
                      (topCellGuard_of D.pure hk D.evalsTo hkv htopF)
                      (rightCellGuard_of D.pure hk D.evalsTo hkv hrightF)
                      (leftCellGuard_of D.pure hk D.evalsTo hkv hleftF)
                      (bottomCellGuard_of D.pure hk D.evalsTo hkv hbottom)
                      (insideGuard_of D.pure hq D.evalsTo hqv hin)
                      (PureFamilyDerivA.eqPauliTrans _ _ _
                        (PureFamilyDerivA.closedStabAtSplit
                          (.recCall (recInnerDT D.dT) (bottomKT D.dT kT)) (innerQT D.dT qT))
                        (surfaceRowChar oracle m D.pred (bottomKT D.dT kT) (innerQT D.dT qT)
                          (innerBottomK d kv) (innerQval d qv)
                          (bottomKT_pure D.pure hk) (innerQT_pure D.pure hq)
                          (fun rho => bottomKT_evalsTo_gen rho (D.evalsTo rho) (hkv rho))
                          (fun rho => innerQT_evalsTo_gen rho (D.evalsTo rho) (hqv rho))))
                  · -- bottom-cell not-inside leaf.
                    have htopF : isTopCell d kv = false := by simpa using htop
                    have hrightF : isRightCell d kv = false := by simpa using hright
                    have hleftF : isLeftCell d kv = false := by simpa using hleft
                    have hinF : isInside d qv = false := by simpa using hin
                    have hleaf : recLeaf (m + 1) kv qv = surfaceCellPauli d kv qv := by
                      simp only [recLeaf, ← hd_def, if_pos hbulk, hintF, htopF, hrightF, hleftF,
                        hbottom, hinF, Bool.false_eq_true, if_false, if_true]
                    rw [hleaf]; exact oracle.resolve (m + 1) D kT qT kv qv hk hq hkv hqv
                · -- base fallback (no cell kind matched): base entry, resolved by oracle.
                  have htopF : isTopCell d kv = false := by simpa using htop
                  have hrightF : isRightCell d kv = false := by simpa using hright
                  have hleftF : isLeftCell d kv = false := by simpa using hleft
                  have hbottomF : isBottomCell d kv = false := by simpa using hbottom
                  have hleaf : recLeaf (m + 1) kv qv = surfaceCellPauli d kv qv := by
                    simp only [recLeaf, ← hd_def, if_pos hbulk, hintF, htopF, hrightF, hleftF,
                      hbottomF, Bool.false_eq_true, if_false]
                  rw [hleaf]; exact oracle.resolve (m + 1) D kT qT kv qv hk hq hkv hqv
      · -- boundary index (kv ≥ bulkCount): base entry, resolved by the oracle.
        have hleaf : recLeaf (m + 1) kv qv = surfaceCellPauli d kv qv := by
          simp only [recLeaf, ← hd_def, if_neg hbulk]
        rw [hleaf]
        exact oracle.resolve (m + 1) D kT qT kv qv hk hq hkv hqv

/-! ## Consumer-facing form over an `OddSurfaceDistance` + non-vacuity

For every odd distance and every stabilizer/qubit, the generated row carries the
recursion-faithful leaf.  `recLeaf` matches the trusted evaluator (validated by
`recLeafAgrees`), so this is the row-entry characterization the distance proof
consumes — established for ALL odd distances and ALL `k` by the discharged
induction (modulo the base-entry leaf `oracle`). -/

def surfaceRowEntryChar {fuel : Nat} (oracle : BaseOracle fuel)
    (D : OddSurfaceDistance) (kv qv : Nat) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed ((.recCall (.natLit D.distance) (.natLit kv)) : Term 0 .stab))
          (SC.closed ((.natLit qv) : Term 0 .nat)))
        (SC.closed ((.pauliLit (recLeaf D.index kv qv)) : Term 0 .pauli))) := by
  have h := surfaceRowChar oracle D.index (DistAt.lit D.index)
    (.natLit kv) (.natLit qv) kv qv
    (SFormula.PureNatTerm.nat _) (SFormula.PureNatTerm.nat _)
    (by intro rho; simp [Term.eval]) (by intro rho; simp [Term.eval])
  simpa only [DistAt.lit, OddSurfaceDistance.distance] using h

/-- **Non-vacuity**: the `d = 5` center cell `(k = 10, q = 12)` is an interior
cell that recurses one layer; `recLeaf 1 10 12 = Z`, so given any base oracle the
keystone yields the concrete `Z` entry there — exercising the genuine interior
recursion (not the oracle). -/
example : recLeaf 1 10 12 = Pauli.Z := by decide

def surfaceRowChar_d5_center_check {fuel : Nat} (oracle : BaseOracle fuel) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed ((.recCall (.natLit 5) (.natLit 10)) : Term 0 .stab))
          (SC.closed ((.natLit 12) : Term 0 .nat)))
        (SC.closed ((.pauliLit (recLeaf 1 10 12)) : Term 0 .pauli))) :=
  surfaceRowEntryChar oracle OddSurfaceDistance.d5 10 12

/-! ## Axiom audit -/

#print axioms surfaceRowEntryChar
#print axioms surfaceCellPauli
#print axioms recLeaf
#print axioms interiorKT_evalsTo_gen
#print axioms topKT_evalsTo_gen
#print axioms bulkGuard_of
#print axioms interiorCellGuardT_eval_gen
#print axioms recTopPromotedInnerPeel
#print axioms recRightPromotedInnerPeel
#print axioms recLeftPromotedInnerPeel
#print axioms recBottomPromotedInnerPeel
#print axioms recTopPromotedRow_withIH
#print axioms recBottomPromotedRow_withIH
#print axioms recInteriorPeelI
#print axioms topCellGuard_of
#print axioms surfaceRowChar

end QHL.CodeLang.Surface.Verify
