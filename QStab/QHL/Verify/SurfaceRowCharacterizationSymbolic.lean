import QStab.QHL.Verify.SurfaceRowCharacterizationUnconditional

/-!
# Symbolic-index generated-row characterization

`surfaceRowCharFull` (`SurfaceRowCharacterizationUnconditional.lean`) is the
**unconditional** per-entry characterization for a *concrete* stabilizer index:
its `kT : Term 0 .nat` must carry an `evalsTo` certificate to a concrete `kv : Nat`,
and the right-hand side leaf is the meta-level `recLeaf m kv qv : Pauli`.

The distance-proof consumers (`rowsCommuteOddF` / the normalizers /
`rowBridgeGeneratedEqF`) are `allNatLt numStab (…)` formulas: they introduce the
stabilizer index as a **symbolic object-logic variable** (`SFormula.boundNat` /
`.var 0` at arity ≥ 1, with `numStab` symbolic in the distance index).  There is
no concrete `kv` to feed `surfaceRowCharFull`.

This file carries the characterization at a **symbolic index term** `kT`.  The
correct symbolic statement is **row-level** (`eqStabUpTo`), not a fixed-Pauli
per-entry equality: the generated row `recCall (natLit 3) kT` *equals* the
unfolded base-entry lambda `stabLam (codeSubstAt (natLit 3) kT 1 baseEntry)`.
This is the form the consumers `eqPauliProj` / `boolCases` on (the RHS is the
genuine cell-kind `ite` tree, with the symbolic index `kT` left free).

Nothing here adds a trusted rule, uses `native_decide`, `Formula.check`,
`Formula.eval`-as-distance, `deriveTrue?`, `admit`, or a new axiom.  Every lemma
is **unconditional**: the only hypotheses are purity certificates on the index /
qubit terms (`SFormula.PureNatTerm`) — never an oracle and never a hypothesis
that asserts the Pauli entry.
-/

namespace QHL.CodeLang.Surface.Verify

open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface

set_option maxRecDepth 65536

/-! ## The closed distance guard `3 < 5` at an arbitrary arity

The base distance `d = 3` selects the base branch of the Surface body
(`3 < 5`).  This guard is closed (independent of the symbolic index `kT`), so it
is discharged by `arithBool` at any arity. -/

/-- The `(natLit 3) < 5` guard, evaluating to `true`, at arity `arity`. -/
def closedThreeLtFive {fuel arity : Nat} :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat (.natLit (arity := arity) 3) (n5 : Term arity .nat)))
        (SC.b true)) :=
  PureFamilyDerivA.arithBool _ (by rfl) (by
    intro rho E
    simp [SFormula.eval, STerm.eval, Term.eval, SC.closed, SC.b, n5])

/-! ## Symbolic-index base-case row equality (`d = 3`)

For an arbitrary pure index term `kT` (in particular the object-logic bound
variable `SFormula.boundNat`), the generated code row `recCall (natLit 3) kT`
equals — as a whole stabilizer, up to `n` qubits — the unfolded base-entry
lambda.  No concrete value of `kT` is required; the proof is `recUnfold`
(symbolic) followed by the base-branch selection (closed `3 < 5` guard). -/
def surfaceRowEqStabSymbolicBase {fuel arity : Nat}
    (n : STerm arity .nat) (kT : Term arity .nat) (hk : SFormula.PureNatTerm kT) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqStabUpTo n
        (SC.closed (.recCall (.natLit 3) kT))
        (SC.closed (.stabLam (codeSubstAt (.natLit 3) kT 1 SurfaceASTPublic.baseEntry)))) :=
  pureEqStabTrans n
    (SC.closed (.recCall (.natLit 3) kT))
    (SC.closed (codeSubstTerm Surface.code.body (.natLit 3) kT))
    (SC.closed (.stabLam (codeSubstAt (.natLit 3) kT 1 SurfaceASTPublic.baseEntry)))
    (PureFamilyDerivA.recUnfold n (.natLit 3) kT (SFormula.PureNatTerm.nat 3) hk)
    (surfaceCodeSubstBodyBase n (.natLit 3) kT closedThreeLtFive)

#print axioms surfaceRowEqStabSymbolicBase

/-! ## Symbolic-index per-entry projection (`d = 3`)

Projecting the row equality at an arbitrary qubit term `qT` gives the
per-entry form the consumers `boolCases`/`pauliIteSelect` on: the generated
entry `stabAt (recCall (natLit 3) kT) qT` equals the **substituted base-entry
cell-kind `ite` tree** at `qT`, with the symbolic index `kT` left free.  No
fixed Pauli is asserted — the RHS is exactly the guarded entry tree. -/
def surfaceRowEntryCharSymbolicBase {fuel arity : Nat}
    (n : STerm arity .nat) (kT qT : Term arity .nat)
    (hk : SFormula.PureNatTerm kT) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.recCall (.natLit 3) kT)) (SC.closed qT))
        (SC.closed (.stabAt
          (.stabLam (codeSubstAt (.natLit 3) kT 1 SurfaceASTPublic.baseEntry)) qT))) :=
  surfaceCodeBaseEntryAt n (.natLit 3) kT qT (SFormula.PureNatTerm.nat 3) hk
    closedThreeLtFive

#print axioms surfaceRowEntryCharSymbolicBase

/-! ## Symbolic-index, symbolic-distance row unfold (`d ≥ 5` recursive branch)

For a distance term `dT` carrying a `DistAt (m+1)` certificate (so `dT` evaluates
to `oddDistance (m+1) ≥ 7 ≥ 5`) and an arbitrary pure index term `kT`, the
generated row `recCall dT kT` equals the unfolded **recursive-entry** lambda.
This is the recursive-branch analogue of `surfaceRowEqStabSymbolicBase`, with the
distance guard discharged from the `DistAt` evaluation certificate (closed,
independent of the symbolic `kT`).  IH-free: it unfolds exactly one level. -/
def surfaceRowEqStabSymbolicRec {fuel arity : Nat}
    (n : STerm arity .nat) (dT kT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT)
    (hDist : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat dT (n5 : Term arity .nat))) (SC.b false))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqStabUpTo n
        (SC.closed (.recCall dT kT))
        (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))) :=
  surfaceCodeRowSelectRecursive n dT kT hd hk hDist

/-- Per-entry projection of the recursive-branch row unfold at a qubit `qT`. -/
def surfaceRowEntryCharSymbolicRec {fuel arity : Nat}
    (n : STerm arity .nat) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT)
    (hDist : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat dT (n5 : Term arity .nat))) (SC.b false))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.recCall dT kT)) (SC.closed qT))
        (SC.closed (.stabAt
          (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)) qT))) :=
  surfaceCodeRecursiveEntryAt n dT kT qT hd hk hDist

#print axioms surfaceRowEqStabSymbolicRec
#print axioms surfaceRowEntryCharSymbolicRec

/-! ## Consumer-facing symbolic-index form keyed to `boundNat`

The distance-proof consumers (`codeRowsCommuteUpTo`, `normalizesCodeUpTo`)
introduce the stabilizer index via `allNatLt numStab`, so inside the body the
index is the object-logic bound variable `SFormula.boundNat` (de Bruijn `var 0`
at arity ≥ 1).  Specialising the symbolic-index row unfold to `kT = .var ⟨0,…⟩`
gives the entry characterization at exactly that bound index. -/

/-- The object-logic bound-index term `var 0` as a pure Nat term (arity ≥ 1). -/
def boundIdx {arity : Nat} : Term (arity + 1) .nat := .var ⟨0, Nat.succ_pos arity⟩

def boundIdx_pure {arity : Nat} : SFormula.PureNatTerm (boundIdx (arity := arity)) :=
  SFormula.PureNatTerm.var ⟨0, Nat.succ_pos arity⟩

/-- Base-case (`d = 3`) row unfold at the object-logic bound index `var 0`.
This is the symbolic-index row characterization the `allNatLt numStab` consumers
expose after `allNatLtIntro`/`allNatLtIntroBounded`. -/
def surfaceRowEqStabBoundIdxBase {fuel arity : Nat} (n : STerm (arity + 1) .nat) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqStabUpTo n
        (SC.closed (.recCall (.natLit 3) (boundIdx (arity := arity))))
        (SC.closed (.stabLam
          (codeSubstAt (.natLit 3) (boundIdx (arity := arity)) 1 SurfaceASTPublic.baseEntry)))) :=
  surfaceRowEqStabSymbolicBase n (boundIdx (arity := arity)) boundIdx_pure

#print axioms surfaceRowEqStabBoundIdxBase

/-! ## Arity-general grid helpers and recursive interior peel

The per-cell recursion infrastructure in `SurfaceRowCharacterization{Full,Grid}`
is written for *closed* (arity-0) index/qubit terms.  To resolve the recursive
interior cell at a **symbolic** index (arity ≥ 1, the object-logic bound
variable), we restate the grid helpers arity-generally and port the interior
peel.  The peel body uses only arity-polymorphic combinators
(`pureStabAtClosedIteLamThen`, `pauliIteSelectThen`), so it ports unchanged. -/

def dm1TA {arity : Nat} (dT : Term arity .nat) : Term arity .nat := .sub dT (.natLit 1)
def bulkCountTA {arity : Nat} (dT : Term arity .nat) : Term arity .nat :=
  .mul (dm1TA dT) (dm1TA dT)
def rTA {arity : Nat} (dT kT : Term arity .nat) : Term arity .nat := .div kT (dm1TA dT)
def cTA {arity : Nat} (dT kT : Term arity .nat) : Term arity .nat := .mod kT (dm1TA dT)
def innerDTA {arity : Nat} (dT : Term arity .nat) : Term arity .nat := .sub dT (.natLit 2)
def innerDm1TA {arity : Nat} (dT : Term arity .nat) : Term arity .nat :=
  .sub (innerDTA dT) (.natLit 1)
def lastCellTA {arity : Nat} (dT : Term arity .nat) : Term arity .nat :=
  .sub (dm1TA dT) (.natLit 1)
def rowTA {arity : Nat} (dT qT : Term arity .nat) : Term arity .nat := .div qT dT
def colTA {arity : Nat} (dT qT : Term arity .nat) : Term arity .nat := .mod qT dT

/-- Outer bulk guard `kT < (dT-1)^2`, arity-general. -/
def bulkGuardTA {arity : Nat} (dT kT : Term arity .nat) : Term arity .bool :=
  .ltNat kT (bulkCountTA dT)

/-- `interiorCell` guard, arity-general. -/
def interiorCellGuardTA {arity : Nat} (dT kT : Term arity .nat) : Term arity .bool :=
  band4 (le (.natLit 1) (rTA dT kT)) (.ltNat (rTA dT kT) (lastCellTA dT))
    (le (.natLit 1) (cTA dT kT)) (.ltNat (cTA dT kT) (lastCellTA dT))

/-- `inside` guard, arity-general. -/
def insideGuardTA {arity : Nat} (dT qT : Term arity .nat) : Term arity .bool :=
  band4 (le (.natLit 1) (rowTA dT qT)) (.ltNat (rowTA dT qT) (dm1TA dT))
    (le (.natLit 1) (colTA dT qT)) (.ltNat (colTA dT qT) (dm1TA dT))

/-- `interiorK = (r-1)*innerDm1 + (c-1)`, arity-general. -/
def interiorKTA {arity : Nat} (dT kT : Term arity .nat) : Term arity .nat :=
  .add (.mul (.sub (rTA dT kT) (.natLit 1)) (innerDm1TA dT))
    (.sub (cTA dT kT) (.natLit 1))

/-- `innerQ = (row-1)*innerD + (col-1)`, arity-general. -/
def innerQTA {arity : Nat} (dT qT : Term arity .nat) : Term arity .nat :=
  .add (.mul (.sub (rowTA dT qT) (.natLit 1)) (innerDTA dT))
    (.sub (colTA dT qT) (.natLit 1))

/-- The inner-code reference produced by the interior cell peel, arity-general. -/
def centerInnerRefA {arity : Nat} (dT kT qT : Term arity .nat) : Term arity .pauli :=
  .stabAt (.recCall (innerDTA dT) (interiorKTA dT kT)) (innerQTA dT qT)

/-- **Arity-general recursive interior-cell peel.**

Given the three grid guards as derivations (now over arbitrary-arity, possibly
symbolic, terms), the generated recursive entry stabilizer-lambda at `qT` equals
the inner-code reference `centerInnerRefA`.  Ports `recInteriorPeel` to arity ≥ 1.
The guards are NOT assumed to hold unconditionally — they are explicit premises,
true only in the relevant `boolCases` branch when `kT`/`qT` are symbolic. -/
def recInteriorPeelA {fuel arity : Nat} (dT kT qT : Term arity .nat)
    (_hd : SFormula.PureNatTerm dT) (_hk : SFormula.PureNatTerm kT)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b true)))
    (hInside : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt
          (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed qT))
        (SC.closed (centerInnerRefA dT kT qT))) := by
  simp only [SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
    SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q,
    codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4, orEqSucc, le]
  -- Step 1: strip `stabLam`, select the outer closed `bulk` branch.
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (pureStabAtClosedIteLamThen (fuel := fuel)
      (.ltNat (Term.lift 0 kT)
        (.mul (.sub (Term.lift 0 dT) (.natLit 1)) (.sub (Term.lift 0 dT) (.natLit 1))))
      _ _ qT hq ?hBulkGuard) ?_
  case hBulkGuard =>
    have heq : Term.instantiateTopNat qT
        (Term.ltNat (Term.lift 0 kT)
          (.mul (.sub (Term.lift 0 dT) (.natLit 1)) (.sub (Term.lift 0 dT) (.natLit 1))))
        = bulkGuardTA dT kT := by
      simp only [bulkGuardTA, bulkCountTA, dm1TA, Term.instantiateTopNat, Term.instantiateNatAt,
        instTop_lift]
    rw [heq]; exact hBulk
  -- Step 2: push the qubit instantiation through the residual `ite` tree.
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]
  -- Step 3: select `interiorCell` (via `hInterior`), then `inside` (via `hInside`).
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectThen _ _ _ ?hInteriorG)
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectThen _ _ _ ?hInsideG)
      (PureFamilyDerivA.eqPauliRefl _))
  case hInteriorG =>
    have heq : interiorCellGuardTA dT kT
        = ((Term.natLit 1).leNat (kT.div (dT.sub (Term.natLit 1)))).and
            (((kT.div (dT.sub (Term.natLit 1))).ltNat ((dT.sub (Term.natLit 1)).sub (Term.natLit 1))).and
              (((Term.natLit 1).leNat (kT.mod (dT.sub (Term.natLit 1)))).and
                ((kT.mod (dT.sub (Term.natLit 1))).ltNat ((dT.sub (Term.natLit 1)).sub (Term.natLit 1))))) := by
      simp only [interiorCellGuardTA, band4, band3, le, rTA, cTA, lastCellTA, dm1TA]
    rw [heq] at hInterior; exact hInterior
  case hInsideG =>
    have heq : insideGuardTA dT qT
        = ((Term.natLit 1).leNat (qT.div dT)).and
            (((qT.div dT).ltNat (dT.sub (Term.natLit 1))).and
              (((Term.natLit 1).leNat (qT.mod dT)).and
                ((qT.mod dT).ltNat (dT.sub (Term.natLit 1))))) := by
      simp only [insideGuardTA, band4, band3, le, rowTA, colTA, dm1TA]
    simp only [Nat.lt_irrefl, dite_false, dite_true]
    rw [heq] at hInside; exact hInside

#print axioms recInteriorPeelA

/-- **Arity-general interior-cell row step with the inductive hypothesis applied.**

The arity-general analogue of `recInteriorRow_withIH`.  Given the recursive
distance guard (`dT ≥ 5`), the three interior grid guards, and a derivation `ih`
resolving the inner-code reference `centerInnerRefA dT kT qT` (i.e. the inner row
`recCall (dT-2) (interiorKTA dT kT)` at `innerQTA dT qT`) to a leaf `p`, the
generated row `recCall dT kT` at `qT` carries `p`.

`ih` is the IH at the **symbolic inner index** `interiorKTA dT kT` — exactly the
shape a structural recursion on the distance index feeds from its recursive call.
This is unconditional: the only data are purity certificates and the explicit
guard/ih derivations; nothing asserts the entry Pauli directly. -/
def recInteriorRowA_withIH {fuel arity : Nat}
    (n : STerm arity .nat) (dT kT qT : Term arity .nat) (p : Term arity .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT)
    (hq : SFormula.PureNatTerm qT)
    (hDist : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat dT (n5 : Term arity .nat))) (SC.b false)))
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b true)))
    (hInside : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b true)))
    (ih : PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (SC.closed (centerInnerRefA dT kT qT)) (SC.closed p))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.recCall dT kT)) (SC.closed qT))
        (SC.closed p)) :=
  surfaceCodeRecursiveEntryEq n dT kT qT p hd hk hDist
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (recInteriorPeelA dT kT qT hd hk hq hBulk hInterior hInside)
      ih)

#print axioms recInteriorRowA_withIH

/-! ## Purity certificates for the symbolic inner index / qubit

To thread the inductive hypothesis through `recInteriorRowA_withIH` a recursion
must supply `SFormula.PureNatTerm` certificates for the inner index
`interiorKTA dT kT` and inner qubit `innerQTA dT qT`.  These follow purely from
the purity of `dT`, `kT`, `qT` (no value information is required), so they hold
at a **symbolic** index. -/

def innerDTA_pure {arity : Nat} {dT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) : SFormula.PureNatTerm (innerDTA dT) :=
  SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 2)

def interiorKTA_pure {arity : Nat} {dT kT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureNatTerm (interiorKTA dT kT) :=
  SFormula.PureNatTerm.add
    (SFormula.PureNatTerm.mul
      (SFormula.PureNatTerm.sub
        (SFormula.PureNatTerm.div hk (SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 1)))
        (SFormula.PureNatTerm.nat 1))
      (SFormula.PureNatTerm.sub
        (SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 2))
        (SFormula.PureNatTerm.nat 1)))
    (SFormula.PureNatTerm.sub
      (SFormula.PureNatTerm.mod hk (SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 1)))
      (SFormula.PureNatTerm.nat 1))

def innerQTA_pure {arity : Nat} {dT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hq : SFormula.PureNatTerm qT) :
    SFormula.PureNatTerm (innerQTA dT qT) :=
  SFormula.PureNatTerm.add
    (SFormula.PureNatTerm.mul
      (SFormula.PureNatTerm.sub
        (SFormula.PureNatTerm.div hq hd)
        (SFormula.PureNatTerm.nat 1))
      (SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 2)))
    (SFormula.PureNatTerm.sub
      (SFormula.PureNatTerm.mod hq hd)
      (SFormula.PureNatTerm.nat 1))

#print axioms interiorKTA_pure
#print axioms innerQTA_pure

/-! ## Arity-general promoted-boundary helper terms

The recursive entry routes a *promoted boundary* cell (one of top / right / left /
bottom) to a `promotedBoundaryEntry oldK outer kind` node, which — when the qubit
`inside` guard holds — delegates to the inner-code reference
`stabAt (recCall (d-2) oldK) innerQ`.  The `oldK` index and the cell-selection
guards are arithmetic in `(d, k)` only; below are their arity-general restatements,
mirroring `SurfaceRowCharacterizationKeystone`'s arity-0 `topBT`/`topCellGuard`/…
but now over arbitrary-arity (possibly symbolic) terms. -/

/-- Inner code distance `d - 2` (= `innerDTA`). -/
def recInnerDTA {arity : Nat} (dT : Term arity .nat) : Term arity .nat := innerDTA dT
/-- Inner bulk side `(d-2) - 1` (= `innerDm1TA`). -/
def recInnerDm1TA {arity : Nat} (dT : Term arity .nat) : Term arity .nat := innerDm1TA dT
/-- Inner bulk count `((d-2)-1)^2`. -/
def recInnerBulkTA {arity : Nat} (dT : Term arity .nat) : Term arity .nat :=
  .mul (recInnerDm1TA dT) (recInnerDm1TA dT)
/-- Inner half-width `((d-2)-1)/2`. -/
def recInnerHalfTA {arity : Nat} (dT : Term arity .nat) : Term arity .nat :=
  .div (recInnerDm1TA dT) (.natLit 2)

/-- `topB = (c - 1) / 2`, arity-general. -/
def topBTA {arity : Nat} (dT kT : Term arity .nat) : Term arity .nat :=
  .div (.sub (cTA dT kT) (.natLit 1)) (.natLit 2)
/-- `topCell` guard, arity-general. -/
def topCellGuardTA {arity : Nat} (dT kT : Term arity .nat) : Term arity .bool :=
  band3 (.eqNat (rTA dT kT) (.natLit 0))
    (.eqNat (cTA dT kT) (.add (.mul (.natLit 2) (topBTA dT kT)) (.natLit 1)))
    (.ltNat (topBTA dT kT) (recInnerHalfTA dT))

/-- `rightB = (r - 1) / 2`, arity-general. -/
def rightBTA {arity : Nat} (dT kT : Term arity .nat) : Term arity .nat :=
  .div (.sub (rTA dT kT) (.natLit 1)) (.natLit 2)
/-- `rightCell` guard, arity-general. -/
def rightCellGuardTA {arity : Nat} (dT kT : Term arity .nat) : Term arity .bool :=
  band3 (.eqNat (cTA dT kT) (lastCellTA dT))
    (.eqNat (rTA dT kT) (.add (.mul (.natLit 2) (rightBTA dT kT)) (.natLit 1)))
    (.ltNat (rightBTA dT kT) (recInnerHalfTA dT))

/-- `leftB = (r - 2) / 2`, arity-general. -/
def leftBTA {arity : Nat} (dT kT : Term arity .nat) : Term arity .nat :=
  .div (.sub (rTA dT kT) (.natLit 2)) (.natLit 2)
/-- `leftCell` guard, arity-general. -/
def leftCellGuardTA {arity : Nat} (dT kT : Term arity .nat) : Term arity .bool :=
  band3 (.eqNat (cTA dT kT) (.natLit 0))
    (.eqNat (rTA dT kT) (.add (.mul (.natLit 2) (leftBTA dT kT)) (.natLit 2)))
    (.ltNat (leftBTA dT kT) (recInnerHalfTA dT))

/-- `bottomB = (c - 2) / 2`, arity-general. -/
def bottomBTA {arity : Nat} (dT kT : Term arity .nat) : Term arity .nat :=
  .div (.sub (cTA dT kT) (.natLit 2)) (.natLit 2)
/-- `bottomCell` guard, arity-general. -/
def bottomCellGuardTA {arity : Nat} (dT kT : Term arity .nat) : Term arity .bool :=
  band3 (.eqNat (rTA dT kT) (lastCellTA dT))
    (.eqNat (cTA dT kT) (.add (.mul (.natLit 2) (bottomBTA dT kT)) (.natLit 2)))
    (.ltNat (bottomBTA dT kT) (recInnerHalfTA dT))

/-- Inner stabilizer index the top cell promotes to, arity-general. -/
def topKTA {arity : Nat} (dT kT : Term arity .nat) : Term arity .nat :=
  .add (recInnerBulkTA dT) (topBTA dT kT)
/-- Inner stabilizer index the right cell promotes to, arity-general. -/
def rightKTA {arity : Nat} (dT kT : Term arity .nat) : Term arity .nat :=
  .add (recInnerBulkTA dT) (.add (recInnerHalfTA dT) (rightBTA dT kT))
/-- Inner stabilizer index the left cell promotes to, arity-general. -/
def leftKTA {arity : Nat} (dT kT : Term arity .nat) : Term arity .nat :=
  .add (recInnerBulkTA dT) (.add (.mul (.natLit 2) (recInnerHalfTA dT)) (leftBTA dT kT))
/-- Inner stabilizer index the bottom cell promotes to, arity-general. -/
def bottomKTA {arity : Nat} (dT kT : Term arity .nat) : Term arity .nat :=
  .add (recInnerBulkTA dT) (.add (.mul (.natLit 3) (recInnerHalfTA dT)) (bottomBTA dT kT))

/-- The inner-code reference produced by a promoted-boundary cell with inner
stabilizer index `oldKT`, arity-general: `stabAt (recCall (d-2) oldK) innerQ`.
Note `innerQTA` is exactly the `innerQ` of `promotedBoundaryEntry`. -/
def promotedInnerRefA {arity : Nat} (dT qT oldKT : Term arity .nat) : Term arity .pauli :=
  .stabAt (.recCall (recInnerDTA dT) oldKT) (innerQTA dT qT)

/-! ### Shared post-`simp` guard rewrites, arity-general

The cell guards in their post-`simp` forms (matching what the `simp only` in each
peel exposes) are shared across the inner-reference peels.  Factoring them keeps
each peel small. -/

private theorem interiorCellGuardTA_simp {arity : Nat} (dT kT : Term arity .nat) :
    interiorCellGuardTA dT kT
      = ((Term.natLit 1).leNat (kT.div (dT.sub (Term.natLit 1)))).and
          (((kT.div (dT.sub (Term.natLit 1))).ltNat ((dT.sub (Term.natLit 1)).sub (Term.natLit 1))).and
            (((Term.natLit 1).leNat (kT.mod (dT.sub (Term.natLit 1)))).and
              ((kT.mod (dT.sub (Term.natLit 1))).ltNat ((dT.sub (Term.natLit 1)).sub (Term.natLit 1))))) := by
  simp only [interiorCellGuardTA, band4, band3, le, rTA, cTA, lastCellTA, dm1TA]

private theorem insideGuardTA_simp {arity : Nat} (dT qT : Term arity .nat) :
    insideGuardTA dT qT
      = ((Term.natLit 1).leNat (qT.div dT)).and
          (((qT.div dT).ltNat (dT.sub (Term.natLit 1))).and
            (((Term.natLit 1).leNat (qT.mod dT)).and
              ((qT.mod dT).ltNat (dT.sub (Term.natLit 1))))) := by
  simp only [insideGuardTA, band4, band3, le, rowTA, colTA, dm1TA]

private theorem topCellGuardTA_simp {arity : Nat} (dT kT : Term arity .nat) :
    topCellGuardTA dT kT
      = (((kT.div (dT.sub (Term.natLit 1))).eqNat (Term.natLit 0)).and
          ((((kT.mod (dT.sub (Term.natLit 1))).eqNat
                (((Term.natLit 2).mul
                      (((kT.mod (dT.sub (Term.natLit 1))).sub (Term.natLit 1)).div (Term.natLit 2))).add
                  (Term.natLit 1)))).and
            ((((kT.mod (dT.sub (Term.natLit 1))).sub (Term.natLit 1)).div (Term.natLit 2)).ltNat
              (((dT.sub (Term.natLit 2)).sub (Term.natLit 1)).div (Term.natLit 2))))) := by
  simp only [topCellGuardTA, band3, topBTA, rTA, cTA, recInnerHalfTA, recInnerDm1TA,
    innerDm1TA, innerDTA, dm1TA]

private theorem rightCellGuardTA_simp {arity : Nat} (dT kT : Term arity .nat) :
    rightCellGuardTA dT kT
      = (((kT.mod (dT.sub (Term.natLit 1))).eqNat ((dT.sub (Term.natLit 1)).sub (Term.natLit 1))).and
          ((((kT.div (dT.sub (Term.natLit 1))).eqNat
                (((Term.natLit 2).mul
                      (((kT.div (dT.sub (Term.natLit 1))).sub (Term.natLit 1)).div (Term.natLit 2))).add
                  (Term.natLit 1)))).and
            ((((kT.div (dT.sub (Term.natLit 1))).sub (Term.natLit 1)).div (Term.natLit 2)).ltNat
              (((dT.sub (Term.natLit 2)).sub (Term.natLit 1)).div (Term.natLit 2))))) := by
  simp only [rightCellGuardTA, band3, rightBTA, rTA, cTA, lastCellTA, recInnerHalfTA, recInnerDm1TA,
    innerDm1TA, innerDTA, dm1TA]

private theorem leftCellGuardTA_simp {arity : Nat} (dT kT : Term arity .nat) :
    leftCellGuardTA dT kT
      = (((kT.mod (dT.sub (Term.natLit 1))).eqNat (Term.natLit 0)).and
          ((((kT.div (dT.sub (Term.natLit 1))).eqNat
                (((Term.natLit 2).mul
                      (((kT.div (dT.sub (Term.natLit 1))).sub (Term.natLit 2)).div (Term.natLit 2))).add
                  (Term.natLit 2)))).and
            ((((kT.div (dT.sub (Term.natLit 1))).sub (Term.natLit 2)).div (Term.natLit 2)).ltNat
              (((dT.sub (Term.natLit 2)).sub (Term.natLit 1)).div (Term.natLit 2))))) := by
  simp only [leftCellGuardTA, band3, leftBTA, rTA, cTA, recInnerHalfTA, recInnerDm1TA,
    innerDm1TA, innerDTA, dm1TA]

private theorem bottomCellGuardTA_simp {arity : Nat} (dT kT : Term arity .nat) :
    bottomCellGuardTA dT kT
      = (((kT.div (dT.sub (Term.natLit 1))).eqNat ((dT.sub (Term.natLit 1)).sub (Term.natLit 1))).and
          ((((kT.mod (dT.sub (Term.natLit 1))).eqNat
                (((Term.natLit 2).mul
                      (((kT.mod (dT.sub (Term.natLit 1))).sub (Term.natLit 2)).div (Term.natLit 2))).add
                  (Term.natLit 2)))).and
            ((((kT.mod (dT.sub (Term.natLit 1))).sub (Term.natLit 2)).div (Term.natLit 2)).ltNat
              (((dT.sub (Term.natLit 2)).sub (Term.natLit 1)).div (Term.natLit 2))))) := by
  simp only [bottomCellGuardTA, band3, bottomBTA, rTA, cTA, lastCellTA, recInnerHalfTA,
    recInnerDm1TA, innerDm1TA, innerDTA, dm1TA]

/-! ## Arity-general promoted-boundary inner peels (`inside` holds)

Each peel selects the outer `bulk` branch (TRUE), then `interiorCell` (FALSE),
then the appropriate sequence of `*Cell` selections to reach the cell's
`promotedBoundaryEntry`, then `inside` (TRUE), landing on the inner-code reference
`promotedInnerRefA dT qT ({top,right,left,bottom}KTA dT kT)`.  These port the
keystone's arity-0 `rec{Top,Right,Left,Bottom}PromotedInnerPeel` to arity ≥ 1.

The guards are NOT assumed unconditionally — they are explicit premises, true only
in the matching `boolCases` branch when `kT`/`qT` are symbolic.  Nothing asserts
the entry Pauli of the conclusion. -/

/-- Shared step 1+2 (arity-general): strip `stabLam`, select `bulk` (TRUE), push
the qubit instantiation through the residual `ite` tree. -/
private def promotedBulkSelectA {fuel arity : Nat} (dT kT qT : Term arity .nat)
    (_hq : SFormula.PureNatTerm qT)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool
        (SC.closed (Term.instantiateTopNat qT
          (.ltNat (Term.lift 0 kT)
            (.mul (.sub (Term.lift 0 dT) (.natLit 1)) (.sub (Term.lift 0 dT) (.natLit 1))))))
        (SC.b true)) := by
  have heq : Term.instantiateTopNat qT
      (Term.ltNat (Term.lift 0 kT)
        (.mul (.sub (Term.lift 0 dT) (.natLit 1)) (.sub (Term.lift 0 dT) (.natLit 1))))
      = bulkGuardTA dT kT := by
    simp only [bulkGuardTA, bulkCountTA, dm1TA, Term.instantiateTopNat, Term.instantiateNatAt,
      instTop_lift]
  rw [heq]; exact hBulk

/-- **Arity-general top-cell promoted-boundary inner peel.** -/
def recTopPromotedInnerPeelA {fuel arity : Nat} (dT kT qT : Term arity .nat)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b true)))
    (hInside : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt
          (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed qT))
        (SC.closed (promotedInnerRefA dT qT (topKTA dT kT)))) := by
  simp only [SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
    SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q,
    codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4, orEqSucc, le]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (pureStabAtClosedIteLamThen (fuel := fuel) _ _ _ qT hq
      (promotedBulkSelectA dT kT qT hq hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← interiorCellGuardTA_simp]; exact hInterior))
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← topCellGuardTA_simp]; exact hTop))
      (PureFamilyDerivA.eqPauliTrans _ _ _
        (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← insideGuardTA_simp]; exact hInside))
        (PureFamilyDerivA.eqPauliRefl _)))

#print axioms recTopPromotedInnerPeelA

/-- **Arity-general right-cell promoted-boundary inner peel.** -/
def recRightPromotedInnerPeelA {fuel arity : Nat} (dT kT qT : Term arity .nat)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b false)))
    (hRight : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (rightCellGuardTA dT kT)) (SC.b true)))
    (hInside : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt
          (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed qT))
        (SC.closed (promotedInnerRefA dT qT (rightKTA dT kT)))) := by
  simp only [SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
    SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q,
    codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4, orEqSucc, le]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (pureStabAtClosedIteLamThen (fuel := fuel) _ _ _ qT hq
      (promotedBulkSelectA dT kT qT hq hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← interiorCellGuardTA_simp]; exact hInterior))
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← topCellGuardTA_simp]; exact hTop))
      (PureFamilyDerivA.eqPauliTrans _ _ _
        (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← rightCellGuardTA_simp]; exact hRight))
        (PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← insideGuardTA_simp]; exact hInside))
          (PureFamilyDerivA.eqPauliRefl _))))

#print axioms recRightPromotedInnerPeelA

/-- **Arity-general left-cell promoted-boundary inner peel.** -/
def recLeftPromotedInnerPeelA {fuel arity : Nat} (dT kT qT : Term arity .nat)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b false)))
    (hRight : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (rightCellGuardTA dT kT)) (SC.b false)))
    (hLeft : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (leftCellGuardTA dT kT)) (SC.b true)))
    (hInside : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt
          (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed qT))
        (SC.closed (promotedInnerRefA dT qT (leftKTA dT kT)))) := by
  simp only [SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
    SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q,
    codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4, orEqSucc, le]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (pureStabAtClosedIteLamThen (fuel := fuel) _ _ _ qT hq
      (promotedBulkSelectA dT kT qT hq hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← interiorCellGuardTA_simp]; exact hInterior))
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← topCellGuardTA_simp]; exact hTop))
      (PureFamilyDerivA.eqPauliTrans _ _ _
        (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← rightCellGuardTA_simp]; exact hRight))
        (PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← leftCellGuardTA_simp]; exact hLeft))
          (PureFamilyDerivA.eqPauliTrans _ _ _
            (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← insideGuardTA_simp]; exact hInside))
            (PureFamilyDerivA.eqPauliRefl _)))))

#print axioms recLeftPromotedInnerPeelA

/-- **Arity-general bottom-cell promoted-boundary inner peel.** -/
def recBottomPromotedInnerPeelA {fuel arity : Nat} (dT kT qT : Term arity .nat)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b false)))
    (hRight : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (rightCellGuardTA dT kT)) (SC.b false)))
    (hLeft : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (leftCellGuardTA dT kT)) (SC.b false)))
    (hBottom : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bottomCellGuardTA dT kT)) (SC.b true)))
    (hInside : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt
          (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed qT))
        (SC.closed (promotedInnerRefA dT qT (bottomKTA dT kT)))) := by
  simp only [SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
    SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q,
    codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4, orEqSucc, le]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (pureStabAtClosedIteLamThen (fuel := fuel) _ _ _ qT hq
      (promotedBulkSelectA dT kT qT hq hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← interiorCellGuardTA_simp]; exact hInterior))
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← topCellGuardTA_simp]; exact hTop))
      (PureFamilyDerivA.eqPauliTrans _ _ _
        (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← rightCellGuardTA_simp]; exact hRight))
        (PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← leftCellGuardTA_simp]; exact hLeft))
          (PureFamilyDerivA.eqPauliTrans _ _ _
            (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← bottomCellGuardTA_simp]; exact hBottom))
            (PureFamilyDerivA.eqPauliTrans _ _ _
              (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← insideGuardTA_simp]; exact hInside))
              (PureFamilyDerivA.eqPauliRefl _))))))

#print axioms recBottomPromotedInnerPeelA

/-! ## Purity certificates for the promoted inner indices

To thread the inductive hypothesis through the promoted `_withIH` row steps a
recursion must supply `SFormula.PureNatTerm` certificates for each promoted inner
stabilizer index (`topKTA` / `rightKTA` / `leftKTA` / `bottomKTA`).  These follow
purely from the purity of `dT`, `kT` (no value information), so they hold at a
**symbolic** index. -/

private def recInnerHalfTA_pure {arity : Nat} {dT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) : SFormula.PureNatTerm (recInnerHalfTA dT) :=
  SFormula.PureNatTerm.div
    (SFormula.PureNatTerm.sub (SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 2))
      (SFormula.PureNatTerm.nat 1))
    (SFormula.PureNatTerm.nat 2)

private def recInnerBulkTA_pure {arity : Nat} {dT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) : SFormula.PureNatTerm (recInnerBulkTA dT) :=
  SFormula.PureNatTerm.mul
    (SFormula.PureNatTerm.sub (SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 2))
      (SFormula.PureNatTerm.nat 1))
    (SFormula.PureNatTerm.sub (SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 2))
      (SFormula.PureNatTerm.nat 1))

def topKTA_pure {arity : Nat} {dT kT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureNatTerm (topKTA dT kT) :=
  SFormula.PureNatTerm.add (recInnerBulkTA_pure hd)
    (SFormula.PureNatTerm.div
      (SFormula.PureNatTerm.sub
        (SFormula.PureNatTerm.mod hk (SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 1)))
        (SFormula.PureNatTerm.nat 1))
      (SFormula.PureNatTerm.nat 2))

def rightKTA_pure {arity : Nat} {dT kT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureNatTerm (rightKTA dT kT) :=
  SFormula.PureNatTerm.add (recInnerBulkTA_pure hd)
    (SFormula.PureNatTerm.add (recInnerHalfTA_pure hd)
      (SFormula.PureNatTerm.div
        (SFormula.PureNatTerm.sub
          (SFormula.PureNatTerm.div hk (SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 1)))
          (SFormula.PureNatTerm.nat 1))
        (SFormula.PureNatTerm.nat 2)))

def leftKTA_pure {arity : Nat} {dT kT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureNatTerm (leftKTA dT kT) :=
  SFormula.PureNatTerm.add (recInnerBulkTA_pure hd)
    (SFormula.PureNatTerm.add
      (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 2) (recInnerHalfTA_pure hd))
      (SFormula.PureNatTerm.div
        (SFormula.PureNatTerm.sub
          (SFormula.PureNatTerm.div hk (SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 1)))
          (SFormula.PureNatTerm.nat 2))
        (SFormula.PureNatTerm.nat 2)))

def bottomKTA_pure {arity : Nat} {dT kT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureNatTerm (bottomKTA dT kT) :=
  SFormula.PureNatTerm.add (recInnerBulkTA_pure hd)
    (SFormula.PureNatTerm.add
      (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 3) (recInnerHalfTA_pure hd))
      (SFormula.PureNatTerm.div
        (SFormula.PureNatTerm.sub
          (SFormula.PureNatTerm.mod hk (SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 1)))
          (SFormula.PureNatTerm.nat 2))
        (SFormula.PureNatTerm.nat 2)))

#print axioms topKTA_pure
#print axioms rightKTA_pure
#print axioms leftKTA_pure
#print axioms bottomKTA_pure

/-! ## Arity-general promoted-boundary row steps with the IH applied

The shape an `OddSurfaceDistance.index` recursion consumes for a promoted-boundary
cell at a symbolic index: compose the recursive-branch row selection
(`surfaceCodeRecursiveEntryEq`, distance guard `dT < 5` FALSE) with the arity-
general promoted inner peel and a *supplied* resolution `ih` of the inner-code
reference `promotedInnerRefA dT qT ({…}KTA dT kT)` to a leaf `p` (the IH one layer
down, at the symbolic inner index).  These port the keystone's arity-0
`rec{Top,Right,Left,Bottom}PromotedRow_withIH` to arity ≥ 1.  Unconditional: only
purity certs and the explicit guard / IH derivations; nothing asserts the entry
Pauli of the conclusion. -/

def recTopPromotedRowA_withIH {fuel arity : Nat} (n : STerm arity .nat)
    (dT kT qT : Term arity .nat) (p : Term arity .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hDist : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat dT (n5 : Term arity .nat))) (SC.b false)))
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b true)))
    (hInside : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b true)))
    (ih : PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (SC.closed (promotedInnerRefA dT qT (topKTA dT kT))) (SC.closed p))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (.stabAt (SC.closed (.recCall dT kT)) (SC.closed qT)) (SC.closed p)) :=
  surfaceCodeRecursiveEntryEq n dT kT qT p hd hk hDist
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (recTopPromotedInnerPeelA dT kT qT hq hBulk hInterior hTop hInside) ih)

def recRightPromotedRowA_withIH {fuel arity : Nat} (n : STerm arity .nat)
    (dT kT qT : Term arity .nat) (p : Term arity .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hDist : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat dT (n5 : Term arity .nat))) (SC.b false)))
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b false)))
    (hRight : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (rightCellGuardTA dT kT)) (SC.b true)))
    (hInside : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b true)))
    (ih : PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (SC.closed (promotedInnerRefA dT qT (rightKTA dT kT))) (SC.closed p))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (.stabAt (SC.closed (.recCall dT kT)) (SC.closed qT)) (SC.closed p)) :=
  surfaceCodeRecursiveEntryEq n dT kT qT p hd hk hDist
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (recRightPromotedInnerPeelA dT kT qT hq hBulk hInterior hTop hRight hInside) ih)

def recLeftPromotedRowA_withIH {fuel arity : Nat} (n : STerm arity .nat)
    (dT kT qT : Term arity .nat) (p : Term arity .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hDist : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat dT (n5 : Term arity .nat))) (SC.b false)))
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b false)))
    (hRight : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (rightCellGuardTA dT kT)) (SC.b false)))
    (hLeft : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (leftCellGuardTA dT kT)) (SC.b true)))
    (hInside : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b true)))
    (ih : PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (SC.closed (promotedInnerRefA dT qT (leftKTA dT kT))) (SC.closed p))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (.stabAt (SC.closed (.recCall dT kT)) (SC.closed qT)) (SC.closed p)) :=
  surfaceCodeRecursiveEntryEq n dT kT qT p hd hk hDist
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (recLeftPromotedInnerPeelA dT kT qT hq hBulk hInterior hTop hRight hLeft hInside) ih)

def recBottomPromotedRowA_withIH {fuel arity : Nat} (n : STerm arity .nat)
    (dT kT qT : Term arity .nat) (p : Term arity .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hDist : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat dT (n5 : Term arity .nat))) (SC.b false)))
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b false)))
    (hRight : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (rightCellGuardTA dT kT)) (SC.b false)))
    (hLeft : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (leftCellGuardTA dT kT)) (SC.b false)))
    (hBottom : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bottomCellGuardTA dT kT)) (SC.b true)))
    (hInside : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b true)))
    (ih : PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (SC.closed (promotedInnerRefA dT qT (bottomKTA dT kT))) (SC.closed p))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (.stabAt (SC.closed (.recCall dT kT)) (SC.closed qT)) (SC.closed p)) :=
  surfaceCodeRecursiveEntryEq n dT kT qT p hd hk hDist
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (recBottomPromotedInnerPeelA dT kT qT hq hBulk hInterior hTop hRight hLeft hBottom hInside) ih)

#print axioms recTopPromotedRowA_withIH
#print axioms recRightPromotedRowA_withIH
#print axioms recLeftPromotedRowA_withIH
#print axioms recBottomPromotedRowA_withIH

/-! ## Arity-general base-entry (NON-recursing) cell guards and peels

For a *base* (`d = 3`) row, or for a `d ≥ 5` row whose non-recursing fallback
selects `baseEntry`, the entry is resolved by the same per-cell peels the Grid
file built at arity 0.  These guards and peels are their arity-general restatements,
mirroring `SurfaceRowCharacterizationGrid`'s arity-0 `recTopXPeel` / `recBasePeelX`
/ … (and the four out-of-band `→ I` complements from
`SurfaceRowCharacterizationUnconditional`), in the style of `recInteriorPeelA`. -/

/-- The bulk-band guard of `baseEntry`, arity-general. -/
def baseBulkBandGuardTA {arity : Nat} (dT kT qT : Term arity .nat) : Term arity .bool :=
  band3
    (orEqSucc (.div qT dT) (.div kT (dm1TA dT)))
    (orEqSucc (.mod qT dT) (.mod kT (dm1TA dT)))
    (.ltNat kT (bulkCountTA dT))

/-- The plaquette-kind guard of `baseEntry`, arity-general. -/
def baseKindGuardTA {arity : Nat} (dT kT : Term arity .nat) : Term arity .bool :=
  .eqNat (.mod (.add (.div kT (dm1TA dT)) (.mod kT (dm1TA dT))) (.natLit 2)) (.natLit 0)

/-- The boundary offset `b = k - bulkCount`, arity-general. -/
def baseBTA {arity : Nat} (dT kT : Term arity .nat) : Term arity .nat :=
  .sub kT (bulkCountTA dT)
/-- The strip half-width `half = (d-1)/2`, arity-general. -/
def baseHalfTA {arity : Nat} (dT : Term arity .nat) : Term arity .nat :=
  .div (dm1TA dT) (.natLit 2)

/-- Top-`X` classifier `b < half`, arity-general. -/
def topClassGuardTA {arity : Nat} (dT kT : Term arity .nat) : Term arity .bool :=
  .ltNat (baseBTA dT kT) (baseHalfTA dT)
/-- Right-`Z` classifier `b < 2·half`, arity-general. -/
def rightClassGuardTA {arity : Nat} (dT kT : Term arity .nat) : Term arity .bool :=
  .ltNat (baseBTA dT kT) (.mul (.natLit 2) (baseHalfTA dT))
/-- Left-`Z` classifier `b < 3·half`, arity-general. -/
def leftClassGuardTA {arity : Nat} (dT kT : Term arity .nat) : Term arity .bool :=
  .ltNat (baseBTA dT kT) (.mul (.natLit 3) (baseHalfTA dT))

/-- Top-`X` band, arity-general. -/
def topBandGuardTA {arity : Nat} (dT kT qT : Term arity .nat) : Term arity .bool :=
  band3 (.ltNat kT (.sub (.mul dT dT) (.natLit 1)))
    (.eqNat (.div qT dT) (.natLit 0))
    (orEqSucc (.mod qT dT) (.mul (.natLit 2) (baseBTA dT kT)))
/-- Right-`Z` band, arity-general. -/
def rightBandGuardTA {arity : Nat} (dT kT qT : Term arity .nat) : Term arity .bool :=
  .and (.eqNat (.mod qT dT) (dm1TA dT))
    (orEqSucc (.div qT dT) (.mul (.natLit 2) (.sub (baseBTA dT kT) (baseHalfTA dT))))
/-- Left-`Z` band, arity-general. -/
def leftBandGuardTA {arity : Nat} (dT kT qT : Term arity .nat) : Term arity .bool :=
  .and (.eqNat (.mod qT dT) (.natLit 0))
    (orEqPair (.div qT dT)
      (.add (.mul (.natLit 2) (.sub (baseBTA dT kT) (.mul (.natLit 2) (baseHalfTA dT)))) (.natLit 1))
      (.add (.mul (.natLit 2) (.sub (baseBTA dT kT) (.mul (.natLit 2) (baseHalfTA dT)))) (.natLit 2)))
/-- Bottom-`X` band, arity-general. -/
def bottomBandGuardTA {arity : Nat} (dT kT qT : Term arity .nat) : Term arity .bool :=
  .and (.eqNat (.div qT dT) (dm1TA dT))
    (orEqPair (.mod qT dT)
      (.add (.mul (.natLit 2) (.sub (baseBTA dT kT) (.mul (.natLit 3) (baseHalfTA dT)))) (.natLit 1))
      (.add (.mul (.natLit 2) (.sub (baseBTA dT kT) (.mul (.natLit 3) (baseHalfTA dT)))) (.natLit 2)))

/-! ### Shared post-`simp` base-guard rewrites, arity-general. -/

private theorem baseBulkBandGuardTA_simp {arity : Nat} (dT kT qT : Term arity .nat) :
    baseBulkBandGuardTA dT kT qT
      = ((((qT.div dT).eqNat (kT.div (dT.sub (Term.natLit 1)))).or
              ((qT.div dT).eqNat ((kT.div (dT.sub (Term.natLit 1))).add (Term.natLit 1)))).and
          ((((qT.mod dT).eqNat (kT.mod (dT.sub (Term.natLit 1)))).or
                ((qT.mod dT).eqNat ((kT.mod (dT.sub (Term.natLit 1))).add (Term.natLit 1)))).and
            (kT.ltNat ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))))) := by
  simp only [baseBulkBandGuardTA, band3, orEqSucc, bulkCountTA, dm1TA]

private theorem baseKindGuardTA_simp {arity : Nat} (dT kT : Term arity .nat) :
    baseKindGuardTA dT kT
      = (((kT.div (dT.sub (Term.natLit 1))).add (kT.mod (dT.sub (Term.natLit 1)))).mod
            (Term.natLit 2)).eqNat (Term.natLit 0) := by
  simp only [baseKindGuardTA, dm1TA]

private theorem topClassGuardTA_simp {arity : Nat} (dT kT : Term arity .nat) :
    topClassGuardTA dT kT
      = (kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))).ltNat
          ((dT.sub (Term.natLit 1)).div (Term.natLit 2)) := by
  simp only [topClassGuardTA, baseBTA, baseHalfTA, bulkCountTA, dm1TA]

private theorem rightClassGuardTA_simp {arity : Nat} (dT kT : Term arity .nat) :
    rightClassGuardTA dT kT
      = (kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))).ltNat
          ((Term.natLit 2).mul ((dT.sub (Term.natLit 1)).div (Term.natLit 2))) := by
  simp only [rightClassGuardTA, baseBTA, baseHalfTA, bulkCountTA, dm1TA]

private theorem leftClassGuardTA_simp {arity : Nat} (dT kT : Term arity .nat) :
    leftClassGuardTA dT kT
      = (kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))).ltNat
          ((Term.natLit 3).mul ((dT.sub (Term.natLit 1)).div (Term.natLit 2))) := by
  simp only [leftClassGuardTA, baseBTA, baseHalfTA, bulkCountTA, dm1TA]

private theorem topBandGuardTA_simp {arity : Nat} (dT kT qT : Term arity .nat) :
    topBandGuardTA dT kT qT
      = (kT.ltNat ((dT.mul dT).sub (Term.natLit 1))).and
          (((qT.div dT).eqNat (Term.natLit 0)).and
            (((qT.mod dT).eqNat ((Term.natLit 2).mul (kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))))).or
              ((qT.mod dT).eqNat (((Term.natLit 2).mul (kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1))))).add (Term.natLit 1))))) := by
  simp only [topBandGuardTA, baseBTA, band3, orEqSucc, bulkCountTA, dm1TA]

private theorem rightBandGuardTA_simp {arity : Nat} (dT kT qT : Term arity .nat) :
    rightBandGuardTA dT kT qT
      = ((qT.mod dT).eqNat (dT.sub (Term.natLit 1))).and
          (((qT.div dT).eqNat ((Term.natLit 2).mul ((kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))).sub ((dT.sub (Term.natLit 1)).div (Term.natLit 2))))).or
            ((qT.div dT).eqNat (((Term.natLit 2).mul ((kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))).sub ((dT.sub (Term.natLit 1)).div (Term.natLit 2)))).add (Term.natLit 1)))) := by
  simp only [rightBandGuardTA, baseBTA, baseHalfTA, orEqSucc, bulkCountTA, dm1TA]

private theorem leftBandGuardTA_simp {arity : Nat} (dT kT qT : Term arity .nat) :
    leftBandGuardTA dT kT qT
      = ((qT.mod dT).eqNat (Term.natLit 0)).and
          (((qT.div dT).eqNat (((Term.natLit 2).mul ((kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))).sub ((Term.natLit 2).mul ((dT.sub (Term.natLit 1)).div (Term.natLit 2))))).add (Term.natLit 1))).or
            ((qT.div dT).eqNat (((Term.natLit 2).mul ((kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))).sub ((Term.natLit 2).mul ((dT.sub (Term.natLit 1)).div (Term.natLit 2))))).add (Term.natLit 2)))) := by
  simp only [leftBandGuardTA, baseBTA, baseHalfTA, orEqPair, bulkCountTA, dm1TA]

private theorem bottomBandGuardTA_simp {arity : Nat} (dT kT qT : Term arity .nat) :
    bottomBandGuardTA dT kT qT
      = ((qT.div dT).eqNat (dT.sub (Term.natLit 1))).and
          (((qT.mod dT).eqNat (((Term.natLit 2).mul ((kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))).sub ((Term.natLit 3).mul ((dT.sub (Term.natLit 1)).div (Term.natLit 2))))).add (Term.natLit 1))).or
            ((qT.mod dT).eqNat (((Term.natLit 2).mul ((kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))).sub ((Term.natLit 3).mul ((dT.sub (Term.natLit 1)).div (Term.natLit 2))))).add (Term.natLit 2)))) := by
  simp only [bottomBandGuardTA, baseBTA, baseHalfTA, orEqPair, bulkCountTA, dm1TA]

/-- Shared step 1 (arity-general): strip `stabLam`, select the outer bulk branch
(TRUE), pushing the qubit instantiation through.  Same as `promotedBulkSelectA`
but produces the form the base peels consume. -/
private def baseBulkSelectTrueA {fuel arity : Nat} (dT kT qT : Term arity .nat)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool
        (SC.closed (Term.instantiateTopNat qT
          (.ltNat (Term.lift 0 kT)
            (.mul (.sub (Term.lift 0 dT) (.natLit 1)) (.sub (Term.lift 0 dT) (.natLit 1))))))
        (SC.b true)) := by
  have heq : Term.instantiateTopNat qT
      (Term.ltNat (Term.lift 0 kT)
        (.mul (.sub (Term.lift 0 dT) (.natLit 1)) (.sub (Term.lift 0 dT) (.natLit 1))))
      = bulkGuardTA dT kT := by
    simp only [bulkGuardTA, bulkCountTA, dm1TA, Term.instantiateTopNat, Term.instantiateNatAt,
      instTop_lift]
  rw [heq]; exact hBulk

/-- Shared step 1 (arity-general): strip `stabLam`, select the outer bulk branch
(FALSE), pushing the qubit instantiation through. -/
private def baseBulkSelectFalseA {fuel arity : Nat} (dT kT qT : Term arity .nat)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool
        (SC.closed (Term.instantiateTopNat qT
          (.ltNat (Term.lift 0 kT)
            (.mul (.sub (Term.lift 0 dT) (.natLit 1)) (.sub (Term.lift 0 dT) (.natLit 1))))))
        (SC.b false)) := by
  have heq : Term.instantiateTopNat qT
      (Term.ltNat (Term.lift 0 kT)
        (.mul (.sub (Term.lift 0 dT) (.natLit 1)) (.sub (Term.lift 0 dT) (.natLit 1))))
      = bulkGuardTA dT kT := by
    simp only [bulkGuardTA, bulkCountTA, dm1TA, Term.instantiateTopNat, Term.instantiateNatAt,
      instTop_lift]
  rw [heq]; exact hBulk

/-- **Arity-general bulk `Z`-plaquette base peel.** -/
def recBasePeelA {fuel arity : Nat} (dT kT qT : Term arity .nat)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hBand : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)))
    (hKind : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.baseEntry)))
          (SC.closed qT))
        (SC.closed (.pauliLit Pauli.Z))) := by
  simp only [SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
    SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN,
    Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, orEqSucc, orEqPair]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (pureStabAtClosedIteLamThen (fuel := fuel) _ _ _ qT hq (baseBulkSelectTrueA dT kT qT hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← baseBulkBandGuardTA_simp]; exact hBand))
    (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← baseKindGuardTA_simp]; exact hKind))

#print axioms recBasePeelA

/-- **Arity-general bulk `X`-plaquette base peel.** -/
def recBasePeelXA {fuel arity : Nat} (dT kT qT : Term arity .nat)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hBand : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)))
    (hKind : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b false))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.baseEntry)))
          (SC.closed qT))
        (SC.closed (.pauliLit Pauli.X))) := by
  simp only [SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
    SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN,
    Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, orEqSucc, orEqPair]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (pureStabAtClosedIteLamThen (fuel := fuel) _ _ _ qT hq (baseBulkSelectTrueA dT kT qT hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← baseBulkBandGuardTA_simp]; exact hBand))
    (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← baseKindGuardTA_simp]; exact hKind))

#print axioms recBasePeelXA

/-- **Arity-general bulk out-of-plaquette base peel (`→ I`).** -/
def recBasePeelIA {fuel arity : Nat} (dT kT qT : Term arity .nat)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hBand : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.baseEntry)))
          (SC.closed qT))
        (SC.closed (.pauliLit Pauli.I))) := by
  simp only [SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
    SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN,
    Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, orEqSucc, orEqPair]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (pureStabAtClosedIteLamThen (fuel := fuel) _ _ _ qT hq (baseBulkSelectTrueA dT kT qT hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]
  exact PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← baseBulkBandGuardTA_simp]; exact hBand)

#print axioms recBasePeelIA

/-- **Arity-general top-`X` boundary base peel (in band).** -/
def recTopXPeelA {fuel arity : Nat} (dT kT qT : Term arity .nat)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b true)))
    (hTopBand : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topBandGuardTA dT kT qT)) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.baseEntry)))
          (SC.closed qT))
        (SC.closed (.pauliLit Pauli.X))) := by
  simp only [SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
    SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN,
    Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, orEqSucc, orEqPair]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (pureStabAtClosedIteLamElse (fuel := fuel) _ _ _ qT hq (baseBulkSelectFalseA dT kT qT hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift,
    Nat.lt_irrefl, dite_false, dite_true]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← topClassGuardTA_simp]; exact hTopClass))
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← topBandGuardTA_simp]; exact hTopBand))
      (PureFamilyDerivA.eqPauliRefl _))

#print axioms recTopXPeelA

/-- **Arity-general top boundary out-of-band base peel (`→ I`).** -/
def recTopIPeelA {fuel arity : Nat} (dT kT qT : Term arity .nat)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b true)))
    (hTopBand : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topBandGuardTA dT kT qT)) (SC.b false))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.baseEntry)))
          (SC.closed qT))
        (SC.closed (.pauliLit Pauli.I))) := by
  simp only [SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
    SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN,
    Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, orEqSucc, orEqPair]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (pureStabAtClosedIteLamElse (fuel := fuel) _ _ _ qT hq (baseBulkSelectFalseA dT kT qT hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift,
    Nat.lt_irrefl, dite_false, dite_true]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← topClassGuardTA_simp]; exact hTopClass))
    (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← topBandGuardTA_simp]; exact hTopBand))

#print axioms recTopIPeelA

/-- **Arity-general right-`Z` boundary base peel (in band).** -/
def recRightZPeelA {fuel arity : Nat} (dT kT qT : Term arity .nat)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false)))
    (hRightClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b true)))
    (hRightBand : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (rightBandGuardTA dT kT qT)) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.baseEntry)))
          (SC.closed qT))
        (SC.closed (.pauliLit Pauli.Z))) := by
  simp only [SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
    SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN,
    Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, orEqSucc, orEqPair]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (pureStabAtClosedIteLamElse (fuel := fuel) _ _ _ qT hq (baseBulkSelectFalseA dT kT qT hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift,
    Nat.lt_irrefl, dite_false, dite_true]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← topClassGuardTA_simp]; exact hTopClass))
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← rightClassGuardTA_simp]; exact hRightClass))
      (PureFamilyDerivA.eqPauliTrans _ _ _
        (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← rightBandGuardTA_simp]; exact hRightBand))
        (PureFamilyDerivA.eqPauliRefl _)))

#print axioms recRightZPeelA

/-- **Arity-general right boundary out-of-band base peel (`→ I`).** -/
def recRightIPeelA {fuel arity : Nat} (dT kT qT : Term arity .nat)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false)))
    (hRightClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b true)))
    (hRightBand : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (rightBandGuardTA dT kT qT)) (SC.b false))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.baseEntry)))
          (SC.closed qT))
        (SC.closed (.pauliLit Pauli.I))) := by
  simp only [SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
    SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN,
    Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, orEqSucc, orEqPair]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (pureStabAtClosedIteLamElse (fuel := fuel) _ _ _ qT hq (baseBulkSelectFalseA dT kT qT hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift,
    Nat.lt_irrefl, dite_false, dite_true]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← topClassGuardTA_simp]; exact hTopClass))
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← rightClassGuardTA_simp]; exact hRightClass))
      (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← rightBandGuardTA_simp]; exact hRightBand)))

#print axioms recRightIPeelA

/-- **Arity-general left-`Z` boundary base peel (in band).** -/
def recLeftZPeelA {fuel arity : Nat} (dT kT qT : Term arity .nat)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false)))
    (hRightClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b false)))
    (hLeftClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (leftClassGuardTA dT kT)) (SC.b true)))
    (hLeftBand : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (leftBandGuardTA dT kT qT)) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.baseEntry)))
          (SC.closed qT))
        (SC.closed (.pauliLit Pauli.Z))) := by
  simp only [SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
    SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN,
    Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, orEqSucc, orEqPair]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (pureStabAtClosedIteLamElse (fuel := fuel) _ _ _ qT hq (baseBulkSelectFalseA dT kT qT hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift,
    Nat.lt_irrefl, dite_false, dite_true]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← topClassGuardTA_simp]; exact hTopClass))
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← rightClassGuardTA_simp]; exact hRightClass))
      (PureFamilyDerivA.eqPauliTrans _ _ _
        (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← leftClassGuardTA_simp]; exact hLeftClass))
        (PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← leftBandGuardTA_simp]; exact hLeftBand))
          (PureFamilyDerivA.eqPauliRefl _))))

#print axioms recLeftZPeelA

/-- **Arity-general left boundary out-of-band base peel (`→ I`).** -/
def recLeftIPeelA {fuel arity : Nat} (dT kT qT : Term arity .nat)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false)))
    (hRightClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b false)))
    (hLeftClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (leftClassGuardTA dT kT)) (SC.b true)))
    (hLeftBand : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (leftBandGuardTA dT kT qT)) (SC.b false))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.baseEntry)))
          (SC.closed qT))
        (SC.closed (.pauliLit Pauli.I))) := by
  simp only [SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
    SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN,
    Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, orEqSucc, orEqPair]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (pureStabAtClosedIteLamElse (fuel := fuel) _ _ _ qT hq (baseBulkSelectFalseA dT kT qT hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift,
    Nat.lt_irrefl, dite_false, dite_true]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← topClassGuardTA_simp]; exact hTopClass))
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← rightClassGuardTA_simp]; exact hRightClass))
      (PureFamilyDerivA.eqPauliTrans _ _ _
        (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← leftClassGuardTA_simp]; exact hLeftClass))
        (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← leftBandGuardTA_simp]; exact hLeftBand))))

#print axioms recLeftIPeelA

/-- **Arity-general bottom-`X` boundary base peel (in band).** -/
def recBottomXPeelA {fuel arity : Nat} (dT kT qT : Term arity .nat)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false)))
    (hRightClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b false)))
    (hLeftClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (leftClassGuardTA dT kT)) (SC.b false)))
    (hBottomBand : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bottomBandGuardTA dT kT qT)) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.baseEntry)))
          (SC.closed qT))
        (SC.closed (.pauliLit Pauli.X))) := by
  simp only [SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
    SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN,
    Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, orEqSucc, orEqPair]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (pureStabAtClosedIteLamElse (fuel := fuel) _ _ _ qT hq (baseBulkSelectFalseA dT kT qT hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift,
    Nat.lt_irrefl, dite_false, dite_true]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← topClassGuardTA_simp]; exact hTopClass))
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← rightClassGuardTA_simp]; exact hRightClass))
      (PureFamilyDerivA.eqPauliTrans _ _ _
        (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← leftClassGuardTA_simp]; exact hLeftClass))
        (PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← bottomBandGuardTA_simp]; exact hBottomBand))
          (PureFamilyDerivA.eqPauliRefl _))))

#print axioms recBottomXPeelA

/-- **Arity-general bottom boundary out-of-band base peel (`→ I`).** -/
def recBottomIPeelA {fuel arity : Nat} (dT kT qT : Term arity .nat)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false)))
    (hRightClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b false)))
    (hLeftClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (leftClassGuardTA dT kT)) (SC.b false)))
    (hBottomBand : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bottomBandGuardTA dT kT qT)) (SC.b false))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.baseEntry)))
          (SC.closed qT))
        (SC.closed (.pauliLit Pauli.I))) := by
  simp only [SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
    SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN,
    Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, orEqSucc, orEqPair]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (pureStabAtClosedIteLamElse (fuel := fuel) _ _ _ qT hq (baseBulkSelectFalseA dT kT qT hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift,
    Nat.lt_irrefl, dite_false, dite_true]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← topClassGuardTA_simp]; exact hTopClass))
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← rightClassGuardTA_simp]; exact hRightClass))
      (PureFamilyDerivA.eqPauliTrans _ _ _
        (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← leftClassGuardTA_simp]; exact hLeftClass))
        (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← bottomBandGuardTA_simp]; exact hBottomBand))))

#print axioms recBottomIPeelA

/-! ## Base-case row resolvers at a symbolic index (the base branch of the dispatch)

For a row of the **base** code (`dT < 5`, e.g. `d = 3`) at a symbolic index `kT`,
the generated row entry `stabAt (recCall dT kT) qT` is resolved by composing the
base-branch row selection `surfaceCodeBaseEntryEq` (distance guard `dT < 5` TRUE)
with the matching base peel.  These are the per-cell-kind base branches a
consumer's `boolCases` (on the bulk / boundary classifier guards at a symbolic
`kT`) routes to.  Each is UNCONDITIONAL: the only data are purity certs and the
explicit guard derivations supplied by the branch — nothing asserts the entry
Pauli of the conclusion.

The supplied `hBaseDist : dT < 5 = true` is the (closed, index-independent) base
guard; for `d = 3` it is `closedThreeLtFive`. -/

/-- Bulk `Z`-plaquette base row resolver. -/
def recBaseRowA_Z {fuel arity : Nat} (n : STerm arity .nat) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hBaseDist : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat dT (n5 : Term arity .nat))) (SC.b true)))
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hBand : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)))
    (hKind : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (.stabAt (SC.closed (.recCall dT kT)) (SC.closed qT))
        (SC.closed (.pauliLit Pauli.Z))) :=
  surfaceCodeBaseEntryEq n dT kT qT (.pauliLit Pauli.Z) hd hk hBaseDist
    (recBasePeelA dT kT qT hq hBulk hBand hKind)

/-- Bulk `X`-plaquette base row resolver. -/
def recBaseRowA_X {fuel arity : Nat} (n : STerm arity .nat) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hBaseDist : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat dT (n5 : Term arity .nat))) (SC.b true)))
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hBand : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)))
    (hKind : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b false))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (.stabAt (SC.closed (.recCall dT kT)) (SC.closed qT))
        (SC.closed (.pauliLit Pauli.X))) :=
  surfaceCodeBaseEntryEq n dT kT qT (.pauliLit Pauli.X) hd hk hBaseDist
    (recBasePeelXA dT kT qT hq hBulk hBand hKind)

/-- Bulk out-of-plaquette base row resolver (`→ I`). -/
def recBaseRowA_bulkI {fuel arity : Nat} (n : STerm arity .nat) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hBaseDist : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat dT (n5 : Term arity .nat))) (SC.b true)))
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hBand : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (.stabAt (SC.closed (.recCall dT kT)) (SC.closed qT))
        (SC.closed (.pauliLit Pauli.I))) :=
  surfaceCodeBaseEntryEq n dT kT qT (.pauliLit Pauli.I) hd hk hBaseDist
    (recBasePeelIA dT kT qT hq hBulk hBand)

/-- Top-`X` boundary base row resolver. -/
def recBaseRowA_topX {fuel arity : Nat} (n : STerm arity .nat) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hBaseDist : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat dT (n5 : Term arity .nat))) (SC.b true)))
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b true)))
    (hTopBand : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topBandGuardTA dT kT qT)) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (.stabAt (SC.closed (.recCall dT kT)) (SC.closed qT))
        (SC.closed (.pauliLit Pauli.X))) :=
  surfaceCodeBaseEntryEq n dT kT qT (.pauliLit Pauli.X) hd hk hBaseDist
    (recTopXPeelA dT kT qT hq hBulk hTopClass hTopBand)

/-- Right-`Z` boundary base row resolver. -/
def recBaseRowA_rightZ {fuel arity : Nat} (n : STerm arity .nat) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hBaseDist : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat dT (n5 : Term arity .nat))) (SC.b true)))
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false)))
    (hRightClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b true)))
    (hRightBand : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (rightBandGuardTA dT kT qT)) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (.stabAt (SC.closed (.recCall dT kT)) (SC.closed qT))
        (SC.closed (.pauliLit Pauli.Z))) :=
  surfaceCodeBaseEntryEq n dT kT qT (.pauliLit Pauli.Z) hd hk hBaseDist
    (recRightZPeelA dT kT qT hq hBulk hTopClass hRightClass hRightBand)

/-- Left-`Z` boundary base row resolver. -/
def recBaseRowA_leftZ {fuel arity : Nat} (n : STerm arity .nat) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hBaseDist : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat dT (n5 : Term arity .nat))) (SC.b true)))
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false)))
    (hRightClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b false)))
    (hLeftClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (leftClassGuardTA dT kT)) (SC.b true)))
    (hLeftBand : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (leftBandGuardTA dT kT qT)) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (.stabAt (SC.closed (.recCall dT kT)) (SC.closed qT))
        (SC.closed (.pauliLit Pauli.Z))) :=
  surfaceCodeBaseEntryEq n dT kT qT (.pauliLit Pauli.Z) hd hk hBaseDist
    (recLeftZPeelA dT kT qT hq hBulk hTopClass hRightClass hLeftClass hLeftBand)

/-- Bottom-`X` boundary base row resolver. -/
def recBaseRowA_bottomX {fuel arity : Nat} (n : STerm arity .nat) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hBaseDist : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat dT (n5 : Term arity .nat))) (SC.b true)))
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false)))
    (hRightClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b false)))
    (hLeftClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (leftClassGuardTA dT kT)) (SC.b false)))
    (hBottomBand : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bottomBandGuardTA dT kT qT)) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (.stabAt (SC.closed (.recCall dT kT)) (SC.closed qT))
        (SC.closed (.pauliLit Pauli.X))) :=
  surfaceCodeBaseEntryEq n dT kT qT (.pauliLit Pauli.X) hd hk hBaseDist
    (recBottomXPeelA dT kT qT hq hBulk hTopClass hRightClass hLeftClass hBottomBand)

#print axioms recBaseRowA_Z
#print axioms recBaseRowA_X
#print axioms recBaseRowA_topX
#print axioms recBaseRowA_rightZ
#print axioms recBaseRowA_leftZ
#print axioms recBaseRowA_bottomX

/-! ## Non-vacuity cross-checks

The symbolic-index lemmas are not vacuous: instantiating the arity-general
interior peel at a concrete cell (the `d = 5` center, index `10`, qubit `12`)
recovers the genuine inner-code reference of the `d = 3` code, exactly as the
literal `recInteriorPeel` would.  This is a *closed* instance of the arity-general
(`recInteriorPeelA`) peel — it forces all three symbolic grid guards to be
discharged at the concrete cell. -/

def recInteriorPeelA_d5_center_check {fuel : Nat} :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt
          (SC.closed (.stabLam
            (codeSubstAt (.natLit (arity := 0) 5) (.natLit 10) 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed (.natLit 12)))
        (SC.closed (centerInnerRefA (.natLit 5) (.natLit 10) (.natLit 12)))) :=
  recInteriorPeelA (.natLit 5) (.natLit 10) (.natLit 12)
    (SFormula.PureNatTerm.nat 5) (SFormula.PureNatTerm.nat 10) (SFormula.PureNatTerm.nat 12)
    (PureFamilyDerivA.arithBool _ (by rfl)
      (by intro rho E; simp [SFormula.eval, STerm.eval, Term.eval, SC.closed, SC.b,
        bulkGuardTA, bulkCountTA, dm1TA]))
    (PureFamilyDerivA.arithBool _ (by rfl)
      (by intro rho E; simp [SFormula.eval, STerm.eval, Term.eval, SC.closed, SC.b,
        interiorCellGuardTA, band4, band3, le, rTA, cTA, lastCellTA, dm1TA]))
    (PureFamilyDerivA.arithBool _ (by rfl)
      (by intro rho E; simp [SFormula.eval, STerm.eval, Term.eval, SC.closed, SC.b,
        insideGuardTA, band4, band3, le, rowTA, colTA, dm1TA]))

#print axioms recInteriorPeelA_d5_center_check

/-- Non-vacuity for the top promoted-boundary peel: at the concrete `d = 5`
top cell (index `1`, qubit `6`) the arity-general peel recovers the genuine
inner-code reference `stabAt (recCall 3 4) 0` of the `d = 3` code (`topKTA 5 1`
reduces to `4`, `innerQTA 5 6` to `0`).  Forces all four symbolic guards to be
discharged at the concrete cell. -/
def recTopPromotedInnerPeelA_d5_check {fuel : Nat} :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt
          (SC.closed (.stabLam
            (codeSubstAt (.natLit (arity := 0) 5) (.natLit 1) 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed (.natLit 6)))
        (SC.closed (promotedInnerRefA (.natLit 5) (.natLit 6) (topKTA (.natLit 5) (.natLit 1))))) :=
  recTopPromotedInnerPeelA (.natLit 5) (.natLit 1) (.natLit 6)
    (SFormula.PureNatTerm.nat 6)
    (PureFamilyDerivA.arithBool _ (by rfl)
      (by intro rho E; simp [SFormula.eval, STerm.eval, Term.eval, SC.closed, SC.b,
        bulkGuardTA, bulkCountTA, dm1TA]))
    (PureFamilyDerivA.arithBool _ (by rfl)
      (by intro rho E; simp [SFormula.eval, STerm.eval, Term.eval, SC.closed, SC.b,
        interiorCellGuardTA, band4, band3, le, rTA, cTA, lastCellTA, dm1TA]))
    (PureFamilyDerivA.arithBool _ (by rfl)
      (by intro rho E; simp [SFormula.eval, STerm.eval, Term.eval, SC.closed, SC.b,
        topCellGuardTA, band3, topBTA, rTA, cTA, recInnerHalfTA, recInnerDm1TA, innerDm1TA,
        innerDTA, dm1TA]))
    (PureFamilyDerivA.arithBool _ (by rfl)
      (by intro rho E; simp [SFormula.eval, STerm.eval, Term.eval, SC.closed, SC.b,
        insideGuardTA, band4, band3, le, rowTA, colTA, dm1TA]))

#print axioms recTopPromotedInnerPeelA_d5_check

/-! ## Status and the one remaining structural gap

**Landed in this file (all unconditional, sorry-free, axiom ⊆
`[propext, Classical.choice, Quot.sound]`):**

* The recursing-cell symbolic peels and row-with-IH steps, every cell kind:
  interior (`recInteriorPeelA` / `recInteriorRowA_withIH`) and the four promoted
  boundaries (`rec{Top,Right,Left,Bottom}PromotedInnerPeelA` /
  `rec{…}PromotedRowA_withIH`), each feeding the IH at the matching symbolic inner
  index (`interiorKTA` / `topKTA` / `rightKTA` / `leftKTA` / `bottomKTA`), with
  purity certificates for every inner index.

* The non-recursing base-entry symbolic peels, every cell kind: bulk `Z`/`X`/`I`
  (`recBasePeel{,X,I}A`), the four in-band boundary checks (`recTopXPeelA`,
  `recRightZPeelA`, `recLeftZPeelA`, `recBottomXPeelA`) and their four out-of-band
  `→ I` complements (`rec{Top,Right,Left,Bottom}IPeelA`).

* The per-cell-kind base-case **row resolvers** (`recBaseRowA_{Z,X,bulkI,topX,
  rightZ,leftZ,bottomX}`): each composes `surfaceCodeBaseEntryEq` (base-branch
  selection, `dT < 5` TRUE) with its base peel, giving the generated row entry
  `stabAt (recCall dT kT) qT = leaf` GIVEN the cell's grid guards.  These are the
  branch bodies a consumer's own `boolCases` (on the closed-but-symbolic guards)
  dispatches to.

* Non-vacuity cross-checks at concrete `d = 5` cells (interior center,
  top-promoted) confirming the symbolic peels recover the genuine inner reference.

Each is UNCONDITIONAL: the only hypotheses are purity certificates on the
index/qubit terms and the explicit grid-guard / IH derivations — never an oracle
and never a hypothesis that asserts the entry Pauli of the conclusion.

**The one remaining gap — and why it cannot be closed at THIS layer.**  Assembling
the per-cell-kind branches above into a single converging `boolCases` dispatch
(and then a structural recursion on the distance index `m`) requires an
object-level *case-split on an undetermined guard* at a symbolic index.  At a
symbolic `kT` no `decide`/`by_cases` applies (there is no concrete `kv`); the only
sound rule is `SFormula.Deriv.boolCases`, which lives in `SFormula.Deriv`.  But:

  * `PureFamilyDerivA` / `PureFamilyDeriv` (the strict-purity layer, FROZEN in
    `PureDeriv.lean`) have **no `boolCases` constructor** — only `core`
    (injecting a closed `SFormula.Deriv []`) and `cut*` (discharging an
    *unconditional* premise, which presupposes the guard's value).
  * `SFormula.Deriv` HAS `boolCases`, but **lacks the `recUnfold`/`arithBool`
    leaves** the peels above are built from, so a pure peel cannot be injected
    into a `boolCases` branch (there is no `PureFamilyDerivA → SFormula.Deriv`
    lift; `Deriv` cannot express `recCall` unfolding).
  * The only layer mixing both, `FamilyDeriv`, does so via the FORBIDDEN
    `checkedBoundFree` leaf.

So the converging dispatch + the `m`-recursion belong in the FROZEN-respecting
consumer (`SurfaceDistanceProver.lean`): there the recursion uses `.recUnfold` +
`.core (SFormula.Deriv tree with boolCases over stabAtClosedIteLamEq* /
pauliIteSelect*)`, `cut`ting in these pure peels' CONCLUSIONS one branch at a
time.  This file delivers exactly those reusable branch leaves; it deliberately
does **not** fabricate a pure `boolCases` (there is no sound way to do so without
editing the frozen kernel), and it does **not** introduce a `recLeaf`-style
resolved-RHS object term (there is none at a symbolic index — the faithful RHS is
the cell-kind guarded `ite` tree, available one level down via
`surfaceRowEntryCharSymbolicRec`). -/

/-! ## The converging symbolic dispatch — base case (`d < 5`)

This is the genuinely-converging dispatch the old "remaining gap" section claimed
could not be built at this layer.  The mechanism is exactly the one the task
spec validated: the cell-kind case-split is performed by `SFormula.Deriv.boolCases`
*inside* the head of a `PureFamilyDerivA.cut1`, while the unconditional premise the
cut discharges is the `surfaceCodeBaseEntryAt` row equality.  No oracle, no
`recLeaf`, no fixed-Pauli hypothesis — only purity certificates and the closed
distance guard. -/

/-- The base-case guarded `ite`-tree of resolved Pauli leaves at a symbolic index.
Mirrors the cell-kind structure of `baseEntry` (in its post-`simp` `*GuardTA`
decomposition) but with every leaf a concrete Pauli literal.  This is the RHS the
converging base dispatch lands on. -/
def baseLeafTreeTA {arity : Nat} (dT kT qT : Term arity .nat) : Term arity .pauli :=
  .ite (bulkGuardTA dT kT)
    (.ite (baseBulkBandGuardTA dT kT qT)
      (.ite (baseKindGuardTA dT kT) (.pauliLit Pauli.Z) (.pauliLit Pauli.X))
      (.pauliLit Pauli.I))
    (.ite (topClassGuardTA dT kT)
      (.ite (topBandGuardTA dT kT qT) (.pauliLit Pauli.X) (.pauliLit Pauli.I))
      (.ite (rightClassGuardTA dT kT)
        (.ite (rightBandGuardTA dT kT qT) (.pauliLit Pauli.Z) (.pauliLit Pauli.I))
        (.ite (leftClassGuardTA dT kT)
          (.ite (leftBandGuardTA dT kT qT) (.pauliLit Pauli.Z) (.pauliLit Pauli.I))
          (.ite (bottomBandGuardTA dT kT qT) (.pauliLit Pauli.X) (.pauliLit Pauli.I)))))

/-! ### Deriv-level base-entry peels

The `SFormula.Deriv` analogues of the `PureFamilyDerivA` base peels above.  Each
reduces the substituted base-entry `stabLam`-`ite` tree at `qT` to its resolved
Pauli leaf, taking the cell guards as **`SFormula.Deriv` premises** (which the
converging dispatch will discharge from the `boolCases` context).  These are the
peels that *can* live inside a `boolCases` head — unlike the `PureFamilyDerivA`
peels, which cannot (`PureFamilyDerivA` has no `boolCases`). -/

/-- Deriv-level bulk strip (TRUE), bridging the instantiated guard to `bulkGuardTA`. -/
def baseBulkSelectTrueD {arity : Nat} {Γ : List (SFormula arity)}
    (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true))) :
    SFormula.Deriv Γ
      (.eqBool
        (SC.closed (Term.instantiateTopNat qT
          (.ltNat (Term.lift 0 kT)
            (.mul (.sub (Term.lift 0 dT) (.natLit 1)) (.sub (Term.lift 0 dT) (.natLit 1))))))
        (SC.b true)) := by
  have heq : Term.instantiateTopNat qT
      (Term.ltNat (Term.lift 0 kT)
        (.mul (.sub (Term.lift 0 dT) (.natLit 1)) (.sub (Term.lift 0 dT) (.natLit 1))))
      = bulkGuardTA dT kT := by
    simp only [bulkGuardTA, bulkCountTA, dm1TA, Term.instantiateTopNat, Term.instantiateNatAt,
      instTop_lift]
  rw [heq]; exact hBulk

/-- Deriv-level bulk strip (FALSE). -/
def baseBulkSelectFalseD {arity : Nat} {Γ : List (SFormula arity)}
    (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false))) :
    SFormula.Deriv Γ
      (.eqBool
        (SC.closed (Term.instantiateTopNat qT
          (.ltNat (Term.lift 0 kT)
            (.mul (.sub (Term.lift 0 dT) (.natLit 1)) (.sub (Term.lift 0 dT) (.natLit 1))))))
        (SC.b false)) := by
  have heq : Term.instantiateTopNat qT
      (Term.ltNat (Term.lift 0 kT)
        (.mul (.sub (Term.lift 0 dT) (.natLit 1)) (.sub (Term.lift 0 dT) (.natLit 1))))
      = bulkGuardTA dT kT := by
    simp only [bulkGuardTA, bulkCountTA, dm1TA, Term.instantiateTopNat, Term.instantiateNatAt,
      instTop_lift]
  rw [heq]; exact hBulk

/-! ### `codeSubstAt`-head exposure for `baseEntry` (NO `WellFounded.fix` whnf)

The base peels' stated type carries `codeSubstAt dT kT 1 baseEntry`, an
opaque application of the *well-founded* recursion `codeSubstAt` over the full
`baseEntry` AST.  Forcing the elaborator to whnf-reduce it (to expose the top
`ite` for `stabAtClosedIteLamEqThen`) deep-unfolds the `WellFounded.fix`
accessibility proof and blows up memory.

We expose the head `ite` *cheaply* instead: `baseEntry` is its own head `ite`
over three literal-projected children (`baseEntryCond`/`Then`/`Else`, all by
`rfl`), and a single `codeSubstAt` equation-lemma step distributes `codeSubstAt`
over that `ite`.  The peel then keeps the lam body as
`ite (codeSubstAt 1 baseEntryCond) (codeSubstAt 1 baseEntryThen)
     (codeSubstAt 1 baseEntryElse)` — a small head with three `codeSubstAt`
leaves, never deep-unfolded.  Only the *selected* branch is expanded (per-branch
simp), and the keystone leaf's `DerivWF` reuses the banked pure-Pauli totality
closure on the un-expanded `codeSubstAt 1 baseEntry` form. -/

/-- One-step head expansion of `codeSubstAt` on an `ite` (children kept as
`codeSubstAt`).  Cheap: a single equation-lemma rewrite, no `WellFounded` whnf. -/
theorem codeSubstAt_ite {arity : Nat} (dT kT : Term arity .nat) (depth : Nat)
    (c : Term (depth + 2) .bool) (t e : Term (depth + 2) .pauli) :
    codeSubstAt dT kT depth (.ite c t e)
      = .ite (codeSubstAt dT kT depth c) (codeSubstAt dT kT depth t)
          (codeSubstAt dT kT depth e) := by
  rw [codeSubstAt]

/-- The condition of `baseEntry`'s top-level `ite` (cheap literal projection). -/
def baseEntryCond : Term 3 .bool :=
  match SurfaceASTPublic.baseEntry with | .ite c _ _ => c | _ => .boolLit true
/-- The then-branch of `baseEntry`'s top-level `ite`. -/
def baseEntryThen : Term 3 .pauli :=
  match SurfaceASTPublic.baseEntry with | .ite _ t _ => t | _ => .pauliLit Pauli.I
/-- The else-branch of `baseEntry`'s top-level `ite`. -/
def baseEntryElse : Term 3 .pauli :=
  match SurfaceASTPublic.baseEntry with | .ite _ _ e => e | _ => .pauliLit Pauli.I

/-- `baseEntry` is its own head `ite` over the projected children (`rfl`). -/
theorem baseEntry_head_eq :
    SurfaceASTPublic.baseEntry = Term.ite baseEntryCond baseEntryThen baseEntryElse := rfl

/-- The head `ite` of `codeSubstAt dT kT 1 baseEntry`, children kept as `codeSubstAt`.
Cheap: `baseEntry`'s head equation plus a single `codeSubstAt_ite` step. -/
theorem codeSubstAt_one_baseEntry_head {arity : Nat} (dT kT : Term arity .nat) :
    codeSubstAt dT kT 1 SurfaceASTPublic.baseEntry
      = Term.ite (codeSubstAt dT kT 1 baseEntryCond)
          (codeSubstAt dT kT 1 baseEntryThen) (codeSubstAt dT kT 1 baseEntryElse) := by
  rw [baseEntry_head_eq, codeSubstAt_ite]

/-- The instantiated head condition of `codeSubstAt 1 baseEntry` IS `bulkGuardTA`.
Cheap: `baseEntryCond` is a literal `ltNat`, so only a *small* `codeSubstAt`
expansion (≈9 nodes) is forced — never the full `baseEntry`. -/
theorem instantiateTopNat_codeSubstAt_one_baseEntryCond {arity : Nat}
    (dT kT qT : Term arity .nat) :
    Term.instantiateTopNat qT (codeSubstAt dT kT 1 baseEntryCond) = bulkGuardTA dT kT := by
  simp only [baseEntryCond, SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
    SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN, Term.weaken,
    Nat.reduceLT, Nat.reduceEqDiff, reduceDIte, eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq,
    Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift, bulkGuardTA, bulkCountTA, dm1TA]

/-- Deriv-level bulk `Z`-plaquette peel. -/
def recBasePeelD_Z {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hBand : SFormula.Deriv Γ (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)))
    (hKind : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b true))) :
    SFormula.Deriv Γ
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.baseEntry)))
          (SC.closed qT))
        (SC.closed (.pauliLit Pauli.Z))) := by
  rw [codeSubstAt_one_baseEntry_head]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.stabAtClosedIteLamEqThen _ _ _ qT hq
      (by rw [instantiateTopNat_codeSubstAt_one_baseEntryCond]; exact hBulk)) ?_
  simp only [baseEntryThen, SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
    SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN, Term.weaken,
    Nat.reduceLT, Nat.reduceEqDiff, reduceDIte, eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq,
    band3, orEqSucc, orEqPair, Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectThen _ _ _ (by rw [← baseBulkBandGuardTA_simp]; exact hBand))
    (SFormula.Deriv.pauliIteSelectThen _ _ _ (by rw [← baseKindGuardTA_simp]; exact hKind))

/-- Deriv-level bulk `X`-plaquette peel. -/
def recBasePeelD_X {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hBand : SFormula.Deriv Γ (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)))
    (hKind : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b false))) :
    SFormula.Deriv Γ
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.baseEntry)))
          (SC.closed qT))
        (SC.closed (.pauliLit Pauli.X))) := by
  rw [codeSubstAt_one_baseEntry_head]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.stabAtClosedIteLamEqThen _ _ _ qT hq
      (by rw [instantiateTopNat_codeSubstAt_one_baseEntryCond]; exact hBulk)) ?_
  simp only [baseEntryThen, SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
    SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN, Term.weaken,
    Nat.reduceLT, Nat.reduceEqDiff, reduceDIte, eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq,
    band3, orEqSucc, orEqPair, Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectThen _ _ _ (by rw [← baseBulkBandGuardTA_simp]; exact hBand))
    (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← baseKindGuardTA_simp]; exact hKind))

/-- Deriv-level bulk out-of-plaquette peel (`→ I`). -/
def recBasePeelD_I {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hBand : SFormula.Deriv Γ (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false))) :
    SFormula.Deriv Γ
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.baseEntry)))
          (SC.closed qT))
        (SC.closed (.pauliLit Pauli.I))) := by
  rw [codeSubstAt_one_baseEntry_head]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.stabAtClosedIteLamEqThen _ _ _ qT hq
      (by rw [instantiateTopNat_codeSubstAt_one_baseEntryCond]; exact hBulk)) ?_
  simp only [baseEntryThen, SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
    SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN, Term.weaken,
    Nat.reduceLT, Nat.reduceEqDiff, reduceDIte, eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq,
    band3, orEqSucc, orEqPair, Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]
  exact SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← baseBulkBandGuardTA_simp]; exact hBand)

/-- Deriv-level top-`X` boundary peel (in band). -/
def recTopXPeelD {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b true)))
    (hTopBand : SFormula.Deriv Γ (.eqBool (SC.closed (topBandGuardTA dT kT qT)) (SC.b true))) :
    SFormula.Deriv Γ
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.baseEntry)))
          (SC.closed qT))
        (SC.closed (.pauliLit Pauli.X))) := by
  rw [codeSubstAt_one_baseEntry_head]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.stabAtClosedIteLamEqElse _ _ _ qT hq
      (by rw [instantiateTopNat_codeSubstAt_one_baseEntryCond]; exact hBulk)) ?_
  simp only [baseEntryElse, SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
    SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN, Term.weaken,
    Nat.reduceLT, Nat.reduceEqDiff, reduceDIte, eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq,
    band3, orEqSucc, orEqPair, Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift,
    Nat.lt_irrefl, dite_false, dite_true]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectThen _ _ _ (by rw [← topClassGuardTA_simp]; exact hTopClass))
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectThen _ _ _ (by rw [← topBandGuardTA_simp]; exact hTopBand))
      (SFormula.Deriv.pauliEqLit _))

/-- Deriv-level top boundary out-of-band peel (`→ I`). -/
def recTopIPeelD {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b true)))
    (hTopBand : SFormula.Deriv Γ (.eqBool (SC.closed (topBandGuardTA dT kT qT)) (SC.b false))) :
    SFormula.Deriv Γ
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.baseEntry)))
          (SC.closed qT))
        (SC.closed (.pauliLit Pauli.I))) := by
  simp only [SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
    SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN,
    Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, orEqSucc, orEqPair]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.stabAtClosedIteLamEqElse _ _ _ qT hq (baseBulkSelectFalseD dT kT qT hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift,
    Nat.lt_irrefl, dite_false, dite_true]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectThen _ _ _ (by rw [← topClassGuardTA_simp]; exact hTopClass))
    (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← topBandGuardTA_simp]; exact hTopBand))

/-- Deriv-level right-`Z` boundary peel (in band). -/
def recRightZPeelD {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false)))
    (hRightClass : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b true)))
    (hRightBand : SFormula.Deriv Γ (.eqBool (SC.closed (rightBandGuardTA dT kT qT)) (SC.b true))) :
    SFormula.Deriv Γ
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.baseEntry)))
          (SC.closed qT))
        (SC.closed (.pauliLit Pauli.Z))) := by
  simp only [SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
    SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN,
    Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, orEqSucc, orEqPair]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.stabAtClosedIteLamEqElse _ _ _ qT hq (baseBulkSelectFalseD dT kT qT hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift,
    Nat.lt_irrefl, dite_false, dite_true]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← topClassGuardTA_simp]; exact hTopClass))
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectThen _ _ _ (by rw [← rightClassGuardTA_simp]; exact hRightClass))
      (SFormula.Deriv.eqPauliTrans _ _ _
        (SFormula.Deriv.pauliIteSelectThen _ _ _ (by rw [← rightBandGuardTA_simp]; exact hRightBand))
        (SFormula.Deriv.pauliEqLit _)))

/-- Deriv-level right boundary out-of-band peel (`→ I`). -/
def recRightIPeelD {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false)))
    (hRightClass : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b true)))
    (hRightBand : SFormula.Deriv Γ (.eqBool (SC.closed (rightBandGuardTA dT kT qT)) (SC.b false))) :
    SFormula.Deriv Γ
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.baseEntry)))
          (SC.closed qT))
        (SC.closed (.pauliLit Pauli.I))) := by
  simp only [SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
    SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN,
    Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, orEqSucc, orEqPair]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.stabAtClosedIteLamEqElse _ _ _ qT hq (baseBulkSelectFalseD dT kT qT hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift,
    Nat.lt_irrefl, dite_false, dite_true]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← topClassGuardTA_simp]; exact hTopClass))
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectThen _ _ _ (by rw [← rightClassGuardTA_simp]; exact hRightClass))
      (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← rightBandGuardTA_simp]; exact hRightBand)))

/-- Deriv-level left-`Z` boundary peel (in band). -/
def recLeftZPeelD {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false)))
    (hRightClass : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b false)))
    (hLeftClass : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA dT kT)) (SC.b true)))
    (hLeftBand : SFormula.Deriv Γ (.eqBool (SC.closed (leftBandGuardTA dT kT qT)) (SC.b true))) :
    SFormula.Deriv Γ
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.baseEntry)))
          (SC.closed qT))
        (SC.closed (.pauliLit Pauli.Z))) := by
  simp only [SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
    SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN,
    Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, orEqSucc, orEqPair]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.stabAtClosedIteLamEqElse _ _ _ qT hq (baseBulkSelectFalseD dT kT qT hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift,
    Nat.lt_irrefl, dite_false, dite_true]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← topClassGuardTA_simp]; exact hTopClass))
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← rightClassGuardTA_simp]; exact hRightClass))
      (SFormula.Deriv.eqPauliTrans _ _ _
        (SFormula.Deriv.pauliIteSelectThen _ _ _ (by rw [← leftClassGuardTA_simp]; exact hLeftClass))
        (SFormula.Deriv.eqPauliTrans _ _ _
          (SFormula.Deriv.pauliIteSelectThen _ _ _ (by rw [← leftBandGuardTA_simp]; exact hLeftBand))
          (SFormula.Deriv.pauliEqLit _))))

/-- Deriv-level left boundary out-of-band peel (`→ I`). -/
def recLeftIPeelD {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false)))
    (hRightClass : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b false)))
    (hLeftClass : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA dT kT)) (SC.b true)))
    (hLeftBand : SFormula.Deriv Γ (.eqBool (SC.closed (leftBandGuardTA dT kT qT)) (SC.b false))) :
    SFormula.Deriv Γ
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.baseEntry)))
          (SC.closed qT))
        (SC.closed (.pauliLit Pauli.I))) := by
  simp only [SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
    SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN,
    Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, orEqSucc, orEqPair]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.stabAtClosedIteLamEqElse _ _ _ qT hq (baseBulkSelectFalseD dT kT qT hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift,
    Nat.lt_irrefl, dite_false, dite_true]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← topClassGuardTA_simp]; exact hTopClass))
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← rightClassGuardTA_simp]; exact hRightClass))
      (SFormula.Deriv.eqPauliTrans _ _ _
        (SFormula.Deriv.pauliIteSelectThen _ _ _ (by rw [← leftClassGuardTA_simp]; exact hLeftClass))
        (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← leftBandGuardTA_simp]; exact hLeftBand))))

/-- Deriv-level bottom-`X` boundary peel (in band). -/
def recBottomXPeelD {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false)))
    (hRightClass : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b false)))
    (hLeftClass : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA dT kT)) (SC.b false)))
    (hBottomBand : SFormula.Deriv Γ (.eqBool (SC.closed (bottomBandGuardTA dT kT qT)) (SC.b true))) :
    SFormula.Deriv Γ
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.baseEntry)))
          (SC.closed qT))
        (SC.closed (.pauliLit Pauli.X))) := by
  simp only [SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
    SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN,
    Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, orEqSucc, orEqPair]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.stabAtClosedIteLamEqElse _ _ _ qT hq (baseBulkSelectFalseD dT kT qT hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift,
    Nat.lt_irrefl, dite_false, dite_true]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← topClassGuardTA_simp]; exact hTopClass))
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← rightClassGuardTA_simp]; exact hRightClass))
      (SFormula.Deriv.eqPauliTrans _ _ _
        (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← leftClassGuardTA_simp]; exact hLeftClass))
        (SFormula.Deriv.eqPauliTrans _ _ _
          (SFormula.Deriv.pauliIteSelectThen _ _ _ (by rw [← bottomBandGuardTA_simp]; exact hBottomBand))
          (SFormula.Deriv.pauliEqLit _))))

/-- Deriv-level bottom boundary out-of-band peel (`→ I`). -/
def recBottomIPeelD {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false)))
    (hRightClass : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b false)))
    (hLeftClass : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA dT kT)) (SC.b false)))
    (hBottomBand : SFormula.Deriv Γ (.eqBool (SC.closed (bottomBandGuardTA dT kT qT)) (SC.b false))) :
    SFormula.Deriv Γ
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.baseEntry)))
          (SC.closed qT))
        (SC.closed (.pauliLit Pauli.I))) := by
  simp only [SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
    SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN,
    Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, orEqSucc, orEqPair]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.stabAtClosedIteLamEqElse _ _ _ qT hq (baseBulkSelectFalseD dT kT qT hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift,
    Nat.lt_irrefl, dite_false, dite_true]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← topClassGuardTA_simp]; exact hTopClass))
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← rightClassGuardTA_simp]; exact hRightClass))
      (SFormula.Deriv.eqPauliTrans _ _ _
        (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← leftClassGuardTA_simp]; exact hLeftClass))
        (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← bottomBandGuardTA_simp]; exact hBottomBand))))

/-! ### `baseLeafTreeTA` reductions to a leaf (given the guards as Deriv premises)

`baseLeafTreeTA` is built *directly* from the `*GuardTA` guard terms, so reducing
it to a leaf needs no `_simp` bridging — `pauliIteSelectThen/Else` applies to the
guard term verbatim. -/

def leafZ {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hBand : SFormula.Deriv Γ (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)))
    (hKind : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b true))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.closed (.pauliLit Pauli.Z))) := by
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectThen _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectThen _ _ _ hBand)
      (SFormula.Deriv.pauliIteSelectThen _ _ _ hKind))

def leafBulkX {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hBand : SFormula.Deriv Γ (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)))
    (hKind : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b false))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.closed (.pauliLit Pauli.X))) := by
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectThen _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectThen _ _ _ hBand)
      (SFormula.Deriv.pauliIteSelectElse _ _ _ hKind))

def leafBulkI {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hBand : SFormula.Deriv Γ (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.closed (.pauliLit Pauli.I))) := by
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectThen _ _ _ hBulk)
    (SFormula.Deriv.pauliIteSelectElse _ _ _ hBand)

def leafTopX {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b true)))
    (hTopBand : SFormula.Deriv Γ (.eqBool (SC.closed (topBandGuardTA dT kT qT)) (SC.b true))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.closed (.pauliLit Pauli.X))) := by
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectThen _ _ _ hTopClass)
      (SFormula.Deriv.pauliIteSelectThen _ _ _ hTopBand))

def leafTopI {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b true)))
    (hTopBand : SFormula.Deriv Γ (.eqBool (SC.closed (topBandGuardTA dT kT qT)) (SC.b false))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.closed (.pauliLit Pauli.I))) := by
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectThen _ _ _ hTopClass)
      (SFormula.Deriv.pauliIteSelectElse _ _ _ hTopBand))

def leafRightZ {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false)))
    (hRightClass : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b true)))
    (hRightBand : SFormula.Deriv Γ (.eqBool (SC.closed (rightBandGuardTA dT kT qT)) (SC.b true))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.closed (.pauliLit Pauli.Z))) := by
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectElse _ _ _ hTopClass)
      (SFormula.Deriv.eqPauliTrans _ _ _
        (SFormula.Deriv.pauliIteSelectThen _ _ _ hRightClass)
        (SFormula.Deriv.pauliIteSelectThen _ _ _ hRightBand)))

def leafRightI {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false)))
    (hRightClass : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b true)))
    (hRightBand : SFormula.Deriv Γ (.eqBool (SC.closed (rightBandGuardTA dT kT qT)) (SC.b false))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.closed (.pauliLit Pauli.I))) := by
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectElse _ _ _ hTopClass)
      (SFormula.Deriv.eqPauliTrans _ _ _
        (SFormula.Deriv.pauliIteSelectThen _ _ _ hRightClass)
        (SFormula.Deriv.pauliIteSelectElse _ _ _ hRightBand)))

def leafLeftZ {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false)))
    (hRightClass : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b false)))
    (hLeftClass : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA dT kT)) (SC.b true)))
    (hLeftBand : SFormula.Deriv Γ (.eqBool (SC.closed (leftBandGuardTA dT kT qT)) (SC.b true))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.closed (.pauliLit Pauli.Z))) := by
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectElse _ _ _ hTopClass)
      (SFormula.Deriv.eqPauliTrans _ _ _
        (SFormula.Deriv.pauliIteSelectElse _ _ _ hRightClass)
        (SFormula.Deriv.eqPauliTrans _ _ _
          (SFormula.Deriv.pauliIteSelectThen _ _ _ hLeftClass)
          (SFormula.Deriv.pauliIteSelectThen _ _ _ hLeftBand))))

def leafLeftI {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false)))
    (hRightClass : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b false)))
    (hLeftClass : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA dT kT)) (SC.b true)))
    (hLeftBand : SFormula.Deriv Γ (.eqBool (SC.closed (leftBandGuardTA dT kT qT)) (SC.b false))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.closed (.pauliLit Pauli.I))) := by
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectElse _ _ _ hTopClass)
      (SFormula.Deriv.eqPauliTrans _ _ _
        (SFormula.Deriv.pauliIteSelectElse _ _ _ hRightClass)
        (SFormula.Deriv.eqPauliTrans _ _ _
          (SFormula.Deriv.pauliIteSelectThen _ _ _ hLeftClass)
          (SFormula.Deriv.pauliIteSelectElse _ _ _ hLeftBand))))

def leafBottomX {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false)))
    (hRightClass : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b false)))
    (hLeftClass : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA dT kT)) (SC.b false)))
    (hBottomBand : SFormula.Deriv Γ (.eqBool (SC.closed (bottomBandGuardTA dT kT qT)) (SC.b true))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.closed (.pauliLit Pauli.X))) := by
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectElse _ _ _ hTopClass)
      (SFormula.Deriv.eqPauliTrans _ _ _
        (SFormula.Deriv.pauliIteSelectElse _ _ _ hRightClass)
        (SFormula.Deriv.eqPauliTrans _ _ _
          (SFormula.Deriv.pauliIteSelectElse _ _ _ hLeftClass)
          (SFormula.Deriv.pauliIteSelectThen _ _ _ hBottomBand))))

def leafBottomI {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false)))
    (hRightClass : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b false)))
    (hLeftClass : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA dT kT)) (SC.b false)))
    (hBottomBand : SFormula.Deriv Γ (.eqBool (SC.closed (bottomBandGuardTA dT kT qT)) (SC.b false))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.closed (.pauliLit Pauli.I))) := by
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectElse _ _ _ hTopClass)
      (SFormula.Deriv.eqPauliTrans _ _ _
        (SFormula.Deriv.pauliIteSelectElse _ _ _ hRightClass)
        (SFormula.Deriv.eqPauliTrans _ _ _
          (SFormula.Deriv.pauliIteSelectElse _ _ _ hLeftClass)
          (SFormula.Deriv.pauliIteSelectElse _ _ _ hBottomBand))))

/-! ### The base-case master reduction (converging `boolCases` dispatch)

A single `SFormula.Deriv` that reduces the substituted base-entry stabLam-tree at
`qT` to the resolved leaf-tree `baseLeafTreeTA`, dispatching on every cell-kind
guard via `boolCases`.  Each branch composes the matching Deriv peel
(`recBasePeelD_*`/`rec*PeelD`, giving `substEntry = leaf`) with the symmetric
`leaf*` reduction (`baseLeafTreeTA = leaf`).  No premise is needed; the guards are
discharged from the `boolCases` context. -/
def baseEntryMasterD {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hq : SFormula.PureNatTerm qT) :
    SFormula.Deriv Γ
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.baseEntry)))
          (SC.closed qT))
        (SC.closed (baseLeafTreeTA dT kT qT))) := by
  refine SFormula.Deriv.boolCases (SC.closed (bulkGuardTA dT kT)) _ ?_ ?_
  · -- bulk = true
    refine SFormula.Deriv.boolCases (SC.closed (baseBulkBandGuardTA dT kT qT)) _ ?_ ?_
    · -- band = true
      refine SFormula.Deriv.boolCases (SC.closed (baseKindGuardTA dT kT)) _ ?_ ?_
      · -- kind = true → Z
        exact SFormula.Deriv.eqPauliTrans _ _ _
          (recBasePeelD_Z dT kT qT hq (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption)
          (SFormula.Deriv.eqPauliSymm _ _
            (leafZ dT kT qT (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption))
      · -- kind = false → X
        exact SFormula.Deriv.eqPauliTrans _ _ _
          (recBasePeelD_X dT kT qT hq (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption)
          (SFormula.Deriv.eqPauliSymm _ _
            (leafBulkX dT kT qT (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption))
    · -- band = false → I
      exact SFormula.Deriv.eqPauliTrans _ _ _
        (recBasePeelD_I dT kT qT hq (.hyp (by right; left)) .assumption)
        (SFormula.Deriv.eqPauliSymm _ _
          (leafBulkI dT kT qT (.hyp (by right; left)) .assumption))
  · -- bulk = false
    refine SFormula.Deriv.boolCases (SC.closed (topClassGuardTA dT kT)) _ ?_ ?_
    · -- topClass = true
      refine SFormula.Deriv.boolCases (SC.closed (topBandGuardTA dT kT qT)) _ ?_ ?_
      · -- topBand = true → topX
        exact SFormula.Deriv.eqPauliTrans _ _ _
          (recTopXPeelD dT kT qT hq (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption)
          (SFormula.Deriv.eqPauliSymm _ _
            (leafTopX dT kT qT (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption))
      · -- topBand = false → topI
        exact SFormula.Deriv.eqPauliTrans _ _ _
          (recTopIPeelD dT kT qT hq (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption)
          (SFormula.Deriv.eqPauliSymm _ _
            (leafTopI dT kT qT (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption))
    · -- topClass = false
      refine SFormula.Deriv.boolCases (SC.closed (rightClassGuardTA dT kT)) _ ?_ ?_
      · -- rightClass = true
        refine SFormula.Deriv.boolCases (SC.closed (rightBandGuardTA dT kT qT)) _ ?_ ?_
        · -- rightBand = true → rightZ
          exact SFormula.Deriv.eqPauliTrans _ _ _
            (recRightZPeelD dT kT qT hq (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
              (.hyp (by right; left)) .assumption)
            (SFormula.Deriv.eqPauliSymm _ _
              (leafRightZ dT kT qT (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
                (.hyp (by right; left)) .assumption))
        · -- rightBand = false → rightI
          exact SFormula.Deriv.eqPauliTrans _ _ _
            (recRightIPeelD dT kT qT hq (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
              (.hyp (by right; left)) .assumption)
            (SFormula.Deriv.eqPauliSymm _ _
              (leafRightI dT kT qT (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
                (.hyp (by right; left)) .assumption))
      · -- rightClass = false
        refine SFormula.Deriv.boolCases (SC.closed (leftClassGuardTA dT kT)) _ ?_ ?_
        · -- leftClass = true
          refine SFormula.Deriv.boolCases (SC.closed (leftBandGuardTA dT kT qT)) _ ?_ ?_
          · -- leftBand = true → leftZ
            exact SFormula.Deriv.eqPauliTrans _ _ _
              (recLeftZPeelD dT kT qT hq (.hyp (by right; right; right; right; left))
                (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
                (.hyp (by right; left)) .assumption)
              (SFormula.Deriv.eqPauliSymm _ _
                (leafLeftZ dT kT qT (.hyp (by right; right; right; right; left))
                  (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
                  (.hyp (by right; left)) .assumption))
          · -- leftBand = false → leftI
            exact SFormula.Deriv.eqPauliTrans _ _ _
              (recLeftIPeelD dT kT qT hq (.hyp (by right; right; right; right; left))
                (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
                (.hyp (by right; left)) .assumption)
              (SFormula.Deriv.eqPauliSymm _ _
                (leafLeftI dT kT qT (.hyp (by right; right; right; right; left))
                  (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
                  (.hyp (by right; left)) .assumption))
        · -- leftClass = false → bottom
          refine SFormula.Deriv.boolCases (SC.closed (bottomBandGuardTA dT kT qT)) _ ?_ ?_
          · -- bottomBand = true → bottomX
            exact SFormula.Deriv.eqPauliTrans _ _ _
              (recBottomXPeelD dT kT qT hq (.hyp (by right; right; right; right; left))
                (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
                (.hyp (by right; left)) .assumption)
              (SFormula.Deriv.eqPauliSymm _ _
                (leafBottomX dT kT qT (.hyp (by right; right; right; right; left))
                  (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
                  (.hyp (by right; left)) .assumption))
          · -- bottomBand = false → bottomI
            exact SFormula.Deriv.eqPauliTrans _ _ _
              (recBottomIPeelD dT kT qT hq (.hyp (by right; right; right; right; left))
                (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
                (.hyp (by right; left)) .assumption)
              (SFormula.Deriv.eqPauliSymm _ _
                (leafBottomI dT kT qT (.hyp (by right; right; right; right; left))
                  (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
                  (.hyp (by right; left)) .assumption))

/-! ### The base-case converging row characterization (`cut1` assembly)

`cut1` discharges the single unconditional premise `surfaceCodeBaseEntryAt` (the
base-branch row equality, distance guard `dT < 5` TRUE) against the master
reduction.  The result: the generated row entry at the symbolic index `kT` equals
the resolved leaf-tree `baseLeafTreeTA dT kT qT` — a genuine converging dispatch,
no oracle, no fixed-Pauli hypothesis. -/
def baseRowConvergeA {fuel arity : Nat} (n : STerm arity .nat) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hBaseDist : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat dT (n5 : Term arity .nat))) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (.stabAt (SC.closed (.recCall dT kT)) (SC.closed qT))
        (SC.closed (baseLeafTreeTA dT kT qT))) :=
  -- premise A is the *split* row-projection: `stabAt(recCall dT kT) qT`
  -- `= stabAt (closed (stabLam baseEntry-subst)) qT`, matching the master's LHS exactly.
  PureFamilyDerivA.cut1
    (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.hyp (by left)) (baseEntryMasterD dT kT qT hq))
    (PureFamilyDerivA.eqPauliProj n
      (SC.closed (.recCall dT kT))
      (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.baseEntry)))
      (SC.closed qT)
      (surfaceCodeRowSelectBase n dT kT hd hk hBaseDist))

#print axioms baseRowConvergeA

/-! ## The converging symbolic dispatch — recursive case (`d ≥ 5`)

The recursive analogue.  The recursing inside-cells (interior + the four promoted
boundaries) are resolved by the **inductive hypothesis** — supplied here as five
`SFormula.Deriv` premises `pInt/pTop/pRight/pLeft/pBottom`, each resolving the
matching inner-code reference (`centerInnerRefA` / `promotedInnerRefA`) to a leaf.
The non-recursing cells (interior-not-inside, promoted-not-inside, the fallback,
and the boundary band) reduce to literals / `baseLeafTreeTA` exactly as in the
base case.  The five IH premises are *exactly* what a structural recursion on the
distance index hands down from its recursive call — see `surfaceRowEntryCharSymbolic`. -/

/-- Arity-general `topOuter` guard (matches `recursiveEntry`'s `topOuter`). -/
def topOuterGuardTA {arity : Nat} (dT kT qT : Term arity .nat) : Term arity .bool :=
  .and (.eqNat (rowTA dT qT) (.natLit 0))
    (orEqSucc (colTA dT qT)
      (.add (.mul (.natLit 2) (.div (.sub (cTA dT kT) (.natLit 1)) (.natLit 2))) (.natLit 1)))
/-- Arity-general `rightOuter` guard. -/
def rightOuterGuardTA {arity : Nat} (dT kT qT : Term arity .nat) : Term arity .bool :=
  .and (.eqNat (colTA dT qT) (dm1TA dT))
    (orEqSucc (rowTA dT qT)
      (.add (.mul (.natLit 2) (.div (.sub (rTA dT kT) (.natLit 1)) (.natLit 2))) (.natLit 1)))
/-- Arity-general `leftOuter` guard. -/
def leftOuterGuardTA {arity : Nat} (dT kT qT : Term arity .nat) : Term arity .bool :=
  .and (.eqNat (colTA dT qT) (.natLit 0))
    (orEqSucc (rowTA dT qT)
      (.add (.mul (.natLit 2) (.div (.sub (rTA dT kT) (.natLit 2)) (.natLit 2))) (.natLit 2)))
/-- Arity-general `bottomOuter` guard. -/
def bottomOuterGuardTA {arity : Nat} (dT kT qT : Term arity .nat) : Term arity .bool :=
  .and (.eqNat (rowTA dT qT) (dm1TA dT))
    (orEqSucc (colTA dT qT)
      (.add (.mul (.natLit 2) (.div (.sub (cTA dT kT) (.natLit 2)) (.natLit 2))) (.natLit 2)))

/-- The recursive-case guarded `ite`-tree of resolved leaves at a symbolic index.
Mirrors the cell-kind structure of `recursiveEntry`; the recursing inside-cells
carry the supplied IH-resolved leaves `pInt/pTop/pRight/pLeft/pBottom`, the
promoted-not-inside cells carry their `ite outer kind I` form, and the fallback /
out-of-bulk branches carry `baseLeafTreeTA`. -/
def recLeafTreeTA {arity : Nat} (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli) : Term arity .pauli :=
  .ite (bulkGuardTA dT kT)
    (.ite (interiorCellGuardTA dT kT)
      (.ite (insideGuardTA dT qT) pInt (.pauliLit Pauli.I))
      (.ite (topCellGuardTA dT kT)
        (.ite (insideGuardTA dT qT) pTop
          (.ite (topOuterGuardTA dT kT qT) (.pauliLit Pauli.X) (.pauliLit Pauli.I)))
        (.ite (rightCellGuardTA dT kT)
          (.ite (insideGuardTA dT qT) pRight
            (.ite (rightOuterGuardTA dT kT qT) (.pauliLit Pauli.Z) (.pauliLit Pauli.I)))
          (.ite (leftCellGuardTA dT kT)
            (.ite (insideGuardTA dT qT) pLeft
              (.ite (leftOuterGuardTA dT kT qT) (.pauliLit Pauli.Z) (.pauliLit Pauli.I)))
            (.ite (bottomCellGuardTA dT kT)
              (.ite (insideGuardTA dT qT) pBottom
                (.ite (bottomOuterGuardTA dT kT qT) (.pauliLit Pauli.X) (.pauliLit Pauli.I)))
              (baseLeafTreeTA dT kT qT))))))
    (baseLeafTreeTA dT kT qT)

/-! ### Deriv-level recursive-entry peels

`SFormula.Deriv` analogues of `recInteriorPeelA` / `rec*PromotedInnerPeelA` plus
the non-recursing leaves, all taking the cell guards as `SFormula.Deriv` premises. -/

/-- Deriv-level interior-inside peel, finished by the IH `pInt`
(`centerInnerRefA = pInt`). -/
def recInteriorPeelD {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (pInt : Term arity .pauli)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b true)))
    (hInside : SFormula.Deriv Γ (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b true)))
    (ih : SFormula.Deriv Γ (.eqPauli (SC.closed (centerInnerRefA dT kT qT)) (SC.closed pInt))) :
    SFormula.Deriv Γ
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed qT))
        (SC.closed pInt)) := by
  simp only [SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
    SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q,
    codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4, orEqSucc, le]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.stabAtClosedIteLamEqThen _ _ _ qT hq (baseBulkSelectTrueD dT kT qT hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectThen _ _ _ (by rw [← interiorCellGuardTA_simp]; exact hInterior))
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectThen _ _ _ (by
        simp only [Nat.lt_irrefl, dite_false, dite_true]
        rw [← insideGuardTA_simp]; exact hInside))
      (by
        simp only [Nat.lt_irrefl, dite_false, dite_true]
        exact ih))

/-- Deriv-level interior-not-inside peel → `I`. -/
def recInteriorIPeelD {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b true)))
    (hInside : SFormula.Deriv Γ (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b false))) :
    SFormula.Deriv Γ
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed qT))
        (SC.closed (.pauliLit Pauli.I))) := by
  simp only [SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
    SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q,
    codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4, orEqSucc, le]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.stabAtClosedIteLamEqThen _ _ _ qT hq (baseBulkSelectTrueD dT kT qT hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectThen _ _ _ (by rw [← interiorCellGuardTA_simp]; exact hInterior))
    (by
      simp only [Nat.lt_irrefl, dite_false, dite_true]
      exact SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← insideGuardTA_simp]; exact hInside))

/-- Deriv-level top-promoted-inside peel, finished by the IH `pTop`. -/
def recTopPromotedPeelD {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (pTop : Term arity .pauli)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : SFormula.Deriv Γ (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b true)))
    (hInside : SFormula.Deriv Γ (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b true)))
    (ih : SFormula.Deriv Γ (.eqPauli (SC.closed (promotedInnerRefA dT qT (topKTA dT kT))) (SC.closed pTop))) :
    SFormula.Deriv Γ
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed qT))
        (SC.closed pTop)) := by
  simp only [SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
    SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q,
    codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4, orEqSucc, le]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.stabAtClosedIteLamEqThen _ _ _ qT hq (baseBulkSelectTrueD dT kT qT hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← interiorCellGuardTA_simp]; exact hInterior))
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectThen _ _ _ (by rw [← topCellGuardTA_simp]; exact hTop))
      (SFormula.Deriv.eqPauliTrans _ _ _
        (SFormula.Deriv.pauliIteSelectThen _ _ _ (by rw [← insideGuardTA_simp]; exact hInside))
        ih))

def recTopPromotedNotInsidePeelD {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : SFormula.Deriv Γ (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b true)))
    (hInside : SFormula.Deriv Γ (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b false))) :
    SFormula.Deriv Γ
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed qT))
        (SC.closed (.ite (topOuterGuardTA dT kT qT) (.pauliLit Pauli.X) (.pauliLit Pauli.I)))) := by
  simp only [SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
    SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q,
    codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4, orEqSucc, le,
    topOuterGuardTA, rowTA, colTA, cTA, dm1TA]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.stabAtClosedIteLamEqThen _ _ _ qT hq (baseBulkSelectTrueD dT kT qT hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift,
    Nat.lt_irrefl, dite_false, dite_true]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← interiorCellGuardTA_simp]; exact hInterior))
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectThen _ _ _ (by rw [← topCellGuardTA_simp]; exact hTop))
      (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← insideGuardTA_simp]; exact hInside)))

/-- Deriv-level right-promoted-inside peel, finished by the IH `pRight`. -/
def recRightPromotedPeelD {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (pRight : Term arity .pauli)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : SFormula.Deriv Γ (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b false)))
    (hRight : SFormula.Deriv Γ (.eqBool (SC.closed (rightCellGuardTA dT kT)) (SC.b true)))
    (hInside : SFormula.Deriv Γ (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b true)))
    (ih : SFormula.Deriv Γ (.eqPauli (SC.closed (promotedInnerRefA dT qT (rightKTA dT kT))) (SC.closed pRight))) :
    SFormula.Deriv Γ
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed qT))
        (SC.closed pRight)) := by
  simp only [SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
    SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q,
    codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4, orEqSucc, le]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.stabAtClosedIteLamEqThen _ _ _ qT hq (baseBulkSelectTrueD dT kT qT hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift,
    Nat.lt_irrefl, dite_false, dite_true]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← interiorCellGuardTA_simp]; exact hInterior))
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← topCellGuardTA_simp]; exact hTop))
      (SFormula.Deriv.eqPauliTrans _ _ _
        (SFormula.Deriv.pauliIteSelectThen _ _ _ (by rw [← rightCellGuardTA_simp]; exact hRight))
        (SFormula.Deriv.eqPauliTrans _ _ _
          (SFormula.Deriv.pauliIteSelectThen _ _ _ (by rw [← insideGuardTA_simp]; exact hInside))
          ih)))

/-- Deriv-level right-promoted-not-inside peel → `ite rightOuter Z I`. -/
def recRightPromotedNotInsidePeelD {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : SFormula.Deriv Γ (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b false)))
    (hRight : SFormula.Deriv Γ (.eqBool (SC.closed (rightCellGuardTA dT kT)) (SC.b true)))
    (hInside : SFormula.Deriv Γ (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b false))) :
    SFormula.Deriv Γ
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed qT))
        (SC.closed (.ite (rightOuterGuardTA dT kT qT) (.pauliLit Pauli.Z) (.pauliLit Pauli.I)))) := by
  simp only [SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
    SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q,
    codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4, orEqSucc, le,
    rightOuterGuardTA, rowTA, colTA, rTA, dm1TA]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.stabAtClosedIteLamEqThen _ _ _ qT hq (baseBulkSelectTrueD dT kT qT hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift,
    Nat.lt_irrefl, dite_false, dite_true]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← interiorCellGuardTA_simp]; exact hInterior))
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← topCellGuardTA_simp]; exact hTop))
      (SFormula.Deriv.eqPauliTrans _ _ _
        (SFormula.Deriv.pauliIteSelectThen _ _ _ (by rw [← rightCellGuardTA_simp]; exact hRight))
        (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← insideGuardTA_simp]; exact hInside))))

/-- Deriv-level left-promoted-inside peel, finished by the IH `pLeft`. -/
def recLeftPromotedPeelD {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (pLeft : Term arity .pauli)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : SFormula.Deriv Γ (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b false)))
    (hRight : SFormula.Deriv Γ (.eqBool (SC.closed (rightCellGuardTA dT kT)) (SC.b false)))
    (hLeft : SFormula.Deriv Γ (.eqBool (SC.closed (leftCellGuardTA dT kT)) (SC.b true)))
    (hInside : SFormula.Deriv Γ (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b true)))
    (ih : SFormula.Deriv Γ (.eqPauli (SC.closed (promotedInnerRefA dT qT (leftKTA dT kT))) (SC.closed pLeft))) :
    SFormula.Deriv Γ
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed qT))
        (SC.closed pLeft)) := by
  simp only [SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
    SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q,
    codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4, orEqSucc, le]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.stabAtClosedIteLamEqThen _ _ _ qT hq (baseBulkSelectTrueD dT kT qT hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift,
    Nat.lt_irrefl, dite_false, dite_true]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← interiorCellGuardTA_simp]; exact hInterior))
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← topCellGuardTA_simp]; exact hTop))
      (SFormula.Deriv.eqPauliTrans _ _ _
        (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← rightCellGuardTA_simp]; exact hRight))
        (SFormula.Deriv.eqPauliTrans _ _ _
          (SFormula.Deriv.pauliIteSelectThen _ _ _ (by rw [← leftCellGuardTA_simp]; exact hLeft))
          (SFormula.Deriv.eqPauliTrans _ _ _
            (SFormula.Deriv.pauliIteSelectThen _ _ _ (by rw [← insideGuardTA_simp]; exact hInside))
            ih))))

/-- Deriv-level left-promoted-not-inside peel → `ite leftOuter Z I`. -/
def recLeftPromotedNotInsidePeelD {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : SFormula.Deriv Γ (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b false)))
    (hRight : SFormula.Deriv Γ (.eqBool (SC.closed (rightCellGuardTA dT kT)) (SC.b false)))
    (hLeft : SFormula.Deriv Γ (.eqBool (SC.closed (leftCellGuardTA dT kT)) (SC.b true)))
    (hInside : SFormula.Deriv Γ (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b false))) :
    SFormula.Deriv Γ
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed qT))
        (SC.closed (.ite (leftOuterGuardTA dT kT qT) (.pauliLit Pauli.Z) (.pauliLit Pauli.I)))) := by
  simp only [SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
    SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q,
    codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4, orEqSucc, le,
    leftOuterGuardTA, rowTA, colTA, rTA, dm1TA]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.stabAtClosedIteLamEqThen _ _ _ qT hq (baseBulkSelectTrueD dT kT qT hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift,
    Nat.lt_irrefl, dite_false, dite_true]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← interiorCellGuardTA_simp]; exact hInterior))
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← topCellGuardTA_simp]; exact hTop))
      (SFormula.Deriv.eqPauliTrans _ _ _
        (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← rightCellGuardTA_simp]; exact hRight))
        (SFormula.Deriv.eqPauliTrans _ _ _
          (SFormula.Deriv.pauliIteSelectThen _ _ _ (by rw [← leftCellGuardTA_simp]; exact hLeft))
          (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← insideGuardTA_simp]; exact hInside)))))

/-- Deriv-level bottom-promoted-inside peel, finished by the IH `pBottom`. -/
def recBottomPromotedPeelD {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (pBottom : Term arity .pauli)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : SFormula.Deriv Γ (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b false)))
    (hRight : SFormula.Deriv Γ (.eqBool (SC.closed (rightCellGuardTA dT kT)) (SC.b false)))
    (hLeft : SFormula.Deriv Γ (.eqBool (SC.closed (leftCellGuardTA dT kT)) (SC.b false)))
    (hBottom : SFormula.Deriv Γ (.eqBool (SC.closed (bottomCellGuardTA dT kT)) (SC.b true)))
    (hInside : SFormula.Deriv Γ (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b true)))
    (ih : SFormula.Deriv Γ (.eqPauli (SC.closed (promotedInnerRefA dT qT (bottomKTA dT kT))) (SC.closed pBottom))) :
    SFormula.Deriv Γ
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed qT))
        (SC.closed pBottom)) := by
  simp only [SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
    SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q,
    codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4, orEqSucc, le]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.stabAtClosedIteLamEqThen _ _ _ qT hq (baseBulkSelectTrueD dT kT qT hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift,
    Nat.lt_irrefl, dite_false, dite_true]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← interiorCellGuardTA_simp]; exact hInterior))
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← topCellGuardTA_simp]; exact hTop))
      (SFormula.Deriv.eqPauliTrans _ _ _
        (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← rightCellGuardTA_simp]; exact hRight))
        (SFormula.Deriv.eqPauliTrans _ _ _
          (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← leftCellGuardTA_simp]; exact hLeft))
          (SFormula.Deriv.eqPauliTrans _ _ _
            (SFormula.Deriv.pauliIteSelectThen _ _ _ (by rw [← bottomCellGuardTA_simp]; exact hBottom))
            (SFormula.Deriv.eqPauliTrans _ _ _
              (SFormula.Deriv.pauliIteSelectThen _ _ _ (by rw [← insideGuardTA_simp]; exact hInside))
              ih)))))

/-- Deriv-level bottom-promoted-not-inside peel → `ite bottomOuter X I`. -/
def recBottomPromotedNotInsidePeelD {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : SFormula.Deriv Γ (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b false)))
    (hRight : SFormula.Deriv Γ (.eqBool (SC.closed (rightCellGuardTA dT kT)) (SC.b false)))
    (hLeft : SFormula.Deriv Γ (.eqBool (SC.closed (leftCellGuardTA dT kT)) (SC.b false)))
    (hBottom : SFormula.Deriv Γ (.eqBool (SC.closed (bottomCellGuardTA dT kT)) (SC.b true)))
    (hInside : SFormula.Deriv Γ (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b false))) :
    SFormula.Deriv Γ
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed qT))
        (SC.closed (.ite (bottomOuterGuardTA dT kT qT) (.pauliLit Pauli.X) (.pauliLit Pauli.I)))) := by
  simp only [SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
    SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q,
    codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4, orEqSucc, le,
    bottomOuterGuardTA, rowTA, colTA, cTA, dm1TA]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.stabAtClosedIteLamEqThen _ _ _ qT hq (baseBulkSelectTrueD dT kT qT hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift,
    Nat.lt_irrefl, dite_false, dite_true]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← interiorCellGuardTA_simp]; exact hInterior))
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← topCellGuardTA_simp]; exact hTop))
      (SFormula.Deriv.eqPauliTrans _ _ _
        (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← rightCellGuardTA_simp]; exact hRight))
        (SFormula.Deriv.eqPauliTrans _ _ _
          (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← leftCellGuardTA_simp]; exact hLeft))
          (SFormula.Deriv.eqPauliTrans _ _ _
            (SFormula.Deriv.pauliIteSelectThen _ _ _ (by rw [← bottomCellGuardTA_simp]; exact hBottom))
            (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← insideGuardTA_simp]; exact hInside))))))

/-! ### Instantiated-form base reduction (for the fallback / boundary leaves)

The recursive entry's fallback (all cells false) and out-of-bulk (`bulk` false)
branches delegate to `baseEntry`.  After the recursive cell-`ite` selections the
residual is the *instantiated* base-entry tree `instantiateTopNat qT baseEntry`,
which is **definitionally `baseLeafTreeTA dT kT qT`** (the same guard/leaf
structure).  `baseLeafSelfEq` provides the `eqPauli baseLeafTreeTA baseLeafTreeTA`
reflexivity (there is no general `Deriv` Pauli-refl, so it is built by the same
`boolCases` dispatch, closing each literal leaf with `pauliEqLit`). -/

/-- `eqPauli baseLeafTreeTA baseLeafTreeTA` by `boolCases` dispatch + `pauliEqLit`. -/
def baseLeafSelfEq {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.closed (baseLeafTreeTA dT kT qT))) := by
  refine SFormula.Deriv.boolCases (SC.closed (bulkGuardTA dT kT)) _ ?_ ?_
  · refine SFormula.Deriv.boolCases (SC.closed (baseBulkBandGuardTA dT kT qT)) _ ?_ ?_
    · refine SFormula.Deriv.boolCases (SC.closed (baseKindGuardTA dT kT)) _ ?_ ?_
      · exact SFormula.Deriv.eqPauliTrans _ _ _
          (leafZ dT kT qT (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption)
          (SFormula.Deriv.eqPauliSymm _ _
            (leafZ dT kT qT (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption))
      · exact SFormula.Deriv.eqPauliTrans _ _ _
          (leafBulkX dT kT qT (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption)
          (SFormula.Deriv.eqPauliSymm _ _
            (leafBulkX dT kT qT (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption))
    · exact SFormula.Deriv.eqPauliTrans _ _ _
        (leafBulkI dT kT qT (.hyp (by right; left)) .assumption)
        (SFormula.Deriv.eqPauliSymm _ _ (leafBulkI dT kT qT (.hyp (by right; left)) .assumption))
  · refine SFormula.Deriv.boolCases (SC.closed (topClassGuardTA dT kT)) _ ?_ ?_
    · refine SFormula.Deriv.boolCases (SC.closed (topBandGuardTA dT kT qT)) _ ?_ ?_
      · exact SFormula.Deriv.eqPauliTrans _ _ _
          (leafTopX dT kT qT (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption)
          (SFormula.Deriv.eqPauliSymm _ _
            (leafTopX dT kT qT (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption))
      · exact SFormula.Deriv.eqPauliTrans _ _ _
          (leafTopI dT kT qT (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption)
          (SFormula.Deriv.eqPauliSymm _ _
            (leafTopI dT kT qT (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption))
    · refine SFormula.Deriv.boolCases (SC.closed (rightClassGuardTA dT kT)) _ ?_ ?_
      · refine SFormula.Deriv.boolCases (SC.closed (rightBandGuardTA dT kT qT)) _ ?_ ?_
        · exact SFormula.Deriv.eqPauliTrans _ _ _
            (leafRightZ dT kT qT (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
              (.hyp (by right; left)) .assumption)
            (SFormula.Deriv.eqPauliSymm _ _
              (leafRightZ dT kT qT (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
                (.hyp (by right; left)) .assumption))
        · exact SFormula.Deriv.eqPauliTrans _ _ _
            (leafRightI dT kT qT (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
              (.hyp (by right; left)) .assumption)
            (SFormula.Deriv.eqPauliSymm _ _
              (leafRightI dT kT qT (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
                (.hyp (by right; left)) .assumption))
      · refine SFormula.Deriv.boolCases (SC.closed (leftClassGuardTA dT kT)) _ ?_ ?_
        · refine SFormula.Deriv.boolCases (SC.closed (leftBandGuardTA dT kT qT)) _ ?_ ?_
          · exact SFormula.Deriv.eqPauliTrans _ _ _
              (leafLeftZ dT kT qT (.hyp (by right; right; right; right; left))
                (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
                (.hyp (by right; left)) .assumption)
              (SFormula.Deriv.eqPauliSymm _ _
                (leafLeftZ dT kT qT (.hyp (by right; right; right; right; left))
                  (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
                  (.hyp (by right; left)) .assumption))
          · exact SFormula.Deriv.eqPauliTrans _ _ _
              (leafLeftI dT kT qT (.hyp (by right; right; right; right; left))
                (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
                (.hyp (by right; left)) .assumption)
              (SFormula.Deriv.eqPauliSymm _ _
                (leafLeftI dT kT qT (.hyp (by right; right; right; right; left))
                  (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
                  (.hyp (by right; left)) .assumption))
        · refine SFormula.Deriv.boolCases (SC.closed (bottomBandGuardTA dT kT qT)) _ ?_ ?_
          · exact SFormula.Deriv.eqPauliTrans _ _ _
              (leafBottomX dT kT qT (.hyp (by right; right; right; right; left))
                (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
                (.hyp (by right; left)) .assumption)
              (SFormula.Deriv.eqPauliSymm _ _
                (leafBottomX dT kT qT (.hyp (by right; right; right; right; left))
                  (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
                  (.hyp (by right; left)) .assumption))
          · exact SFormula.Deriv.eqPauliTrans _ _ _
              (leafBottomI dT kT qT (.hyp (by right; right; right; right; left))
                (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
                (.hyp (by right; left)) .assumption)
              (SFormula.Deriv.eqPauliSymm _ _
                (leafBottomI dT kT qT (.hyp (by right; right; right; right; left))
                  (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
                  (.hyp (by right; left)) .assumption))

/-- Boundary / fallback strip: `bulk` FALSE selects the recursive entry's
`baseEntry` else-branch, whose instantiation is definitionally `baseLeafTreeTA`. -/
def baseBoundaryStripD {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false))) :
    SFormula.Deriv Γ
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed qT))
        (SC.closed (baseLeafTreeTA dT kT qT))) := by
  simp only [SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
    SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q,
    codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4, orEqSucc, le]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.stabAtClosedIteLamEqElse _ _ _ qT hq (baseBulkSelectFalseD dT kT qT hBulk))
    ?_
  rw [show Term.instantiateTopNat qT (codeSubstAt dT kT 1 SurfaceASTPublic.baseEntry)
        = baseLeafTreeTA dT kT qT from by
    simp only [SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
      SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN, Term.weaken,
      Nat.reduceLT, Nat.reduceEqDiff, reduceDIte, eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq,
      Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift,
      baseLeafTreeTA, bulkGuardTA, bulkCountTA, dm1TA, baseBulkBandGuardTA, band3, orEqSucc,
      baseKindGuardTA, topClassGuardTA, baseBTA, baseHalfTA, topBandGuardTA, rightClassGuardTA,
      rightBandGuardTA, leftClassGuardTA, leftBandGuardTA, orEqPair, bottomBandGuardTA]]
  exact baseLeafSelfEq dT kT qT

/-- Fallback peel (bulk TRUE, no cell matched) → `baseLeafTreeTA`. -/
def recFallbackPeelD {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : SFormula.Deriv Γ (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b false)))
    (hRight : SFormula.Deriv Γ (.eqBool (SC.closed (rightCellGuardTA dT kT)) (SC.b false)))
    (hLeft : SFormula.Deriv Γ (.eqBool (SC.closed (leftCellGuardTA dT kT)) (SC.b false)))
    (hBottom : SFormula.Deriv Γ (.eqBool (SC.closed (bottomCellGuardTA dT kT)) (SC.b false))) :
    SFormula.Deriv Γ
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed qT))
        (SC.closed (baseLeafTreeTA dT kT qT))) := by
  simp only [SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
    SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q,
    codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4, orEqSucc, le]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.stabAtClosedIteLamEqThen _ _ _ qT hq (baseBulkSelectTrueD dT kT qT hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift,
    Nat.lt_irrefl, dite_false, dite_true]
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← interiorCellGuardTA_simp]; exact hInterior))
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← topCellGuardTA_simp]; exact hTop))
      (SFormula.Deriv.eqPauliTrans _ _ _
        (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← rightCellGuardTA_simp]; exact hRight))
        (SFormula.Deriv.eqPauliTrans _ _ _
          (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← leftCellGuardTA_simp]; exact hLeft))
          (SFormula.Deriv.eqPauliTrans _ _ _
            (SFormula.Deriv.pauliIteSelectElse _ _ _ (by rw [← bottomCellGuardTA_simp]; exact hBottom))
            (by
              have hbe : Term.instantiateNatAt 0 qT (by omega)
                    (codeSubstAt dT kT 1 SurfaceASTPublic.baseEntry)
                    = baseLeafTreeTA dT kT qT := by
                simp only [SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
                  SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN,
                  Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte, eq_mp_eq_cast,
                  eq_mpr_eq_cast, cast_eq, Term.instantiateNatAt, instTop_lift,
                  baseLeafTreeTA, bulkGuardTA, bulkCountTA, dm1TA, baseBulkBandGuardTA, band3,
                  orEqSucc, baseKindGuardTA, topClassGuardTA, baseBTA, baseHalfTA, topBandGuardTA,
                  rightClassGuardTA, rightBandGuardTA, leftClassGuardTA, leftBandGuardTA, orEqPair,
                  bottomBandGuardTA]
              rw [hbe]
              exact baseLeafSelfEq dT kT qT)))))

/-! ### `recLeafTreeTA` reductions to a leaf (given guards as Deriv premises)

As with `baseLeafTreeTA`, `recLeafTreeTA` is built directly from the `*GuardTA`
guards, so `pauliIteSelectThen/Else` applies verbatim. -/

def recLeafInt {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b true)))
    (hInside : SFormula.Deriv Γ (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b true))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (recLeafTreeTA dT kT qT pInt pTop pRight pLeft pBottom)) (SC.closed pInt)) := by
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectThen _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectThen _ _ _ hInterior)
      (SFormula.Deriv.pauliIteSelectThen _ _ _ hInside))

def recLeafIntI {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b true)))
    (hInside : SFormula.Deriv Γ (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b false))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (recLeafTreeTA dT kT qT pInt pTop pRight pLeft pBottom))
        (SC.closed (.pauliLit Pauli.I))) := by
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectThen _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectThen _ _ _ hInterior)
      (SFormula.Deriv.pauliIteSelectElse _ _ _ hInside))

def recLeafTop {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : SFormula.Deriv Γ (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b true)))
    (hInside : SFormula.Deriv Γ (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b true))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (recLeafTreeTA dT kT qT pInt pTop pRight pLeft pBottom)) (SC.closed pTop)) := by
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectThen _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectElse _ _ _ hInterior)
      (SFormula.Deriv.eqPauliTrans _ _ _
        (SFormula.Deriv.pauliIteSelectThen _ _ _ hTop)
        (SFormula.Deriv.pauliIteSelectThen _ _ _ hInside)))

def recLeafTopNI {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : SFormula.Deriv Γ (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b true)))
    (hInside : SFormula.Deriv Γ (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b false))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (recLeafTreeTA dT kT qT pInt pTop pRight pLeft pBottom))
        (SC.closed (.ite (topOuterGuardTA dT kT qT) (.pauliLit Pauli.X) (.pauliLit Pauli.I)))) := by
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectThen _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectElse _ _ _ hInterior)
      (SFormula.Deriv.eqPauliTrans _ _ _
        (SFormula.Deriv.pauliIteSelectThen _ _ _ hTop)
        (SFormula.Deriv.pauliIteSelectElse _ _ _ hInside)))

def recLeafRight {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : SFormula.Deriv Γ (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b false)))
    (hRight : SFormula.Deriv Γ (.eqBool (SC.closed (rightCellGuardTA dT kT)) (SC.b true)))
    (hInside : SFormula.Deriv Γ (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b true))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (recLeafTreeTA dT kT qT pInt pTop pRight pLeft pBottom)) (SC.closed pRight)) := by
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectThen _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectElse _ _ _ hInterior)
      (SFormula.Deriv.eqPauliTrans _ _ _
        (SFormula.Deriv.pauliIteSelectElse _ _ _ hTop)
        (SFormula.Deriv.eqPauliTrans _ _ _
          (SFormula.Deriv.pauliIteSelectThen _ _ _ hRight)
          (SFormula.Deriv.pauliIteSelectThen _ _ _ hInside))))

def recLeafRightNI {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : SFormula.Deriv Γ (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b false)))
    (hRight : SFormula.Deriv Γ (.eqBool (SC.closed (rightCellGuardTA dT kT)) (SC.b true)))
    (hInside : SFormula.Deriv Γ (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b false))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (recLeafTreeTA dT kT qT pInt pTop pRight pLeft pBottom))
        (SC.closed (.ite (rightOuterGuardTA dT kT qT) (.pauliLit Pauli.Z) (.pauliLit Pauli.I)))) := by
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectThen _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectElse _ _ _ hInterior)
      (SFormula.Deriv.eqPauliTrans _ _ _
        (SFormula.Deriv.pauliIteSelectElse _ _ _ hTop)
        (SFormula.Deriv.eqPauliTrans _ _ _
          (SFormula.Deriv.pauliIteSelectThen _ _ _ hRight)
          (SFormula.Deriv.pauliIteSelectElse _ _ _ hInside))))

def recLeafLeft {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : SFormula.Deriv Γ (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b false)))
    (hRight : SFormula.Deriv Γ (.eqBool (SC.closed (rightCellGuardTA dT kT)) (SC.b false)))
    (hLeft : SFormula.Deriv Γ (.eqBool (SC.closed (leftCellGuardTA dT kT)) (SC.b true)))
    (hInside : SFormula.Deriv Γ (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b true))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (recLeafTreeTA dT kT qT pInt pTop pRight pLeft pBottom)) (SC.closed pLeft)) := by
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectThen _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectElse _ _ _ hInterior)
      (SFormula.Deriv.eqPauliTrans _ _ _
        (SFormula.Deriv.pauliIteSelectElse _ _ _ hTop)
        (SFormula.Deriv.eqPauliTrans _ _ _
          (SFormula.Deriv.pauliIteSelectElse _ _ _ hRight)
          (SFormula.Deriv.eqPauliTrans _ _ _
            (SFormula.Deriv.pauliIteSelectThen _ _ _ hLeft)
            (SFormula.Deriv.pauliIteSelectThen _ _ _ hInside)))))

def recLeafLeftNI {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : SFormula.Deriv Γ (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b false)))
    (hRight : SFormula.Deriv Γ (.eqBool (SC.closed (rightCellGuardTA dT kT)) (SC.b false)))
    (hLeft : SFormula.Deriv Γ (.eqBool (SC.closed (leftCellGuardTA dT kT)) (SC.b true)))
    (hInside : SFormula.Deriv Γ (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b false))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (recLeafTreeTA dT kT qT pInt pTop pRight pLeft pBottom))
        (SC.closed (.ite (leftOuterGuardTA dT kT qT) (.pauliLit Pauli.Z) (.pauliLit Pauli.I)))) := by
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectThen _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectElse _ _ _ hInterior)
      (SFormula.Deriv.eqPauliTrans _ _ _
        (SFormula.Deriv.pauliIteSelectElse _ _ _ hTop)
        (SFormula.Deriv.eqPauliTrans _ _ _
          (SFormula.Deriv.pauliIteSelectElse _ _ _ hRight)
          (SFormula.Deriv.eqPauliTrans _ _ _
            (SFormula.Deriv.pauliIteSelectThen _ _ _ hLeft)
            (SFormula.Deriv.pauliIteSelectElse _ _ _ hInside)))))

def recLeafBottom {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : SFormula.Deriv Γ (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b false)))
    (hRight : SFormula.Deriv Γ (.eqBool (SC.closed (rightCellGuardTA dT kT)) (SC.b false)))
    (hLeft : SFormula.Deriv Γ (.eqBool (SC.closed (leftCellGuardTA dT kT)) (SC.b false)))
    (hBottom : SFormula.Deriv Γ (.eqBool (SC.closed (bottomCellGuardTA dT kT)) (SC.b true)))
    (hInside : SFormula.Deriv Γ (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b true))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (recLeafTreeTA dT kT qT pInt pTop pRight pLeft pBottom)) (SC.closed pBottom)) := by
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectThen _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectElse _ _ _ hInterior)
      (SFormula.Deriv.eqPauliTrans _ _ _
        (SFormula.Deriv.pauliIteSelectElse _ _ _ hTop)
        (SFormula.Deriv.eqPauliTrans _ _ _
          (SFormula.Deriv.pauliIteSelectElse _ _ _ hRight)
          (SFormula.Deriv.eqPauliTrans _ _ _
            (SFormula.Deriv.pauliIteSelectElse _ _ _ hLeft)
            (SFormula.Deriv.eqPauliTrans _ _ _
              (SFormula.Deriv.pauliIteSelectThen _ _ _ hBottom)
              (SFormula.Deriv.pauliIteSelectThen _ _ _ hInside))))))

def recLeafBottomNI {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : SFormula.Deriv Γ (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b false)))
    (hRight : SFormula.Deriv Γ (.eqBool (SC.closed (rightCellGuardTA dT kT)) (SC.b false)))
    (hLeft : SFormula.Deriv Γ (.eqBool (SC.closed (leftCellGuardTA dT kT)) (SC.b false)))
    (hBottom : SFormula.Deriv Γ (.eqBool (SC.closed (bottomCellGuardTA dT kT)) (SC.b true)))
    (hInside : SFormula.Deriv Γ (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b false))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (recLeafTreeTA dT kT qT pInt pTop pRight pLeft pBottom))
        (SC.closed (.ite (bottomOuterGuardTA dT kT qT) (.pauliLit Pauli.X) (.pauliLit Pauli.I)))) := by
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectThen _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectElse _ _ _ hInterior)
      (SFormula.Deriv.eqPauliTrans _ _ _
        (SFormula.Deriv.pauliIteSelectElse _ _ _ hTop)
        (SFormula.Deriv.eqPauliTrans _ _ _
          (SFormula.Deriv.pauliIteSelectElse _ _ _ hRight)
          (SFormula.Deriv.eqPauliTrans _ _ _
            (SFormula.Deriv.pauliIteSelectElse _ _ _ hLeft)
            (SFormula.Deriv.eqPauliTrans _ _ _
              (SFormula.Deriv.pauliIteSelectThen _ _ _ hBottom)
              (SFormula.Deriv.pauliIteSelectElse _ _ _ hInside))))))

def recLeafFallback {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : SFormula.Deriv Γ (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b false)))
    (hRight : SFormula.Deriv Γ (.eqBool (SC.closed (rightCellGuardTA dT kT)) (SC.b false)))
    (hLeft : SFormula.Deriv Γ (.eqBool (SC.closed (leftCellGuardTA dT kT)) (SC.b false)))
    (hBottom : SFormula.Deriv Γ (.eqBool (SC.closed (bottomCellGuardTA dT kT)) (SC.b false))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (recLeafTreeTA dT kT qT pInt pTop pRight pLeft pBottom))
        (SC.closed (baseLeafTreeTA dT kT qT))) := by
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectThen _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectElse _ _ _ hInterior)
      (SFormula.Deriv.eqPauliTrans _ _ _
        (SFormula.Deriv.pauliIteSelectElse _ _ _ hTop)
        (SFormula.Deriv.eqPauliTrans _ _ _
          (SFormula.Deriv.pauliIteSelectElse _ _ _ hRight)
          (SFormula.Deriv.eqPauliTrans _ _ _
            (SFormula.Deriv.pauliIteSelectElse _ _ _ hLeft)
            (SFormula.Deriv.pauliIteSelectElse _ _ _ hBottom)))))

def recLeafBoundary {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (recLeafTreeTA dT kT qT pInt pTop pRight pLeft pBottom))
        (SC.closed (baseLeafTreeTA dT kT qT))) :=
  SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk

/-! ### The recursive-case master reduction (converging `boolCases` dispatch)

A single `SFormula.Deriv` reducing the substituted recursive-entry stabLam-tree at
`qT` to `recLeafTreeTA`, dispatching on every cell-kind guard via `boolCases`.  The
five recursing inside-cells (`interior` + the four promoted boundaries) are closed
by the supplied **IH** premises `pIntD/pTopD/pRightD/pLeftD/pBottomD`; the
non-recursing leaves reduce as in the base case.  The IH premises are weakened
into each `boolCases` branch via `contextWeakening`. -/
def recEntryMasterD {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hq : SFormula.PureNatTerm qT)
    (pIntD : SFormula.Deriv Γ (.eqPauli (SC.closed (centerInnerRefA dT kT qT)) (SC.closed pInt)))
    (pTopD : SFormula.Deriv Γ (.eqPauli (SC.closed (promotedInnerRefA dT qT (topKTA dT kT))) (SC.closed pTop)))
    (pRightD : SFormula.Deriv Γ (.eqPauli (SC.closed (promotedInnerRefA dT qT (rightKTA dT kT))) (SC.closed pRight)))
    (pLeftD : SFormula.Deriv Γ (.eqPauli (SC.closed (promotedInnerRefA dT qT (leftKTA dT kT))) (SC.closed pLeft)))
    (pBottomD : SFormula.Deriv Γ (.eqPauli (SC.closed (promotedInnerRefA dT qT (bottomKTA dT kT))) (SC.closed pBottom))) :
    SFormula.Deriv Γ
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed qT))
        (SC.closed (recLeafTreeTA dT kT qT pInt pTop pRight pLeft pBottom))) := by
  -- `wk` weakens a `Γ`-level IH premise into the current (deeper) branch context.
  refine SFormula.Deriv.boolCases (SC.closed (bulkGuardTA dT kT)) _ ?_ ?_
  · -- bulk = true
    refine SFormula.Deriv.boolCases (SC.closed (interiorCellGuardTA dT kT)) _ ?_ ?_
    · -- interiorCell = true  (ctx: inside :: interior :: bulk :: Γ)
      refine SFormula.Deriv.boolCases (SC.closed (insideGuardTA dT qT)) _ ?_ ?_
      · -- inside = true → interior IH
        exact SFormula.Deriv.eqPauliTrans _ _ _
          (recInteriorPeelD dT kT qT pInt hq (.hyp (by right; right; left)) (.hyp (by right; left))
            .assumption
            (SFormula.Deriv.contextWeakening (by intro C hC; simp_all) pIntD))
          (SFormula.Deriv.eqPauliSymm _ _
            (recLeafInt dT kT qT pInt pTop pRight pLeft pBottom
              (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption))
      · -- inside = false → I
        exact SFormula.Deriv.eqPauliTrans _ _ _
          (recInteriorIPeelD dT kT qT hq (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption)
          (SFormula.Deriv.eqPauliSymm _ _
            (recLeafIntI dT kT qT pInt pTop pRight pLeft pBottom
              (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption))
    · -- interiorCell = false
      refine SFormula.Deriv.boolCases (SC.closed (topCellGuardTA dT kT)) _ ?_ ?_
      · -- topCell = true  (ctx: inside :: top :: interior :: bulk :: Γ)
        refine SFormula.Deriv.boolCases (SC.closed (insideGuardTA dT qT)) _ ?_ ?_
        · -- inside = true → top IH
          exact SFormula.Deriv.eqPauliTrans _ _ _
            (recTopPromotedPeelD dT kT qT pTop hq (.hyp (by right; right; right; left))
              (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption
              (SFormula.Deriv.contextWeakening (by intro C hC; simp_all) pTopD))
            (SFormula.Deriv.eqPauliSymm _ _
              (recLeafTop dT kT qT pInt pTop pRight pLeft pBottom (.hyp (by right; right; right; left))
                (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption))
        · -- inside = false → ite topOuter X I
          exact SFormula.Deriv.eqPauliTrans _ _ _
            (recTopPromotedNotInsidePeelD dT kT qT hq (.hyp (by right; right; right; left))
              (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption)
            (SFormula.Deriv.eqPauliSymm _ _
              (recLeafTopNI dT kT qT pInt pTop pRight pLeft pBottom (.hyp (by right; right; right; left))
                (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption))
      · -- topCell = false
        refine SFormula.Deriv.boolCases (SC.closed (rightCellGuardTA dT kT)) _ ?_ ?_
        · -- rightCell = true  (ctx: inside :: right :: top :: interior :: bulk :: Γ)
          refine SFormula.Deriv.boolCases (SC.closed (insideGuardTA dT qT)) _ ?_ ?_
          · -- inside = true → right IH
            exact SFormula.Deriv.eqPauliTrans _ _ _
              (recRightPromotedPeelD dT kT qT pRight hq (.hyp (by right; right; right; right; left))
                (.hyp (by right; right; right; left)) (.hyp (by right; right; left)) (.hyp (by right; left))
                .assumption
                (SFormula.Deriv.contextWeakening (by intro C hC; simp_all) pRightD))
              (SFormula.Deriv.eqPauliSymm _ _
                (recLeafRight dT kT qT pInt pTop pRight pLeft pBottom (.hyp (by right; right; right; right; left))
                  (.hyp (by right; right; right; left)) (.hyp (by right; right; left)) (.hyp (by right; left))
                  .assumption))
          · -- inside = false → ite rightOuter Z I
            exact SFormula.Deriv.eqPauliTrans _ _ _
              (recRightPromotedNotInsidePeelD dT kT qT hq (.hyp (by right; right; right; right; left))
                (.hyp (by right; right; right; left)) (.hyp (by right; right; left)) (.hyp (by right; left))
                .assumption)
              (SFormula.Deriv.eqPauliSymm _ _
                (recLeafRightNI dT kT qT pInt pTop pRight pLeft pBottom (.hyp (by right; right; right; right; left))
                  (.hyp (by right; right; right; left)) (.hyp (by right; right; left)) (.hyp (by right; left))
                  .assumption))
        · -- rightCell = false
          refine SFormula.Deriv.boolCases (SC.closed (leftCellGuardTA dT kT)) _ ?_ ?_
          · -- leftCell = true  (ctx: inside :: left :: right :: top :: interior :: bulk :: Γ)
            refine SFormula.Deriv.boolCases (SC.closed (insideGuardTA dT qT)) _ ?_ ?_
            · -- inside = true → left IH
              exact SFormula.Deriv.eqPauliTrans _ _ _
                (recLeftPromotedPeelD dT kT qT pLeft hq (.hyp (by right; right; right; right; right; left))
                  (.hyp (by right; right; right; right; left)) (.hyp (by right; right; right; left))
                  (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption
                  (SFormula.Deriv.contextWeakening (by intro C hC; simp_all) pLeftD))
                (SFormula.Deriv.eqPauliSymm _ _
                  (recLeafLeft dT kT qT pInt pTop pRight pLeft pBottom (.hyp (by right; right; right; right; right; left))
                    (.hyp (by right; right; right; right; left)) (.hyp (by right; right; right; left))
                    (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption))
            · -- inside = false → ite leftOuter Z I
              exact SFormula.Deriv.eqPauliTrans _ _ _
                (recLeftPromotedNotInsidePeelD dT kT qT hq (.hyp (by right; right; right; right; right; left))
                  (.hyp (by right; right; right; right; left)) (.hyp (by right; right; right; left))
                  (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption)
                (SFormula.Deriv.eqPauliSymm _ _
                  (recLeafLeftNI dT kT qT pInt pTop pRight pLeft pBottom (.hyp (by right; right; right; right; right; left))
                    (.hyp (by right; right; right; right; left)) (.hyp (by right; right; right; left))
                    (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption))
          · -- leftCell = false
            refine SFormula.Deriv.boolCases (SC.closed (bottomCellGuardTA dT kT)) _ ?_ ?_
            · -- bottomCell = true  (ctx: inside :: bottom :: left :: right :: top :: interior :: bulk :: Γ)
              refine SFormula.Deriv.boolCases (SC.closed (insideGuardTA dT qT)) _ ?_ ?_
              · -- inside = true → bottom IH
                exact SFormula.Deriv.eqPauliTrans _ _ _
                  (recBottomPromotedPeelD dT kT qT pBottom hq
                    (.hyp (by right; right; right; right; right; right; left))
                    (.hyp (by right; right; right; right; right; left))
                    (.hyp (by right; right; right; right; left)) (.hyp (by right; right; right; left))
                    (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption
                    (SFormula.Deriv.contextWeakening (by intro C hC; simp_all) pBottomD))
                  (SFormula.Deriv.eqPauliSymm _ _
                    (recLeafBottom dT kT qT pInt pTop pRight pLeft pBottom
                      (.hyp (by right; right; right; right; right; right; left))
                      (.hyp (by right; right; right; right; right; left))
                      (.hyp (by right; right; right; right; left)) (.hyp (by right; right; right; left))
                      (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption))
              · -- inside = false → ite bottomOuter X I
                exact SFormula.Deriv.eqPauliTrans _ _ _
                  (recBottomPromotedNotInsidePeelD dT kT qT hq
                    (.hyp (by right; right; right; right; right; right; left))
                    (.hyp (by right; right; right; right; right; left))
                    (.hyp (by right; right; right; right; left)) (.hyp (by right; right; right; left))
                    (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption)
                  (SFormula.Deriv.eqPauliSymm _ _
                    (recLeafBottomNI dT kT qT pInt pTop pRight pLeft pBottom
                      (.hyp (by right; right; right; right; right; right; left))
                      (.hyp (by right; right; right; right; right; left))
                      (.hyp (by right; right; right; right; left)) (.hyp (by right; right; right; left))
                      (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption))
            · -- bottomCell = false → fallback baseEntry
              -- (ctx: bottom :: left :: right :: top :: interior :: bulk :: Γ)
              exact SFormula.Deriv.eqPauliTrans _ _ _
                (recFallbackPeelD dT kT qT hq (.hyp (by right; right; right; right; right; left))
                  (.hyp (by right; right; right; right; left)) (.hyp (by right; right; right; left))
                  (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption)
                (SFormula.Deriv.eqPauliSymm _ _
                  (recLeafFallback dT kT qT pInt pTop pRight pLeft pBottom
                    (.hyp (by right; right; right; right; right; left))
                    (.hyp (by right; right; right; right; left)) (.hyp (by right; right; right; left))
                    (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption))
  · -- bulk = false → boundary baseEntry
    exact SFormula.Deriv.eqPauliTrans _ _ _
      (baseBoundaryStripD dT kT qT hq .assumption)
      (SFormula.Deriv.eqPauliSymm _ _
        (recLeafBoundary dT kT qT pInt pTop pRight pLeft pBottom .assumption))

/-! ### The recursive-case converging row characterization (`cut1` + folded IH)

`cut1` discharges a single conjunction premise bundling the row projection and the
five IH equalities (mechanism (B): fold N premises into one conjunction).  Inside
the cut head each conjunct is recovered by `andElim` and routed through
`recEntryMasterD`.  The result: the generated recursive row entry at the symbolic
index equals `recLeafTreeTA`, with the recursing cells resolved by the IH. -/
def recRowConvergeA {fuel arity : Nat} (n : STerm arity .nat) (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hDist : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat dT (n5 : Term arity .nat))) (SC.b false)))
    (pIntA : PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (SC.closed (centerInnerRefA dT kT qT)) (SC.closed pInt)))
    (pTopA : PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (SC.closed (promotedInnerRefA dT qT (topKTA dT kT))) (SC.closed pTop)))
    (pRightA : PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (SC.closed (promotedInnerRefA dT qT (rightKTA dT kT))) (SC.closed pRight)))
    (pLeftA : PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (SC.closed (promotedInnerRefA dT qT (leftKTA dT kT))) (SC.closed pLeft)))
    (pBottomA : PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (SC.closed (promotedInnerRefA dT qT (bottomKTA dT kT))) (SC.closed pBottom))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (.stabAt (SC.closed (.recCall dT kT)) (SC.closed qT))
        (SC.closed (recLeafTreeTA dT kT qT pInt pTop pRight pLeft pBottom))) := by
  -- the row projection: stabAt(recCall dT kT) qT = stabAt (closed (stabLam recEntry-subst)) qT
  set P0 : SFormula arity :=
    .eqPauli (.stabAt (SC.closed (.recCall dT kT)) (SC.closed qT))
      (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry))) (SC.closed qT))
    with hP0
  set Pi : SFormula arity := .eqPauli (SC.closed (centerInnerRefA dT kT qT)) (SC.closed pInt)
  set Pt : SFormula arity := .eqPauli (SC.closed (promotedInnerRefA dT qT (topKTA dT kT))) (SC.closed pTop)
  set Pr : SFormula arity := .eqPauli (SC.closed (promotedInnerRefA dT qT (rightKTA dT kT))) (SC.closed pRight)
  set Pl : SFormula arity := .eqPauli (SC.closed (promotedInnerRefA dT qT (leftKTA dT kT))) (SC.closed pLeft)
  set Pb : SFormula arity := .eqPauli (SC.closed (promotedInnerRefA dT qT (bottomKTA dT kT))) (SC.closed pBottom)
  -- the row projection as a PFDA fact
  have hProj : PureFamilyDerivA Surface.code.body fuel P0 :=
    PureFamilyDerivA.eqPauliProj n
      (SC.closed (.recCall dT kT))
      (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
      (SC.closed qT)
      (surfaceCodeRowSelectRecursive n dT kT hd hk hDist)
  -- fold the six facts into one nested conjunction
  have hConj : PureFamilyDerivA Surface.code.body fuel
      (.and P0 (.and Pi (.and Pt (.and Pr (.and Pl Pb))))) :=
    PureFamilyDerivA.cut2
      (SFormula.Deriv.andIntro (SFormula.Deriv.hyp (by left))
        (SFormula.Deriv.hyp (by right; left)))
      hProj
      (PureFamilyDerivA.cut2
        (SFormula.Deriv.andIntro (SFormula.Deriv.hyp (by left)) (SFormula.Deriv.hyp (by right; left)))
        pIntA
        (PureFamilyDerivA.cut2
          (SFormula.Deriv.andIntro (SFormula.Deriv.hyp (by left)) (SFormula.Deriv.hyp (by right; left)))
          pTopA
          (PureFamilyDerivA.cut2
            (SFormula.Deriv.andIntro (SFormula.Deriv.hyp (by left)) (SFormula.Deriv.hyp (by right; left)))
            pRightA
            (PureFamilyDerivA.cut2
              (SFormula.Deriv.andIntro (SFormula.Deriv.hyp (by left)) (SFormula.Deriv.hyp (by right; left)))
              pLeftA pBottomA))))
  -- cut1: in the head, andElim each conjunct out of the single hypothesis, then dispatch
  refine PureFamilyDerivA.cut1 ?_ hConj
  refine SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.andElimLeft (SFormula.Deriv.hyp (by left)))
    (recEntryMasterD dT kT qT pInt pTop pRight pLeft pBottom hq
      (SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.hyp (by left))))
      (SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.hyp (by left)))))
      (SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.hyp (by left))))))
      (SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.hyp (by left)))))))
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.hyp (by left))))))))

#print axioms recRowConvergeA

/-! ## The genuine structural recursion on the distance index

`surfaceRowEntryCharSymbolic` resolves the generated row entry at a **symbolic**
(arbitrary pure, *no `evalsTo` value*) stabilizer index `kT` and qubit `qT`, to a
fully-resolved leaf tree `rowSymTree`.  It is genuine structural recursion on the
distance index `m`: the recursive case feeds the recursive call (the IH, at the
five inner indices) into `recRowConvergeA`.  Unlike `surfaceRowCharFull` (which
needs `kT`/`qT` *concrete* with `evalsTo` certificates and uses meta-level
`by_cases`), here the dispatch is the object-logic `boolCases`, so `kT`/`qT` stay
fully symbolic. -/

/-- The fully-resolved leaf tree at distance index `m`, distance term `dT`, index
`kT`, qubit `qT`.  Structural recursion on `m` mirroring the code's own recursion:
recursing inside-cells reference the tree one layer down at the inner indices. -/
def rowSymTree : (m : Nat) → (dT kT qT : Term 0 .nat) → Term 0 .pauli
  | 0, dT, kT, qT => baseLeafTreeTA dT kT qT
  | m + 1, dT, kT, qT =>
      recLeafTreeTA dT kT qT
        (rowSymTree m (innerDTA dT) (interiorKTA dT kT) (innerQTA dT qT))
        (rowSymTree m (recInnerDTA dT) (topKTA dT kT) (innerQTA dT qT))
        (rowSymTree m (recInnerDTA dT) (rightKTA dT kT) (innerQTA dT qT))
        (rowSymTree m (recInnerDTA dT) (leftKTA dT kT) (innerQTA dT qT))
        (rowSymTree m (recInnerDTA dT) (bottomKTA dT kT) (innerQTA dT qT))

/-- **The genuine structural recursion.**  At a symbolic pure index `kT` / qubit
`qT` the generated code row entry equals the resolved leaf tree `rowSymTree m`. -/
def surfaceRowEntryCharSymbolic {fuel : Nat} :
    (m : Nat) → (D : DistAt m) → (kT qT : Term 0 .nat) →
    SFormula.PureNatTerm kT → SFormula.PureNatTerm qT →
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.recCall D.dT kT)) (SC.closed qT))
        (SC.closed (rowSymTree m D.dT kT qT)))
  | 0, D, kT, qT, hk, hq => by
      -- base d = 3: converging boolCases dispatch to baseLeafTreeTA.
      have h := baseRowConvergeA (fuel := fuel) (SC.n (nQubits (oddDistance 0))) D.dT kT qT
        D.pure hk hq (distLtFiveTrue_of_DistAt D)
      simpa only [rowSymTree] using h
  | m + 1, D, kT, qT, hk, hq => by
      -- recursive d ≥ 5: converging dispatch, recursing cells via the IH.
      have ih : ∀ (kT' qT' : Term 0 .nat),
          SFormula.PureNatTerm kT' → SFormula.PureNatTerm qT' →
          PureFamilyDerivA Surface.code.body fuel
            (.eqPauli (.stabAt (SC.closed (.recCall D.pred.dT kT')) (SC.closed qT'))
              (SC.closed (rowSymTree m D.pred.dT kT' qT'))) :=
        fun kT' qT' hk' hq' => surfaceRowEntryCharSymbolic m D.pred kT' qT' hk' hq'
      -- the five IH equalities at the inner indices, retargeted to centerInnerRefA / promotedInnerRefA.
      have pIntA : PureFamilyDerivA Surface.code.body fuel
          (.eqPauli (SC.closed (centerInnerRefA D.dT kT qT))
            (SC.closed (rowSymTree m (innerDTA D.dT) (interiorKTA D.dT kT) (innerQTA D.dT qT)))) := by
        have := ih (interiorKTA D.dT kT) (innerQTA D.dT qT)
          (interiorKTA_pure D.pure hk) (innerQTA_pure D.pure hq)
        refine PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.closedStabAtSplit (.recCall (innerDTA D.dT) (interiorKTA D.dT kT)) (innerQTA D.dT qT)) ?_
        simpa only [centerInnerRefA, DistAt.pred] using this
      have pTopA : PureFamilyDerivA Surface.code.body fuel
          (.eqPauli (SC.closed (promotedInnerRefA D.dT qT (topKTA D.dT kT)))
            (SC.closed (rowSymTree m (recInnerDTA D.dT) (topKTA D.dT kT) (innerQTA D.dT qT)))) := by
        have := ih (topKTA D.dT kT) (innerQTA D.dT qT)
          (topKTA_pure D.pure hk) (innerQTA_pure D.pure hq)
        refine PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.closedStabAtSplit (.recCall (recInnerDTA D.dT) (topKTA D.dT kT)) (innerQTA D.dT qT)) ?_
        simpa only [promotedInnerRefA, recInnerDTA, DistAt.pred] using this
      have pRightA : PureFamilyDerivA Surface.code.body fuel
          (.eqPauli (SC.closed (promotedInnerRefA D.dT qT (rightKTA D.dT kT)))
            (SC.closed (rowSymTree m (recInnerDTA D.dT) (rightKTA D.dT kT) (innerQTA D.dT qT)))) := by
        have := ih (rightKTA D.dT kT) (innerQTA D.dT qT)
          (rightKTA_pure D.pure hk) (innerQTA_pure D.pure hq)
        refine PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.closedStabAtSplit (.recCall (recInnerDTA D.dT) (rightKTA D.dT kT)) (innerQTA D.dT qT)) ?_
        simpa only [promotedInnerRefA, recInnerDTA, DistAt.pred] using this
      have pLeftA : PureFamilyDerivA Surface.code.body fuel
          (.eqPauli (SC.closed (promotedInnerRefA D.dT qT (leftKTA D.dT kT)))
            (SC.closed (rowSymTree m (recInnerDTA D.dT) (leftKTA D.dT kT) (innerQTA D.dT qT)))) := by
        have := ih (leftKTA D.dT kT) (innerQTA D.dT qT)
          (leftKTA_pure D.pure hk) (innerQTA_pure D.pure hq)
        refine PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.closedStabAtSplit (.recCall (recInnerDTA D.dT) (leftKTA D.dT kT)) (innerQTA D.dT qT)) ?_
        simpa only [promotedInnerRefA, recInnerDTA, DistAt.pred] using this
      have pBottomA : PureFamilyDerivA Surface.code.body fuel
          (.eqPauli (SC.closed (promotedInnerRefA D.dT qT (bottomKTA D.dT kT)))
            (SC.closed (rowSymTree m (recInnerDTA D.dT) (bottomKTA D.dT kT) (innerQTA D.dT qT)))) := by
        have := ih (bottomKTA D.dT kT) (innerQTA D.dT qT)
          (bottomKTA_pure D.pure hk) (innerQTA_pure D.pure hq)
        refine PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.closedStabAtSplit (.recCall (recInnerDTA D.dT) (bottomKTA D.dT kT)) (innerQTA D.dT qT)) ?_
        simpa only [promotedInnerRefA, recInnerDTA, DistAt.pred] using this
      have h := recRowConvergeA (fuel := fuel) (SC.n (nQubits (oddDistance (m + 1)))) D.dT kT qT
        (rowSymTree m (innerDTA D.dT) (interiorKTA D.dT kT) (innerQTA D.dT qT))
        (rowSymTree m (recInnerDTA D.dT) (topKTA D.dT kT) (innerQTA D.dT qT))
        (rowSymTree m (recInnerDTA D.dT) (rightKTA D.dT kT) (innerQTA D.dT qT))
        (rowSymTree m (recInnerDTA D.dT) (leftKTA D.dT kT) (innerQTA D.dT qT))
        (rowSymTree m (recInnerDTA D.dT) (bottomKTA D.dT kT) (innerQTA D.dT qT))
        D.pure hk hq (distLtFiveFalse_of_DistAt D)
        pIntA pTopA pRightA pLeftA pBottomA
      simpa only [rowSymTree] using h

#print axioms surfaceRowEntryCharSymbolic

/-! ## TASK A — arity lift of the symbolic-index row characterization

`surfaceRowEntryCharSymbolic` (above) resolves the generated row entry at a
symbolic *index*/*qubit* (`kT`/`qT`), but its distance witness `DistAt` carries an
**arity-0** distance term `dT : Term 0 .nat`, locking the whole statement to
arity 0.  The downstream consumers (the logical normalizers / pairwise-commutation
formulas) introduce the stabilizer index via `allNatLt numStab`, so inside the
body `kT` is the **object-logic bound variable** `boundIdx = .var 0` at arity ≥ 1.
The closed distance literal is still arity-0 in spirit, but the *type* of the
whole derivation must live at the consumer arity.

The lift is genuine plumbing: every combinator the recursion uses
(`baseRowConvergeA`, `recRowConvergeA`, the peels, the `*_pure` lemmas,
`closedStabAtSplit`, `n5`, `arithBool`) is already arity-polymorphic.  Only the
distance carrier (`DistAt`) and the resolved-leaf tree (`rowSymTree`) were
arity-0.  We restate both at an arbitrary arity and re-run the identical recursion.

The distance term is still required to evaluate to the fixed value `oddDistance m`
**independent of the environment** — the only thing that becomes symbolic is the
index/qubit, exactly as the consumer needs. -/

/-- Arity-general distance carrier: a pure Nat distance term at arity `arity`
together with a proof it evaluates (at every fuel, under the canonical body, in
*every* environment) to the fixed value `oddDistance m`.  The arity-0 instance
`DistAt` is the special case `arity = 0`. -/
structure DistAtA (arity : Nat) (m : Nat) where
  dT : Term arity .nat
  pure : SFormula.PureNatTerm dT
  evalsTo : ∀ {fuel : Nat} (rho : Env arity),
    Term.eval Surface.code.body fuel dT rho = some (oddDistance m)

/-- The literal distance term at index `m`, arity-general. -/
def DistAtA.lit (arity m : Nat) : DistAtA arity m where
  dT := .natLit (oddDistance m)
  pure := SFormula.PureNatTerm.nat (oddDistance m)
  evalsTo := by intro fuel rho; simp [Term.eval]

/-- Descend the distance term one recursion layer (`dT - 2`), arity-general.
Mirrors `DistAt.pred`. -/
def DistAtA.pred {arity m : Nat} (D : DistAtA arity (m + 1)) : DistAtA arity m where
  dT := .sub D.dT (.natLit 2)
  pure := SFormula.PureNatTerm.sub D.pure (SFormula.PureNatTerm.nat 2)
  evalsTo := by
    intro fuel rho
    simp only [Term.eval, D.evalsTo rho]
    have : oddDistance (m + 1) - 2 = oddDistance m := by
      simp [oddDistance]; omega
    simp [this]

/-- The `eqBool (closed cond) (b v)` formula is in the arithmetic-boolean fragment
whenever `cond` is a pure boolean term, arity-general.  (Arity-general analogue of
`pureBool_eqBool_in_fragment`, which is fixed at arity 0.) -/
private theorem pureBool_eqBool_in_fragmentA {arity : Nat} {cond : Term arity .bool}
    (v : Bool) (hc : SFormula.PureBoolTerm cond) :
    arithBoolFragment (.eqBool (SC.closed cond) (SC.b v)) = true := by
  simp [arithBoolFragment, ArithBoolFragment.formula, ArithBoolFragment.sterm,
    SC.closed, SC.b, ArithBoolFragment.term, pureTerm_in_fragment hc]

/-- Discharge a closed pure-boolean guard from an `Env`-uniform `Term.eval`
certificate, arity-general (analogue of `guardTrueEval`). -/
private def guardTrueEvalA {fuel arity : Nat} {cond : Term arity .bool}
    (hc : SFormula.PureBoolTerm cond)
    (hEval : ∀ (rho : Env arity), Term.eval Surface.code.body fuel cond rho = some true) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed cond) (SC.b true)) :=
  PureFamilyDerivA.arithBool _ (pureBool_eqBool_in_fragmentA true hc) (by
    intro rho E
    simp [SFormula.eval, STerm.eval, Term.eval, SC.closed, SC.b, hEval rho])

private def guardFalseEvalA {fuel arity : Nat} {cond : Term arity .bool}
    (hc : SFormula.PureBoolTerm cond)
    (hEval : ∀ (rho : Env arity), Term.eval Surface.code.body fuel cond rho = some false) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed cond) (SC.b false)) :=
  PureFamilyDerivA.arithBool _ (pureBool_eqBool_in_fragmentA false hc) (by
    intro rho E
    simp [SFormula.eval, STerm.eval, Term.eval, SC.closed, SC.b, hEval rho])

/-- The base distance guard `dT < 5` evaluates to `true` for a `DistAtA arity 0`,
arity-general (analogue of `distLtFiveTrue_of_DistAt`). -/
def distLtFiveTrue_of_DistAtA {fuel arity : Nat} (D : DistAtA arity 0) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat D.dT (n5 : Term arity .nat))) (SC.b true)) :=
  guardTrueEvalA (SFormula.PureBoolTerm.ltNat D.pure (SFormula.PureNatTerm.nat 5)) (by
    intro rho
    simp only [n5, Term.eval, D.evalsTo rho, Option.bind, Option.pure_def, Option.bind_eq_bind]
    decide)

/-- The recursive distance guard `dT < 5` evaluates to `false` for a
`DistAtA arity (m+1)`, arity-general (analogue of `distLtFiveFalse_of_DistAt`). -/
def distLtFiveFalse_of_DistAtA {fuel arity m : Nat} (D : DistAtA arity (m + 1)) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat D.dT (n5 : Term arity .nat))) (SC.b false)) :=
  guardFalseEvalA (SFormula.PureBoolTerm.ltNat D.pure (SFormula.PureNatTerm.nat 5)) (by
    intro rho
    have hlt : ¬ (oddDistance (m + 1) < 5) := by simp only [oddDistance]; omega
    simp only [n5, Term.eval, D.evalsTo rho, Option.bind, Option.pure_def, Option.bind_eq_bind,
      Option.some.injEq, decide_eq_false_iff_not, hlt, not_false_eq_true])

#print axioms distLtFiveTrue_of_DistAtA
#print axioms distLtFiveFalse_of_DistAtA

/-- The fully-resolved leaf tree at distance index `m`, arity-general (analogue of
`rowSymTree`).  Structurally identical: recursing inside-cells reference the tree
one layer down at the inner indices.  The genuine code entry, since the derivation
below is sound. -/
def rowSymTreeA {arity : Nat} : (m : Nat) → (dT kT qT : Term arity .nat) → Term arity .pauli
  | 0, dT, kT, qT => baseLeafTreeTA dT kT qT
  | m + 1, dT, kT, qT =>
      recLeafTreeTA dT kT qT
        (rowSymTreeA m (innerDTA dT) (interiorKTA dT kT) (innerQTA dT qT))
        (rowSymTreeA m (recInnerDTA dT) (topKTA dT kT) (innerQTA dT qT))
        (rowSymTreeA m (recInnerDTA dT) (rightKTA dT kT) (innerQTA dT qT))
        (rowSymTreeA m (recInnerDTA dT) (leftKTA dT kT) (innerQTA dT qT))
        (rowSymTreeA m (recInnerDTA dT) (bottomKTA dT kT) (innerQTA dT qT))

/-- **TASK A: the arity-general structural recursion.**  At a symbolic pure index
`kT` / qubit `qT` (arbitrary arity, in particular the object-logic bound variable
`boundIdx = .var 0`), the generated code row entry equals the resolved leaf tree
`rowSymTreeA m`.  Identical recursion to `surfaceRowEntryCharSymbolic`, now keyed
to a `DistAtA arity m` so it lives at the consumer arity. -/
def surfaceRowEntryCharSymbolicA {fuel arity : Nat} :
    (m : Nat) → (D : DistAtA arity m) → (kT qT : Term arity .nat) →
    SFormula.PureNatTerm kT → SFormula.PureNatTerm qT →
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.recCall D.dT kT)) (SC.closed qT))
        (SC.closed (rowSymTreeA m D.dT kT qT)))
  | 0, D, kT, qT, hk, hq => by
      have h := baseRowConvergeA (fuel := fuel) (SC.n (nQubits (oddDistance 0))) D.dT kT qT
        D.pure hk hq (distLtFiveTrue_of_DistAtA D)
      simpa only [rowSymTreeA] using h
  | m + 1, D, kT, qT, hk, hq => by
      have ih : ∀ (kT' qT' : Term arity .nat),
          SFormula.PureNatTerm kT' → SFormula.PureNatTerm qT' →
          PureFamilyDerivA Surface.code.body fuel
            (.eqPauli (.stabAt (SC.closed (.recCall D.pred.dT kT')) (SC.closed qT'))
              (SC.closed (rowSymTreeA m D.pred.dT kT' qT'))) :=
        fun kT' qT' hk' hq' => surfaceRowEntryCharSymbolicA m D.pred kT' qT' hk' hq'
      have pIntA : PureFamilyDerivA Surface.code.body fuel
          (.eqPauli (SC.closed (centerInnerRefA D.dT kT qT))
            (SC.closed (rowSymTreeA m (innerDTA D.dT) (interiorKTA D.dT kT) (innerQTA D.dT qT)))) := by
        have := ih (interiorKTA D.dT kT) (innerQTA D.dT qT)
          (interiorKTA_pure D.pure hk) (innerQTA_pure D.pure hq)
        refine PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.closedStabAtSplit (.recCall (innerDTA D.dT) (interiorKTA D.dT kT)) (innerQTA D.dT qT)) ?_
        simpa only [centerInnerRefA, DistAtA.pred] using this
      have pTopA : PureFamilyDerivA Surface.code.body fuel
          (.eqPauli (SC.closed (promotedInnerRefA D.dT qT (topKTA D.dT kT)))
            (SC.closed (rowSymTreeA m (recInnerDTA D.dT) (topKTA D.dT kT) (innerQTA D.dT qT)))) := by
        have := ih (topKTA D.dT kT) (innerQTA D.dT qT)
          (topKTA_pure D.pure hk) (innerQTA_pure D.pure hq)
        refine PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.closedStabAtSplit (.recCall (recInnerDTA D.dT) (topKTA D.dT kT)) (innerQTA D.dT qT)) ?_
        simpa only [promotedInnerRefA, recInnerDTA, DistAtA.pred] using this
      have pRightA : PureFamilyDerivA Surface.code.body fuel
          (.eqPauli (SC.closed (promotedInnerRefA D.dT qT (rightKTA D.dT kT)))
            (SC.closed (rowSymTreeA m (recInnerDTA D.dT) (rightKTA D.dT kT) (innerQTA D.dT qT)))) := by
        have := ih (rightKTA D.dT kT) (innerQTA D.dT qT)
          (rightKTA_pure D.pure hk) (innerQTA_pure D.pure hq)
        refine PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.closedStabAtSplit (.recCall (recInnerDTA D.dT) (rightKTA D.dT kT)) (innerQTA D.dT qT)) ?_
        simpa only [promotedInnerRefA, recInnerDTA, DistAtA.pred] using this
      have pLeftA : PureFamilyDerivA Surface.code.body fuel
          (.eqPauli (SC.closed (promotedInnerRefA D.dT qT (leftKTA D.dT kT)))
            (SC.closed (rowSymTreeA m (recInnerDTA D.dT) (leftKTA D.dT kT) (innerQTA D.dT qT)))) := by
        have := ih (leftKTA D.dT kT) (innerQTA D.dT qT)
          (leftKTA_pure D.pure hk) (innerQTA_pure D.pure hq)
        refine PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.closedStabAtSplit (.recCall (recInnerDTA D.dT) (leftKTA D.dT kT)) (innerQTA D.dT qT)) ?_
        simpa only [promotedInnerRefA, recInnerDTA, DistAtA.pred] using this
      have pBottomA : PureFamilyDerivA Surface.code.body fuel
          (.eqPauli (SC.closed (promotedInnerRefA D.dT qT (bottomKTA D.dT kT)))
            (SC.closed (rowSymTreeA m (recInnerDTA D.dT) (bottomKTA D.dT kT) (innerQTA D.dT qT)))) := by
        have := ih (bottomKTA D.dT kT) (innerQTA D.dT qT)
          (bottomKTA_pure D.pure hk) (innerQTA_pure D.pure hq)
        refine PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.closedStabAtSplit (.recCall (recInnerDTA D.dT) (bottomKTA D.dT kT)) (innerQTA D.dT qT)) ?_
        simpa only [promotedInnerRefA, recInnerDTA, DistAtA.pred] using this
      have h := recRowConvergeA (fuel := fuel) (SC.n (nQubits (oddDistance (m + 1)))) D.dT kT qT
        (rowSymTreeA m (innerDTA D.dT) (interiorKTA D.dT kT) (innerQTA D.dT qT))
        (rowSymTreeA m (recInnerDTA D.dT) (topKTA D.dT kT) (innerQTA D.dT qT))
        (rowSymTreeA m (recInnerDTA D.dT) (rightKTA D.dT kT) (innerQTA D.dT qT))
        (rowSymTreeA m (recInnerDTA D.dT) (leftKTA D.dT kT) (innerQTA D.dT qT))
        (rowSymTreeA m (recInnerDTA D.dT) (bottomKTA D.dT kT) (innerQTA D.dT qT))
        D.pure hk hq (distLtFiveFalse_of_DistAtA D)
        pIntA pTopA pRightA pLeftA pBottomA
      simpa only [rowSymTreeA] using h

#print axioms surfaceRowEntryCharSymbolicA

end QHL.CodeLang.Surface.Verify
