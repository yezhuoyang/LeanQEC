import QStab.QHL.Verify.SurfaceRowCharacterizationFull

/-!
# Grid-classifier generalization of the discharged Surface row characterization

`SurfaceRowCharacterizationFull.lean` proves the *center cell* of every odd
Surface code carries `Z`, via a genuinely-discharged induction on
`OddSurfaceDistance.index` (`recCenterChar`).  That file's per-cell peels
(`recBasePeel`, `recInteriorPeel`) are specialised to a single cell kind:
`recBasePeel` only handles a bulk `Z`-plaquette; `recInteriorPeel` only handles
the interior recursing cell.

This file *generalises the peels to every base-entry cell kind* — the bulk
plaquettes (`Z`/`X`) and the four boundary checks (top-`X`, right-`Z`, left-`Z`,
bottom-`X`).  Each peel is fully parametric in pure closed terms `dT`/`kT`/`qT`
and takes the relevant grid guards as `PureFamilyDerivA` derivations, exactly in
the style of `recBasePeel`.  These are the leaves the *grid classifier* dispatches
to: at any odd distance, a stabilizer index `k < numStab d` lands in exactly one
of these cell kinds, and the matching peel resolves the entry.

The forall-`k` base case (`d = 3`, every `k < numStab 3 = 8`, symbolic `q`) is
assembled at the end (`surfaceD3BaseCellChar`), giving for every base-cell index
the entry Pauli at a symbolic qubit under the cell's band guard.

Nothing here adds a trusted rule, uses `native_decide`, `Formula.check`,
`Formula.eval`-as-distance, `deriveTrue?`, `admit`, or a new axiom.  Everything
reuses the foundation peel infrastructure of `SurfaceRowCharacterizationFull`.
-/

namespace QHL.CodeLang.Surface.Verify

open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface

set_option maxRecDepth 65536

/-! ## Grid coordinate helper terms for the base-entry boundary classifier

After the bulk-`else` branch of the base entry, the boundary offset is
`b = k - bulkCount` and the strip half-width is `half = (d-1)/2`.  The four
boundary kinds are selected by `b < half`, `b < 2·half`, `b < 3·half`, else. -/

/-- The boundary offset `b = k - bulkCount` of the base entry. -/
def baseBT (dT kT : Term 0 .nat) : Term 0 .nat := .sub kT (bulkCountT dT)
/-- The strip half-width `half = (d-1)/2`. -/
def baseHalfT (dT : Term 0 .nat) : Term 0 .nat := .div (dm1T dT) (.natLit 2)

/-! ### The four boundary classifier guards (depend only on `d`, `k`). -/

/-- Top-`X` classifier: `b < half`. -/
def topClassGuard (dT kT : Term 0 .nat) : Term 0 .bool :=
  .ltNat (baseBT dT kT) (baseHalfT dT)
/-- Right-`Z` classifier: `b < 2·half`. -/
def rightClassGuard (dT kT : Term 0 .nat) : Term 0 .bool :=
  .ltNat (baseBT dT kT) (.mul (.natLit 2) (baseHalfT dT))
/-- Left-`Z` classifier: `b < 3·half`. -/
def leftClassGuard (dT kT : Term 0 .nat) : Term 0 .bool :=
  .ltNat (baseBT dT kT) (.mul (.natLit 3) (baseHalfT dT))

/-! ### The four boundary band guards (depend on `d`, `k`, `q`). -/

/-- Top-`X` band: `k < d² - 1 ∧ row = 0 ∧ (col = 2b ∨ col = 2b+1)`. -/
def topBandGuard (dT kT qT : Term 0 .nat) : Term 0 .bool :=
  band3 (.ltNat kT (.sub (.mul dT dT) (.natLit 1)))
    (.eqNat (.div qT dT) (.natLit 0))
    (orEqSucc (.mod qT dT) (.mul (.natLit 2) (baseBT dT kT)))

/-- Right-`Z` band: `col = d-1 ∧ (row = 2·bbR ∨ row = 2·bbR+1)`, `bbR = b - half`. -/
def rightBandGuard (dT kT qT : Term 0 .nat) : Term 0 .bool :=
  .and (.eqNat (.mod qT dT) (dm1T dT))
    (orEqSucc (.div qT dT) (.mul (.natLit 2) (.sub (baseBT dT kT) (baseHalfT dT))))

/-- Left-`Z` band: `col = 0 ∧ (row = 2·bbL+1 ∨ row = 2·bbL+2)`, `bbL = b - 2·half`. -/
def leftBandGuard (dT kT qT : Term 0 .nat) : Term 0 .bool :=
  .and (.eqNat (.mod qT dT) (.natLit 0))
    (orEqPair (.div qT dT)
      (.add (.mul (.natLit 2) (.sub (baseBT dT kT) (.mul (.natLit 2) (baseHalfT dT)))) (.natLit 1))
      (.add (.mul (.natLit 2) (.sub (baseBT dT kT) (.mul (.natLit 2) (baseHalfT dT)))) (.natLit 2)))

/-- Bottom-`X` band: `row = d-1 ∧ (col = 2·bbB+1 ∨ col = 2·bbB+2)`, `bbB = b - 3·half`. -/
def bottomBandGuard (dT kT qT : Term 0 .nat) : Term 0 .bool :=
  .and (.eqNat (.div qT dT) (dm1T dT))
    (orEqPair (.mod qT dT)
      (.add (.mul (.natLit 2) (.sub (baseBT dT kT) (.mul (.natLit 3) (baseHalfT dT)))) (.natLit 1))
      (.add (.mul (.natLit 2) (.sub (baseBT dT kT) (.mul (.natLit 3) (baseHalfT dT)))) (.natLit 2)))

/-! ## Bulk `X`-plaquette peel

`recBasePeel` (in `SurfaceRowCharacterizationFull`) peels a bulk **Z**-plaquette:
it selects the kind branch with `(r+c) % 2 = 0` true.  The bulk **X**-plaquette
is the transpose: the same bulk band guard with the kind guard `(r+c) % 2 = 0`
**false**, landing on `X`. -/

/-- **Parametric base-entry bulk `X`-plaquette peel.**

For symbolic `dT`/`kT`/`qT` satisfying the outer bulk guard, the bulk band guard,
and the kind guard `(r+c) % 2 = 0` **false**, the generated base entry
stabilizer-lambda at `qT` carries `X`. -/
def recBasePeelX {fuel : Nat} (dT kT qT : Term 0 .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardT dT kT)) (SC.b true)))
    (hBand : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (baseBulkBandGuard dT kT qT)) (SC.b true)))
    (hKind : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (baseKindGuard dT kT)) (SC.b false))) :
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
    (pureStabAtClosedIteLamThen (fuel := fuel)
      (.ltNat (Term.lift 0 kT)
        (.mul (.sub (Term.lift 0 dT) (.natLit 1)) (.sub (Term.lift 0 dT) (.natLit 1))))
      _ _ qT hq ?hBulkGuard) ?_
  case hBulkGuard =>
    have heq : Term.instantiateTopNat qT
        (Term.ltNat (Term.lift 0 kT)
          (.mul (.sub (Term.lift 0 dT) (.natLit 1)) (.sub (Term.lift 0 dT) (.natLit 1))))
        = bulkGuardT dT kT := by
      simp only [bulkGuardT, bulkCountT, dm1T, Term.instantiateTopNat, Term.instantiateNatAt,
        instTop_lift]
    rw [heq]; exact hBulk
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectThen _ _ _ ?hBandG)
    (PureFamilyDerivA.pauliIteSelectElse _ _ _ ?hKindG)
  case hBandG =>
    have heq : baseBulkBandGuard dT kT qT
        = ((((qT.div dT).eqNat (kT.div (dT.sub (Term.natLit 1)))).or
                ((qT.div dT).eqNat ((kT.div (dT.sub (Term.natLit 1))).add (Term.natLit 1)))).and
            ((((qT.mod dT).eqNat (kT.mod (dT.sub (Term.natLit 1)))).or
                  ((qT.mod dT).eqNat ((kT.mod (dT.sub (Term.natLit 1))).add (Term.natLit 1)))).and
              (kT.ltNat ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))))) := by
      simp only [baseBulkBandGuard, band3, orEqSucc, bulkCountT, dm1T]
    rw [heq] at hBand; exact hBand
  case hKindG =>
    have heq : baseKindGuard dT kT
        = (((kT.div (dT.sub (Term.natLit 1))).add (kT.mod (dT.sub (Term.natLit 1)))).mod
              (Term.natLit 2)).eqNat (Term.natLit 0) := by
      simp only [baseKindGuard, dm1T]
    rw [heq] at hKind; exact hKind

/-! ## Bulk out-of-plaquette peel

When `kT` is a bulk index but the qubit `qT` falls outside the plaquette band,
the entry is `I` (selects the bulk branch, then the band-`else`). -/

/-- **Parametric base-entry bulk out-of-plaquette peel.**  Bulk index, band guard
**false**, landing on `I`. -/
def recBasePeelI {fuel : Nat} (dT kT qT : Term 0 .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardT dT kT)) (SC.b true)))
    (hBand : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (baseBulkBandGuard dT kT qT)) (SC.b false))) :
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
    (pureStabAtClosedIteLamThen (fuel := fuel)
      (.ltNat (Term.lift 0 kT)
        (.mul (.sub (Term.lift 0 dT) (.natLit 1)) (.sub (Term.lift 0 dT) (.natLit 1))))
      _ _ qT hq ?hBulkGuard) ?_
  case hBulkGuard =>
    have heq : Term.instantiateTopNat qT
        (Term.ltNat (Term.lift 0 kT)
          (.mul (.sub (Term.lift 0 dT) (.natLit 1)) (.sub (Term.lift 0 dT) (.natLit 1))))
        = bulkGuardT dT kT := by
      simp only [bulkGuardT, bulkCountT, dm1T, Term.instantiateTopNat, Term.instantiateNatAt,
        instTop_lift]
    rw [heq]; exact hBulk
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]
  refine PureFamilyDerivA.pauliIteSelectElse _ _ _ ?hBandG
  case hBandG =>
    have heq : baseBulkBandGuard dT kT qT
        = ((((qT.div dT).eqNat (kT.div (dT.sub (Term.natLit 1)))).or
                ((qT.div dT).eqNat ((kT.div (dT.sub (Term.natLit 1))).add (Term.natLit 1)))).and
            ((((qT.mod dT).eqNat (kT.mod (dT.sub (Term.natLit 1)))).or
                  ((qT.mod dT).eqNat ((kT.mod (dT.sub (Term.natLit 1))).add (Term.natLit 1)))).and
              (kT.ltNat ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))))) := by
      simp only [baseBulkBandGuard, band3, orEqSucc, bulkCountT, dm1T]
    rw [heq] at hBand; exact hBand

/-! ## Boundary-cell peels

Each boundary cell takes the bulk-`else` branch (`bulkGuardT` **false**), then
descends the boundary classifier (`b < half` / `b < 2·half` / `b < 3·half`),
then resolves the cell's own band guard.  Two variants per cell kind: the in-band
case (kind Pauli) and the out-of-band case (`I`).

The peel structure mirrors `recBasePeel`, except the first selection is the
bulk-`else` (via `pureStabAtClosedIteLamElse`), and the residual `instantiateNatAt`
on the bound qubit variable is collapsed by `Nat.lt_irrefl, dite_false, dite_true`.
-/

/-- **Top-`X` boundary peel (in band).**  Selects bulk-else, `b < half`, top band,
landing on `X`. -/
def recTopXPeel {fuel : Nat} (dT kT qT : Term 0 .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardT dT kT)) (SC.b false)))
    (hTopClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topClassGuard dT kT)) (SC.b true)))
    (hTopBand : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topBandGuard dT kT qT)) (SC.b true))) :
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
    (pureStabAtClosedIteLamElse (fuel := fuel)
      (.ltNat (Term.lift 0 kT)
        (.mul (.sub (Term.lift 0 dT) (.natLit 1)) (.sub (Term.lift 0 dT) (.natLit 1))))
      _ _ qT hq ?hBulkGuard) ?_
  case hBulkGuard =>
    have heq : Term.instantiateTopNat qT
        (Term.ltNat (Term.lift 0 kT)
          (.mul (.sub (Term.lift 0 dT) (.natLit 1)) (.sub (Term.lift 0 dT) (.natLit 1))))
        = bulkGuardT dT kT := by
      simp only [bulkGuardT, bulkCountT, dm1T, Term.instantiateTopNat, Term.instantiateNatAt,
        instTop_lift]
    rw [heq]; exact hBulk
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift,
    Nat.lt_irrefl, dite_false, dite_true]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectThen _ _ _ ?hTopClassG)
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectThen _ _ _ ?hTopBandG)
      (PureFamilyDerivA.eqPauliRefl _))
  case hTopClassG =>
    have heq : topClassGuard dT kT
        = (kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))).ltNat
            ((dT.sub (Term.natLit 1)).div (Term.natLit 2)) := by
      simp only [topClassGuard, baseBT, baseHalfT, bulkCountT, dm1T]
    rw [heq] at hTopClass; exact hTopClass
  case hTopBandG =>
    have heq : topBandGuard dT kT qT
        = (kT.ltNat ((dT.mul dT).sub (Term.natLit 1))).and
            (((qT.div dT).eqNat (Term.natLit 0)).and
              (((qT.mod dT).eqNat ((Term.natLit 2).mul (kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))))).or
                ((qT.mod dT).eqNat (((Term.natLit 2).mul (kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1))))).add (Term.natLit 1))))) := by
      simp only [topBandGuard, baseBT, band3, orEqSucc, bulkCountT, dm1T]
    rw [heq] at hTopBand; exact hTopBand

/-- **Right-`Z` boundary peel (in band).**  Selects bulk-else, `b < half` false,
`b < 2·half`, right band, landing on `Z`. -/
def recRightZPeel {fuel : Nat} (dT kT qT : Term 0 .nat)
    (_hd : SFormula.PureNatTerm dT) (_hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardT dT kT)) (SC.b false)))
    (hTopClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topClassGuard dT kT)) (SC.b false)))
    (hRightClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (rightClassGuard dT kT)) (SC.b true)))
    (hRightBand : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (rightBandGuard dT kT qT)) (SC.b true))) :
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
    (pureStabAtClosedIteLamElse (fuel := fuel)
      (.ltNat (Term.lift 0 kT)
        (.mul (.sub (Term.lift 0 dT) (.natLit 1)) (.sub (Term.lift 0 dT) (.natLit 1))))
      _ _ qT hq ?hBulkGuard) ?_
  case hBulkGuard =>
    have heq : Term.instantiateTopNat qT
        (Term.ltNat (Term.lift 0 kT)
          (.mul (.sub (Term.lift 0 dT) (.natLit 1)) (.sub (Term.lift 0 dT) (.natLit 1))))
        = bulkGuardT dT kT := by
      simp only [bulkGuardT, bulkCountT, dm1T, Term.instantiateTopNat, Term.instantiateNatAt,
        instTop_lift]
    rw [heq]; exact hBulk
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift,
    Nat.lt_irrefl, dite_false, dite_true]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectElse _ _ _ ?hTopClassG)
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectThen _ _ _ ?hRightClassG)
      (PureFamilyDerivA.eqPauliTrans _ _ _
        (PureFamilyDerivA.pauliIteSelectThen _ _ _ ?hRightBandG)
        (PureFamilyDerivA.eqPauliRefl _)))
  case hTopClassG =>
    have heq : topClassGuard dT kT
        = (kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))).ltNat
            ((dT.sub (Term.natLit 1)).div (Term.natLit 2)) := by
      simp only [topClassGuard, baseBT, baseHalfT, bulkCountT, dm1T]
    rw [heq] at hTopClass; exact hTopClass
  case hRightClassG =>
    have heq : rightClassGuard dT kT
        = (kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))).ltNat
            ((Term.natLit 2).mul ((dT.sub (Term.natLit 1)).div (Term.natLit 2))) := by
      simp only [rightClassGuard, baseBT, baseHalfT, bulkCountT, dm1T]
    rw [heq] at hRightClass; exact hRightClass
  case hRightBandG =>
    have heq : rightBandGuard dT kT qT
        = ((qT.mod dT).eqNat (dT.sub (Term.natLit 1))).and
            (((qT.div dT).eqNat ((Term.natLit 2).mul ((kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))).sub ((dT.sub (Term.natLit 1)).div (Term.natLit 2))))).or
              ((qT.div dT).eqNat (((Term.natLit 2).mul ((kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))).sub ((dT.sub (Term.natLit 1)).div (Term.natLit 2)))).add (Term.natLit 1)))) := by
      simp only [rightBandGuard, baseBT, baseHalfT, orEqSucc, bulkCountT, dm1T]
    rw [heq] at hRightBand; exact hRightBand

/-- **Left-`Z` boundary peel (in band).**  Selects bulk-else, `b < half` false,
`b < 2·half` false, `b < 3·half`, left band, landing on `Z`. -/
def recLeftZPeel {fuel : Nat} (dT kT qT : Term 0 .nat)
    (_hd : SFormula.PureNatTerm dT) (_hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardT dT kT)) (SC.b false)))
    (hTopClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topClassGuard dT kT)) (SC.b false)))
    (hRightClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (rightClassGuard dT kT)) (SC.b false)))
    (hLeftClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (leftClassGuard dT kT)) (SC.b true)))
    (hLeftBand : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (leftBandGuard dT kT qT)) (SC.b true))) :
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
    (pureStabAtClosedIteLamElse (fuel := fuel)
      (.ltNat (Term.lift 0 kT)
        (.mul (.sub (Term.lift 0 dT) (.natLit 1)) (.sub (Term.lift 0 dT) (.natLit 1))))
      _ _ qT hq ?hBulkGuard) ?_
  case hBulkGuard =>
    have heq : Term.instantiateTopNat qT
        (Term.ltNat (Term.lift 0 kT)
          (.mul (.sub (Term.lift 0 dT) (.natLit 1)) (.sub (Term.lift 0 dT) (.natLit 1))))
        = bulkGuardT dT kT := by
      simp only [bulkGuardT, bulkCountT, dm1T, Term.instantiateTopNat, Term.instantiateNatAt,
        instTop_lift]
    rw [heq]; exact hBulk
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift,
    Nat.lt_irrefl, dite_false, dite_true]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectElse _ _ _ ?hTopClassG)
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectElse _ _ _ ?hRightClassG)
      (PureFamilyDerivA.eqPauliTrans _ _ _
        (PureFamilyDerivA.pauliIteSelectThen _ _ _ ?hLeftClassG)
        (PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.pauliIteSelectThen _ _ _ ?hLeftBandG)
          (PureFamilyDerivA.eqPauliRefl _))))
  case hTopClassG =>
    have heq : topClassGuard dT kT
        = (kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))).ltNat
            ((dT.sub (Term.natLit 1)).div (Term.natLit 2)) := by
      simp only [topClassGuard, baseBT, baseHalfT, bulkCountT, dm1T]
    rw [heq] at hTopClass; exact hTopClass
  case hRightClassG =>
    have heq : rightClassGuard dT kT
        = (kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))).ltNat
            ((Term.natLit 2).mul ((dT.sub (Term.natLit 1)).div (Term.natLit 2))) := by
      simp only [rightClassGuard, baseBT, baseHalfT, bulkCountT, dm1T]
    rw [heq] at hRightClass; exact hRightClass
  case hLeftClassG =>
    have heq : leftClassGuard dT kT
        = (kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))).ltNat
            ((Term.natLit 3).mul ((dT.sub (Term.natLit 1)).div (Term.natLit 2))) := by
      simp only [leftClassGuard, baseBT, baseHalfT, bulkCountT, dm1T]
    rw [heq] at hLeftClass; exact hLeftClass
  case hLeftBandG =>
    have heq : leftBandGuard dT kT qT
        = ((qT.mod dT).eqNat (Term.natLit 0)).and
            (((qT.div dT).eqNat (((Term.natLit 2).mul ((kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))).sub ((Term.natLit 2).mul ((dT.sub (Term.natLit 1)).div (Term.natLit 2))))).add (Term.natLit 1))).or
              ((qT.div dT).eqNat (((Term.natLit 2).mul ((kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))).sub ((Term.natLit 2).mul ((dT.sub (Term.natLit 1)).div (Term.natLit 2))))).add (Term.natLit 2)))) := by
      simp only [leftBandGuard, baseBT, baseHalfT, orEqPair, bulkCountT, dm1T]
    rw [heq] at hLeftBand; exact hLeftBand

/-- **Bottom-`X` boundary peel (in band).**  Selects bulk-else, all three boundary
classifiers false, bottom band, landing on `X`. -/
def recBottomXPeel {fuel : Nat} (dT kT qT : Term 0 .nat)
    (_hd : SFormula.PureNatTerm dT) (_hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardT dT kT)) (SC.b false)))
    (hTopClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topClassGuard dT kT)) (SC.b false)))
    (hRightClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (rightClassGuard dT kT)) (SC.b false)))
    (hLeftClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (leftClassGuard dT kT)) (SC.b false)))
    (hBottomBand : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bottomBandGuard dT kT qT)) (SC.b true))) :
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
    (pureStabAtClosedIteLamElse (fuel := fuel)
      (.ltNat (Term.lift 0 kT)
        (.mul (.sub (Term.lift 0 dT) (.natLit 1)) (.sub (Term.lift 0 dT) (.natLit 1))))
      _ _ qT hq ?hBulkGuard) ?_
  case hBulkGuard =>
    have heq : Term.instantiateTopNat qT
        (Term.ltNat (Term.lift 0 kT)
          (.mul (.sub (Term.lift 0 dT) (.natLit 1)) (.sub (Term.lift 0 dT) (.natLit 1))))
        = bulkGuardT dT kT := by
      simp only [bulkGuardT, bulkCountT, dm1T, Term.instantiateTopNat, Term.instantiateNatAt,
        instTop_lift]
    rw [heq]; exact hBulk
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift,
    Nat.lt_irrefl, dite_false, dite_true]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectElse _ _ _ ?hTopClassG)
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectElse _ _ _ ?hRightClassG)
      (PureFamilyDerivA.eqPauliTrans _ _ _
        (PureFamilyDerivA.pauliIteSelectElse _ _ _ ?hLeftClassG)
        (PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.pauliIteSelectThen _ _ _ ?hBottomBandG)
          (PureFamilyDerivA.eqPauliRefl _))))
  case hTopClassG =>
    have heq : topClassGuard dT kT
        = (kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))).ltNat
            ((dT.sub (Term.natLit 1)).div (Term.natLit 2)) := by
      simp only [topClassGuard, baseBT, baseHalfT, bulkCountT, dm1T]
    rw [heq] at hTopClass; exact hTopClass
  case hRightClassG =>
    have heq : rightClassGuard dT kT
        = (kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))).ltNat
            ((Term.natLit 2).mul ((dT.sub (Term.natLit 1)).div (Term.natLit 2))) := by
      simp only [rightClassGuard, baseBT, baseHalfT, bulkCountT, dm1T]
    rw [heq] at hRightClass; exact hRightClass
  case hLeftClassG =>
    have heq : leftClassGuard dT kT
        = (kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))).ltNat
            ((Term.natLit 3).mul ((dT.sub (Term.natLit 1)).div (Term.natLit 2))) := by
      simp only [leftClassGuard, baseBT, baseHalfT, bulkCountT, dm1T]
    rw [heq] at hLeftClass; exact hLeftClass
  case hBottomBandG =>
    have heq : bottomBandGuard dT kT qT
        = ((qT.div dT).eqNat (dT.sub (Term.natLit 1))).and
            (((qT.mod dT).eqNat (((Term.natLit 2).mul ((kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))).sub ((Term.natLit 3).mul ((dT.sub (Term.natLit 1)).div (Term.natLit 2))))).add (Term.natLit 1))).or
              ((qT.mod dT).eqNat (((Term.natLit 2).mul ((kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))).sub ((Term.natLit 3).mul ((dT.sub (Term.natLit 1)).div (Term.natLit 2))))).add (Term.natLit 2)))) := by
      simp only [bottomBandGuard, baseBT, baseHalfT, orEqPair, bulkCountT, dm1T]
    rw [heq] at hBottomBand; exact hBottomBand

/-! ## Induction-step bulk-interior cell for ARBITRARY interior `k`

`recInteriorPeel` (in `SurfaceRowCharacterizationFull`) is already parametric in
`kT`: given the three grid guards (`bulkGuardT`, `interiorCellGuardT`,
`insideGuardT`) as derivations, it reduces the recursive-entry stabilizer-lambda
at `qT` to the inner-code reference `centerInnerRef dT kT qT`.  The center
characterization `recCenterChar` only ever instantiates it at the *center* `kT`.

The combinator below threads an *arbitrary* interior `k` together with a supplied
resolution of the inner reference — the inductive hypothesis (the `d-2` row
characterization, instantiated at the projected inner index `interiorKT dT kT`
and inner qubit `innerQT dT qT`).  It is the generalisation of
`surfaceD5Rec_k5_interior_withIH` (which is fixed at `d = 5`, `k = 5`) to any
distance term and any interior stabilizer index.

This is the reusable engine for the induction step's bulk-interior cells: a
forall-`k` IH at `d-2` supplies `ih` for whichever inner index the cell projects
to, and `recInteriorPeel_withIH` discharges the cell. -/

/-- **Induction-step bulk-interior peel with the inductive hypothesis applied
(arbitrary interior `k`).**

Given the three grid guards for an interior bulk cell at distance `dT`,
stabilizer index `kT`, qubit `qT`, and a derivation `ih` resolving the inner-code
reference `centerInnerRef dT kT qT` to a leaf Pauli `p`, the generated recursive
entry stabilizer-lambda at `qT` carries `p`. -/
def recInteriorPeel_withIH {fuel : Nat} (dT kT qT : Term 0 .nat) (p : Term 0 .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardT dT kT)) (SC.b true)))
    (hInterior : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (interiorCellGuardT dT kT)) (SC.b true)))
    (hInside : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (insideGuardT dT qT)) (SC.b true)))
    (ih : PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (SC.closed (centerInnerRef dT kT qT)) (SC.closed p))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt
          (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed qT))
        (SC.closed p)) :=
  PureFamilyDerivA.eqPauliTrans _ _ _
    (recInteriorPeel dT kT qT hd hk hq hBulk hInterior hInside)
    ih

/-- The same step phrased over the *generated row* `recCall dT kT` (rather than the
already-unfolded `stabLam` body).  Composes the recursive-branch row selection
with `recInteriorPeel_withIH`; this is the shape an `OddSurfaceDistance.index`
induction consumes directly for an interior cell. -/
def recInteriorRow_withIH {fuel : Nat} (n : STerm 0 .nat)
    (dT kT qT : Term 0 .nat) (p : Term 0 .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hDist : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat dT (n5 : Term 0 .nat))) (SC.b false)))
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardT dT kT)) (SC.b true)))
    (hInterior : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (interiorCellGuardT dT kT)) (SC.b true)))
    (hInside : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (insideGuardT dT qT)) (SC.b true)))
    (ih : PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (SC.closed (centerInnerRef dT kT qT)) (SC.closed p))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.recCall dT kT)) (SC.closed qT))
        (SC.closed p)) :=
  surfaceCodeRecursiveEntryEq n dT kT qT p hd hk hDist
    (recInteriorPeel_withIH dT kT qT p hd hk hq hBulk hInterior hInside ih)

/-! ## Remaining cell kind: promoted-boundary cells (NOT YET MECHANIZED)

The third recursive-entry cell kind is the *promoted boundary* check
(`SurfaceASTPublic.promotedBoundaryEntry`, see `CodeSurface.lean`).  For an
interior bulk index `k` that lands in `topCell` / `rightCell` / `leftCell` /
`bottomCell` (rather than the deep interior), the recursive entry routes to

  `promotedBoundaryEntry oldK outer kind`
    = `ite inside (stabAt (recCall (d-2) oldK) innerQ) (ite outer (kind) I)`

with `oldK ∈ {topK, rightK, leftK, bottomK}` an inner stabilizer index.  Peeling
it requires:

  1. selecting the recursive entry's classifier branch (`topCell`/… closed
     guards, dischargeable exactly like `interiorCellGuardT`);
  2. an analogue of `recInteriorPeel` over `promotedBoundaryEntry`: when the
     `inside` guard holds, the cell is the inner reference
     `stabAt (recCall (d-2) oldK) innerQ` — resolved by the SAME forall-`k` IH at
     `d-2` (instantiated at `oldK`); when `inside` fails, the entry is the closed
     `ite outer (kind) I` leaf (resolved by a `q`-grid `boolCases` on `outer`).

This peel has the identical structure to `recInteriorPeel_withIH` (a recursive
inner reference resolved by the IH plus a closed-leaf fallback), but over the
`promotedBoundaryEntry` AST node and gated by the recursive entry's boundary
classifier rather than `interiorCell`.  It is left for the next session; the
`recInteriorPeel_withIH` engine above is the template.  No stub lemma is provided
for it (to avoid a gap inside a "finished" lemma). -/

/-! ## Forall-`k` base case (`d = 3`, every `k < numStab 3 = 8`, symbolic `q`)

At the base distance `d = 3` the classifier guards (`bulkGuardT`, `topClassGuard`,
…) are **closed** booleans once `k` is a literal: they mention only `d = 3` and
`k`, never `q`.  Each is dischargeable by `decide` through `guardTrueEval` /
`guardFalseEval`.  The only `q`-dependent guards are the per-cell band guards,
which the consumer supplies (after its own grid `boolCases` on `q`).

The eight base cells of `d = 3` (`numStab 3 = 8`) are:
* `k = 0`  bulk `Z`-plaquette (grid `(0,0)`);
* `k = 1`  bulk `X`-plaquette (grid `(0,1)`);
* `k = 2`  bulk `X`-plaquette (grid `(1,0)`);
* `k = 3`  bulk `Z`-plaquette (grid `(1,1)`, the center cell);
* `k = 4`  top-`X` boundary;
* `k = 5`  right-`Z` boundary;
* `k = 6`  left-`Z` boundary;
* `k = 7`  bottom-`X` boundary.

For each we expose the row entry at a symbolic `q` under the cell's band guard.
These are the per-cell leaves the `d = 3` base of the row-commutation /
normalization / bridge proofs consume. -/

/-! ### Purity certificates for the classifier / band guards (literal `d`/`k`). -/

private def baseBT_pure {dT kT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureNatTerm (baseBT dT kT) :=
  SFormula.PureNatTerm.sub hk
    (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 1))
      (SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 1)))

private def baseHalfT_pure {dT : Term 0 .nat} (hd : SFormula.PureNatTerm dT) :
    SFormula.PureNatTerm (baseHalfT dT) :=
  SFormula.PureNatTerm.div
    (SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 1)) (SFormula.PureNatTerm.nat 2)

private def topClassGuard_pure {dT kT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureBoolTerm (topClassGuard dT kT) :=
  SFormula.PureBoolTerm.ltNat (baseBT_pure hd hk) (baseHalfT_pure hd)

private def rightClassGuard_pure {dT kT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureBoolTerm (rightClassGuard dT kT) :=
  SFormula.PureBoolTerm.ltNat (baseBT_pure hd hk)
    (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 2) (baseHalfT_pure hd))

private def leftClassGuard_pure {dT kT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureBoolTerm (leftClassGuard dT kT) :=
  SFormula.PureBoolTerm.ltNat (baseBT_pure hd hk)
    (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 3) (baseHalfT_pure hd))

/-- Discharge a closed classifier guard (no `q` dependence) at literal `d = 3`
that evaluates to `true`. -/
private def d3GuardTrue {fuel : Nat} {cond : Term 0 .bool}
    (hc : SFormula.PureBoolTerm cond)
    (hEval : ∀ (rho : Env 0), Term.eval Surface.code.body fuel cond rho = some true) :
    PureFamilyDerivA Surface.code.body fuel (.eqBool (SC.closed cond) (SC.b true)) :=
  guardTrueEval hc hEval

/-- Discharge a closed classifier guard at literal `d = 3` that evaluates to
`false`. -/
private def d3GuardFalse {fuel : Nat} {cond : Term 0 .bool}
    (hc : SFormula.PureBoolTerm cond)
    (hEval : ∀ (rho : Env 0), Term.eval Surface.code.body fuel cond rho = some false) :
    PureFamilyDerivA Surface.code.body fuel (.eqBool (SC.closed cond) (SC.b false)) :=
  guardFalseEval hc hEval

/-! ### The eight `d = 3` per-cell row-entry characterizations (symbolic `q`).

The generated code row `recCall 3 k` at a symbolic qubit `qT` carries the cell's
kind Pauli whenever the cell band guard holds at `qT`.  The closed classifier
guards are discharged internally by `decide`; the consumer supplies only the
`q`-dependent band guard. -/

/-- `d = 3`, `k = 0`: bulk `Z`-plaquette. -/
def surfaceD3Row_k0_band {fuel : Nat}
    (qT : Term 0 .nat) (hq : SFormula.PureNatTerm qT)
    (hBand : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (baseBulkBandGuard (.natLit 3) (.natLit 0) qT)) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.recCall (.natLit (arity := 0) 3) (.natLit 0))) (SC.closed qT))
        (SC.closed (.pauliLit Pauli.Z))) :=
  surfaceCodeBaseEntryEq (SC.n (nQubits 3)) (.natLit 3) (.natLit 0) qT (.pauliLit Pauli.Z)
    (SFormula.PureNatTerm.nat 3) (SFormula.PureNatTerm.nat 0)
    (closedLtFiveTrue (by decide))
    (recBasePeel (.natLit 3) (.natLit 0) qT
      (SFormula.PureNatTerm.nat 3) (SFormula.PureNatTerm.nat 0) hq
      (d3GuardTrue (bulkGuardT_pure (.nat 3) (.nat 0))
        (by intro rho; simp [bulkGuardT, bulkCountT, dm1T, Term.eval]))
      hBand
      (d3GuardTrue (baseKindGuard_pure (.nat 3) (.nat 0))
        (by intro rho; simp [baseKindGuard, dm1T, Term.eval])))

/-- `d = 3`, `k = 1`: bulk `X`-plaquette. -/
def surfaceD3Row_k1_band {fuel : Nat}
    (qT : Term 0 .nat) (hq : SFormula.PureNatTerm qT)
    (hBand : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (baseBulkBandGuard (.natLit 3) (.natLit 1) qT)) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.recCall (.natLit (arity := 0) 3) (.natLit 1))) (SC.closed qT))
        (SC.closed (.pauliLit Pauli.X))) :=
  surfaceCodeBaseEntryEq (SC.n (nQubits 3)) (.natLit 3) (.natLit 1) qT (.pauliLit Pauli.X)
    (SFormula.PureNatTerm.nat 3) (SFormula.PureNatTerm.nat 1)
    (closedLtFiveTrue (by decide))
    (recBasePeelX (.natLit 3) (.natLit 1) qT
      (SFormula.PureNatTerm.nat 3) (SFormula.PureNatTerm.nat 1) hq
      (d3GuardTrue (bulkGuardT_pure (.nat 3) (.nat 1))
        (by intro rho; simp [bulkGuardT, bulkCountT, dm1T, Term.eval]))
      hBand
      (d3GuardFalse (baseKindGuard_pure (.nat 3) (.nat 1))
        (by intro rho; simp [baseKindGuard, dm1T, Term.eval])))

/-- `d = 3`, `k = 2`: bulk `X`-plaquette. -/
def surfaceD3Row_k2_band {fuel : Nat}
    (qT : Term 0 .nat) (hq : SFormula.PureNatTerm qT)
    (hBand : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (baseBulkBandGuard (.natLit 3) (.natLit 2) qT)) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.recCall (.natLit (arity := 0) 3) (.natLit 2))) (SC.closed qT))
        (SC.closed (.pauliLit Pauli.X))) :=
  surfaceCodeBaseEntryEq (SC.n (nQubits 3)) (.natLit 3) (.natLit 2) qT (.pauliLit Pauli.X)
    (SFormula.PureNatTerm.nat 3) (SFormula.PureNatTerm.nat 2)
    (closedLtFiveTrue (by decide))
    (recBasePeelX (.natLit 3) (.natLit 2) qT
      (SFormula.PureNatTerm.nat 3) (SFormula.PureNatTerm.nat 2) hq
      (d3GuardTrue (bulkGuardT_pure (.nat 3) (.nat 2))
        (by intro rho; simp [bulkGuardT, bulkCountT, dm1T, Term.eval]))
      hBand
      (d3GuardFalse (baseKindGuard_pure (.nat 3) (.nat 2))
        (by intro rho; simp [baseKindGuard, dm1T, Term.eval])))

/-- `d = 3`, `k = 3`: bulk `Z`-plaquette (the center cell). -/
def surfaceD3Row_k3_band {fuel : Nat}
    (qT : Term 0 .nat) (hq : SFormula.PureNatTerm qT)
    (hBand : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (baseBulkBandGuard (.natLit 3) (.natLit 3) qT)) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.recCall (.natLit (arity := 0) 3) (.natLit 3))) (SC.closed qT))
        (SC.closed (.pauliLit Pauli.Z))) :=
  surfaceCodeBaseEntryEq (SC.n (nQubits 3)) (.natLit 3) (.natLit 3) qT (.pauliLit Pauli.Z)
    (SFormula.PureNatTerm.nat 3) (SFormula.PureNatTerm.nat 3)
    (closedLtFiveTrue (by decide))
    (recBasePeel (.natLit 3) (.natLit 3) qT
      (SFormula.PureNatTerm.nat 3) (SFormula.PureNatTerm.nat 3) hq
      (d3GuardTrue (bulkGuardT_pure (.nat 3) (.nat 3))
        (by intro rho; simp [bulkGuardT, bulkCountT, dm1T, Term.eval]))
      hBand
      (d3GuardTrue (baseKindGuard_pure (.nat 3) (.nat 3))
        (by intro rho; simp [baseKindGuard, dm1T, Term.eval])))

/-- `d = 3`, `k = 4`: top-`X` boundary check. -/
def surfaceD3Row_k4_band {fuel : Nat}
    (qT : Term 0 .nat) (hq : SFormula.PureNatTerm qT)
    (hBand : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topBandGuard (.natLit 3) (.natLit 4) qT)) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.recCall (.natLit (arity := 0) 3) (.natLit 4))) (SC.closed qT))
        (SC.closed (.pauliLit Pauli.X))) :=
  surfaceCodeBaseEntryEq (SC.n (nQubits 3)) (.natLit 3) (.natLit 4) qT (.pauliLit Pauli.X)
    (SFormula.PureNatTerm.nat 3) (SFormula.PureNatTerm.nat 4)
    (closedLtFiveTrue (by decide))
    (recTopXPeel (.natLit 3) (.natLit 4) qT
      (SFormula.PureNatTerm.nat 3) (SFormula.PureNatTerm.nat 4) hq
      (d3GuardFalse (bulkGuardT_pure (.nat 3) (.nat 4))
        (by intro rho; simp [bulkGuardT, bulkCountT, dm1T, Term.eval]))
      (d3GuardTrue (topClassGuard_pure (.nat 3) (.nat 4))
        (by intro rho; simp [topClassGuard, baseBT, baseHalfT, bulkCountT, dm1T, Term.eval]))
      hBand)

/-- `d = 3`, `k = 5`: right-`Z` boundary check. -/
def surfaceD3Row_k5_band {fuel : Nat}
    (qT : Term 0 .nat) (hq : SFormula.PureNatTerm qT)
    (hBand : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (rightBandGuard (.natLit 3) (.natLit 5) qT)) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.recCall (.natLit (arity := 0) 3) (.natLit 5))) (SC.closed qT))
        (SC.closed (.pauliLit Pauli.Z))) :=
  surfaceCodeBaseEntryEq (SC.n (nQubits 3)) (.natLit 3) (.natLit 5) qT (.pauliLit Pauli.Z)
    (SFormula.PureNatTerm.nat 3) (SFormula.PureNatTerm.nat 5)
    (closedLtFiveTrue (by decide))
    (recRightZPeel (.natLit 3) (.natLit 5) qT
      (SFormula.PureNatTerm.nat 3) (SFormula.PureNatTerm.nat 5) hq
      (d3GuardFalse (bulkGuardT_pure (.nat 3) (.nat 5))
        (by intro rho; simp [bulkGuardT, bulkCountT, dm1T, Term.eval]))
      (d3GuardFalse (topClassGuard_pure (.nat 3) (.nat 5))
        (by intro rho; simp [topClassGuard, baseBT, baseHalfT, bulkCountT, dm1T, Term.eval]))
      (d3GuardTrue (rightClassGuard_pure (.nat 3) (.nat 5))
        (by intro rho; simp [rightClassGuard, baseBT, baseHalfT, bulkCountT, dm1T, Term.eval]))
      hBand)

/-- `d = 3`, `k = 6`: left-`Z` boundary check. -/
def surfaceD3Row_k6_band {fuel : Nat}
    (qT : Term 0 .nat) (hq : SFormula.PureNatTerm qT)
    (hBand : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (leftBandGuard (.natLit 3) (.natLit 6) qT)) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.recCall (.natLit (arity := 0) 3) (.natLit 6))) (SC.closed qT))
        (SC.closed (.pauliLit Pauli.Z))) :=
  surfaceCodeBaseEntryEq (SC.n (nQubits 3)) (.natLit 3) (.natLit 6) qT (.pauliLit Pauli.Z)
    (SFormula.PureNatTerm.nat 3) (SFormula.PureNatTerm.nat 6)
    (closedLtFiveTrue (by decide))
    (recLeftZPeel (.natLit 3) (.natLit 6) qT
      (SFormula.PureNatTerm.nat 3) (SFormula.PureNatTerm.nat 6) hq
      (d3GuardFalse (bulkGuardT_pure (.nat 3) (.nat 6))
        (by intro rho; simp [bulkGuardT, bulkCountT, dm1T, Term.eval]))
      (d3GuardFalse (topClassGuard_pure (.nat 3) (.nat 6))
        (by intro rho; simp [topClassGuard, baseBT, baseHalfT, bulkCountT, dm1T, Term.eval]))
      (d3GuardFalse (rightClassGuard_pure (.nat 3) (.nat 6))
        (by intro rho; simp [rightClassGuard, baseBT, baseHalfT, bulkCountT, dm1T, Term.eval]))
      (d3GuardTrue (leftClassGuard_pure (.nat 3) (.nat 6))
        (by intro rho; simp [leftClassGuard, baseBT, baseHalfT, bulkCountT, dm1T, Term.eval]))
      hBand)

/-- `d = 3`, `k = 7`: bottom-`X` boundary check. -/
def surfaceD3Row_k7_band {fuel : Nat}
    (qT : Term 0 .nat) (hq : SFormula.PureNatTerm qT)
    (hBand : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bottomBandGuard (.natLit 3) (.natLit 7) qT)) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.recCall (.natLit (arity := 0) 3) (.natLit 7))) (SC.closed qT))
        (SC.closed (.pauliLit Pauli.X))) :=
  surfaceCodeBaseEntryEq (SC.n (nQubits 3)) (.natLit 3) (.natLit 7) qT (.pauliLit Pauli.X)
    (SFormula.PureNatTerm.nat 3) (SFormula.PureNatTerm.nat 7)
    (closedLtFiveTrue (by decide))
    (recBottomXPeel (.natLit 3) (.natLit 7) qT
      (SFormula.PureNatTerm.nat 3) (SFormula.PureNatTerm.nat 7) hq
      (d3GuardFalse (bulkGuardT_pure (.nat 3) (.nat 7))
        (by intro rho; simp [bulkGuardT, bulkCountT, dm1T, Term.eval]))
      (d3GuardFalse (topClassGuard_pure (.nat 3) (.nat 7))
        (by intro rho; simp [topClassGuard, baseBT, baseHalfT, bulkCountT, dm1T, Term.eval]))
      (d3GuardFalse (rightClassGuard_pure (.nat 3) (.nat 7))
        (by intro rho; simp [rightClassGuard, baseBT, baseHalfT, bulkCountT, dm1T, Term.eval]))
      (d3GuardFalse (leftClassGuard_pure (.nat 3) (.nat 7))
        (by intro rho; simp [leftClassGuard, baseBT, baseHalfT, bulkCountT, dm1T, Term.eval]))
      hBand)

/-! ### Forall-`k` dispatcher for the `d = 3` base case

The eight per-cell lemmas above are unified into a single `∀ k < numStab 3`
statement.  `surfaceD3CellBandGuard k qT` is the band guard of cell `k` (the bulk
plaquette band for `k < 4`, the matching boundary band otherwise);
`surfaceD3CellPauli k` is its kind Pauli.  Given the band guard holds at the
symbolic qubit `qT`, the generated row `recCall 3 k` carries `surfaceD3CellPauli k`. -/

/-- The band guard of `d = 3` base cell `k`, at a symbolic qubit `qT`. -/
def surfaceD3CellBandGuard (k : Nat) (qT : Term 0 .nat) : Term 0 .bool :=
  match k with
  | 0 => baseBulkBandGuard (.natLit 3) (.natLit 0) qT
  | 1 => baseBulkBandGuard (.natLit 3) (.natLit 1) qT
  | 2 => baseBulkBandGuard (.natLit 3) (.natLit 2) qT
  | 3 => baseBulkBandGuard (.natLit 3) (.natLit 3) qT
  | 4 => topBandGuard (.natLit 3) (.natLit 4) qT
  | 5 => rightBandGuard (.natLit 3) (.natLit 5) qT
  | 6 => leftBandGuard (.natLit 3) (.natLit 6) qT
  | _ => bottomBandGuard (.natLit 3) (.natLit 7) qT

/-- The kind Pauli of `d = 3` base cell `k`. -/
def surfaceD3CellPauli (k : Nat) : Pauli :=
  match k with
  | 0 => Pauli.Z
  | 1 => Pauli.X
  | 2 => Pauli.X
  | 3 => Pauli.Z
  | 4 => Pauli.X
  | 5 => Pauli.Z
  | 6 => Pauli.Z
  | _ => Pauli.X

/-- **Forall-`k` `d = 3` base-case row characterization (symbolic `q`).**

For every base stabilizer index `k < numStab 3 = 8` and every symbolic qubit
`qT`, the generated code row `recCall 3 k` at `qT` carries `surfaceD3CellPauli k`,
provided the cell's band guard `surfaceD3CellBandGuard k qT` holds at `qT`.

This is the fully-discharged forall-`k` base case: it dispatches each of the eight
cell kinds to its parametric peel, with the closed `d = 3` classifier guards
discharged internally by `decide`. -/
def surfaceD3BaseChar {fuel : Nat} :
    (k : Nat) → k < numStab 3 →
    (qT : Term 0 .nat) → SFormula.PureNatTerm qT →
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (surfaceD3CellBandGuard k qT)) (SC.b true)) →
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.recCall (.natLit (arity := 0) 3) (.natLit k))) (SC.closed qT))
        (SC.closed (.pauliLit (surfaceD3CellPauli k))))
  | 0, _, qT, hq, hBand => surfaceD3Row_k0_band qT hq hBand
  | 1, _, qT, hq, hBand => surfaceD3Row_k1_band qT hq hBand
  | 2, _, qT, hq, hBand => surfaceD3Row_k2_band qT hq hBand
  | 3, _, qT, hq, hBand => surfaceD3Row_k3_band qT hq hBand
  | 4, _, qT, hq, hBand => surfaceD3Row_k4_band qT hq hBand
  | 5, _, qT, hq, hBand => surfaceD3Row_k5_band qT hq hBand
  | 6, _, qT, hq, hBand => surfaceD3Row_k6_band qT hq hBand
  | 7, _, qT, hq, hBand => surfaceD3Row_k7_band qT hq hBand
  | (n + 8), hk, _, _, _ => absurd hk (by
      have : numStab 3 = 8 := by decide
      omega)

/-! ### Non-vacuity cross-checks (literal qubit recovers the `#eval` ground truth)

For a literal qubit the cell band guard is a closed boolean dischargeable by
`decide`.  Feeding it into the dispatcher recovers the concrete entries computed
by `Surface.code.evalAt? 3 k q`, confirming the parametric peels are not vacuous:
* `k = 4` (top-`X`), `q = 0` → `X` (grid `(0,0)`, in the top-left top check);
* `k = 5` (right-`Z`), `q = 2` → `Z` (grid `(0,2)`, right column);
* `k = 7` (bottom-`X`), `q = 8` → `X` (grid `(2,2)`, bottom row). -/

def surfaceD3_k4_q0_check {fuel : Nat} :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.recCall (.natLit (arity := 0) 3) (.natLit 4))) (SC.closed (.natLit 0)))
        (SC.closed (.pauliLit Pauli.X))) :=
  surfaceD3Row_k4_band (.natLit 0) (SFormula.PureNatTerm.nat 0)
    (guardTrue _ (by decide)
      (by intro rho; simp [topBandGuard, baseBT, bulkCountT, dm1T, band3, orEqSucc, Term.eval]))

def surfaceD3_k5_q2_check {fuel : Nat} :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.recCall (.natLit (arity := 0) 3) (.natLit 5))) (SC.closed (.natLit 2)))
        (SC.closed (.pauliLit Pauli.Z))) :=
  surfaceD3Row_k5_band (.natLit 2) (SFormula.PureNatTerm.nat 2)
    (guardTrue _ (by decide)
      (by intro rho; simp [rightBandGuard, baseBT, baseHalfT, bulkCountT, dm1T, orEqSucc, Term.eval]))

def surfaceD3_k7_q8_check {fuel : Nat} :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.recCall (.natLit (arity := 0) 3) (.natLit 7))) (SC.closed (.natLit 8)))
        (SC.closed (.pauliLit Pauli.X))) :=
  surfaceD3Row_k7_band (.natLit 8) (SFormula.PureNatTerm.nat 8)
    (guardTrue _ (by decide)
      (by intro rho; simp [bottomBandGuard, baseBT, baseHalfT, bulkCountT, dm1T, orEqPair, Term.eval]))

/-! ## Axiom audit -/

#print axioms recBasePeelX
#print axioms recBasePeelI
#print axioms recTopXPeel
#print axioms recRightZPeel
#print axioms recLeftZPeel
#print axioms recBottomXPeel
#print axioms surfaceD3Row_k0_band
#print axioms surfaceD3Row_k4_band
#print axioms surfaceD3Row_k7_band
#print axioms surfaceD3BaseChar
#print axioms recInteriorPeel_withIH
#print axioms recInteriorRow_withIH

end QHL.CodeLang.Surface.Verify
