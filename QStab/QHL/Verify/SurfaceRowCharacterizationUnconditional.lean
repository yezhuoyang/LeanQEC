import QStab.QHL.Verify.SurfaceRowCharacterizationKeystone

/-!
# Unconditional forall-`k` Surface row characterization (NO oracle)

`SurfaceRowCharacterizationKeystone.lean` proves the forall-`k` characterization
`surfaceRowChar`, but only *relative to a `BaseOracle`* whose `resolve` field
resolves every non-recursing base-entry cell to `surfaceCellPauli`.  As used by
its consumers the oracle is instantiated *universally* (`resolve` returning the
conclusion for ALL `m,k,q`), which makes the theorem circular.

This file removes the oracle entirely.  It builds, from the *parametric* Grid /
Keystone peel infrastructure (the genuine, non-circular parts):

1. The **general-`d` non-recursing base-cell characterization**
   `recBaseBodyResolve`: for arbitrary closed pure terms `dT`/`kT`/`qT` carrying
   eval certificates `dT→d`, `kT→kv`, `qT→qv`, the *substituted `baseEntry` body*
   at `qT` carries `surfaceCellPauli d kv qv` — discharged by a Nat-level case
   analysis of `surfaceCellPauli`'s `ite` tree, dispatching each branch to the
   matching parametric base peel (`recBasePeel{,X,I}` / `recTopXPeel` / … plus the
   four boundary out-of-band `→ I` peels added here).  NO oracle, NO hypothesis
   equivalent to the conclusion.

2. The **promoted-boundary outer-leaf peels** (`recPromotedOuter*`): when a
   recursive-entry promoted cell's `inside` guard fails, the entry is the closed
   `ite outer (kind) I` leaf, which resolves to `surfaceCellPauli d kv qv` — the
   keystone left these unmechanized.

3. `surfaceRowCharFull`: the **unconditional** structural recursion on the index
   `m` (exactly the shape of the keystone's `surfaceRowChar`, but with every
   `oracle.resolve` replaced by the genuine resolvers above).

Nothing here adds a trusted rule, uses `native_decide`, `Formula.check`,
`Formula.eval`-as-distance, `deriveTrue?`, `admit`, or a new axiom.
-/

namespace QHL.CodeLang.Surface.Verify

open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface

set_option maxRecDepth 65536

/-! ## Boundary out-of-band base peels (`→ I`)

The Grid file provides the in-band boundary base peels (`recTopXPeel` etc.).  The
four peels below are their out-of-band complements: the same outer bulk-else +
boundary-classifier selections, but the cell's own band guard is **false**, so the
`baseEntry` lands on the closed `I` leaf. -/

/-- **Top boundary, out of band → `I`.** -/
def recTopIPeel {fuel : Nat} (dT kT qT : Term 0 .nat)
    (_hd : SFormula.PureNatTerm dT) (_hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardT dT kT)) (SC.b false)))
    (hTopClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topClassGuard dT kT)) (SC.b true)))
    (hTopBand : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topBandGuard dT kT qT)) (SC.b false))) :
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
    (PureFamilyDerivA.pauliIteSelectElse _ _ _ ?hTopBandG)
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

/-- **Right boundary, out of band → `I`.** -/
def recRightIPeel {fuel : Nat} (dT kT qT : Term 0 .nat)
    (_hd : SFormula.PureNatTerm dT) (_hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardT dT kT)) (SC.b false)))
    (hTopClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topClassGuard dT kT)) (SC.b false)))
    (hRightClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (rightClassGuard dT kT)) (SC.b true)))
    (hRightBand : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (rightBandGuard dT kT qT)) (SC.b false))) :
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
      (PureFamilyDerivA.pauliIteSelectElse _ _ _ ?hRightBandG))
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

/-- **Left boundary, out of band → `I`.** -/
def recLeftIPeel {fuel : Nat} (dT kT qT : Term 0 .nat)
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
      (.eqBool (SC.closed (leftBandGuard dT kT qT)) (SC.b false))) :
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
        (PureFamilyDerivA.pauliIteSelectElse _ _ _ ?hLeftBandG)))
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

/-- **Bottom boundary, out of band → `I`.** -/
def recBottomIPeel {fuel : Nat} (dT kT qT : Term 0 .nat)
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
      (.eqBool (SC.closed (bottomBandGuard dT kT qT)) (SC.b false))) :
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
        (PureFamilyDerivA.pauliIteSelectElse _ _ _ ?hBottomBandG)))
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

/-! ## Nat-level band predicates matching the term-level band guards

For each base-entry band guard we name the decidable `Nat`-level boolean it
evaluates to (under eval certificates `dT→d`, `kT→kv`, `qT→qv`).  These are
exactly the conditions appearing inside `surfaceCellPauli`'s `ite` tree, so the
correspondence with `surfaceCellPauli` is by `decide`/`rfl` on `Nat`. -/

/-- Bulk band: `(row=r ∨ row=r+1) ∧ (col=c ∨ col=c+1) ∧ k < bulkCount`. -/
def baseBulkBandVal (d k q : Nat) : Bool :=
  let row := cellRow d q; let col := cellCol d q; let r := cellR d k; let c := cellC d k
  (decide (row = r) || decide (row = r + 1)) &&
    ((decide (col = c) || decide (col = c + 1)) && decide (k < (d-1)*(d-1)))

/-- Kind guard: `(r + c) % 2 = 0`. -/
def baseKindVal (d k : Nat) : Bool :=
  decide ((cellR d k + cellC d k) % 2 = 0)

/-- Top band: `k < d*d-1 ∧ row = 0 ∧ (col = 2b ∨ col = 2b+1)`, `b = k - bulkCount`. -/
def topBandVal (d k q : Nat) : Bool :=
  let row := cellRow d q; let col := cellCol d q; let b := k - (d-1)*(d-1)
  decide (k < d*d - 1) && (decide (row = 0) && (decide (col = 2*b) || decide (col = 2*b + 1)))

/-- Right band: `col = d-1 ∧ (row = 2bbR ∨ row = 2bbR+1)`, `bbR = b - half`. -/
def rightBandVal (d k q : Nat) : Bool :=
  let row := cellRow d q; let col := cellCol d q
  let b := k - (d-1)*(d-1); let half := (d-1)/2; let bbR := b - half
  decide (col = d-1) && (decide (row = 2*bbR) || decide (row = 2*bbR + 1))

/-- Left band: `col = 0 ∧ (row = 2bbL+1 ∨ row = 2bbL+2)`, `bbL = b - 2*half`. -/
def leftBandVal (d k q : Nat) : Bool :=
  let row := cellRow d q; let col := cellCol d q
  let b := k - (d-1)*(d-1); let half := (d-1)/2; let bbL := b - 2*half
  decide (col = 0) && (decide (row = 2*bbL + 1) || decide (row = 2*bbL + 2))

/-- Bottom band: `row = d-1 ∧ (col = 2bbB+1 ∨ col = 2bbB+2)`, `bbB = b - 3*half`. -/
def bottomBandVal (d k q : Nat) : Bool :=
  let row := cellRow d q; let col := cellCol d q
  let b := k - (d-1)*(d-1); let half := (d-1)/2; let bbB := b - 3*half
  decide (row = d-1) && (decide (col = 2*bbB + 1) || decide (col = 2*bbB + 2))

/-- `baseBulkBandGuard` evaluates to `baseBulkBandVal d kv qv`. -/
theorem baseBulkBandGuard_eval_gen {fuel d kv qv : Nat} {dT kT qT : Term 0 .nat} (rho : Env 0)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : Term.eval Surface.code.body fuel qT rho = some qv) :
    Term.eval Surface.code.body fuel (baseBulkBandGuard dT kT qT) rho
      = some (baseBulkBandVal d kv qv) := by
  simp only [baseBulkBandGuard, band3, orEqSucc, bulkCountT, dm1T, Term.eval, hdv, hkv, hqv,
    Option.bind, Option.bind_eq_bind, baseBulkBandVal, cellRow, cellCol, cellR, cellC]
  by_cases h1 : qv / d = kv / (d-1) <;> by_cases h2 : qv % d = kv % (d-1) <;>
    simp [h1, h2] <;> (try split) <;> simp_all <;> (try split) <;> simp_all

/-- `baseKindGuard` evaluates to `baseKindVal d kv`. -/
theorem baseKindGuard_eval_gen {fuel d kv : Nat} {dT kT : Term 0 .nat} (rho : Env 0)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv) :
    Term.eval Surface.code.body fuel (baseKindGuard dT kT) rho = some (baseKindVal d kv) := by
  simp only [baseKindGuard, dm1T, Term.eval, hdv, hkv, Option.bind, Option.bind_eq_bind,
    baseKindVal, cellR, cellC]

/-- `topBandGuard` evaluates to `topBandVal d kv qv`. -/
theorem topBandGuard_eval_gen {fuel d kv qv : Nat} {dT kT qT : Term 0 .nat} (rho : Env 0)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : Term.eval Surface.code.body fuel qT rho = some qv) :
    Term.eval Surface.code.body fuel (topBandGuard dT kT qT) rho = some (topBandVal d kv qv) := by
  simp only [topBandGuard, band3, orEqSucc, baseBT, bulkCountT, dm1T, Term.eval, hdv, hkv, hqv,
    Option.bind, Option.bind_eq_bind, topBandVal, cellRow, cellCol]
  by_cases h1 : kv < d*d - 1 <;> by_cases h2 : qv / d = 0 <;>
    simp [h1, h2] <;> split <;> simp_all

/-- `rightBandGuard` evaluates to `rightBandVal d kv qv`. -/
theorem rightBandGuard_eval_gen {fuel d kv qv : Nat} {dT kT qT : Term 0 .nat} (rho : Env 0)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : Term.eval Surface.code.body fuel qT rho = some qv) :
    Term.eval Surface.code.body fuel (rightBandGuard dT kT qT) rho
      = some (rightBandVal d kv qv) := by
  simp only [rightBandGuard, orEqSucc, baseBT, baseHalfT, bulkCountT, dm1T, Term.eval, hdv, hkv,
    hqv, Option.bind, Option.bind_eq_bind, rightBandVal, cellRow, cellCol]
  by_cases h1 : qv % d = d-1 <;> simp [h1] <;> split <;> simp_all

/-- `leftBandGuard` evaluates to `leftBandVal d kv qv`. -/
theorem leftBandGuard_eval_gen {fuel d kv qv : Nat} {dT kT qT : Term 0 .nat} (rho : Env 0)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : Term.eval Surface.code.body fuel qT rho = some qv) :
    Term.eval Surface.code.body fuel (leftBandGuard dT kT qT) rho = some (leftBandVal d kv qv) := by
  simp only [leftBandGuard, orEqPair, baseBT, baseHalfT, bulkCountT, dm1T, Term.eval, hdv, hkv,
    hqv, Option.bind, Option.bind_eq_bind, leftBandVal, cellRow, cellCol]
  by_cases h1 : qv % d = 0 <;> simp [h1] <;> split <;> simp_all

/-- `bottomBandGuard` evaluates to `bottomBandVal d kv qv`. -/
theorem bottomBandGuard_eval_gen {fuel d kv qv : Nat} {dT kT qT : Term 0 .nat} (rho : Env 0)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : Term.eval Surface.code.body fuel qT rho = some qv) :
    Term.eval Surface.code.body fuel (bottomBandGuard dT kT qT) rho
      = some (bottomBandVal d kv qv) := by
  simp only [bottomBandGuard, orEqPair, baseBT, baseHalfT, bulkCountT, dm1T, Term.eval, hdv, hkv,
    hqv, Option.bind, Option.bind_eq_bind, bottomBandVal, cellRow, cellCol]
  by_cases h1 : qv / d = d-1 <;> simp [h1] <;> split <;> simp_all

/-! ## Purity certificates for the band / classifier guards

`SurfaceRowCharacterizationFull` exposes `baseBulkBandGuard_pure` and
`baseKindGuard_pure`; the boundary band guards and the boundary classifier guards
need their own purity certificates (the Grid-file ones are `private`). -/

def topBandGuard_pure {dT kT qT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    SFormula.PureBoolTerm (topBandGuard dT kT qT) := by
  have hdm1 := SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 1)
  have hb := SFormula.PureNatTerm.sub hk (SFormula.PureNatTerm.mul hdm1 hdm1)
  exact SFormula.PureBoolTerm.and
    (SFormula.PureBoolTerm.ltNat hk
      (SFormula.PureNatTerm.sub (SFormula.PureNatTerm.mul hd hd) (SFormula.PureNatTerm.nat 1)))
    (SFormula.PureBoolTerm.and
      (SFormula.PureBoolTerm.eqNat (SFormula.PureNatTerm.div hq hd) (SFormula.PureNatTerm.nat 0))
      (SFormula.PureBoolTerm.or
        (SFormula.PureBoolTerm.eqNat (SFormula.PureNatTerm.mod hq hd)
          (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 2) hb))
        (SFormula.PureBoolTerm.eqNat (SFormula.PureNatTerm.mod hq hd)
          (SFormula.PureNatTerm.add (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 2) hb)
            (SFormula.PureNatTerm.nat 1)))))

def rightBandGuard_pure {dT kT qT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    SFormula.PureBoolTerm (rightBandGuard dT kT qT) := by
  have hdm1 := SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 1)
  have hb := SFormula.PureNatTerm.sub hk (SFormula.PureNatTerm.mul hdm1 hdm1)
  have hhalf := SFormula.PureNatTerm.div hdm1 (SFormula.PureNatTerm.nat 2)
  have hbb := SFormula.PureNatTerm.sub hb hhalf
  exact SFormula.PureBoolTerm.and
    (SFormula.PureBoolTerm.eqNat (SFormula.PureNatTerm.mod hq hd) hdm1)
    (SFormula.PureBoolTerm.or
      (SFormula.PureBoolTerm.eqNat (SFormula.PureNatTerm.div hq hd)
        (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 2) hbb))
      (SFormula.PureBoolTerm.eqNat (SFormula.PureNatTerm.div hq hd)
        (SFormula.PureNatTerm.add (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 2) hbb)
          (SFormula.PureNatTerm.nat 1))))

def leftBandGuard_pure {dT kT qT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    SFormula.PureBoolTerm (leftBandGuard dT kT qT) := by
  have hdm1 := SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 1)
  have hb := SFormula.PureNatTerm.sub hk (SFormula.PureNatTerm.mul hdm1 hdm1)
  have hhalf := SFormula.PureNatTerm.div hdm1 (SFormula.PureNatTerm.nat 2)
  have hbb := SFormula.PureNatTerm.sub hb (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 2) hhalf)
  exact SFormula.PureBoolTerm.and
    (SFormula.PureBoolTerm.eqNat (SFormula.PureNatTerm.mod hq hd) (SFormula.PureNatTerm.nat 0))
    (SFormula.PureBoolTerm.or
      (SFormula.PureBoolTerm.eqNat (SFormula.PureNatTerm.div hq hd)
        (SFormula.PureNatTerm.add (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 2) hbb)
          (SFormula.PureNatTerm.nat 1)))
      (SFormula.PureBoolTerm.eqNat (SFormula.PureNatTerm.div hq hd)
        (SFormula.PureNatTerm.add (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 2) hbb)
          (SFormula.PureNatTerm.nat 2))))

def bottomBandGuard_pure {dT kT qT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    SFormula.PureBoolTerm (bottomBandGuard dT kT qT) := by
  have hdm1 := SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 1)
  have hb := SFormula.PureNatTerm.sub hk (SFormula.PureNatTerm.mul hdm1 hdm1)
  have hhalf := SFormula.PureNatTerm.div hdm1 (SFormula.PureNatTerm.nat 2)
  have hbb := SFormula.PureNatTerm.sub hb (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 3) hhalf)
  exact SFormula.PureBoolTerm.and
    (SFormula.PureBoolTerm.eqNat (SFormula.PureNatTerm.div hq hd) hdm1)
    (SFormula.PureBoolTerm.or
      (SFormula.PureBoolTerm.eqNat (SFormula.PureNatTerm.mod hq hd)
        (SFormula.PureNatTerm.add (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 2) hbb)
          (SFormula.PureNatTerm.nat 1)))
      (SFormula.PureBoolTerm.eqNat (SFormula.PureNatTerm.mod hq hd)
        (SFormula.PureNatTerm.add (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 2) hbb)
          (SFormula.PureNatTerm.nat 2))))

def topClassGuard_pure {dT kT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureBoolTerm (topClassGuard dT kT) := by
  have hdm1 := SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 1)
  have hb := SFormula.PureNatTerm.sub hk (SFormula.PureNatTerm.mul hdm1 hdm1)
  exact SFormula.PureBoolTerm.ltNat hb
    (SFormula.PureNatTerm.div hdm1 (SFormula.PureNatTerm.nat 2))

def rightClassGuard_pure {dT kT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureBoolTerm (rightClassGuard dT kT) := by
  have hdm1 := SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 1)
  have hb := SFormula.PureNatTerm.sub hk (SFormula.PureNatTerm.mul hdm1 hdm1)
  exact SFormula.PureBoolTerm.ltNat hb
    (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 2)
      (SFormula.PureNatTerm.div hdm1 (SFormula.PureNatTerm.nat 2)))

def leftClassGuard_pure {dT kT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureBoolTerm (leftClassGuard dT kT) := by
  have hdm1 := SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 1)
  have hb := SFormula.PureNatTerm.sub hk (SFormula.PureNatTerm.mul hdm1 hdm1)
  exact SFormula.PureBoolTerm.ltNat hb
    (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 3)
      (SFormula.PureNatTerm.div hdm1 (SFormula.PureNatTerm.nat 2)))

/-! ## Nat-level classifier predicates and their eval-gens

The boundary classifier guards `topClassGuard`/`rightClassGuard`/`leftClassGuard`
test only `b = k - bulkCount` against `half`/`2*half`/`3*half`. -/

def topClassVal (d k : Nat) : Bool := decide (k - (d-1)*(d-1) < (d-1)/2)
def rightClassVal (d k : Nat) : Bool := decide (k - (d-1)*(d-1) < 2*((d-1)/2))
def leftClassVal (d k : Nat) : Bool := decide (k - (d-1)*(d-1) < 3*((d-1)/2))

theorem topClassGuard_eval_gen {fuel d kv : Nat} {dT kT : Term 0 .nat} (rho : Env 0)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv) :
    Term.eval Surface.code.body fuel (topClassGuard dT kT) rho = some (topClassVal d kv) := by
  simp only [topClassGuard, baseBT, baseHalfT, bulkCountT, dm1T, Term.eval, hdv, hkv,
    Option.bind, Option.bind_eq_bind, topClassVal]

theorem rightClassGuard_eval_gen {fuel d kv : Nat} {dT kT : Term 0 .nat} (rho : Env 0)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv) :
    Term.eval Surface.code.body fuel (rightClassGuard dT kT) rho = some (rightClassVal d kv) := by
  simp only [rightClassGuard, baseBT, baseHalfT, bulkCountT, dm1T, Term.eval, hdv, hkv,
    Option.bind, Option.bind_eq_bind, rightClassVal]

theorem leftClassGuard_eval_gen {fuel d kv : Nat} {dT kT : Term 0 .nat} (rho : Env 0)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv) :
    Term.eval Surface.code.body fuel (leftClassGuard dT kT) rho = some (leftClassVal d kv) := by
  simp only [leftClassGuard, baseBT, baseHalfT, bulkCountT, dm1T, Term.eval, hdv, hkv,
    Option.bind, Option.bind_eq_bind, leftClassVal]

/-! ## Guard generators (TRUE/FALSE) from the Nat-level values -/

def baseBulkBandGuard_of {fuel d kv qv : Nat} {dT kT qT : Term 0 .nat} {b : Bool}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hdv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel qT rho = some qv)
    (hfact : baseBulkBandVal d kv qv = b) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (baseBulkBandGuard dT kT qT)) (SC.b b)) :=
  cellGuard_of (baseBulkBandGuard_pure hd hk hq)
    (by intro rho; rw [baseBulkBandGuard_eval_gen rho (hdv rho) (hkv rho) (hqv rho), hfact])

def baseKindGuard_of {fuel d kv : Nat} {dT kT : Term 0 .nat} {b : Bool}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT)
    (hdv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel kT rho = some kv)
    (hfact : baseKindVal d kv = b) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (baseKindGuard dT kT)) (SC.b b)) :=
  cellGuard_of (baseKindGuard_pure hd hk)
    (by intro rho; rw [baseKindGuard_eval_gen rho (hdv rho) (hkv rho), hfact])

def topBandGuard_of {fuel d kv qv : Nat} {dT kT qT : Term 0 .nat} {b : Bool}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hdv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel qT rho = some qv)
    (hfact : topBandVal d kv qv = b) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topBandGuard dT kT qT)) (SC.b b)) :=
  cellGuard_of (topBandGuard_pure hd hk hq)
    (by intro rho; rw [topBandGuard_eval_gen rho (hdv rho) (hkv rho) (hqv rho), hfact])

def rightBandGuard_of {fuel d kv qv : Nat} {dT kT qT : Term 0 .nat} {b : Bool}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hdv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel qT rho = some qv)
    (hfact : rightBandVal d kv qv = b) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (rightBandGuard dT kT qT)) (SC.b b)) :=
  cellGuard_of (rightBandGuard_pure hd hk hq)
    (by intro rho; rw [rightBandGuard_eval_gen rho (hdv rho) (hkv rho) (hqv rho), hfact])

def leftBandGuard_of {fuel d kv qv : Nat} {dT kT qT : Term 0 .nat} {b : Bool}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hdv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel qT rho = some qv)
    (hfact : leftBandVal d kv qv = b) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (leftBandGuard dT kT qT)) (SC.b b)) :=
  cellGuard_of (leftBandGuard_pure hd hk hq)
    (by intro rho; rw [leftBandGuard_eval_gen rho (hdv rho) (hkv rho) (hqv rho), hfact])

def bottomBandGuard_of {fuel d kv qv : Nat} {dT kT qT : Term 0 .nat} {b : Bool}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hdv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel qT rho = some qv)
    (hfact : bottomBandVal d kv qv = b) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bottomBandGuard dT kT qT)) (SC.b b)) :=
  cellGuard_of (bottomBandGuard_pure hd hk hq)
    (by intro rho; rw [bottomBandGuard_eval_gen rho (hdv rho) (hkv rho) (hqv rho), hfact])

def topClassGuard_of {fuel d kv : Nat} {dT kT : Term 0 .nat} {b : Bool}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT)
    (hdv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel kT rho = some kv)
    (hfact : topClassVal d kv = b) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topClassGuard dT kT)) (SC.b b)) :=
  cellGuard_of (topClassGuard_pure hd hk)
    (by intro rho; rw [topClassGuard_eval_gen rho (hdv rho) (hkv rho), hfact])

def rightClassGuard_of {fuel d kv : Nat} {dT kT : Term 0 .nat} {b : Bool}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT)
    (hdv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel kT rho = some kv)
    (hfact : rightClassVal d kv = b) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (rightClassGuard dT kT)) (SC.b b)) :=
  cellGuard_of (rightClassGuard_pure hd hk)
    (by intro rho; rw [rightClassGuard_eval_gen rho (hdv rho) (hkv rho), hfact])

def leftClassGuard_of {fuel d kv : Nat} {dT kT : Term 0 .nat} {b : Bool}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT)
    (hdv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel kT rho = some kv)
    (hfact : leftClassVal d kv = b) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (leftClassGuard dT kT)) (SC.b b)) :=
  cellGuard_of (leftClassGuard_pure hd hk)
    (by intro rho; rw [leftClassGuard_eval_gen rho (hdv rho) (hkv rho), hfact])

/-! ## The general-`d` base-entry body resolver (NO oracle)

For arbitrary closed pure terms `dT`/`kT`/`qT` with eval certificates
`dT→d`, `kT→kv`, `qT→qv`, the substituted `baseEntry` body at `qT` carries
`surfaceCellPauli d kv qv`.  This is the genuine replacement for the keystone's
universal `oracle.resolve`: it dispatches on the *decidable* `Nat`-level cell kind
of `(d, kv, qv)` and routes each branch to the matching parametric base peel,
proving in each branch that `surfaceCellPauli d kv qv` equals the peel's literal
Pauli (by `simp`/`decide` on `Nat`).  No hypothesis equivalent to the conclusion. -/

/-- Relate `inBulkBand`/`baseBulkBandVal` (used by the bulk peels' guards) and
`surfaceCellPauli`'s `bulkKind` to the kind guard `baseKindVal`. -/
private theorem inBulkBand_eq_baseBulkBandVal (d k q : Nat) :
    inBulkBand d k q = baseBulkBandVal d k q := by
  simp only [inBulkBand, baseBulkBandVal, cellRow, cellCol, cellR, cellC, Bool.and_assoc]

def recBaseBodyResolve {fuel d kv qv : Nat} (dT kT qT : Term 0 .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hdv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel qT rho = some qv) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.baseEntry)))
          (SC.closed qT))
        (SC.closed (.pauliLit (surfaceCellPauli d kv qv)))) := by
  by_cases hbulk : kv < (d-1)*(d-1)
  · -- bulk plaquette
    by_cases hband : inBulkBand d kv qv = true
    · -- in band: kind Z or X
      by_cases hkind : (cellR d kv + cellC d kv) % 2 = 0
      · -- Z plaquette
        have hcp : surfaceCellPauli d kv qv = Pauli.Z := by
          simp only [surfaceCellPauli, bulkKind, if_pos hbulk, hband, if_true, if_pos hkind]
        rw [hcp]
        exact recBasePeel dT kT qT hd hk hq
          (bulkGuard_of hd hk hdv hkv (decide_eq_true hbulk))
          (baseBulkBandGuard_of hd hk hq hdv hkv hqv
            (by rw [← inBulkBand_eq_baseBulkBandVal]; exact hband))
          (baseKindGuard_of hd hk hdv hkv (by simp [baseKindVal, hkind]))
      · -- X plaquette
        have hcp : surfaceCellPauli d kv qv = Pauli.X := by
          simp only [surfaceCellPauli, bulkKind, if_pos hbulk, hband, if_true, if_neg hkind]
        rw [hcp]
        exact recBasePeelX dT kT qT hd hk hq
          (bulkGuard_of hd hk hdv hkv (decide_eq_true hbulk))
          (baseBulkBandGuard_of hd hk hq hdv hkv hqv
            (by rw [← inBulkBand_eq_baseBulkBandVal]; exact hband))
          (baseKindGuard_of hd hk hdv hkv (by simp [baseKindVal, hkind]))
    · -- out of band: I
      have hbandF : inBulkBand d kv qv = false := by simpa using hband
      have hcp : surfaceCellPauli d kv qv = Pauli.I := by
        simp only [surfaceCellPauli, if_pos hbulk, hbandF, Bool.false_eq_true, if_false]
      rw [hcp]
      exact recBasePeelI dT kT qT hd hk hq
        (bulkGuard_of hd hk hdv hkv (decide_eq_true hbulk))
        (baseBulkBandGuard_of hd hk hq hdv hkv hqv
          (by rw [← inBulkBand_eq_baseBulkBandVal]; exact hbandF))
  · -- boundary index (kv ≥ bulkCount): top / right / left / bottom
    have hbulkF : decide (kv < (d-1)*(d-1)) = false := by simp [hbulk]
    by_cases htop : kv - (d-1)*(d-1) < (d-1)/2
    · -- top-X strip (`b < half`)
      have htopclass : topClassVal d kv = true := by simp [topClassVal, htop]
      have hcondtop : (kv < d*d - 1 && cellRow d qv = 0 &&
          (cellCol d qv = 2*(kv - (d-1)*(d-1)) || cellCol d qv = 2*(kv - (d-1)*(d-1)) + 1))
            = topBandVal d kv qv := by
        simp only [topBandVal, cellRow, cellCol, Bool.and_assoc]
      by_cases htb : topBandVal d kv qv = true
      · have hcp : surfaceCellPauli d kv qv = Pauli.X := by
          simp only [surfaceCellPauli, if_neg hbulk, if_pos htop, hcondtop, htb, if_true]
        rw [hcp]
        exact recTopXPeel dT kT qT hd hk hq
          (bulkGuardFalse_of hd hk hdv hkv hbulkF)
          (topClassGuard_of hd hk hdv hkv htopclass)
          (topBandGuard_of hd hk hq hdv hkv hqv htb)
      · have htbF : topBandVal d kv qv = false := by simpa using htb
        have hcp : surfaceCellPauli d kv qv = Pauli.I := by
          simp only [surfaceCellPauli, if_neg hbulk, if_pos htop, hcondtop, htbF,
            Bool.false_eq_true, if_false]
        rw [hcp]
        exact recTopIPeel dT kT qT hd hk hq
          (bulkGuardFalse_of hd hk hdv hkv hbulkF)
          (topClassGuard_of hd hk hdv hkv htopclass)
          (topBandGuard_of hd hk hq hdv hkv hqv htbF)
    · -- not top: right / left / bottom
      have htopclassF : topClassVal d kv = false := by simp [topClassVal, htop]
      by_cases hright : kv - (d-1)*(d-1) < 2*((d-1)/2)
      · -- right-Z strip (`half ≤ b < 2*half`)
        have hrightclass : rightClassVal d kv = true := by simp [rightClassVal, hright]
        have hcondright : (cellCol d qv = d-1 &&
            (cellRow d qv = 2*(kv - (d-1)*(d-1) - (d-1)/2) ||
              cellRow d qv = 2*(kv - (d-1)*(d-1) - (d-1)/2) + 1)) = rightBandVal d kv qv := by
          simp only [rightBandVal, cellRow, cellCol]
        by_cases hrb : rightBandVal d kv qv = true
        · have hcp : surfaceCellPauli d kv qv = Pauli.Z := by
            simp only [surfaceCellPauli, if_neg hbulk, if_neg htop, if_pos hright,
              hcondright, hrb, if_true]
          rw [hcp]
          exact recRightZPeel dT kT qT hd hk hq
            (bulkGuardFalse_of hd hk hdv hkv hbulkF)
            (topClassGuard_of hd hk hdv hkv htopclassF)
            (rightClassGuard_of hd hk hdv hkv hrightclass)
            (rightBandGuard_of hd hk hq hdv hkv hqv hrb)
        · have hrbF : rightBandVal d kv qv = false := by simpa using hrb
          have hcp : surfaceCellPauli d kv qv = Pauli.I := by
            simp only [surfaceCellPauli, if_neg hbulk, if_neg htop, if_pos hright,
              hcondright, hrbF, Bool.false_eq_true, if_false]
          rw [hcp]
          exact recRightIPeel dT kT qT hd hk hq
            (bulkGuardFalse_of hd hk hdv hkv hbulkF)
            (topClassGuard_of hd hk hdv hkv htopclassF)
            (rightClassGuard_of hd hk hdv hkv hrightclass)
            (rightBandGuard_of hd hk hq hdv hkv hqv hrbF)
      · -- not right: left / bottom
        have hrightclassF : rightClassVal d kv = false := by simp [rightClassVal, hright]
        by_cases hleft : kv - (d-1)*(d-1) < 3*((d-1)/2)
        · -- left-Z strip (`2*half ≤ b < 3*half`)
          have hleftclass : leftClassVal d kv = true := by simp [leftClassVal, hleft]
          have hcondleft : (cellCol d qv = 0 &&
              (cellRow d qv = 2*(kv - (d-1)*(d-1) - 2*((d-1)/2)) + 1 ||
                cellRow d qv = 2*(kv - (d-1)*(d-1) - 2*((d-1)/2)) + 2)) = leftBandVal d kv qv := by
            simp only [leftBandVal, cellRow, cellCol]
          by_cases hlb : leftBandVal d kv qv = true
          · have hcp : surfaceCellPauli d kv qv = Pauli.Z := by
              simp only [surfaceCellPauli, if_neg hbulk, if_neg htop, if_neg hright, if_pos hleft,
                hcondleft, hlb, if_true]
            rw [hcp]
            exact recLeftZPeel dT kT qT hd hk hq
              (bulkGuardFalse_of hd hk hdv hkv hbulkF)
              (topClassGuard_of hd hk hdv hkv htopclassF)
              (rightClassGuard_of hd hk hdv hkv hrightclassF)
              (leftClassGuard_of hd hk hdv hkv hleftclass)
              (leftBandGuard_of hd hk hq hdv hkv hqv hlb)
          · have hlbF : leftBandVal d kv qv = false := by simpa using hlb
            have hcp : surfaceCellPauli d kv qv = Pauli.I := by
              simp only [surfaceCellPauli, if_neg hbulk, if_neg htop, if_neg hright, if_pos hleft,
                hcondleft, hlbF, Bool.false_eq_true, if_false]
            rw [hcp]
            exact recLeftIPeel dT kT qT hd hk hq
              (bulkGuardFalse_of hd hk hdv hkv hbulkF)
              (topClassGuard_of hd hk hdv hkv htopclassF)
              (rightClassGuard_of hd hk hdv hkv hrightclassF)
              (leftClassGuard_of hd hk hdv hkv hleftclass)
              (leftBandGuard_of hd hk hq hdv hkv hqv hlbF)
        · -- bottom-X strip (`b ≥ 3*half`)
          have hleftclassF : leftClassVal d kv = false := by simp [leftClassVal, hleft]
          have hcondbot : (cellRow d qv = d-1 &&
              (cellCol d qv = 2*(kv - (d-1)*(d-1) - 3*((d-1)/2)) + 1 ||
                cellCol d qv = 2*(kv - (d-1)*(d-1) - 3*((d-1)/2)) + 2)) = bottomBandVal d kv qv := by
            simp only [bottomBandVal, cellRow, cellCol]
          by_cases hbb : bottomBandVal d kv qv = true
          · have hcp : surfaceCellPauli d kv qv = Pauli.X := by
              simp only [surfaceCellPauli, if_neg hbulk, if_neg htop, if_neg hright, if_neg hleft,
                hcondbot, hbb, if_true]
            rw [hcp]
            exact recBottomXPeel dT kT qT hd hk hq
              (bulkGuardFalse_of hd hk hdv hkv hbulkF)
              (topClassGuard_of hd hk hdv hkv htopclassF)
              (rightClassGuard_of hd hk hdv hkv hrightclassF)
              (leftClassGuard_of hd hk hdv hkv hleftclassF)
              (bottomBandGuard_of hd hk hq hdv hkv hqv hbb)
          · have hbbF : bottomBandVal d kv qv = false := by simpa using hbb
            have hcp : surfaceCellPauli d kv qv = Pauli.I := by
              simp only [surfaceCellPauli, if_neg hbulk, if_neg htop, if_neg hright, if_neg hleft,
                hcondbot, hbbF, Bool.false_eq_true, if_false]
            rw [hcp]
            exact recBottomIPeel dT kT qT hd hk hq
              (bulkGuardFalse_of hd hk hdv hkv hbulkF)
              (topClassGuard_of hd hk hdv hkv htopclassF)
              (rightClassGuard_of hd hk hdv hkv hrightclassF)
              (leftClassGuard_of hd hk hdv hkv hleftclassF)
              (bottomBandGuard_of hd hk hq hdv hkv hqv hbbF)

/-! ## Recursive-entry boundary peels (distance `d ≥ 5`)

For the recursive entry, a *boundary* stabilizer index (`k ≥ bulkCount`) selects
the outer `else`, which is literally `baseEntry`.  After that single outer-`else`
selection the residual is the substituted-`baseEntry` `ite` tree — the same tree
the base-entry peels resolve.  Each peel below performs the outer-`else` selection
then the matching base-entry boundary selections (top / right / left / bottom; in
band → kind, out of band → `I`). -/

/-- Strip the recursive entry's `stabLam` and select the outer boundary `else`
(`k ≥ bulkCount`), exposing the substituted `baseEntry` residual `ite` tree. -/
private def recBoundaryOuterSelect {fuel : Nat} (dT kT qT : Term 0 .nat)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardT dT kT)) (SC.b false))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed qT))
        (SC.closed (Term.instantiateTopNat qT
          (codeSubstAt dT kT 1 SurfaceASTPublic.baseEntry)))) := by
  simp only [SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
    SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q,
    C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT,
    Nat.reduceEqDiff, reduceDIte, eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4,
    orEqSucc, orEqPair, le]
  exact pureStabAtClosedIteLamElse (fuel := fuel)
    (.ltNat (Term.lift 0 kT)
      (.mul (.sub (Term.lift 0 dT) (.natLit 1)) (.sub (Term.lift 0 dT) (.natLit 1))))
    _ _ qT hq (by
      have heq : Term.instantiateTopNat qT
          (Term.ltNat (Term.lift 0 kT)
            (.mul (.sub (Term.lift 0 dT) (.natLit 1)) (.sub (Term.lift 0 dT) (.natLit 1))))
          = bulkGuardT dT kT := by
        simp only [bulkGuardT, bulkCountT, dm1T, Term.instantiateTopNat, Term.instantiateNatAt,
          instTop_lift]
      rw [heq]; exact hBulk)

/-- Shared simp normalizing the `recBoundaryOuterSelect` residual to the
substituted-`baseEntry` boundary `ite` tree (with the inner `k<bulkCount` exposed). -/
private theorem recBoundaryGuardRewrites (dT kT qT : Term 0 .nat) :
    (bulkGuardT dT kT
        = kT.ltNat ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))) ∧
    (topClassGuard dT kT
        = (kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))).ltNat
            ((dT.sub (Term.natLit 1)).div (Term.natLit 2))) ∧
    (rightClassGuard dT kT
        = (kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))).ltNat
            ((Term.natLit 2).mul ((dT.sub (Term.natLit 1)).div (Term.natLit 2)))) ∧
    (leftClassGuard dT kT
        = (kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))).ltNat
            ((Term.natLit 3).mul ((dT.sub (Term.natLit 1)).div (Term.natLit 2)))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [bulkGuardT, bulkCountT, dm1T]
  · simp only [topClassGuard, baseBT, baseHalfT, bulkCountT, dm1T]
  · simp only [rightClassGuard, baseBT, baseHalfT, bulkCountT, dm1T]
  · simp only [leftClassGuard, baseBT, baseHalfT, bulkCountT, dm1T]

/-- **Recursive-entry boundary top-X peel.** -/
def recRecTopXPeel {fuel : Nat} (dT kT qT : Term 0 .nat)
    (_hd : SFormula.PureNatTerm dT) (_hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardT dT kT)) (SC.b false)))
    (hTopClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topClassGuard dT kT)) (SC.b true)))
    (hTopBand : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topBandGuard dT kT qT)) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed qT))
        (SC.closed (.pauliLit Pauli.X))) := by
  obtain ⟨hbg, htg, _, _⟩ := recBoundaryGuardRewrites dT kT qT
  refine PureFamilyDerivA.eqPauliTrans _ _ _ (recBoundaryOuterSelect dT kT qT hq hBulk) ?_
  simp only [SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
    SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN,
    Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, orEqSucc, orEqPair,
    Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift, Nat.lt_irrefl,
    dite_false, dite_true]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [hbg] at hBulk; exact hBulk))
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [htg] at hTopClass; exact hTopClass))
      (PureFamilyDerivA.eqPauliTrans _ _ _
        (PureFamilyDerivA.pauliIteSelectThen _ _ _ ?hTopBandG)
        (PureFamilyDerivA.eqPauliRefl _)))
  case hTopBandG =>
    have heq : topBandGuard dT kT qT
        = (kT.ltNat ((dT.mul dT).sub (Term.natLit 1))).and
            (((qT.div dT).eqNat (Term.natLit 0)).and
              (((qT.mod dT).eqNat ((Term.natLit 2).mul (kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))))).or
                ((qT.mod dT).eqNat (((Term.natLit 2).mul (kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1))))).add (Term.natLit 1))))) := by
      simp only [topBandGuard, baseBT, band3, orEqSucc, bulkCountT, dm1T]
    rw [heq] at hTopBand; exact hTopBand

/-- **Recursive-entry boundary top out-of-band → `I` peel.** -/
def recRecTopIPeel {fuel : Nat} (dT kT qT : Term 0 .nat)
    (_hd : SFormula.PureNatTerm dT) (_hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardT dT kT)) (SC.b false)))
    (hTopClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topClassGuard dT kT)) (SC.b true)))
    (hTopBand : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topBandGuard dT kT qT)) (SC.b false))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed qT))
        (SC.closed (.pauliLit Pauli.I))) := by
  obtain ⟨hbg, htg, _, _⟩ := recBoundaryGuardRewrites dT kT qT
  refine PureFamilyDerivA.eqPauliTrans _ _ _ (recBoundaryOuterSelect dT kT qT hq hBulk) ?_
  simp only [SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
    SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN,
    Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, orEqSucc, orEqPair,
    Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift, Nat.lt_irrefl,
    dite_false, dite_true]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [hbg] at hBulk; exact hBulk))
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [htg] at hTopClass; exact hTopClass))
      (PureFamilyDerivA.pauliIteSelectElse _ _ _ ?hTopBandG))
  case hTopBandG =>
    have heq : topBandGuard dT kT qT
        = (kT.ltNat ((dT.mul dT).sub (Term.natLit 1))).and
            (((qT.div dT).eqNat (Term.natLit 0)).and
              (((qT.mod dT).eqNat ((Term.natLit 2).mul (kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))))).or
                ((qT.mod dT).eqNat (((Term.natLit 2).mul (kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1))))).add (Term.natLit 1))))) := by
      simp only [topBandGuard, baseBT, band3, orEqSucc, bulkCountT, dm1T]
    rw [heq] at hTopBand; exact hTopBand

/-- **Recursive-entry boundary right-Z peel.** -/
def recRecRightZPeel {fuel : Nat} (dT kT qT : Term 0 .nat)
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
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed qT))
        (SC.closed (.pauliLit Pauli.Z))) := by
  obtain ⟨hbg, htg, hrg, _⟩ := recBoundaryGuardRewrites dT kT qT
  refine PureFamilyDerivA.eqPauliTrans _ _ _ (recBoundaryOuterSelect dT kT qT hq hBulk) ?_
  simp only [SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
    SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN,
    Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, orEqSucc, orEqPair,
    Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift, Nat.lt_irrefl,
    dite_false, dite_true]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [hbg] at hBulk; exact hBulk))
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [htg] at hTopClass; exact hTopClass))
      (PureFamilyDerivA.eqPauliTrans _ _ _
        (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [hrg] at hRightClass; exact hRightClass))
        (PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.pauliIteSelectThen _ _ _ ?hRightBandG)
          (PureFamilyDerivA.eqPauliRefl _))))
  case hRightBandG =>
    have heq : rightBandGuard dT kT qT
        = ((qT.mod dT).eqNat (dT.sub (Term.natLit 1))).and
            (((qT.div dT).eqNat ((Term.natLit 2).mul ((kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))).sub ((dT.sub (Term.natLit 1)).div (Term.natLit 2))))).or
              ((qT.div dT).eqNat (((Term.natLit 2).mul ((kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))).sub ((dT.sub (Term.natLit 1)).div (Term.natLit 2)))).add (Term.natLit 1)))) := by
      simp only [rightBandGuard, baseBT, baseHalfT, orEqSucc, bulkCountT, dm1T]
    rw [heq] at hRightBand; exact hRightBand

/-- **Recursive-entry boundary right out-of-band → `I` peel.** -/
def recRecRightIPeel {fuel : Nat} (dT kT qT : Term 0 .nat)
    (_hd : SFormula.PureNatTerm dT) (_hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardT dT kT)) (SC.b false)))
    (hTopClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topClassGuard dT kT)) (SC.b false)))
    (hRightClass : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (rightClassGuard dT kT)) (SC.b true)))
    (hRightBand : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (rightBandGuard dT kT qT)) (SC.b false))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed qT))
        (SC.closed (.pauliLit Pauli.I))) := by
  obtain ⟨hbg, htg, hrg, _⟩ := recBoundaryGuardRewrites dT kT qT
  refine PureFamilyDerivA.eqPauliTrans _ _ _ (recBoundaryOuterSelect dT kT qT hq hBulk) ?_
  simp only [SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
    SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN,
    Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, orEqSucc, orEqPair,
    Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift, Nat.lt_irrefl,
    dite_false, dite_true]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [hbg] at hBulk; exact hBulk))
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [htg] at hTopClass; exact hTopClass))
      (PureFamilyDerivA.eqPauliTrans _ _ _
        (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [hrg] at hRightClass; exact hRightClass))
        (PureFamilyDerivA.pauliIteSelectElse _ _ _ ?hRightBandG)))
  case hRightBandG =>
    have heq : rightBandGuard dT kT qT
        = ((qT.mod dT).eqNat (dT.sub (Term.natLit 1))).and
            (((qT.div dT).eqNat ((Term.natLit 2).mul ((kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))).sub ((dT.sub (Term.natLit 1)).div (Term.natLit 2))))).or
              ((qT.div dT).eqNat (((Term.natLit 2).mul ((kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))).sub ((dT.sub (Term.natLit 1)).div (Term.natLit 2)))).add (Term.natLit 1)))) := by
      simp only [rightBandGuard, baseBT, baseHalfT, orEqSucc, bulkCountT, dm1T]
    rw [heq] at hRightBand; exact hRightBand

/-- **Recursive-entry boundary left-Z peel.** -/
def recRecLeftZPeel {fuel : Nat} (dT kT qT : Term 0 .nat)
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
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed qT))
        (SC.closed (.pauliLit Pauli.Z))) := by
  obtain ⟨hbg, htg, hrg, hlg⟩ := recBoundaryGuardRewrites dT kT qT
  refine PureFamilyDerivA.eqPauliTrans _ _ _ (recBoundaryOuterSelect dT kT qT hq hBulk) ?_
  simp only [SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
    SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN,
    Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, orEqSucc, orEqPair,
    Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift, Nat.lt_irrefl,
    dite_false, dite_true]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [hbg] at hBulk; exact hBulk))
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [htg] at hTopClass; exact hTopClass))
      (PureFamilyDerivA.eqPauliTrans _ _ _
        (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [hrg] at hRightClass; exact hRightClass))
        (PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [hlg] at hLeftClass; exact hLeftClass))
          (PureFamilyDerivA.eqPauliTrans _ _ _
            (PureFamilyDerivA.pauliIteSelectThen _ _ _ ?hLeftBandG)
            (PureFamilyDerivA.eqPauliRefl _)))))
  case hLeftBandG =>
    have heq : leftBandGuard dT kT qT
        = ((qT.mod dT).eqNat (Term.natLit 0)).and
            (((qT.div dT).eqNat (((Term.natLit 2).mul ((kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))).sub ((Term.natLit 2).mul ((dT.sub (Term.natLit 1)).div (Term.natLit 2))))).add (Term.natLit 1))).or
              ((qT.div dT).eqNat (((Term.natLit 2).mul ((kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))).sub ((Term.natLit 2).mul ((dT.sub (Term.natLit 1)).div (Term.natLit 2))))).add (Term.natLit 2)))) := by
      simp only [leftBandGuard, baseBT, baseHalfT, orEqPair, bulkCountT, dm1T]
    rw [heq] at hLeftBand; exact hLeftBand

/-- **Recursive-entry boundary left out-of-band → `I` peel.** -/
def recRecLeftIPeel {fuel : Nat} (dT kT qT : Term 0 .nat)
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
      (.eqBool (SC.closed (leftBandGuard dT kT qT)) (SC.b false))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed qT))
        (SC.closed (.pauliLit Pauli.I))) := by
  obtain ⟨hbg, htg, hrg, hlg⟩ := recBoundaryGuardRewrites dT kT qT
  refine PureFamilyDerivA.eqPauliTrans _ _ _ (recBoundaryOuterSelect dT kT qT hq hBulk) ?_
  simp only [SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
    SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN,
    Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, orEqSucc, orEqPair,
    Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift, Nat.lt_irrefl,
    dite_false, dite_true]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [hbg] at hBulk; exact hBulk))
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [htg] at hTopClass; exact hTopClass))
      (PureFamilyDerivA.eqPauliTrans _ _ _
        (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [hrg] at hRightClass; exact hRightClass))
        (PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [hlg] at hLeftClass; exact hLeftClass))
          (PureFamilyDerivA.pauliIteSelectElse _ _ _ ?hLeftBandG))))
  case hLeftBandG =>
    have heq : leftBandGuard dT kT qT
        = ((qT.mod dT).eqNat (Term.natLit 0)).and
            (((qT.div dT).eqNat (((Term.natLit 2).mul ((kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))).sub ((Term.natLit 2).mul ((dT.sub (Term.natLit 1)).div (Term.natLit 2))))).add (Term.natLit 1))).or
              ((qT.div dT).eqNat (((Term.natLit 2).mul ((kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))).sub ((Term.natLit 2).mul ((dT.sub (Term.natLit 1)).div (Term.natLit 2))))).add (Term.natLit 2)))) := by
      simp only [leftBandGuard, baseBT, baseHalfT, orEqPair, bulkCountT, dm1T]
    rw [heq] at hLeftBand; exact hLeftBand

/-- **Recursive-entry boundary bottom-X peel.** -/
def recRecBottomXPeel {fuel : Nat} (dT kT qT : Term 0 .nat)
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
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed qT))
        (SC.closed (.pauliLit Pauli.X))) := by
  obtain ⟨hbg, htg, hrg, hlg⟩ := recBoundaryGuardRewrites dT kT qT
  refine PureFamilyDerivA.eqPauliTrans _ _ _ (recBoundaryOuterSelect dT kT qT hq hBulk) ?_
  simp only [SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
    SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN,
    Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, orEqSucc, orEqPair,
    Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift, Nat.lt_irrefl,
    dite_false, dite_true]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [hbg] at hBulk; exact hBulk))
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [htg] at hTopClass; exact hTopClass))
      (PureFamilyDerivA.eqPauliTrans _ _ _
        (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [hrg] at hRightClass; exact hRightClass))
        (PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [hlg] at hLeftClass; exact hLeftClass))
          (PureFamilyDerivA.eqPauliTrans _ _ _
            (PureFamilyDerivA.pauliIteSelectThen _ _ _ ?hBottomBandG)
            (PureFamilyDerivA.eqPauliRefl _)))))
  case hBottomBandG =>
    have heq : bottomBandGuard dT kT qT
        = ((qT.div dT).eqNat (dT.sub (Term.natLit 1))).and
            (((qT.mod dT).eqNat (((Term.natLit 2).mul ((kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))).sub ((Term.natLit 3).mul ((dT.sub (Term.natLit 1)).div (Term.natLit 2))))).add (Term.natLit 1))).or
              ((qT.mod dT).eqNat (((Term.natLit 2).mul ((kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))).sub ((Term.natLit 3).mul ((dT.sub (Term.natLit 1)).div (Term.natLit 2))))).add (Term.natLit 2)))) := by
      simp only [bottomBandGuard, baseBT, baseHalfT, orEqPair, bulkCountT, dm1T]
    rw [heq] at hBottomBand; exact hBottomBand

/-- **Recursive-entry boundary bottom out-of-band → `I` peel.** -/
def recRecBottomIPeel {fuel : Nat} (dT kT qT : Term 0 .nat)
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
      (.eqBool (SC.closed (bottomBandGuard dT kT qT)) (SC.b false))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed qT))
        (SC.closed (.pauliLit Pauli.I))) := by
  obtain ⟨hbg, htg, hrg, hlg⟩ := recBoundaryGuardRewrites dT kT qT
  refine PureFamilyDerivA.eqPauliTrans _ _ _ (recBoundaryOuterSelect dT kT qT hq hBulk) ?_
  simp only [SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
    SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN,
    Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, orEqSucc, orEqPair,
    Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift, Nat.lt_irrefl,
    dite_false, dite_true]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [hbg] at hBulk; exact hBulk))
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [htg] at hTopClass; exact hTopClass))
      (PureFamilyDerivA.eqPauliTrans _ _ _
        (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [hrg] at hRightClass; exact hRightClass))
        (PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [hlg] at hLeftClass; exact hLeftClass))
          (PureFamilyDerivA.pauliIteSelectElse _ _ _ ?hBottomBandG))))
  case hBottomBandG =>
    have heq : bottomBandGuard dT kT qT
        = ((qT.div dT).eqNat (dT.sub (Term.natLit 1))).and
            (((qT.mod dT).eqNat (((Term.natLit 2).mul ((kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))).sub ((Term.natLit 3).mul ((dT.sub (Term.natLit 1)).div (Term.natLit 2))))).add (Term.natLit 1))).or
              ((qT.mod dT).eqNat (((Term.natLit 2).mul ((kT.sub ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))).sub ((Term.natLit 3).mul ((dT.sub (Term.natLit 1)).div (Term.natLit 2))))).add (Term.natLit 2)))) := by
      simp only [bottomBandGuard, baseBT, baseHalfT, orEqPair, bulkCountT, dm1T]
    rw [heq] at hBottomBand; exact hBottomBand

/-- **Recursive-entry base-fallback Z peel.** -/
def recRecFallbackZPeel {fuel : Nat} (dT kT qT : Term 0 .nat)
    (_hd : SFormula.PureNatTerm dT) (_hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
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
      (.eqBool (SC.closed (bottomCellGuard dT kT)) (SC.b false)))
    (hBand : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (baseBulkBandGuard dT kT qT)) (SC.b true)))
    (hKind : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (baseKindGuard dT kT)) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed qT))
        (SC.closed (.pauliLit Pauli.Z))) := by
  simp only [SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
    SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q,
    C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT,
    Nat.reduceEqDiff, reduceDIte, eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4,
    orEqSucc, orEqPair, le]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (pureStabAtClosedIteLamThen (fuel := fuel)
      (.ltNat (Term.lift 0 kT)
        (.mul (.sub (Term.lift 0 dT) (.natLit 1)) (.sub (Term.lift 0 dT) (.natLit 1))))
      _ _ qT hq ?hBulkSel) ?_
  case hBulkSel =>
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
    (PureFamilyDerivA.pauliIteSelectElse _ _ _ ?hInteriorG)
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectElse _ _ _ ?hTopG)
      (PureFamilyDerivA.eqPauliTrans _ _ _
        (PureFamilyDerivA.pauliIteSelectElse _ _ _ ?hRightG)
        (PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.pauliIteSelectElse _ _ _ ?hLeftG)
          (PureFamilyDerivA.eqPauliTrans _ _ _
            (PureFamilyDerivA.pauliIteSelectElse _ _ _ ?hBottomG)
            (PureFamilyDerivA.eqPauliTrans _ _ _
              (PureFamilyDerivA.pauliIteSelectThen _ _ _ ?hBaseBulkG)
              (PureFamilyDerivA.eqPauliTrans _ _ _
                (PureFamilyDerivA.pauliIteSelectThen _ _ _ ?hBandG)
                (PureFamilyDerivA.eqPauliTrans _ _ _
                  (PureFamilyDerivA.pauliIteSelectThen _ _ _ ?hKindG)
                  (PureFamilyDerivA.eqPauliRefl _))))))))
  case hInteriorG =>
    have heq : interiorCellGuardT dT kT
        = ((Term.natLit 1).leNat (kT.div (dT.sub (Term.natLit 1)))).and
            (((kT.div (dT.sub (Term.natLit 1))).ltNat ((dT.sub (Term.natLit 1)).sub (Term.natLit 1))).and
              (((Term.natLit 1).leNat (kT.mod (dT.sub (Term.natLit 1)))).and
                ((kT.mod (dT.sub (Term.natLit 1))).ltNat ((dT.sub (Term.natLit 1)).sub (Term.natLit 1))))) := by
      simp only [interiorCellGuardT, band4, band3, le, rT, cT, lastCellT, dm1T]
    rw [heq] at hInterior; exact hInterior
  case hTopG =>
    have heq : topCellGuard dT kT
        = (((kT.div (dT.sub (Term.natLit 1))).eqNat (Term.natLit 0)).and
            ((((kT.mod (dT.sub (Term.natLit 1))).eqNat
                  (((Term.natLit 2).mul
                        (((kT.mod (dT.sub (Term.natLit 1))).sub (Term.natLit 1)).div (Term.natLit 2))).add
                    (Term.natLit 1)))).and
              ((((kT.mod (dT.sub (Term.natLit 1))).sub (Term.natLit 1)).div (Term.natLit 2)).ltNat
                (((dT.sub (Term.natLit 2)).sub (Term.natLit 1)).div (Term.natLit 2))))) := by
      simp only [topCellGuard, band3, topBT, rT, cT, recInnerHalfT, recInnerDm1T, recInnerDT, dm1T]
    rw [heq] at hTop; exact hTop
  case hRightG =>
    have heq : rightCellGuard dT kT
        = (((kT.mod (dT.sub (Term.natLit 1))).eqNat ((dT.sub (Term.natLit 1)).sub (Term.natLit 1))).and
            ((((kT.div (dT.sub (Term.natLit 1))).eqNat
                  (((Term.natLit 2).mul
                        (((kT.div (dT.sub (Term.natLit 1))).sub (Term.natLit 1)).div (Term.natLit 2))).add
                    (Term.natLit 1)))).and
              ((((kT.div (dT.sub (Term.natLit 1))).sub (Term.natLit 1)).div (Term.natLit 2)).ltNat
                (((dT.sub (Term.natLit 2)).sub (Term.natLit 1)).div (Term.natLit 2))))) := by
      simp only [rightCellGuard, band3, rightBT, rT, cT, lastCellT, recInnerHalfT, recInnerDm1T,
        recInnerDT, dm1T]
    rw [heq] at hRight; exact hRight
  case hLeftG =>
    have heq : leftCellGuard dT kT
        = (((kT.mod (dT.sub (Term.natLit 1))).eqNat (Term.natLit 0)).and
            ((((kT.div (dT.sub (Term.natLit 1))).eqNat
                  (((Term.natLit 2).mul
                        (((kT.div (dT.sub (Term.natLit 1))).sub (Term.natLit 2)).div (Term.natLit 2))).add
                    (Term.natLit 2)))).and
              ((((kT.div (dT.sub (Term.natLit 1))).sub (Term.natLit 2)).div (Term.natLit 2)).ltNat
                (((dT.sub (Term.natLit 2)).sub (Term.natLit 1)).div (Term.natLit 2))))) := by
      simp only [leftCellGuard, band3, leftBT, rT, cT, recInnerHalfT, recInnerDm1T, recInnerDT, dm1T]
    rw [heq] at hLeft; exact hLeft
  case hBottomG =>
    have heq : bottomCellGuard dT kT
        = (((kT.div (dT.sub (Term.natLit 1))).eqNat ((dT.sub (Term.natLit 1)).sub (Term.natLit 1))).and
            ((((kT.mod (dT.sub (Term.natLit 1))).eqNat
                  (((Term.natLit 2).mul
                        (((kT.mod (dT.sub (Term.natLit 1))).sub (Term.natLit 2)).div (Term.natLit 2))).add
                    (Term.natLit 2)))).and
              ((((kT.mod (dT.sub (Term.natLit 1))).sub (Term.natLit 2)).div (Term.natLit 2)).ltNat
                (((dT.sub (Term.natLit 2)).sub (Term.natLit 1)).div (Term.natLit 2))))) := by
      simp only [bottomCellGuard, band3, bottomBT, rT, cT, lastCellT, recInnerHalfT, recInnerDm1T,
        recInnerDT, dm1T]
    rw [heq] at hBottom; exact hBottom
  case hBaseBulkG =>
    have heq : bulkGuardT dT kT
        = kT.ltNat ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1))) := by
      simp only [bulkGuardT, bulkCountT, dm1T]
    rw [heq] at hBulk; exact hBulk
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

/-- **Recursive-entry base-fallback X peel.** -/
def recRecFallbackXPeel {fuel : Nat} (dT kT qT : Term 0 .nat)
    (_hd : SFormula.PureNatTerm dT) (_hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
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
      (.eqBool (SC.closed (bottomCellGuard dT kT)) (SC.b false)))
    (hBand : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (baseBulkBandGuard dT kT qT)) (SC.b true)))
    (hKind : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (baseKindGuard dT kT)) (SC.b false))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed qT))
        (SC.closed (.pauliLit Pauli.X))) := by
  simp only [SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
    SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q,
    C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT,
    Nat.reduceEqDiff, reduceDIte, eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4,
    orEqSucc, orEqPair, le]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (pureStabAtClosedIteLamThen (fuel := fuel)
      (.ltNat (Term.lift 0 kT)
        (.mul (.sub (Term.lift 0 dT) (.natLit 1)) (.sub (Term.lift 0 dT) (.natLit 1))))
      _ _ qT hq ?hBulkSel) ?_
  case hBulkSel =>
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
    (PureFamilyDerivA.pauliIteSelectElse _ _ _ ?hInteriorG)
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectElse _ _ _ ?hTopG)
      (PureFamilyDerivA.eqPauliTrans _ _ _
        (PureFamilyDerivA.pauliIteSelectElse _ _ _ ?hRightG)
        (PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.pauliIteSelectElse _ _ _ ?hLeftG)
          (PureFamilyDerivA.eqPauliTrans _ _ _
            (PureFamilyDerivA.pauliIteSelectElse _ _ _ ?hBottomG)
            (PureFamilyDerivA.eqPauliTrans _ _ _
              (PureFamilyDerivA.pauliIteSelectThen _ _ _ ?hBaseBulkG)
              (PureFamilyDerivA.eqPauliTrans _ _ _
                (PureFamilyDerivA.pauliIteSelectThen _ _ _ ?hBandG)
                (PureFamilyDerivA.pauliIteSelectElse _ _ _ ?hKindG)))))))
  case hInteriorG =>
    have heq : interiorCellGuardT dT kT
        = ((Term.natLit 1).leNat (kT.div (dT.sub (Term.natLit 1)))).and
            (((kT.div (dT.sub (Term.natLit 1))).ltNat ((dT.sub (Term.natLit 1)).sub (Term.natLit 1))).and
              (((Term.natLit 1).leNat (kT.mod (dT.sub (Term.natLit 1)))).and
                ((kT.mod (dT.sub (Term.natLit 1))).ltNat ((dT.sub (Term.natLit 1)).sub (Term.natLit 1))))) := by
      simp only [interiorCellGuardT, band4, band3, le, rT, cT, lastCellT, dm1T]
    rw [heq] at hInterior; exact hInterior
  case hTopG =>
    have heq : topCellGuard dT kT
        = (((kT.div (dT.sub (Term.natLit 1))).eqNat (Term.natLit 0)).and
            ((((kT.mod (dT.sub (Term.natLit 1))).eqNat
                  (((Term.natLit 2).mul
                        (((kT.mod (dT.sub (Term.natLit 1))).sub (Term.natLit 1)).div (Term.natLit 2))).add
                    (Term.natLit 1)))).and
              ((((kT.mod (dT.sub (Term.natLit 1))).sub (Term.natLit 1)).div (Term.natLit 2)).ltNat
                (((dT.sub (Term.natLit 2)).sub (Term.natLit 1)).div (Term.natLit 2))))) := by
      simp only [topCellGuard, band3, topBT, rT, cT, recInnerHalfT, recInnerDm1T, recInnerDT, dm1T]
    rw [heq] at hTop; exact hTop
  case hRightG =>
    have heq : rightCellGuard dT kT
        = (((kT.mod (dT.sub (Term.natLit 1))).eqNat ((dT.sub (Term.natLit 1)).sub (Term.natLit 1))).and
            ((((kT.div (dT.sub (Term.natLit 1))).eqNat
                  (((Term.natLit 2).mul
                        (((kT.div (dT.sub (Term.natLit 1))).sub (Term.natLit 1)).div (Term.natLit 2))).add
                    (Term.natLit 1)))).and
              ((((kT.div (dT.sub (Term.natLit 1))).sub (Term.natLit 1)).div (Term.natLit 2)).ltNat
                (((dT.sub (Term.natLit 2)).sub (Term.natLit 1)).div (Term.natLit 2))))) := by
      simp only [rightCellGuard, band3, rightBT, rT, cT, lastCellT, recInnerHalfT, recInnerDm1T,
        recInnerDT, dm1T]
    rw [heq] at hRight; exact hRight
  case hLeftG =>
    have heq : leftCellGuard dT kT
        = (((kT.mod (dT.sub (Term.natLit 1))).eqNat (Term.natLit 0)).and
            ((((kT.div (dT.sub (Term.natLit 1))).eqNat
                  (((Term.natLit 2).mul
                        (((kT.div (dT.sub (Term.natLit 1))).sub (Term.natLit 2)).div (Term.natLit 2))).add
                    (Term.natLit 2)))).and
              ((((kT.div (dT.sub (Term.natLit 1))).sub (Term.natLit 2)).div (Term.natLit 2)).ltNat
                (((dT.sub (Term.natLit 2)).sub (Term.natLit 1)).div (Term.natLit 2))))) := by
      simp only [leftCellGuard, band3, leftBT, rT, cT, recInnerHalfT, recInnerDm1T, recInnerDT, dm1T]
    rw [heq] at hLeft; exact hLeft
  case hBottomG =>
    have heq : bottomCellGuard dT kT
        = (((kT.div (dT.sub (Term.natLit 1))).eqNat ((dT.sub (Term.natLit 1)).sub (Term.natLit 1))).and
            ((((kT.mod (dT.sub (Term.natLit 1))).eqNat
                  (((Term.natLit 2).mul
                        (((kT.mod (dT.sub (Term.natLit 1))).sub (Term.natLit 2)).div (Term.natLit 2))).add
                    (Term.natLit 2)))).and
              ((((kT.mod (dT.sub (Term.natLit 1))).sub (Term.natLit 2)).div (Term.natLit 2)).ltNat
                (((dT.sub (Term.natLit 2)).sub (Term.natLit 1)).div (Term.natLit 2))))) := by
      simp only [bottomCellGuard, band3, bottomBT, rT, cT, lastCellT, recInnerHalfT, recInnerDm1T,
        recInnerDT, dm1T]
    rw [heq] at hBottom; exact hBottom
  case hBaseBulkG =>
    have heq : bulkGuardT dT kT
        = kT.ltNat ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1))) := by
      simp only [bulkGuardT, bulkCountT, dm1T]
    rw [heq] at hBulk; exact hBulk
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

/-- **Recursive-entry base-fallback out-of-band → `I` peel.** -/
def recRecFallbackIPeel {fuel : Nat} (dT kT qT : Term 0 .nat)
    (_hd : SFormula.PureNatTerm dT) (_hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
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
      (.eqBool (SC.closed (bottomCellGuard dT kT)) (SC.b false)))
    (hBand : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (baseBulkBandGuard dT kT qT)) (SC.b false))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed qT))
        (SC.closed (.pauliLit Pauli.I))) := by
  simp only [SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
    SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q,
    C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT,
    Nat.reduceEqDiff, reduceDIte, eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4,
    orEqSucc, orEqPair, le]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (pureStabAtClosedIteLamThen (fuel := fuel)
      (.ltNat (Term.lift 0 kT)
        (.mul (.sub (Term.lift 0 dT) (.natLit 1)) (.sub (Term.lift 0 dT) (.natLit 1))))
      _ _ qT hq ?hBulkSel) ?_
  case hBulkSel =>
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
    (PureFamilyDerivA.pauliIteSelectElse _ _ _ ?hInteriorG)
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectElse _ _ _ ?hTopG)
      (PureFamilyDerivA.eqPauliTrans _ _ _
        (PureFamilyDerivA.pauliIteSelectElse _ _ _ ?hRightG)
        (PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.pauliIteSelectElse _ _ _ ?hLeftG)
          (PureFamilyDerivA.eqPauliTrans _ _ _
            (PureFamilyDerivA.pauliIteSelectElse _ _ _ ?hBottomG)
            (PureFamilyDerivA.eqPauliTrans _ _ _
              (PureFamilyDerivA.pauliIteSelectThen _ _ _ ?hBaseBulkG)
              (PureFamilyDerivA.pauliIteSelectElse _ _ _ ?hBandG))))))
  case hInteriorG =>
    have heq : interiorCellGuardT dT kT
        = ((Term.natLit 1).leNat (kT.div (dT.sub (Term.natLit 1)))).and
            (((kT.div (dT.sub (Term.natLit 1))).ltNat ((dT.sub (Term.natLit 1)).sub (Term.natLit 1))).and
              (((Term.natLit 1).leNat (kT.mod (dT.sub (Term.natLit 1)))).and
                ((kT.mod (dT.sub (Term.natLit 1))).ltNat ((dT.sub (Term.natLit 1)).sub (Term.natLit 1))))) := by
      simp only [interiorCellGuardT, band4, band3, le, rT, cT, lastCellT, dm1T]
    rw [heq] at hInterior; exact hInterior
  case hTopG =>
    have heq : topCellGuard dT kT
        = (((kT.div (dT.sub (Term.natLit 1))).eqNat (Term.natLit 0)).and
            ((((kT.mod (dT.sub (Term.natLit 1))).eqNat
                  (((Term.natLit 2).mul
                        (((kT.mod (dT.sub (Term.natLit 1))).sub (Term.natLit 1)).div (Term.natLit 2))).add
                    (Term.natLit 1)))).and
              ((((kT.mod (dT.sub (Term.natLit 1))).sub (Term.natLit 1)).div (Term.natLit 2)).ltNat
                (((dT.sub (Term.natLit 2)).sub (Term.natLit 1)).div (Term.natLit 2))))) := by
      simp only [topCellGuard, band3, topBT, rT, cT, recInnerHalfT, recInnerDm1T, recInnerDT, dm1T]
    rw [heq] at hTop; exact hTop
  case hRightG =>
    have heq : rightCellGuard dT kT
        = (((kT.mod (dT.sub (Term.natLit 1))).eqNat ((dT.sub (Term.natLit 1)).sub (Term.natLit 1))).and
            ((((kT.div (dT.sub (Term.natLit 1))).eqNat
                  (((Term.natLit 2).mul
                        (((kT.div (dT.sub (Term.natLit 1))).sub (Term.natLit 1)).div (Term.natLit 2))).add
                    (Term.natLit 1)))).and
              ((((kT.div (dT.sub (Term.natLit 1))).sub (Term.natLit 1)).div (Term.natLit 2)).ltNat
                (((dT.sub (Term.natLit 2)).sub (Term.natLit 1)).div (Term.natLit 2))))) := by
      simp only [rightCellGuard, band3, rightBT, rT, cT, lastCellT, recInnerHalfT, recInnerDm1T,
        recInnerDT, dm1T]
    rw [heq] at hRight; exact hRight
  case hLeftG =>
    have heq : leftCellGuard dT kT
        = (((kT.mod (dT.sub (Term.natLit 1))).eqNat (Term.natLit 0)).and
            ((((kT.div (dT.sub (Term.natLit 1))).eqNat
                  (((Term.natLit 2).mul
                        (((kT.div (dT.sub (Term.natLit 1))).sub (Term.natLit 2)).div (Term.natLit 2))).add
                    (Term.natLit 2)))).and
              ((((kT.div (dT.sub (Term.natLit 1))).sub (Term.natLit 2)).div (Term.natLit 2)).ltNat
                (((dT.sub (Term.natLit 2)).sub (Term.natLit 1)).div (Term.natLit 2))))) := by
      simp only [leftCellGuard, band3, leftBT, rT, cT, recInnerHalfT, recInnerDm1T, recInnerDT, dm1T]
    rw [heq] at hLeft; exact hLeft
  case hBottomG =>
    have heq : bottomCellGuard dT kT
        = (((kT.div (dT.sub (Term.natLit 1))).eqNat ((dT.sub (Term.natLit 1)).sub (Term.natLit 1))).and
            ((((kT.mod (dT.sub (Term.natLit 1))).eqNat
                  (((Term.natLit 2).mul
                        (((kT.mod (dT.sub (Term.natLit 1))).sub (Term.natLit 2)).div (Term.natLit 2))).add
                    (Term.natLit 2)))).and
              ((((kT.mod (dT.sub (Term.natLit 1))).sub (Term.natLit 2)).div (Term.natLit 2)).ltNat
                (((dT.sub (Term.natLit 2)).sub (Term.natLit 1)).div (Term.natLit 2))))) := by
      simp only [bottomCellGuard, band3, bottomBT, rT, cT, lastCellT, recInnerHalfT, recInnerDm1T,
        recInnerDT, dm1T]
    rw [heq] at hBottom; exact hBottom
  case hBaseBulkG =>
    have heq : bulkGuardT dT kT
        = kT.ltNat ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1))) := by
      simp only [bulkGuardT, bulkCountT, dm1T]
    rw [heq] at hBulk; exact hBulk
  case hBandG =>
    have heq : baseBulkBandGuard dT kT qT
        = ((((qT.div dT).eqNat (kT.div (dT.sub (Term.natLit 1)))).or
                ((qT.div dT).eqNat ((kT.div (dT.sub (Term.natLit 1))).add (Term.natLit 1)))).and
            ((((qT.mod dT).eqNat (kT.mod (dT.sub (Term.natLit 1)))).or
                  ((qT.mod dT).eqNat ((kT.mod (dT.sub (Term.natLit 1))).add (Term.natLit 1)))).and
              (kT.ltNat ((dT.sub (Term.natLit 1)).mul (dT.sub (Term.natLit 1)))))) := by
      simp only [baseBulkBandGuard, band3, orEqSucc, bulkCountT, dm1T]
    rw [heq] at hBand; exact hBand

/-! ## Row-level resolvers for the recursive entry's non-recursing cells

These produce the *generated row* `recCall dT kT @ qT = surfaceCellPauli d kv qv`
for the recursive entry (`d ≥ 5`), composing the recursive-entry peels above with
the recursive-branch row selection `surfaceCodeRecursiveEntryEq` (distance guard
`dT < 5` FALSE).  Two dispatchers: boundary index (`kv ≥ bulkCount`) and
bulk-with-no-cell-kind (the base fallback). -/

/-- **Boundary-index row resolver (recursive entry).**  For a boundary stabilizer
index (`kv ≥ bulkCount`), the generated row carries `surfaceCellPauli d kv qv`. -/
def recBoundaryRowResolve {fuel d kv qv : Nat} (dT kT qT : Term 0 .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hDist : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat dT (n5 : Term 0 .nat))) (SC.b false)))
    (hdv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel qT rho = some qv)
    (hbulk : ¬ kv < (d-1)*(d-1)) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.recCall dT kT)) (SC.closed qT))
        (SC.closed (.pauliLit (surfaceCellPauli d kv qv)))) := by
  have hbulkF : decide (kv < (d-1)*(d-1)) = false := by simp [hbulk]
  refine surfaceCodeRecursiveEntryEq (SC.n (nQubits d)) dT kT qT _ hd hk hDist ?_
  by_cases htop : kv - (d-1)*(d-1) < (d-1)/2
  · -- top-X strip
    have htopclass : topClassVal d kv = true := by simp [topClassVal, htop]
    have hcondtop : (kv < d*d - 1 && cellRow d qv = 0 &&
        (cellCol d qv = 2*(kv - (d-1)*(d-1)) || cellCol d qv = 2*(kv - (d-1)*(d-1)) + 1))
          = topBandVal d kv qv := by
      simp only [topBandVal, cellRow, cellCol, Bool.and_assoc]
    by_cases htb : topBandVal d kv qv = true
    · have hcp : surfaceCellPauli d kv qv = Pauli.X := by
        simp only [surfaceCellPauli, if_neg hbulk, if_pos htop, hcondtop, htb, if_true]
      rw [hcp]
      exact recRecTopXPeel dT kT qT hd hk hq (bulkGuardFalse_of hd hk hdv hkv hbulkF)
        (topClassGuard_of hd hk hdv hkv htopclass) (topBandGuard_of hd hk hq hdv hkv hqv htb)
    · have htbF : topBandVal d kv qv = false := by simpa using htb
      have hcp : surfaceCellPauli d kv qv = Pauli.I := by
        simp only [surfaceCellPauli, if_neg hbulk, if_pos htop, hcondtop, htbF,
          Bool.false_eq_true, if_false]
      rw [hcp]
      exact recRecTopIPeel dT kT qT hd hk hq (bulkGuardFalse_of hd hk hdv hkv hbulkF)
        (topClassGuard_of hd hk hdv hkv htopclass) (topBandGuard_of hd hk hq hdv hkv hqv htbF)
  · have htopclassF : topClassVal d kv = false := by simp [topClassVal, htop]
    by_cases hright : kv - (d-1)*(d-1) < 2*((d-1)/2)
    · -- right-Z strip
      have hrightclass : rightClassVal d kv = true := by simp [rightClassVal, hright]
      have hcondright : (cellCol d qv = d-1 &&
          (cellRow d qv = 2*(kv - (d-1)*(d-1) - (d-1)/2) ||
            cellRow d qv = 2*(kv - (d-1)*(d-1) - (d-1)/2) + 1)) = rightBandVal d kv qv := by
        simp only [rightBandVal, cellRow, cellCol]
      by_cases hrb : rightBandVal d kv qv = true
      · have hcp : surfaceCellPauli d kv qv = Pauli.Z := by
          simp only [surfaceCellPauli, if_neg hbulk, if_neg htop, if_pos hright, hcondright, hrb,
            if_true]
        rw [hcp]
        exact recRecRightZPeel dT kT qT hd hk hq (bulkGuardFalse_of hd hk hdv hkv hbulkF)
          (topClassGuard_of hd hk hdv hkv htopclassF)
          (rightClassGuard_of hd hk hdv hkv hrightclass) (rightBandGuard_of hd hk hq hdv hkv hqv hrb)
      · have hrbF : rightBandVal d kv qv = false := by simpa using hrb
        have hcp : surfaceCellPauli d kv qv = Pauli.I := by
          simp only [surfaceCellPauli, if_neg hbulk, if_neg htop, if_pos hright, hcondright, hrbF,
            Bool.false_eq_true, if_false]
        rw [hcp]
        exact recRecRightIPeel dT kT qT hd hk hq (bulkGuardFalse_of hd hk hdv hkv hbulkF)
          (topClassGuard_of hd hk hdv hkv htopclassF)
          (rightClassGuard_of hd hk hdv hkv hrightclass) (rightBandGuard_of hd hk hq hdv hkv hqv hrbF)
    · have hrightclassF : rightClassVal d kv = false := by simp [rightClassVal, hright]
      by_cases hleft : kv - (d-1)*(d-1) < 3*((d-1)/2)
      · -- left-Z strip
        have hleftclass : leftClassVal d kv = true := by simp [leftClassVal, hleft]
        have hcondleft : (cellCol d qv = 0 &&
            (cellRow d qv = 2*(kv - (d-1)*(d-1) - 2*((d-1)/2)) + 1 ||
              cellRow d qv = 2*(kv - (d-1)*(d-1) - 2*((d-1)/2)) + 2)) = leftBandVal d kv qv := by
          simp only [leftBandVal, cellRow, cellCol]
        by_cases hlb : leftBandVal d kv qv = true
        · have hcp : surfaceCellPauli d kv qv = Pauli.Z := by
            simp only [surfaceCellPauli, if_neg hbulk, if_neg htop, if_neg hright, if_pos hleft,
              hcondleft, hlb, if_true]
          rw [hcp]
          exact recRecLeftZPeel dT kT qT hd hk hq (bulkGuardFalse_of hd hk hdv hkv hbulkF)
            (topClassGuard_of hd hk hdv hkv htopclassF)
            (rightClassGuard_of hd hk hdv hkv hrightclassF)
            (leftClassGuard_of hd hk hdv hkv hleftclass) (leftBandGuard_of hd hk hq hdv hkv hqv hlb)
        · have hlbF : leftBandVal d kv qv = false := by simpa using hlb
          have hcp : surfaceCellPauli d kv qv = Pauli.I := by
            simp only [surfaceCellPauli, if_neg hbulk, if_neg htop, if_neg hright, if_pos hleft,
              hcondleft, hlbF, Bool.false_eq_true, if_false]
          rw [hcp]
          exact recRecLeftIPeel dT kT qT hd hk hq (bulkGuardFalse_of hd hk hdv hkv hbulkF)
            (topClassGuard_of hd hk hdv hkv htopclassF)
            (rightClassGuard_of hd hk hdv hkv hrightclassF)
            (leftClassGuard_of hd hk hdv hkv hleftclass) (leftBandGuard_of hd hk hq hdv hkv hqv hlbF)
      · -- bottom-X strip
        have hleftclassF : leftClassVal d kv = false := by simp [leftClassVal, hleft]
        have hcondbot : (cellRow d qv = d-1 &&
            (cellCol d qv = 2*(kv - (d-1)*(d-1) - 3*((d-1)/2)) + 1 ||
              cellCol d qv = 2*(kv - (d-1)*(d-1) - 3*((d-1)/2)) + 2)) = bottomBandVal d kv qv := by
          simp only [bottomBandVal, cellRow, cellCol]
        by_cases hbb : bottomBandVal d kv qv = true
        · have hcp : surfaceCellPauli d kv qv = Pauli.X := by
            simp only [surfaceCellPauli, if_neg hbulk, if_neg htop, if_neg hright, if_neg hleft,
              hcondbot, hbb, if_true]
          rw [hcp]
          exact recRecBottomXPeel dT kT qT hd hk hq (bulkGuardFalse_of hd hk hdv hkv hbulkF)
            (topClassGuard_of hd hk hdv hkv htopclassF)
            (rightClassGuard_of hd hk hdv hkv hrightclassF)
            (leftClassGuard_of hd hk hdv hkv hleftclassF)
            (bottomBandGuard_of hd hk hq hdv hkv hqv hbb)
        · have hbbF : bottomBandVal d kv qv = false := by simpa using hbb
          have hcp : surfaceCellPauli d kv qv = Pauli.I := by
            simp only [surfaceCellPauli, if_neg hbulk, if_neg htop, if_neg hright, if_neg hleft,
              hcondbot, hbbF, Bool.false_eq_true, if_false]
          rw [hcp]
          exact recRecBottomIPeel dT kT qT hd hk hq (bulkGuardFalse_of hd hk hdv hkv hbulkF)
            (topClassGuard_of hd hk hdv hkv htopclassF)
            (rightClassGuard_of hd hk hdv hkv hrightclassF)
            (leftClassGuard_of hd hk hdv hkv hleftclassF)
            (bottomBandGuard_of hd hk hq hdv hkv hqv hbbF)

/-- **Base-fallback row resolver (recursive entry).**  For a *bulk* stabilizer
index (`kv < bulkCount`) that is NOT an interior / top / right / left / bottom
cell, the generated row carries `surfaceCellPauli d kv qv` (the bulk plaquette
kind or `I`).  The cell-kind-`false` facts are supplied by the caller. -/
def recFallbackRowResolve {fuel d kv qv : Nat} (dT kT qT : Term 0 .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hDist : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat dT (n5 : Term 0 .nat))) (SC.b false)))
    (hdv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel qT rho = some qv)
    (hbulk : kv < (d-1)*(d-1))
    (hintF : isInteriorCell d kv = false) (htopF : isTopCell d kv = false)
    (hrightF : isRightCell d kv = false) (hleftF : isLeftCell d kv = false)
    (hbottomF : isBottomCell d kv = false) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.recCall dT kT)) (SC.closed qT))
        (SC.closed (.pauliLit (surfaceCellPauli d kv qv)))) := by
  refine surfaceCodeRecursiveEntryEq (SC.n (nQubits d)) dT kT qT _ hd hk hDist ?_
  have hbulkD : decide (kv < (d-1)*(d-1)) = true := decide_eq_true hbulk
  have hb := bulkGuard_of hd hk hdv hkv hbulkD
  have hint := interiorCellGuardFalse_of hd hk hdv hkv hintF
  have htop := topCellGuard_of hd hk hdv hkv htopF
  have hright := rightCellGuard_of hd hk hdv hkv hrightF
  have hleft := leftCellGuard_of hd hk hdv hkv hleftF
  have hbottom := bottomCellGuard_of hd hk hdv hkv hbottomF
  by_cases hband : inBulkBand d kv qv = true
  · by_cases hkind : (cellR d kv + cellC d kv) % 2 = 0
    · have hcp : surfaceCellPauli d kv qv = Pauli.Z := by
        simp only [surfaceCellPauli, bulkKind, if_pos hbulk, hband, if_true, if_pos hkind]
      rw [hcp]
      exact recRecFallbackZPeel dT kT qT hd hk hq hb hint htop hright hleft hbottom
        (baseBulkBandGuard_of hd hk hq hdv hkv hqv
          (by rw [← inBulkBand_eq_baseBulkBandVal]; exact hband))
        (baseKindGuard_of hd hk hdv hkv (by simp [baseKindVal, hkind]))
    · have hcp : surfaceCellPauli d kv qv = Pauli.X := by
        simp only [surfaceCellPauli, bulkKind, if_pos hbulk, hband, if_true, if_neg hkind]
      rw [hcp]
      exact recRecFallbackXPeel dT kT qT hd hk hq hb hint htop hright hleft hbottom
        (baseBulkBandGuard_of hd hk hq hdv hkv hqv
          (by rw [← inBulkBand_eq_baseBulkBandVal]; exact hband))
        (baseKindGuard_of hd hk hdv hkv (by simp [baseKindVal, hkind]))
  · have hbandF : inBulkBand d kv qv = false := by simpa using hband
    have hcp : surfaceCellPauli d kv qv = Pauli.I := by
      simp only [surfaceCellPauli, if_pos hbulk, hbandF, Bool.false_eq_true, if_false]
    rw [hcp]
    exact recRecFallbackIPeel dT kT qT hd hk hq hb hint htop hright hleft hbottom
      (baseBulkBandGuard_of hd hk hq hdv hkv hqv
        (by rw [← inBulkBand_eq_baseBulkBandVal]; exact hbandF))

/-- **Base-case (m = 0) row resolver.**  At distance `d = oddDistance 0 = 3` the
generated row is the base entry; it carries `surfaceCellPauli d kv qv` at every
`kv`/`qv`.  Composes the base-branch row selection (`dT < 5` TRUE) with the
general-`d` base-entry body resolver `recBaseBodyResolve`. -/
def recBaseRowResolve {fuel d kv qv : Nat} (dT kT qT : Term 0 .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hDist : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat dT (n5 : Term 0 .nat))) (SC.b true)))
    (hdv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel qT rho = some qv) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.recCall dT kT)) (SC.closed qT))
        (SC.closed (.pauliLit (surfaceCellPauli d kv qv)))) :=
  surfaceCodeBaseEntryEq (SC.n (nQubits d)) dT kT qT _ hd hk hDist
    (recBaseBodyResolve dT kT qT hd hk hq hdv hkv hqv)

/-! ## Promoted-boundary outer-leaf Nat identities

When a recursive-entry promoted cell's `inside` guard fails, the entry is the
closed `ite outer (kind) I` leaf.  Its value coincides with the base-entry
classifier `surfaceCellPauli` (self-similarity, cross-validated by
`recLeafAgrees`).  The four lemmas below establish this coincidence at the `Nat`
level: for a `topCell`/`rightCell`/`leftCell`/`bottomCell` index with `inside`
false, `surfaceCellPauli d kv qv = if outerVal then kind else I`. -/

/-- Top-cell outer Nat predicate (the `topOuter` guard, at `(d, kv, qv)`). -/
def topOuterVal (d k q : Nat) : Bool :=
  decide (cellRow d q = 0) &&
    (decide (cellCol d q = 2*((cellC d k - 1)/2) + 1) ||
      decide (cellCol d q = 2*((cellC d k - 1)/2) + 2))
def rightOuterVal (d k q : Nat) : Bool :=
  decide (cellCol d q = d-1) &&
    (decide (cellRow d q = 2*((cellR d k - 1)/2) + 1) ||
      decide (cellRow d q = 2*((cellR d k - 1)/2) + 2))
def leftOuterVal (d k q : Nat) : Bool :=
  decide (cellCol d q = 0) &&
    (decide (cellRow d q = 2*((cellR d k - 2)/2) + 2) ||
      decide (cellRow d q = 2*((cellR d k - 2)/2) + 3))
def bottomOuterVal (d k q : Nat) : Bool :=
  decide (cellRow d q = d-1) &&
    (decide (cellCol d q = 2*((cellC d k - 2)/2) + 2) ||
      decide (cellCol d q = 2*((cellC d k - 2)/2) + 3))

theorem surfaceCellPauli_topCell_notInside {d kv qv : Nat}
    (htop : isTopCell d kv = true) (hinF : isInside d qv = false) :
    surfaceCellPauli d kv qv = (if topOuterVal d kv qv then Pauli.X else Pauli.I) := by
  -- extract the topCell geometry: r = 0, c = 2*tb+1, tb < (d-3)/2
  simp only [isTopCell, cellR, cellC, cellLastCell, cellInnerHalf, Bool.and_eq_true,
    decide_eq_true_eq] at htop
  obtain ⟨hr, hc, htb⟩ := htop
  simp only [isInside, cellRow, cellCol, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true,
    Bool.and_eq_false_iff, decide_eq_false_iff_not, not_and, not_le, not_lt] at hinF
  have hd5 : 5 ≤ d := by omega
  have hdm1 : 1 ≤ d - 1 := by omega
  -- kv < d-1 (since kv/(d-1) = 0), hence kv < bulkCount
  have hkvlt : kv < d - 1 := by
    rcases Nat.lt_or_ge kv (d-1) with h|h
    · exact h
    · exact absurd hr (by
        have : 1 ≤ kv / (d-1) := (Nat.one_le_div_iff (by omega)).mpr h
        omega)
  have hbulk : kv < (d-1)*(d-1) :=
    lt_of_lt_of_le hkvlt (Nat.le_mul_of_pos_left _ hdm1)
  have hkindodd : ¬ (kv / (d-1) + kv % (d-1)) % 2 = 0 := by rw [hr, hc]; omega
  -- col bound for topCell cells: 2*tb+2 ≤ d-3, so the band columns lie in [1, d-2]
  have htb' : (kv % (d-1) - 1) / 2 < (d - 3) / 2 := by
    have he : (d - 2 - 1) = d - 3 := by omega
    rw [he] at htb; exact htb
  have hcolbound : kv % (d-1) + 1 < d - 1 := by
    rw [hc]; omega
  have hcpos : 1 ≤ kv % (d-1) := by rw [hc]; omega
  -- unfold the LHS bulk branch (rw, not simp, to avoid recursion blowup)
  rw [surfaceCellPauli, if_pos hbulk, bulkKind, if_neg hkindodd, inBulkBand, topOuterVal]
  simp only [cellRow, cellCol, cellR, cellC]
  -- align the RHS column literals with `kv%(d-1)` and `kv%(d-1)+1` via `hc`,
  -- and the LHS row literal `kv/(d-1)` with `0` via `hr`.
  have hc1 : 2 * ((kv % (d-1) - 1) / 2) + 1 = kv % (d-1) := by omega
  have hc2 : 2 * ((kv % (d-1) - 1) / 2) + 2 = kv % (d-1) + 1 := by omega
  rw [hc1, hc2]
  simp only [hr, decide_true, Bool.and_true]
  -- the col-band condition `qv%d = c ∨ qv%d = c+1` is shared by both sides.
  by_cases hcband : qv % d = kv % (d-1) ∨ qv % d = kv % (d-1) + 1
  · have hqcol1 : 1 ≤ qv % d := by rcases hcband with h|h <;> omega
    have hqcolbd : qv % d < d - 1 := by rcases hcband with h|h <;> omega
    by_cases hrow0 : qv / d = 0
    · rcases hcband with h|h <;> simp_all
    · -- row ≠ 0; in-band row would force `inside`, contradicting hinF
      have hrow_not1 : qv / d ≠ 1 := by
        intro h1; omega
      have hrowF : ¬ (qv / d = 0 ∨ qv / d = 1) := by omega
      rcases hcband with h|h <;> simp_all
  · push_neg at hcband
    rcases hcband with ⟨hne1, hne2⟩
    simp_all

theorem surfaceCellPauli_rightCell_notInside {d kv qv : Nat}
    (hright : isRightCell d kv = true) (hinF : isInside d qv = false) (hodd : d % 2 = 1) :
    surfaceCellPauli d kv qv = (if rightOuterVal d kv qv then Pauli.Z else Pauli.I) := by
  -- extract the rightCell geometry: c = d-2, r = 2*rb+1, rb < (d-3)/2
  simp only [isRightCell, cellR, cellC, cellLastCell, cellInnerHalf, Bool.and_eq_true,
    decide_eq_true_eq] at hright
  obtain ⟨hc, hr, hrb⟩ := hright
  -- `qv` is NOT inside: the four-condition conjunction fails.
  have hins : ¬ (1 ≤ qv / d ∧ qv / d < d-1 ∧ 1 ≤ qv % d ∧ qv % d < d-1) := by
    rintro ⟨h1, h2, h3, h4⟩
    have : isInside d qv = true := by
      simp only [isInside, cellRow, cellCol, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨h1, h2, h3, h4⟩
    rw [this] at hinF; exact absurd hinF (by decide)
  have hd5 : 5 ≤ d := by omega
  have hdm1 : 1 ≤ d - 1 := by omega
  -- row bound for rightCell cells: 2*rb+1 ≤ d-2, so the band rows lie in [1, d-2]
  have hrb' : (kv / (d-1) - 1) / 2 < (d - 3) / 2 := by
    have he : (d - 2 - 1) = d - 3 := by omega
    rw [he] at hrb; exact hrb
  have hrowbound : kv / (d-1) + 1 < d - 1 := by
    rw [hr]; omega
  have hrpos : 1 ≤ kv / (d-1) := by rw [hr]; omega
  -- kv / (d-1) < d - 1, hence kv < bulkCount
  have hbulk : kv < (d-1)*(d-1) := by
    have hrlt : kv / (d-1) < d - 1 := by omega
    have := (Nat.div_lt_iff_lt_mul (show 0 < d-1 by omega)).mp hrlt
    omega
  have hbulkD : decide (kv < (d-1)*(d-1)) = true := decide_eq_true hbulk
  -- right cell is the Z plaquette: (r + c) even (uses d odd)
  have hkindeven : (kv / (d-1) + kv % (d-1)) % 2 = 0 := by rw [hr, hc]; omega
  -- the column band: c = d-2, c+1 = d-1; rightOuter requires col = d-1
  have hcpos : 1 ≤ kv % (d-1) := by rw [hc]; omega
  -- unfold the LHS bulk branch (rw, not simp, to avoid recursion blowup)
  rw [surfaceCellPauli, if_pos hbulk, bulkKind, if_pos hkindeven, inBulkBand, rightOuterVal]
  simp only [cellRow, cellCol, cellR, cellC]
  -- align the RHS row literals with `kv/(d-1)` and `kv/(d-1)+1` via `hr`,
  -- and the LHS col literal `kv%(d-1)` with `d-2` via `hc`.
  have hr1 : 2 * ((kv / (d-1) - 1) / 2) + 1 = kv / (d-1) := by omega
  have hr2 : 2 * ((kv / (d-1) - 1) / 2) + 2 = kv / (d-1) + 1 := by omega
  rw [hr1, hr2]
  simp only [hc, hbulkD, Bool.and_true]
  -- the row-band condition `qv/d = r ∨ qv/d = r+1` is shared by both sides.
  by_cases hrband : qv / d = kv / (d-1) ∨ qv / d = kv / (d-1) + 1
  · have hqrow1 : 1 ≤ qv / d := by rcases hrband with h|h <;> omega
    have hqrowbd : qv / d < d - 1 := by rcases hrband with h|h <;> omega
    have hrowdec : (decide (qv / d = kv / (d - 1)) || decide (qv / d = kv / (d - 1) + 1)) = true := by
      rcases hrband with h|h <;> simp [h]
    by_cases hcol_dm1 : qv % d = d - 1
    · -- col = d-1 (last col): both sides → Z (LHS via c+1, RHS via outer)
      have ec1 : decide (qv % d = d - 1 - 1) = false := by simp; omega
      have ec2 : decide (qv % d = d - 1 - 1 + 1) = true := by simp; omega
      have ec3 : decide (qv % d = d - 1) = true := by simp [hcol_dm1]
      rw [hrowdec, ec1, ec2, ec3]; rfl
    · -- col ≠ d-1; in-band col = d-2 would force `inside`, contradicting hinF
      have hcol_not_dm2 : qv % d ≠ d - 1 - 1 := by
        intro h2
        exact hins ⟨hqrow1, hqrowbd, by omega, by omega⟩
      have ec1 : decide (qv % d = d - 1 - 1) = false := by simp [hcol_not_dm2]
      have ec2 : decide (qv % d = d - 1 - 1 + 1) = false := by simp; omega
      have ec3 : decide (qv % d = d - 1) = false := by simp [hcol_dm1]
      rw [ec1, ec2, ec3]; simp
  · push_neg at hrband
    rcases hrband with ⟨hne1, hne2⟩
    have er1 : decide (qv / d = kv / (d - 1)) = false := by simp [hne1]
    have er2 : decide (qv / d = kv / (d - 1) + 1) = false := by simp [hne2]
    rw [er1, er2]; simp

theorem surfaceCellPauli_leftCell_notInside {d kv qv : Nat}
    (hleft : isLeftCell d kv = true) (hinF : isInside d qv = false) :
    surfaceCellPauli d kv qv = (if leftOuterVal d kv qv then Pauli.Z else Pauli.I) := by
  -- extract the leftCell geometry: c = 0, r = 2*lb+2, lb < (d-3)/2
  simp only [isLeftCell, cellR, cellC, cellInnerHalf, Bool.and_eq_true,
    decide_eq_true_eq] at hleft
  obtain ⟨hc, hr, hlb⟩ := hleft
  -- `qv` is NOT inside: the four-condition conjunction fails.
  have hins : ¬ (1 ≤ qv / d ∧ qv / d < d-1 ∧ 1 ≤ qv % d ∧ qv % d < d-1) := by
    rintro ⟨h1, h2, h3, h4⟩
    have : isInside d qv = true := by
      simp only [isInside, cellRow, cellCol, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨h1, h2, h3, h4⟩
    rw [this] at hinF; exact absurd hinF (by decide)
  have hd5 : 5 ≤ d := by omega
  have hdm1 : 1 ≤ d - 1 := by omega
  have hlb' : (kv / (d-1) - 2) / 2 < (d - 3) / 2 := by
    have he : (d - 2 - 1) = d - 3 := by omega
    rw [he] at hlb; exact hlb
  have hrowbound : kv / (d-1) + 1 < d - 1 := by
    rw [hr]; omega
  have hrpos : 2 ≤ kv / (d-1) := by rw [hr]; omega
  have hbulk : kv < (d-1)*(d-1) := by
    have hrlt : kv / (d-1) < d - 1 := by omega
    have := (Nat.div_lt_iff_lt_mul (show 0 < d-1 by omega)).mp hrlt
    omega
  have hbulkD : decide (kv < (d-1)*(d-1)) = true := decide_eq_true hbulk
  -- left cell is the Z plaquette: (r + c) even (c = 0, r even)
  have hkindeven : (kv / (d-1) + kv % (d-1)) % 2 = 0 := by rw [hr, hc]; omega
  rw [surfaceCellPauli, if_pos hbulk, bulkKind, if_pos hkindeven, inBulkBand, leftOuterVal]
  simp only [cellRow, cellCol, cellR, cellC]
  -- align the RHS row literals with `kv/(d-1)` and `kv/(d-1)+1` via `hr`.
  have hr1 : 2 * ((kv / (d-1) - 2) / 2) + 2 = kv / (d-1) := by omega
  have hr2 : 2 * ((kv / (d-1) - 2) / 2) + 3 = kv / (d-1) + 1 := by omega
  rw [hr1, hr2]
  simp only [hc, hbulkD, Bool.and_true]
  by_cases hrband : qv / d = kv / (d-1) ∨ qv / d = kv / (d-1) + 1
  · have hqrow1 : 1 ≤ qv / d := by rcases hrband with h|h <;> omega
    have hqrowbd : qv / d < d - 1 := by rcases hrband with h|h <;> omega
    have hrowdec : (decide (qv / d = kv / (d - 1)) || decide (qv / d = kv / (d - 1) + 1)) = true := by
      rcases hrband with h|h <;> simp [h]
    by_cases hcol0 : qv % d = 0
    · -- col = 0 (left edge): both sides → Z (LHS via c=0, RHS via outer)
      have ec1 : decide (qv % d = 0) = true := by simp [hcol0]
      have ec2 : decide (qv % d = 0 + 1) = false := by simp; omega
      rw [hrowdec, ec1, ec2]; rfl
    · -- col ≠ 0; in-band col = 1 (= c+1) would force `inside`, contradicting hinF
      have hcol_not_1 : qv % d ≠ 0 + 1 := by
        intro h2
        exact hins ⟨hqrow1, hqrowbd, by omega, by omega⟩
      have ec1 : decide (qv % d = 0) = false := by simp [hcol0]
      have ec2 : decide (qv % d = 0 + 1) = false := by simp [hcol_not_1]
      rw [ec1, ec2]; simp
  · push_neg at hrband
    rcases hrband with ⟨hne1, hne2⟩
    have er1 : decide (qv / d = kv / (d - 1)) = false := by simp [hne1]
    have er2 : decide (qv / d = kv / (d - 1) + 1) = false := by simp [hne2]
    rw [er1, er2]; simp

theorem surfaceCellPauli_bottomCell_notInside {d kv qv : Nat}
    (hbottom : isBottomCell d kv = true) (hinF : isInside d qv = false) (hodd : d % 2 = 1) :
    surfaceCellPauli d kv qv = (if bottomOuterVal d kv qv then Pauli.X else Pauli.I) := by
  -- extract the bottomCell geometry: r = d-2, c = 2*bb+2, bb < (d-3)/2
  simp only [isBottomCell, cellR, cellC, cellLastCell, cellInnerHalf, Bool.and_eq_true,
    decide_eq_true_eq] at hbottom
  obtain ⟨hr, hc, hbb⟩ := hbottom
  -- `qv` is NOT inside: the four-condition conjunction fails.
  have hins : ¬ (1 ≤ qv / d ∧ qv / d < d-1 ∧ 1 ≤ qv % d ∧ qv % d < d-1) := by
    rintro ⟨h1, h2, h3, h4⟩
    have : isInside d qv = true := by
      simp only [isInside, cellRow, cellCol, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨h1, h2, h3, h4⟩
    rw [this] at hinF; exact absurd hinF (by decide)
  have hd5 : 5 ≤ d := by omega
  have hdm1 : 1 ≤ d - 1 := by omega
  have hbb' : (kv % (d-1) - 2) / 2 < (d - 3) / 2 := by
    have he : (d - 2 - 1) = d - 3 := by omega
    rw [he] at hbb; exact hbb
  have hcolbound : kv % (d-1) + 1 < d - 1 := by
    rw [hc]; omega
  have hcpos : 2 ≤ kv % (d-1) := by rw [hc]; omega
  -- r = d-2 < d-1, c < d-1, hence kv < bulkCount
  have hbulk : kv < (d-1)*(d-1) := by
    have hrlt : kv / (d-1) < d - 1 := by rw [hr]; omega
    have := (Nat.div_lt_iff_lt_mul (show 0 < d-1 by omega)).mp hrlt
    omega
  have hbulkD : decide (kv < (d-1)*(d-1)) = true := decide_eq_true hbulk
  -- bottom cell is the X plaquette: (r + c) odd (uses d odd: r = d-2 odd)
  have hkindodd : ¬ (kv / (d-1) + kv % (d-1)) % 2 = 0 := by rw [hr, hc]; omega
  rw [surfaceCellPauli, if_pos hbulk, bulkKind, if_neg hkindodd, inBulkBand, bottomOuterVal]
  simp only [cellRow, cellCol, cellR, cellC]
  -- align the RHS col literals with `kv%(d-1)` and `kv%(d-1)+1` via `hc`,
  -- and the LHS row literal `kv/(d-1)` with `d-2` via `hr`.
  have hc1 : 2 * ((kv % (d-1) - 2) / 2) + 2 = kv % (d-1) := by omega
  have hc2 : 2 * ((kv % (d-1) - 2) / 2) + 3 = kv % (d-1) + 1 := by omega
  rw [hc1, hc2]
  simp only [hr, hbulkD, Bool.and_true]
  by_cases hcband : qv % d = kv % (d-1) ∨ qv % d = kv % (d-1) + 1
  · have hqcol1 : 1 ≤ qv % d := by rcases hcband with h|h <;> omega
    have hqcolbd : qv % d < d - 1 := by rcases hcband with h|h <;> omega
    have hcoldec : (decide (qv % d = kv % (d - 1)) || decide (qv % d = kv % (d - 1) + 1)) = true := by
      rcases hcband with h|h <;> simp [h]
    by_cases hrow_dm1 : qv / d = d - 1
    · -- row = d-1 (bottom edge): both sides → X (LHS via r+1, RHS via outer)
      have er1 : decide (qv / d = d - 1 - 1) = false := by simp; omega
      have er2 : decide (qv / d = d - 1 - 1 + 1) = true := by simp; omega
      have er3 : decide (qv / d = d - 1) = true := by simp [hrow_dm1]
      rw [hcoldec, er1, er2, er3]; rfl
    · -- row ≠ d-1; in-band row = d-2 would force `inside`, contradicting hinF
      have hrow_not_dm2 : qv / d ≠ d - 1 - 1 := by
        intro h2
        exact hins ⟨by omega, by omega, hqcol1, hqcolbd⟩
      have er1 : decide (qv / d = d - 1 - 1) = false := by simp [hrow_not_dm2]
      have er2 : decide (qv / d = d - 1 - 1 + 1) = false := by simp; omega
      have er3 : decide (qv / d = d - 1) = false := by simp [hrow_dm1]
      rw [er1, er2, er3]; simp
  · push_neg at hcband
    rcases hcband with ⟨hne1, hne2⟩
    have ec1 : decide (qv % d = kv % (d - 1)) = false := by simp [hne1]
    have ec2 : decide (qv % d = kv % (d - 1) + 1) = false := by simp [hne2]
    rw [ec1, ec2]; simp

/-! ## Outer-guard generators for the promoted-outer leaves -/

def topOuterGuard_pure {dT kT qT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    SFormula.PureBoolTerm (topOuterGuard dT kT qT) := by
  have hdm1 := SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 1)
  have htb := SFormula.PureNatTerm.div
    (SFormula.PureNatTerm.sub (SFormula.PureNatTerm.mod hk hdm1) (SFormula.PureNatTerm.nat 1))
    (SFormula.PureNatTerm.nat 2)
  have hx := SFormula.PureNatTerm.add (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 2) htb)
    (SFormula.PureNatTerm.nat 1)
  exact SFormula.PureBoolTerm.and
    (SFormula.PureBoolTerm.eqNat (SFormula.PureNatTerm.div hq hd) (SFormula.PureNatTerm.nat 0))
    (SFormula.PureBoolTerm.or
      (SFormula.PureBoolTerm.eqNat (SFormula.PureNatTerm.mod hq hd) hx)
      (SFormula.PureBoolTerm.eqNat (SFormula.PureNatTerm.mod hq hd)
        (SFormula.PureNatTerm.add hx (SFormula.PureNatTerm.nat 1))))

theorem topOuterGuard_eval_gen {fuel d kv qv : Nat} {dT kT qT : Term 0 .nat} (rho : Env 0)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : Term.eval Surface.code.body fuel qT rho = some qv) :
    Term.eval Surface.code.body fuel (topOuterGuard dT kT qT) rho = some (topOuterVal d kv qv) := by
  simp only [topOuterGuard, orEqSucc, topBT, rowT, colT, cT, dm1T, Term.eval, hdv, hkv, hqv,
    Option.bind, Option.bind_eq_bind, topOuterVal, cellRow, cellCol, cellC]
  by_cases h1 : qv / d = 0 <;> simp [h1] <;> split <;> simp_all

def topOuterGuard_of {fuel d kv qv : Nat} {dT kT qT : Term 0 .nat} {b : Bool}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hdv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel qT rho = some qv)
    (hfact : topOuterVal d kv qv = b) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topOuterGuard dT kT qT)) (SC.b b)) :=
  cellGuard_of (topOuterGuard_pure hd hk hq)
    (by intro rho; rw [topOuterGuard_eval_gen rho (hdv rho) (hkv rho) (hqv rho), hfact])

/-- Purity of the right-cell outer guard. -/
def rightOuterGuard_pure {dT kT qT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    SFormula.PureBoolTerm (rightOuterGuard dT kT qT) := by
  have hdm1 := SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 1)
  have hrb := SFormula.PureNatTerm.div
    (SFormula.PureNatTerm.sub (SFormula.PureNatTerm.div hk hdm1) (SFormula.PureNatTerm.nat 1))
    (SFormula.PureNatTerm.nat 2)
  have hx := SFormula.PureNatTerm.add (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 2) hrb)
    (SFormula.PureNatTerm.nat 1)
  exact SFormula.PureBoolTerm.and
    (SFormula.PureBoolTerm.eqNat (SFormula.PureNatTerm.mod hq hd) hdm1)
    (SFormula.PureBoolTerm.or
      (SFormula.PureBoolTerm.eqNat (SFormula.PureNatTerm.div hq hd) hx)
      (SFormula.PureBoolTerm.eqNat (SFormula.PureNatTerm.div hq hd)
        (SFormula.PureNatTerm.add hx (SFormula.PureNatTerm.nat 1))))

theorem rightOuterGuard_eval_gen {fuel d kv qv : Nat} {dT kT qT : Term 0 .nat} (rho : Env 0)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : Term.eval Surface.code.body fuel qT rho = some qv) :
    Term.eval Surface.code.body fuel (rightOuterGuard dT kT qT) rho
      = some (rightOuterVal d kv qv) := by
  simp only [rightOuterGuard, orEqSucc, rightBT, rowT, colT, rT, dm1T, Term.eval, hdv, hkv, hqv,
    Option.bind, Option.bind_eq_bind, rightOuterVal, cellRow, cellCol, cellR]
  by_cases h1 : qv % d = d-1 <;> simp [h1] <;> split <;> simp_all

def rightOuterGuard_of {fuel d kv qv : Nat} {dT kT qT : Term 0 .nat} {b : Bool}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hdv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel qT rho = some qv)
    (hfact : rightOuterVal d kv qv = b) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (rightOuterGuard dT kT qT)) (SC.b b)) :=
  cellGuard_of (rightOuterGuard_pure hd hk hq)
    (by intro rho; rw [rightOuterGuard_eval_gen rho (hdv rho) (hkv rho) (hqv rho), hfact])

/-- Purity of the left-cell outer guard. -/
def leftOuterGuard_pure {dT kT qT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    SFormula.PureBoolTerm (leftOuterGuard dT kT qT) := by
  have hdm1 := SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 1)
  have hlb := SFormula.PureNatTerm.div
    (SFormula.PureNatTerm.sub (SFormula.PureNatTerm.div hk hdm1) (SFormula.PureNatTerm.nat 2))
    (SFormula.PureNatTerm.nat 2)
  have hx := SFormula.PureNatTerm.add (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 2) hlb)
    (SFormula.PureNatTerm.nat 2)
  exact SFormula.PureBoolTerm.and
    (SFormula.PureBoolTerm.eqNat (SFormula.PureNatTerm.mod hq hd) (SFormula.PureNatTerm.nat 0))
    (SFormula.PureBoolTerm.or
      (SFormula.PureBoolTerm.eqNat (SFormula.PureNatTerm.div hq hd) hx)
      (SFormula.PureBoolTerm.eqNat (SFormula.PureNatTerm.div hq hd)
        (SFormula.PureNatTerm.add hx (SFormula.PureNatTerm.nat 1))))

theorem leftOuterGuard_eval_gen {fuel d kv qv : Nat} {dT kT qT : Term 0 .nat} (rho : Env 0)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : Term.eval Surface.code.body fuel qT rho = some qv) :
    Term.eval Surface.code.body fuel (leftOuterGuard dT kT qT) rho
      = some (leftOuterVal d kv qv) := by
  simp only [leftOuterGuard, orEqSucc, leftBT, rowT, colT, rT, dm1T, Term.eval, hdv, hkv, hqv,
    Option.bind, Option.bind_eq_bind, leftOuterVal, cellRow, cellCol, cellR]
  by_cases h1 : qv % d = 0 <;> simp [h1] <;> split <;> simp_all

def leftOuterGuard_of {fuel d kv qv : Nat} {dT kT qT : Term 0 .nat} {b : Bool}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hdv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel qT rho = some qv)
    (hfact : leftOuterVal d kv qv = b) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (leftOuterGuard dT kT qT)) (SC.b b)) :=
  cellGuard_of (leftOuterGuard_pure hd hk hq)
    (by intro rho; rw [leftOuterGuard_eval_gen rho (hdv rho) (hkv rho) (hqv rho), hfact])

/-- Purity of the bottom-cell outer guard. -/
def bottomOuterGuard_pure {dT kT qT : Term 0 .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    SFormula.PureBoolTerm (bottomOuterGuard dT kT qT) := by
  have hdm1 := SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 1)
  have hbb := SFormula.PureNatTerm.div
    (SFormula.PureNatTerm.sub (SFormula.PureNatTerm.mod hk hdm1) (SFormula.PureNatTerm.nat 2))
    (SFormula.PureNatTerm.nat 2)
  have hx := SFormula.PureNatTerm.add (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 2) hbb)
    (SFormula.PureNatTerm.nat 2)
  exact SFormula.PureBoolTerm.and
    (SFormula.PureBoolTerm.eqNat (SFormula.PureNatTerm.div hq hd) hdm1)
    (SFormula.PureBoolTerm.or
      (SFormula.PureBoolTerm.eqNat (SFormula.PureNatTerm.mod hq hd) hx)
      (SFormula.PureBoolTerm.eqNat (SFormula.PureNatTerm.mod hq hd)
        (SFormula.PureNatTerm.add hx (SFormula.PureNatTerm.nat 1))))

theorem bottomOuterGuard_eval_gen {fuel d kv qv : Nat} {dT kT qT : Term 0 .nat} (rho : Env 0)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : Term.eval Surface.code.body fuel qT rho = some qv) :
    Term.eval Surface.code.body fuel (bottomOuterGuard dT kT qT) rho
      = some (bottomOuterVal d kv qv) := by
  simp only [bottomOuterGuard, orEqSucc, bottomBT, rowT, colT, cT, dm1T, Term.eval, hdv, hkv, hqv,
    Option.bind, Option.bind_eq_bind, bottomOuterVal, cellRow, cellCol, cellC]
  by_cases h1 : qv / d = d-1 <;> simp [h1] <;> split <;> simp_all

def bottomOuterGuard_of {fuel d kv qv : Nat} {dT kT qT : Term 0 .nat} {b : Bool}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hdv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel qT rho = some qv)
    (hfact : bottomOuterVal d kv qv = b) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bottomOuterGuard dT kT qT)) (SC.b b)) :=
  cellGuard_of (bottomOuterGuard_pure hd hk hq)
    (by intro rho; rw [bottomOuterGuard_eval_gen rho (hdv rho) (hkv rho) (hqv rho), hfact])

/-! ## Promoted-boundary outer-leaf peels (`inside` FALSE)

The complements of the keystone's `recTopPromotedInnerPeel` etc.: when the
`inside` guard fails, the entry is the closed `ite outer (kind) I` leaf.  Each
peel performs the same `bulk`/`interiorCell`/`*Cell` selections, then selects
`inside`=ELSE (`insideGuardT` FALSE), then dispatches the outer guard: a `Then`
variant landing on the cell's `kind` literal, and an `Else` variant landing on
`I`. -/

/-- Local copy of the keystone's (private) `promotedBulkSelect`: strip `stabLam`,
select the outer `bulk` (TRUE), exposing the residual `ite` tree. -/
private def promotedBulkSelect' {fuel : Nat} (dT kT qT : Term 0 .nat)
    (_hq : SFormula.PureNatTerm qT)
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

/-- Local copy of the keystone's (private) `interiorCellGuardT_simp`. -/
private theorem interiorCellGuardT_simp' (dT kT : Term 0 .nat) :
    interiorCellGuardT dT kT
      = ((Term.natLit 1).leNat (kT.div (dT.sub (Term.natLit 1)))).and
          (((kT.div (dT.sub (Term.natLit 1))).ltNat ((dT.sub (Term.natLit 1)).sub (Term.natLit 1))).and
            (((Term.natLit 1).leNat (kT.mod (dT.sub (Term.natLit 1)))).and
              ((kT.mod (dT.sub (Term.natLit 1))).ltNat ((dT.sub (Term.natLit 1)).sub (Term.natLit 1))))) := by
  simp only [interiorCellGuardT, band4, band3, le, rT, cT, lastCellT, dm1T]

/-- Local copy of the keystone's (private) `insideGuardT_simp`. -/
private theorem insideGuardT_simp' (dT qT : Term 0 .nat) :
    insideGuardT dT qT
      = ((Term.natLit 1).leNat (qT.div dT)).and
          (((qT.div dT).ltNat (dT.sub (Term.natLit 1))).and
            (((Term.natLit 1).leNat (qT.mod dT)).and
              ((qT.mod dT).ltNat (dT.sub (Term.natLit 1))))) := by
  simp only [insideGuardT, band4, band3, le, rowT, colT, dm1T]

/-- Local copy of the keystone's (private) `topCellGuard_simp`. -/
private theorem topCellGuard_simp' (dT kT : Term 0 .nat) :
    topCellGuard dT kT
      = (((kT.div (dT.sub (Term.natLit 1))).eqNat (Term.natLit 0)).and
          ((((kT.mod (dT.sub (Term.natLit 1))).eqNat
                (((Term.natLit 2).mul
                      (((kT.mod (dT.sub (Term.natLit 1))).sub (Term.natLit 1)).div (Term.natLit 2))).add
                  (Term.natLit 1)))).and
            ((((kT.mod (dT.sub (Term.natLit 1))).sub (Term.natLit 1)).div (Term.natLit 2)).ltNat
              (((dT.sub (Term.natLit 2)).sub (Term.natLit 1)).div (Term.natLit 2))))) := by
  simp only [topCellGuard, band3, topBT, rT, cT, recInnerHalfT, recInnerDm1T, recInnerDT, dm1T]

/-- Local copy of the keystone's (private) `rightCellGuard_simp`. -/
private theorem rightCellGuard_simp' (dT kT : Term 0 .nat) :
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

/-- Local copy of the keystone's (private) `leftCellGuard_simp`. -/
private theorem leftCellGuard_simp' (dT kT : Term 0 .nat) :
    leftCellGuard dT kT
      = (((kT.mod (dT.sub (Term.natLit 1))).eqNat (Term.natLit 0)).and
          ((((kT.div (dT.sub (Term.natLit 1))).eqNat
                (((Term.natLit 2).mul
                      (((kT.div (dT.sub (Term.natLit 1))).sub (Term.natLit 2)).div (Term.natLit 2))).add
                  (Term.natLit 2)))).and
            ((((kT.div (dT.sub (Term.natLit 1))).sub (Term.natLit 2)).div (Term.natLit 2)).ltNat
              (((dT.sub (Term.natLit 2)).sub (Term.natLit 1)).div (Term.natLit 2))))) := by
  simp only [leftCellGuard, band3, leftBT, rT, cT, recInnerHalfT, recInnerDm1T, recInnerDT, dm1T]

/-- Local copy of the keystone's (private) `bottomCellGuard_simp`. -/
private theorem bottomCellGuard_simp' (dT kT : Term 0 .nat) :
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

/-- Post-substitution form of the top-cell outer guard. -/
private theorem topOuterGuard_simp (dT kT qT : Term 0 .nat) :
    topOuterGuard dT kT qT
      = (((qT.div dT).eqNat (Term.natLit 0)).and
          ((((qT.mod dT).eqNat
                (((Term.natLit 2).mul
                      (((kT.mod (dT.sub (Term.natLit 1))).sub (Term.natLit 1)).div (Term.natLit 2))).add
                  (Term.natLit 1)))).or
            (((qT.mod dT).eqNat
                ((((Term.natLit 2).mul
                      (((kT.mod (dT.sub (Term.natLit 1))).sub (Term.natLit 1)).div (Term.natLit 2))).add
                  (Term.natLit 1)).add (Term.natLit 1)))))) := by
  simp only [topOuterGuard, orEqSucc, topBT, rowT, colT, cT, dm1T]

/-- Post-substitution form of the right-cell outer guard. -/
private theorem rightOuterGuard_simp (dT kT qT : Term 0 .nat) :
    rightOuterGuard dT kT qT
      = (((qT.mod dT).eqNat (dT.sub (Term.natLit 1))).and
          ((((qT.div dT).eqNat
                (((Term.natLit 2).mul
                      (((kT.div (dT.sub (Term.natLit 1))).sub (Term.natLit 1)).div (Term.natLit 2))).add
                  (Term.natLit 1)))).or
            (((qT.div dT).eqNat
                ((((Term.natLit 2).mul
                      (((kT.div (dT.sub (Term.natLit 1))).sub (Term.natLit 1)).div (Term.natLit 2))).add
                  (Term.natLit 1)).add (Term.natLit 1)))))) := by
  simp only [rightOuterGuard, orEqSucc, rightBT, rowT, colT, rT, dm1T]

/-- Post-substitution form of the left-cell outer guard. -/
private theorem leftOuterGuard_simp (dT kT qT : Term 0 .nat) :
    leftOuterGuard dT kT qT
      = (((qT.mod dT).eqNat (Term.natLit 0)).and
          ((((qT.div dT).eqNat
                (((Term.natLit 2).mul
                      (((kT.div (dT.sub (Term.natLit 1))).sub (Term.natLit 2)).div (Term.natLit 2))).add
                  (Term.natLit 2)))).or
            (((qT.div dT).eqNat
                ((((Term.natLit 2).mul
                      (((kT.div (dT.sub (Term.natLit 1))).sub (Term.natLit 2)).div (Term.natLit 2))).add
                  (Term.natLit 2)).add (Term.natLit 1)))))) := by
  simp only [leftOuterGuard, orEqSucc, leftBT, rowT, colT, rT, dm1T]

/-- Post-substitution form of the bottom-cell outer guard. -/
private theorem bottomOuterGuard_simp (dT kT qT : Term 0 .nat) :
    bottomOuterGuard dT kT qT
      = (((qT.div dT).eqNat (dT.sub (Term.natLit 1))).and
          ((((qT.mod dT).eqNat
                (((Term.natLit 2).mul
                      (((kT.mod (dT.sub (Term.natLit 1))).sub (Term.natLit 2)).div (Term.natLit 2))).add
                  (Term.natLit 2)))).or
            (((qT.mod dT).eqNat
                ((((Term.natLit 2).mul
                      (((kT.mod (dT.sub (Term.natLit 1))).sub (Term.natLit 2)).div (Term.natLit 2))).add
                  (Term.natLit 2)).add (Term.natLit 1)))))) := by
  simp only [bottomOuterGuard, orEqSucc, bottomBT, rowT, colT, cT, dm1T]

/-- **Top-cell promoted-boundary outer X peel** (`inside` FALSE, `outer` TRUE). -/
def recTopPromotedOuterXPeel {fuel : Nat} (dT kT qT : Term 0 .nat)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardT dT kT)) (SC.b true)))
    (hInterior : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (interiorCellGuardT dT kT)) (SC.b false)))
    (hTop : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topCellGuard dT kT)) (SC.b true)))
    (hInside : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (insideGuardT dT qT)) (SC.b false)))
    (hOuter : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topOuterGuard dT kT qT)) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt
          (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed qT))
        (SC.closed (.pauliLit Pauli.X))) := by
  simp only [SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
    SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q,
    codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4, orEqSucc, le]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (pureStabAtClosedIteLamThen (fuel := fuel) _ _ _ qT hq
      (promotedBulkSelect' dT kT qT hq hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← interiorCellGuardT_simp']; exact hInterior))
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← topCellGuard_simp']; exact hTop))
      (PureFamilyDerivA.eqPauliTrans _ _ _
        (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← insideGuardT_simp']; exact hInside))
        (PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← topOuterGuard_simp]; exact hOuter))
          (PureFamilyDerivA.eqPauliRefl _))))

/-- **Top-cell promoted-boundary outer I peel** (`inside` FALSE, `outer` FALSE). -/
def recTopPromotedOuterIPeel {fuel : Nat} (dT kT qT : Term 0 .nat)
    (hq : SFormula.PureNatTerm qT)
    (hBulk : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bulkGuardT dT kT)) (SC.b true)))
    (hInterior : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (interiorCellGuardT dT kT)) (SC.b false)))
    (hTop : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topCellGuard dT kT)) (SC.b true)))
    (hInside : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (insideGuardT dT qT)) (SC.b false)))
    (hOuter : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (topOuterGuard dT kT qT)) (SC.b false))) :
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
      (promotedBulkSelect' dT kT qT hq hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← interiorCellGuardT_simp']; exact hInterior))
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← topCellGuard_simp']; exact hTop))
      (PureFamilyDerivA.eqPauliTrans _ _ _
        (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← insideGuardT_simp']; exact hInside))
        (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← topOuterGuard_simp]; exact hOuter))))

/-- **Right-cell promoted-boundary outer Z peel** (`inside` FALSE, `outer` TRUE). -/
def recRightPromotedOuterZPeel {fuel : Nat} (dT kT qT : Term 0 .nat)
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
      (.eqBool (SC.closed (insideGuardT dT qT)) (SC.b false)))
    (hOuter : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (rightOuterGuard dT kT qT)) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt
          (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed qT))
        (SC.closed (.pauliLit Pauli.Z))) := by
  simp only [SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
    SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q,
    codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4, orEqSucc, le]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (pureStabAtClosedIteLamThen (fuel := fuel) _ _ _ qT hq
      (promotedBulkSelect' dT kT qT hq hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← interiorCellGuardT_simp']; exact hInterior))
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← topCellGuard_simp']; exact hTop))
      (PureFamilyDerivA.eqPauliTrans _ _ _
        (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← rightCellGuard_simp']; exact hRight))
        (PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← insideGuardT_simp']; exact hInside))
          (PureFamilyDerivA.eqPauliTrans _ _ _
            (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← rightOuterGuard_simp]; exact hOuter))
            (PureFamilyDerivA.eqPauliRefl _)))))

/-- **Right-cell promoted-boundary outer I peel** (`inside` FALSE, `outer` FALSE). -/
def recRightPromotedOuterIPeel {fuel : Nat} (dT kT qT : Term 0 .nat)
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
      (.eqBool (SC.closed (insideGuardT dT qT)) (SC.b false)))
    (hOuter : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (rightOuterGuard dT kT qT)) (SC.b false))) :
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
      (promotedBulkSelect' dT kT qT hq hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← interiorCellGuardT_simp']; exact hInterior))
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← topCellGuard_simp']; exact hTop))
      (PureFamilyDerivA.eqPauliTrans _ _ _
        (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← rightCellGuard_simp']; exact hRight))
        (PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← insideGuardT_simp']; exact hInside))
          (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← rightOuterGuard_simp]; exact hOuter)))))

/-- **Left-cell promoted-boundary outer Z peel** (`inside` FALSE, `outer` TRUE). -/
def recLeftPromotedOuterZPeel {fuel : Nat} (dT kT qT : Term 0 .nat)
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
      (.eqBool (SC.closed (insideGuardT dT qT)) (SC.b false)))
    (hOuter : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (leftOuterGuard dT kT qT)) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt
          (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed qT))
        (SC.closed (.pauliLit Pauli.Z))) := by
  simp only [SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
    SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q,
    codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4, orEqSucc, le]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (pureStabAtClosedIteLamThen (fuel := fuel) _ _ _ qT hq
      (promotedBulkSelect' dT kT qT hq hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← interiorCellGuardT_simp']; exact hInterior))
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← topCellGuard_simp']; exact hTop))
      (PureFamilyDerivA.eqPauliTrans _ _ _
        (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← rightCellGuard_simp']; exact hRight))
        (PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← leftCellGuard_simp']; exact hLeft))
          (PureFamilyDerivA.eqPauliTrans _ _ _
            (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← insideGuardT_simp']; exact hInside))
            (PureFamilyDerivA.eqPauliTrans _ _ _
              (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← leftOuterGuard_simp]; exact hOuter))
              (PureFamilyDerivA.eqPauliRefl _))))))

/-- **Left-cell promoted-boundary outer I peel** (`inside` FALSE, `outer` FALSE). -/
def recLeftPromotedOuterIPeel {fuel : Nat} (dT kT qT : Term 0 .nat)
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
      (.eqBool (SC.closed (insideGuardT dT qT)) (SC.b false)))
    (hOuter : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (leftOuterGuard dT kT qT)) (SC.b false))) :
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
      (promotedBulkSelect' dT kT qT hq hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← interiorCellGuardT_simp']; exact hInterior))
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← topCellGuard_simp']; exact hTop))
      (PureFamilyDerivA.eqPauliTrans _ _ _
        (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← rightCellGuard_simp']; exact hRight))
        (PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← leftCellGuard_simp']; exact hLeft))
          (PureFamilyDerivA.eqPauliTrans _ _ _
            (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← insideGuardT_simp']; exact hInside))
            (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← leftOuterGuard_simp]; exact hOuter))))))

/-- **Bottom-cell promoted-boundary outer X peel** (`inside` FALSE, `outer` TRUE). -/
def recBottomPromotedOuterXPeel {fuel : Nat} (dT kT qT : Term 0 .nat)
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
      (.eqBool (SC.closed (insideGuardT dT qT)) (SC.b false)))
    (hOuter : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bottomOuterGuard dT kT qT)) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt
          (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
          (SC.closed qT))
        (SC.closed (.pauliLit Pauli.X))) := by
  simp only [SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
    SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q,
    codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4, orEqSucc, le]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (pureStabAtClosedIteLamThen (fuel := fuel) _ _ _ qT hq
      (promotedBulkSelect' dT kT qT hq hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← interiorCellGuardT_simp']; exact hInterior))
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← topCellGuard_simp']; exact hTop))
      (PureFamilyDerivA.eqPauliTrans _ _ _
        (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← rightCellGuard_simp']; exact hRight))
        (PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← leftCellGuard_simp']; exact hLeft))
          (PureFamilyDerivA.eqPauliTrans _ _ _
            (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← bottomCellGuard_simp']; exact hBottom))
            (PureFamilyDerivA.eqPauliTrans _ _ _
              (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← insideGuardT_simp']; exact hInside))
              (PureFamilyDerivA.eqPauliTrans _ _ _
                (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← bottomOuterGuard_simp]; exact hOuter))
                (PureFamilyDerivA.eqPauliRefl _)))))))

/-- **Bottom-cell promoted-boundary outer I peel** (`inside` FALSE, `outer` FALSE). -/
def recBottomPromotedOuterIPeel {fuel : Nat} (dT kT qT : Term 0 .nat)
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
      (.eqBool (SC.closed (insideGuardT dT qT)) (SC.b false)))
    (hOuter : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (bottomOuterGuard dT kT qT)) (SC.b false))) :
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
      (promotedBulkSelect' dT kT qT hq hBulk)) ?_
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← interiorCellGuardT_simp']; exact hInterior))
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← topCellGuard_simp']; exact hTop))
      (PureFamilyDerivA.eqPauliTrans _ _ _
        (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← rightCellGuard_simp']; exact hRight))
        (PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← leftCellGuard_simp']; exact hLeft))
          (PureFamilyDerivA.eqPauliTrans _ _ _
            (PureFamilyDerivA.pauliIteSelectThen _ _ _ (by rw [← bottomCellGuard_simp']; exact hBottom))
            (PureFamilyDerivA.eqPauliTrans _ _ _
              (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← insideGuardT_simp']; exact hInside))
              (PureFamilyDerivA.pauliIteSelectElse _ _ _ (by rw [← bottomOuterGuard_simp]; exact hOuter)))))))

/-! ## Promoted-boundary outer-leaf ROW resolvers (`inside` FALSE)

For a recursive-entry promoted cell (`d ≥ 5`) whose `inside` guard fails, the
generated row `recCall dT kT @ qT` carries `surfaceCellPauli d kv qv`.  Each
resolver composes `surfaceCodeRecursiveEntryEq` (distance `dT < 5` FALSE) with the
matching promoted-outer peel, dispatching on the `Nat`-level outer predicate via
the cell's outer-leaf Nat identity. -/

/-- **Top-cell promoted outer-leaf row resolver.** -/
def recTopPromotedRowResolve {fuel d kv qv : Nat} (dT kT qT : Term 0 .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hDist : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat dT (n5 : Term 0 .nat))) (SC.b false)))
    (hdv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel qT rho = some qv)
    (hbulk : kv < (d-1)*(d-1)) (hintF : isInteriorCell d kv = false)
    (htop : isTopCell d kv = true) (hinF : isInside d qv = false) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.recCall dT kT)) (SC.closed qT))
        (SC.closed (.pauliLit (surfaceCellPauli d kv qv)))) := by
  rw [surfaceCellPauli_topCell_notInside htop hinF]
  have hb := bulkGuard_of hd hk hdv hkv (decide_eq_true hbulk)
  have hint := interiorCellGuardFalse_of hd hk hdv hkv hintF
  have htopg := topCellGuard_of hd hk hdv hkv htop
  have hins := insideGuardFalse_of hd hq hdv hqv hinF
  by_cases ho : topOuterVal d kv qv = true
  · rw [if_pos ho]
    exact surfaceCodeRecursiveEntryEq (SC.n (nQubits d)) dT kT qT _ hd hk hDist
      (recTopPromotedOuterXPeel dT kT qT hq hb hint htopg hins
        (topOuterGuard_of hd hk hq hdv hkv hqv ho))
  · have hoF : topOuterVal d kv qv = false := by simpa using ho
    rw [if_neg ho]
    exact surfaceCodeRecursiveEntryEq (SC.n (nQubits d)) dT kT qT _ hd hk hDist
      (recTopPromotedOuterIPeel dT kT qT hq hb hint htopg hins
        (topOuterGuard_of hd hk hq hdv hkv hqv hoF))

/-- **Right-cell promoted outer-leaf row resolver.** -/
def recRightPromotedRowResolve {fuel d kv qv : Nat} (dT kT qT : Term 0 .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hDist : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat dT (n5 : Term 0 .nat))) (SC.b false)))
    (hdv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel qT rho = some qv)
    (hbulk : kv < (d-1)*(d-1)) (hintF : isInteriorCell d kv = false)
    (htopF : isTopCell d kv = false) (hright : isRightCell d kv = true)
    (hinF : isInside d qv = false) (hodd : d % 2 = 1) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.recCall dT kT)) (SC.closed qT))
        (SC.closed (.pauliLit (surfaceCellPauli d kv qv)))) := by
  rw [surfaceCellPauli_rightCell_notInside hright hinF hodd]
  have hb := bulkGuard_of hd hk hdv hkv (decide_eq_true hbulk)
  have hint := interiorCellGuardFalse_of hd hk hdv hkv hintF
  have htopg := topCellGuard_of hd hk hdv hkv htopF
  have hrightg := rightCellGuard_of hd hk hdv hkv hright
  have hins := insideGuardFalse_of hd hq hdv hqv hinF
  by_cases ho : rightOuterVal d kv qv = true
  · rw [if_pos ho]
    exact surfaceCodeRecursiveEntryEq (SC.n (nQubits d)) dT kT qT _ hd hk hDist
      (recRightPromotedOuterZPeel dT kT qT hq hb hint htopg hrightg hins
        (rightOuterGuard_of hd hk hq hdv hkv hqv ho))
  · have hoF : rightOuterVal d kv qv = false := by simpa using ho
    rw [if_neg ho]
    exact surfaceCodeRecursiveEntryEq (SC.n (nQubits d)) dT kT qT _ hd hk hDist
      (recRightPromotedOuterIPeel dT kT qT hq hb hint htopg hrightg hins
        (rightOuterGuard_of hd hk hq hdv hkv hqv hoF))

/-- **Left-cell promoted outer-leaf row resolver.** -/
def recLeftPromotedRowResolve {fuel d kv qv : Nat} (dT kT qT : Term 0 .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hDist : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat dT (n5 : Term 0 .nat))) (SC.b false)))
    (hdv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel qT rho = some qv)
    (hbulk : kv < (d-1)*(d-1)) (hintF : isInteriorCell d kv = false)
    (htopF : isTopCell d kv = false) (hrightF : isRightCell d kv = false)
    (hleft : isLeftCell d kv = true) (hinF : isInside d qv = false) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.recCall dT kT)) (SC.closed qT))
        (SC.closed (.pauliLit (surfaceCellPauli d kv qv)))) := by
  rw [surfaceCellPauli_leftCell_notInside hleft hinF]
  have hb := bulkGuard_of hd hk hdv hkv (decide_eq_true hbulk)
  have hint := interiorCellGuardFalse_of hd hk hdv hkv hintF
  have htopg := topCellGuard_of hd hk hdv hkv htopF
  have hrightg := rightCellGuard_of hd hk hdv hkv hrightF
  have hleftg := leftCellGuard_of hd hk hdv hkv hleft
  have hins := insideGuardFalse_of hd hq hdv hqv hinF
  by_cases ho : leftOuterVal d kv qv = true
  · rw [if_pos ho]
    exact surfaceCodeRecursiveEntryEq (SC.n (nQubits d)) dT kT qT _ hd hk hDist
      (recLeftPromotedOuterZPeel dT kT qT hq hb hint htopg hrightg hleftg hins
        (leftOuterGuard_of hd hk hq hdv hkv hqv ho))
  · have hoF : leftOuterVal d kv qv = false := by simpa using ho
    rw [if_neg ho]
    exact surfaceCodeRecursiveEntryEq (SC.n (nQubits d)) dT kT qT _ hd hk hDist
      (recLeftPromotedOuterIPeel dT kT qT hq hb hint htopg hrightg hleftg hins
        (leftOuterGuard_of hd hk hq hdv hkv hqv hoF))

/-- **Bottom-cell promoted outer-leaf row resolver.** -/
def recBottomPromotedRowResolve {fuel d kv qv : Nat} (dT kT qT : Term 0 .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hDist : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat dT (n5 : Term 0 .nat))) (SC.b false)))
    (hdv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : ∀ (rho : Env 0), Term.eval Surface.code.body fuel qT rho = some qv)
    (hbulk : kv < (d-1)*(d-1)) (hintF : isInteriorCell d kv = false)
    (htopF : isTopCell d kv = false) (hrightF : isRightCell d kv = false)
    (hleftF : isLeftCell d kv = false) (hbottom : isBottomCell d kv = true)
    (hinF : isInside d qv = false) (hodd : d % 2 = 1) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.recCall dT kT)) (SC.closed qT))
        (SC.closed (.pauliLit (surfaceCellPauli d kv qv)))) := by
  rw [surfaceCellPauli_bottomCell_notInside hbottom hinF hodd]
  have hb := bulkGuard_of hd hk hdv hkv (decide_eq_true hbulk)
  have hint := interiorCellGuardFalse_of hd hk hdv hkv hintF
  have htopg := topCellGuard_of hd hk hdv hkv htopF
  have hrightg := rightCellGuard_of hd hk hdv hkv hrightF
  have hleftg := leftCellGuard_of hd hk hdv hkv hleftF
  have hbottomg := bottomCellGuard_of hd hk hdv hkv hbottom
  have hins := insideGuardFalse_of hd hq hdv hqv hinF
  by_cases ho : bottomOuterVal d kv qv = true
  · rw [if_pos ho]
    exact surfaceCodeRecursiveEntryEq (SC.n (nQubits d)) dT kT qT _ hd hk hDist
      (recBottomPromotedOuterXPeel dT kT qT hq hb hint htopg hrightg hleftg hbottomg hins
        (bottomOuterGuard_of hd hk hq hdv hkv hqv ho))
  · have hoF : bottomOuterVal d kv qv = false := by simpa using ho
    rw [if_neg ho]
    exact surfaceCodeRecursiveEntryEq (SC.n (nQubits d)) dT kT qT _ hd hk hDist
      (recBottomPromotedOuterIPeel dT kT qT hq hb hint htopg hrightg hleftg hbottomg hins
        (bottomOuterGuard_of hd hk hq hdv hkv hqv hoF))

/-! ## The unconditional forall-`k` row characterization (NO oracle)

`surfaceRowCharFull` is the keystone `surfaceRowChar` with every `oracle.resolve`
call replaced by a genuine resolver from this file: the base case by
`recBaseRowResolve`; the boundary index by `recBoundaryRowResolve`; the base
fallback by `recFallbackRowResolve`; and the four promoted not-inside leaves by the
promoted-outer row resolvers above.  It is structurally recursive on `m` (the
recursing cells feed the IH from the recursive call). -/

def surfaceRowCharFull {fuel : Nat} :
    (m : Nat) → (D : DistAt m) → (kT qT : Term 0 .nat) → (kv qv : Nat) →
    SFormula.PureNatTerm kT → SFormula.PureNatTerm qT →
    (∀ (rho : Env 0), Term.eval Surface.code.body fuel kT rho = some kv) →
    (∀ (rho : Env 0), Term.eval Surface.code.body fuel qT rho = some qv) →
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.recCall D.dT kT)) (SC.closed qT))
        (SC.closed (.pauliLit (recLeaf m kv qv))))
  | 0, D, kT, qT, kv, qv, hk, hq, hkv, hqv => by
      -- Base case d = 3: recLeaf 0 = surfaceCellPauli 3, resolved by recBaseRowResolve.
      have h := recBaseRowResolve (fuel := fuel) (d := oddDistance 0) D.dT kT qT D.pure hk hq
        (distLtFiveTrue_of_DistAt (fuel := fuel) D) (fun rho => D.evalsTo (fuel := fuel) rho) hkv hqv
      simpa only [recLeaf] using h
  | m + 1, D, kT, qT, kv, qv, hk, hq, hkv, hqv => by
      -- Recursive case d ≥ 5.  Dispatch on the Nat-level cell kind of (kv, qv).
      set d := oddDistance (m + 1) with hd_def
      have hodd : d % 2 = 1 := by rw [hd_def]; simp only [oddDistance]; omega
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
                (surfaceRowCharFull m D.pred (interiorKT D.dT kT) (innerQT D.dT qT)
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
                  (surfaceRowCharFull m D.pred (topKT D.dT kT) (innerQT D.dT qT)
                    (innerTopK d kv) (innerQval d qv)
                    (topKT_pure D.pure hk) (innerQT_pure D.pure hq)
                    (fun rho => topKT_evalsTo_gen rho (D.evalsTo rho) (hkv rho))
                    (fun rho => innerQT_evalsTo_gen rho (D.evalsTo rho) (hqv rho))))
            · -- top-cell not-inside leaf: recLeaf = surfaceCellPauli, promoted-outer resolves.
              have hinF : isInside d qv = false := by simpa using hin
              have hleaf : recLeaf (m + 1) kv qv = surfaceCellPauli d kv qv := by
                simp only [recLeaf, ← hd_def, if_pos hbulk, hintF, htop, hinF,
                  Bool.false_eq_true, if_false, if_true]
              rw [hleaf]
              exact recTopPromotedRowResolve D.dT kT qT D.pure hk hq
                (distLtFiveFalse_of_DistAt D) D.evalsTo hkv hqv hbulk hintF htop hinF
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
                    (surfaceRowCharFull m D.pred (rightKT D.dT kT) (innerQT D.dT qT)
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
                rw [hleaf]
                exact recRightPromotedRowResolve D.dT kT qT D.pure hk hq
                  (distLtFiveFalse_of_DistAt D) D.evalsTo hkv hqv hbulk hintF htopF hright hinF hodd
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
                      (surfaceRowCharFull m D.pred (leftKT D.dT kT) (innerQT D.dT qT)
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
                  rw [hleaf]
                  exact recLeftPromotedRowResolve D.dT kT qT D.pure hk hq
                    (distLtFiveFalse_of_DistAt D) D.evalsTo hkv hqv hbulk hintF htopF hrightF hleft hinF
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
                        (surfaceRowCharFull m D.pred (bottomKT D.dT kT) (innerQT D.dT qT)
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
                    rw [hleaf]
                    exact recBottomPromotedRowResolve D.dT kT qT D.pure hk hq
                      (distLtFiveFalse_of_DistAt D) D.evalsTo hkv hqv hbulk hintF htopF hrightF
                      hleftF hbottom hinF hodd
                · -- base fallback (no cell kind matched): resolved by recFallbackRowResolve.
                  have htopF : isTopCell d kv = false := by simpa using htop
                  have hrightF : isRightCell d kv = false := by simpa using hright
                  have hleftF : isLeftCell d kv = false := by simpa using hleft
                  have hbottomF : isBottomCell d kv = false := by simpa using hbottom
                  have hleaf : recLeaf (m + 1) kv qv = surfaceCellPauli d kv qv := by
                    simp only [recLeaf, ← hd_def, if_pos hbulk, hintF, htopF, hrightF, hleftF,
                      hbottomF, Bool.false_eq_true, if_false]
                  rw [hleaf]
                  exact recFallbackRowResolve D.dT kT qT D.pure hk hq
                    (distLtFiveFalse_of_DistAt D) D.evalsTo hkv hqv hbulk hintF htopF hrightF
                    hleftF hbottomF
      · -- boundary index (kv ≥ bulkCount): resolved by recBoundaryRowResolve.
        have hleaf : recLeaf (m + 1) kv qv = surfaceCellPauli d kv qv := by
          simp only [recLeaf, ← hd_def, if_neg hbulk]
        rw [hleaf]
        exact recBoundaryRowResolve D.dT kT qT D.pure hk hq
          (distLtFiveFalse_of_DistAt D) D.evalsTo hkv hqv hbulk

/-! ## Consumer-facing form over an `OddSurfaceDistance` (NO oracle) -/

def surfaceRowEntryCharFull {fuel : Nat} (D : OddSurfaceDistance) (kv qv : Nat) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed ((.recCall (.natLit D.distance) (.natLit kv)) : Term 0 .stab))
          (SC.closed ((.natLit qv) : Term 0 .nat)))
        (SC.closed ((.pauliLit (recLeaf D.index kv qv)) : Term 0 .pauli))) := by
  have h := surfaceRowCharFull (fuel := fuel) D.index (DistAt.lit D.index)
    (.natLit kv) (.natLit qv) kv qv
    (SFormula.PureNatTerm.nat _) (SFormula.PureNatTerm.nat _)
    (by intro rho; simp [Term.eval]) (by intro rho; simp [Term.eval])
  simpa only [DistAt.lit, OddSurfaceDistance.distance] using h

end QHL.CodeLang.Surface.Verify
