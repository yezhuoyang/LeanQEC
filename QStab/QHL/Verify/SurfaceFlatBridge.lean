import QStab.QHL.Verify.SurfaceRowCharacterizationSymbolic
import QStab.QHL.Verify.SurfaceRecLeafFlat

/-!
# Closed-form (flat) bridge: `rowSymTreeA m = baseLeafTreeTA` (at a concrete cell)

The resolved row-entry tree `rowSymTreeA m` is *recursive* (interior / promoted-
inside cells delegate to the inner code one layer down).  `baseLeafTreeTA` is the
*flat* base-entry classifier (bulk band/kind + four boundary bands) — exactly the
non-recursing `surfaceCellPauli` geometry.

`rowSymTreeFlatBridge` proves, as a pure object-logic `eqPauli` derivation, that at
a concrete stabilizer index `kv` / qubit `qv` (carried by pure terms `kT`/`qT` with
eval certificates) and a distance `dT` evaluating to `oddDistance m = 2m+3`, the
recursive tree EQUALS the flat classifier:
`rowSymTreeA m dT kT qT = baseLeafTreeTA dT kT qT`.

The self-similarity is FALSE for arbitrary `dT`; it holds only because `dT`
evaluates to `oddDistance m` — that is why the bridge is keyed to a `DistAtA`.

Mechanism: both trees reduce (as `PureFamilyDerivA` derivations) to a single Pauli
literal — `rowSymTreeA` to `recLeaf m kv qv`, `baseLeafTreeTA` to
`surfaceCellPauli (oddDistance m) kv qv` — by selecting the active `ite` branches
through the guard facts (`PureFamilyDerivA.pauliIteSelect{Then,Else}` fed by
`guardTrueEvalA`/`guardFalseEvalA`).  The two literals are equal by the Nat-level
global self-similarity `recLeaf_eq_surfaceCellPauli`.  `arithBoolFragment` rejects
`eqPauli`, so the discharge is via the `pauliIteSelect`/`pauliEqLit` ctors and the
Nat literal identity, NOT via `arithBool`.

No `native_decide` / `Formula.check` / `Formula.eval`-as-proof / `deriveTrue?` /
`admit` / new `axiom` / `@[implemented_by]` / `unsafe` / `checkedBoundFree`.
-/

namespace QHL.CodeLang.Surface.Verify

open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface

set_option maxRecDepth 65536

/-! ## Arity-general guard purity certificates

Each `*GuardTA` / `*CellGuardTA` / `*OuterGuardTA` / base-leaf class/band guard is a
pure boolean term in `dT`, `kT`, `qT`, so it carries a `PureBoolTerm` certificate
built structurally from the purity of `dT`/`kT`/`qT`. -/

private def dm1TA_pure {arity : Nat} {dT : Term arity .nat} (hd : SFormula.PureNatTerm dT) :
    SFormula.PureNatTerm (dm1TA dT) :=
  SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 1)

private def bulkCountTA_pure {arity : Nat} {dT : Term arity .nat} (hd : SFormula.PureNatTerm dT) :
    SFormula.PureNatTerm (bulkCountTA dT) :=
  SFormula.PureNatTerm.mul (dm1TA_pure hd) (dm1TA_pure hd)

private def rTA_pure {arity : Nat} {dT kT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureNatTerm (rTA dT kT) :=
  SFormula.PureNatTerm.div hk (dm1TA_pure hd)

private def cTA_pure {arity : Nat} {dT kT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureNatTerm (cTA dT kT) :=
  SFormula.PureNatTerm.mod hk (dm1TA_pure hd)

private def lastCellTA_pure {arity : Nat} {dT : Term arity .nat} (hd : SFormula.PureNatTerm dT) :
    SFormula.PureNatTerm (lastCellTA dT) :=
  SFormula.PureNatTerm.sub (dm1TA_pure hd) (SFormula.PureNatTerm.nat 1)

private def rowTA_pure {arity : Nat} {dT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hq : SFormula.PureNatTerm qT) :
    SFormula.PureNatTerm (rowTA dT qT) :=
  SFormula.PureNatTerm.div hq hd

private def colTA_pure {arity : Nat} {dT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hq : SFormula.PureNatTerm qT) :
    SFormula.PureNatTerm (colTA dT qT) :=
  SFormula.PureNatTerm.mod hq hd

private def baseBTA_pure {arity : Nat} {dT kT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureNatTerm (baseBTA dT kT) :=
  SFormula.PureNatTerm.sub hk (bulkCountTA_pure hd)

private def baseHalfTA_pure {arity : Nat} {dT : Term arity .nat} (hd : SFormula.PureNatTerm dT) :
    SFormula.PureNatTerm (baseHalfTA dT) :=
  SFormula.PureNatTerm.div (dm1TA_pure hd) (SFormula.PureNatTerm.nat 2)

private def recInnerDm1TA_pure {arity : Nat} {dT : Term arity .nat} (hd : SFormula.PureNatTerm dT) :
    SFormula.PureNatTerm (recInnerDm1TA dT) :=
  SFormula.PureNatTerm.sub (SFormula.PureNatTerm.sub hd (SFormula.PureNatTerm.nat 2))
    (SFormula.PureNatTerm.nat 1)

private def recInnerHalfTA_pure' {arity : Nat} {dT : Term arity .nat} (hd : SFormula.PureNatTerm dT) :
    SFormula.PureNatTerm (recInnerHalfTA dT) :=
  SFormula.PureNatTerm.div (recInnerDm1TA_pure hd) (SFormula.PureNatTerm.nat 2)

private def topBTA_pure {arity : Nat} {dT kT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureNatTerm (topBTA dT kT) :=
  SFormula.PureNatTerm.div (SFormula.PureNatTerm.sub (cTA_pure hd hk) (SFormula.PureNatTerm.nat 1))
    (SFormula.PureNatTerm.nat 2)

private def rightBTA_pure {arity : Nat} {dT kT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureNatTerm (rightBTA dT kT) :=
  SFormula.PureNatTerm.div (SFormula.PureNatTerm.sub (rTA_pure hd hk) (SFormula.PureNatTerm.nat 1))
    (SFormula.PureNatTerm.nat 2)

private def leftBTA_pure {arity : Nat} {dT kT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureNatTerm (leftBTA dT kT) :=
  SFormula.PureNatTerm.div (SFormula.PureNatTerm.sub (rTA_pure hd hk) (SFormula.PureNatTerm.nat 2))
    (SFormula.PureNatTerm.nat 2)

private def bottomBTA_pure {arity : Nat} {dT kT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureNatTerm (bottomBTA dT kT) :=
  SFormula.PureNatTerm.div (SFormula.PureNatTerm.sub (cTA_pure hd hk) (SFormula.PureNatTerm.nat 2))
    (SFormula.PureNatTerm.nat 2)

/-- `band3` / `band4` / `orEqSucc` / `orEqPair` / `le` purity helpers. -/
private def band3_pure {arity : Nat} {a b c : Term arity .bool}
    (ha : SFormula.PureBoolTerm a) (hb : SFormula.PureBoolTerm b) (hc : SFormula.PureBoolTerm c) :
    SFormula.PureBoolTerm (band3 a b c) :=
  SFormula.PureBoolTerm.and ha (SFormula.PureBoolTerm.and hb hc)

private def band4_pure {arity : Nat} {a b c d : Term arity .bool}
    (ha : SFormula.PureBoolTerm a) (hb : SFormula.PureBoolTerm b) (hc : SFormula.PureBoolTerm c)
    (hdd : SFormula.PureBoolTerm d) : SFormula.PureBoolTerm (band4 a b c d) :=
  SFormula.PureBoolTerm.and ha (band3_pure hb hc hdd)

private def orEqSucc_pure {arity : Nat} {x base : Term arity .nat}
    (hx : SFormula.PureNatTerm x) (hb : SFormula.PureNatTerm base) :
    SFormula.PureBoolTerm (orEqSucc x base) :=
  SFormula.PureBoolTerm.or (SFormula.PureBoolTerm.eqNat hx hb)
    (SFormula.PureBoolTerm.eqNat hx (SFormula.PureNatTerm.add hb (SFormula.PureNatTerm.nat 1)))

private def orEqPair_pure {arity : Nat} {x a b : Term arity .nat}
    (hx : SFormula.PureNatTerm x) (ha : SFormula.PureNatTerm a) (hb : SFormula.PureNatTerm b) :
    SFormula.PureBoolTerm (orEqPair x a b) :=
  SFormula.PureBoolTerm.or (SFormula.PureBoolTerm.eqNat hx ha) (SFormula.PureBoolTerm.eqNat hx hb)

private def le_pure {arity : Nat} {a b : Term arity .nat}
    (ha : SFormula.PureNatTerm a) (hb : SFormula.PureNatTerm b) :
    SFormula.PureBoolTerm (le a b) :=
  SFormula.PureBoolTerm.leNat ha hb

private def bulkGuardTA_pure {arity : Nat} {dT kT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureBoolTerm (bulkGuardTA dT kT) :=
  SFormula.PureBoolTerm.ltNat hk (bulkCountTA_pure hd)

private def interiorCellGuardTA_pure {arity : Nat} {dT kT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureBoolTerm (interiorCellGuardTA dT kT) :=
  band4_pure (le_pure (SFormula.PureNatTerm.nat 1) (rTA_pure hd hk))
    (SFormula.PureBoolTerm.ltNat (rTA_pure hd hk) (lastCellTA_pure hd))
    (le_pure (SFormula.PureNatTerm.nat 1) (cTA_pure hd hk))
    (SFormula.PureBoolTerm.ltNat (cTA_pure hd hk) (lastCellTA_pure hd))

private def insideGuardTA_pure {arity : Nat} {dT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hq : SFormula.PureNatTerm qT) :
    SFormula.PureBoolTerm (insideGuardTA dT qT) :=
  band4_pure (le_pure (SFormula.PureNatTerm.nat 1) (rowTA_pure hd hq))
    (SFormula.PureBoolTerm.ltNat (rowTA_pure hd hq) (dm1TA_pure hd))
    (le_pure (SFormula.PureNatTerm.nat 1) (colTA_pure hd hq))
    (SFormula.PureBoolTerm.ltNat (colTA_pure hd hq) (dm1TA_pure hd))

private def topCellGuardTA_pure {arity : Nat} {dT kT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureBoolTerm (topCellGuardTA dT kT) :=
  band3_pure (SFormula.PureBoolTerm.eqNat (rTA_pure hd hk) (SFormula.PureNatTerm.nat 0))
    (SFormula.PureBoolTerm.eqNat (cTA_pure hd hk)
      (SFormula.PureNatTerm.add (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 2) (topBTA_pure hd hk))
        (SFormula.PureNatTerm.nat 1)))
    (SFormula.PureBoolTerm.ltNat (topBTA_pure hd hk) (recInnerHalfTA_pure' hd))

private def rightCellGuardTA_pure {arity : Nat} {dT kT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureBoolTerm (rightCellGuardTA dT kT) :=
  band3_pure (SFormula.PureBoolTerm.eqNat (cTA_pure hd hk) (lastCellTA_pure hd))
    (SFormula.PureBoolTerm.eqNat (rTA_pure hd hk)
      (SFormula.PureNatTerm.add (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 2) (rightBTA_pure hd hk))
        (SFormula.PureNatTerm.nat 1)))
    (SFormula.PureBoolTerm.ltNat (rightBTA_pure hd hk) (recInnerHalfTA_pure' hd))

private def leftCellGuardTA_pure {arity : Nat} {dT kT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureBoolTerm (leftCellGuardTA dT kT) :=
  band3_pure (SFormula.PureBoolTerm.eqNat (cTA_pure hd hk) (SFormula.PureNatTerm.nat 0))
    (SFormula.PureBoolTerm.eqNat (rTA_pure hd hk)
      (SFormula.PureNatTerm.add (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 2) (leftBTA_pure hd hk))
        (SFormula.PureNatTerm.nat 2)))
    (SFormula.PureBoolTerm.ltNat (leftBTA_pure hd hk) (recInnerHalfTA_pure' hd))

private def bottomCellGuardTA_pure {arity : Nat} {dT kT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureBoolTerm (bottomCellGuardTA dT kT) :=
  band3_pure (SFormula.PureBoolTerm.eqNat (rTA_pure hd hk) (lastCellTA_pure hd))
    (SFormula.PureBoolTerm.eqNat (cTA_pure hd hk)
      (SFormula.PureNatTerm.add (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 2) (bottomBTA_pure hd hk))
        (SFormula.PureNatTerm.nat 2)))
    (SFormula.PureBoolTerm.ltNat (bottomBTA_pure hd hk) (recInnerHalfTA_pure' hd))

private def topOuterGuardTA_pure {arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    SFormula.PureBoolTerm (topOuterGuardTA dT kT qT) :=
  SFormula.PureBoolTerm.and (SFormula.PureBoolTerm.eqNat (rowTA_pure hd hq) (SFormula.PureNatTerm.nat 0))
    (orEqSucc_pure (colTA_pure hd hq)
      (SFormula.PureNatTerm.add (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 2)
        (SFormula.PureNatTerm.div (SFormula.PureNatTerm.sub (cTA_pure hd hk) (SFormula.PureNatTerm.nat 1))
          (SFormula.PureNatTerm.nat 2))) (SFormula.PureNatTerm.nat 1)))

private def rightOuterGuardTA_pure {arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    SFormula.PureBoolTerm (rightOuterGuardTA dT kT qT) :=
  SFormula.PureBoolTerm.and (SFormula.PureBoolTerm.eqNat (colTA_pure hd hq) (dm1TA_pure hd))
    (orEqSucc_pure (rowTA_pure hd hq)
      (SFormula.PureNatTerm.add (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 2)
        (SFormula.PureNatTerm.div (SFormula.PureNatTerm.sub (rTA_pure hd hk) (SFormula.PureNatTerm.nat 1))
          (SFormula.PureNatTerm.nat 2))) (SFormula.PureNatTerm.nat 1)))

private def leftOuterGuardTA_pure {arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    SFormula.PureBoolTerm (leftOuterGuardTA dT kT qT) :=
  SFormula.PureBoolTerm.and (SFormula.PureBoolTerm.eqNat (colTA_pure hd hq) (SFormula.PureNatTerm.nat 0))
    (orEqSucc_pure (rowTA_pure hd hq)
      (SFormula.PureNatTerm.add (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 2)
        (SFormula.PureNatTerm.div (SFormula.PureNatTerm.sub (rTA_pure hd hk) (SFormula.PureNatTerm.nat 2))
          (SFormula.PureNatTerm.nat 2))) (SFormula.PureNatTerm.nat 2)))

private def bottomOuterGuardTA_pure {arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    SFormula.PureBoolTerm (bottomOuterGuardTA dT kT qT) :=
  SFormula.PureBoolTerm.and (SFormula.PureBoolTerm.eqNat (rowTA_pure hd hq) (dm1TA_pure hd))
    (orEqSucc_pure (colTA_pure hd hq)
      (SFormula.PureNatTerm.add (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 2)
        (SFormula.PureNatTerm.div (SFormula.PureNatTerm.sub (cTA_pure hd hk) (SFormula.PureNatTerm.nat 2))
          (SFormula.PureNatTerm.nat 2))) (SFormula.PureNatTerm.nat 2)))

private def baseBulkBandGuardTA_pure {arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    SFormula.PureBoolTerm (baseBulkBandGuardTA dT kT qT) :=
  band3_pure (orEqSucc_pure (SFormula.PureNatTerm.div hq hd) (rTA_pure hd hk))
    (orEqSucc_pure (SFormula.PureNatTerm.mod hq hd) (cTA_pure hd hk))
    (SFormula.PureBoolTerm.ltNat hk (bulkCountTA_pure hd))

private def baseKindGuardTA_pure {arity : Nat} {dT kT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureBoolTerm (baseKindGuardTA dT kT) :=
  SFormula.PureBoolTerm.eqNat
    (SFormula.PureNatTerm.mod (SFormula.PureNatTerm.add (rTA_pure hd hk) (cTA_pure hd hk))
      (SFormula.PureNatTerm.nat 2)) (SFormula.PureNatTerm.nat 0)

private def topClassGuardTA_pure {arity : Nat} {dT kT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureBoolTerm (topClassGuardTA dT kT) :=
  SFormula.PureBoolTerm.ltNat (baseBTA_pure hd hk) (baseHalfTA_pure hd)

private def rightClassGuardTA_pure {arity : Nat} {dT kT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureBoolTerm (rightClassGuardTA dT kT) :=
  SFormula.PureBoolTerm.ltNat (baseBTA_pure hd hk)
    (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 2) (baseHalfTA_pure hd))

private def leftClassGuardTA_pure {arity : Nat} {dT kT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureBoolTerm (leftClassGuardTA dT kT) :=
  SFormula.PureBoolTerm.ltNat (baseBTA_pure hd hk)
    (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 3) (baseHalfTA_pure hd))

private def topBandGuardTA_pure {arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    SFormula.PureBoolTerm (topBandGuardTA dT kT qT) :=
  band3_pure
    (SFormula.PureBoolTerm.ltNat hk
      (SFormula.PureNatTerm.sub (SFormula.PureNatTerm.mul hd hd) (SFormula.PureNatTerm.nat 1)))
    (SFormula.PureBoolTerm.eqNat (SFormula.PureNatTerm.div hq hd) (SFormula.PureNatTerm.nat 0))
    (orEqSucc_pure (SFormula.PureNatTerm.mod hq hd)
      (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 2) (baseBTA_pure hd hk)))

private def rightBandGuardTA_pure {arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    SFormula.PureBoolTerm (rightBandGuardTA dT kT qT) :=
  SFormula.PureBoolTerm.and (SFormula.PureBoolTerm.eqNat (SFormula.PureNatTerm.mod hq hd) (dm1TA_pure hd))
    (orEqSucc_pure (SFormula.PureNatTerm.div hq hd)
      (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 2)
        (SFormula.PureNatTerm.sub (baseBTA_pure hd hk) (baseHalfTA_pure hd))))

private def leftBandGuardTA_pure {arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    SFormula.PureBoolTerm (leftBandGuardTA dT kT qT) :=
  SFormula.PureBoolTerm.and (SFormula.PureBoolTerm.eqNat (SFormula.PureNatTerm.mod hq hd) (SFormula.PureNatTerm.nat 0))
    (orEqPair_pure (SFormula.PureNatTerm.div hq hd)
      (SFormula.PureNatTerm.add (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 2)
        (SFormula.PureNatTerm.sub (baseBTA_pure hd hk)
          (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 2) (baseHalfTA_pure hd)))) (SFormula.PureNatTerm.nat 1))
      (SFormula.PureNatTerm.add (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 2)
        (SFormula.PureNatTerm.sub (baseBTA_pure hd hk)
          (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 2) (baseHalfTA_pure hd)))) (SFormula.PureNatTerm.nat 2)))

private def bottomBandGuardTA_pure {arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    SFormula.PureBoolTerm (bottomBandGuardTA dT kT qT) :=
  SFormula.PureBoolTerm.and (SFormula.PureBoolTerm.eqNat (SFormula.PureNatTerm.div hq hd) (dm1TA_pure hd))
    (orEqPair_pure (SFormula.PureNatTerm.mod hq hd)
      (SFormula.PureNatTerm.add (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 2)
        (SFormula.PureNatTerm.sub (baseBTA_pure hd hk)
          (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 3) (baseHalfTA_pure hd)))) (SFormula.PureNatTerm.nat 1))
      (SFormula.PureNatTerm.add (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 2)
        (SFormula.PureNatTerm.sub (baseBTA_pure hd hk)
          (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.nat 3) (baseHalfTA_pure hd)))) (SFormula.PureNatTerm.nat 2)))

/-! ## Arity-general guard-fact generator

`cellGuardA_of` discharges any closed pure-bool guard `g` from an `Env`-uniform
`Term.eval` certificate `g → b₀`, producing the `PureFamilyDerivA` fact
`eqBool (closed g) (b b₀)`.  Composed with the per-guard `Term.eval`-evaluation
lemmas below it gives each cell / band / class / outer guard fact at a concrete
`(kv, qv)`. -/

/-- `eqBool (closed cond) (b v)` lies in the arithmetic-boolean fragment whenever
`cond` is a pure boolean term, arity-general. -/
private theorem pureBool_eqBool_in_fragment_local {arity : Nat} {cond : Term arity .bool}
    (v : Bool) (hc : SFormula.PureBoolTerm cond) :
    arithBoolFragment (.eqBool (SC.closed cond) (SC.b v)) = true := by
  simp [arithBoolFragment, ArithBoolFragment.formula, ArithBoolFragment.sterm,
    SC.closed, SC.b, ArithBoolFragment.term, pureTerm_in_fragment hc]

def cellGuardA_of {fuel arity : Nat} {b : Bool} {g : Term arity .bool}
    (gpure : SFormula.PureBoolTerm g)
    (geval : ∀ (rho : Env arity), Term.eval Surface.code.body fuel g rho = some b) :
    PureFamilyDerivA Surface.code.body fuel (.eqBool (SC.closed g) (SC.b b)) :=
  PureFamilyDerivA.arithBool _ (pureBool_eqBool_in_fragment_local b gpure) (by
    intro rho E
    simp [SFormula.eval, STerm.eval, Term.eval, SC.closed, SC.b, geval rho])

/-- `imp P (eqBool (closed g) (b v))` lies in the arithmetic-boolean fragment when
`P` is in the fragment and `g` is a pure boolean term. -/
private theorem imp_eqBool_in_fragment {arity : Nat} {P : SFormula arity}
    {g : Term arity .bool} (v : Bool)
    (hP : arithBoolFragment P = true) (hg : SFormula.PureBoolTerm g) :
    arithBoolFragment (.imp P (.eqBool (SC.closed g) (SC.b v))) = true := by
  simp only [arithBoolFragment, ArithBoolFragment.formula] at hP ⊢
  simp [hP, ArithBoolFragment.sterm, SC.closed, SC.b, ArithBoolFragment.term,
    pureTerm_in_fragment hg]

/-- Build an `arithBool` *implication* fact `imp P (eqBool (closed g) (b v))` from
an `Env`-uniform validity certificate.  This is the implication analogue of
`cellGuardA_of`: it discharges a guard *correspondence* (the inner classifier guard
takes value `v` whenever the outer-guard premise `P` holds), folded into the cut
premise and consumed by the leaf via `mp`. -/
def impGuardA_of {fuel arity : Nat} {v : Bool} {P : SFormula arity} {g : Term arity .bool}
    (hP : arithBoolFragment P = true) (gpure : SFormula.PureBoolTerm g)
    (hPtot : ∀ (rho : Env arity) (E : PartialStabilizer),
      (P.eval Surface.code.body fuel rho E).isSome = true)
    (hvalid : ∀ (rho : Env arity) (E : PartialStabilizer),
      P.eval Surface.code.body fuel rho E = some true →
        Term.eval Surface.code.body fuel g rho = some v) :
    PureFamilyDerivA Surface.code.body fuel
      (.imp P (.eqBool (SC.closed g) (SC.b v))) :=
  PureFamilyDerivA.arithBool _ (imp_eqBool_in_fragment v hP gpure) (by
    intro rho E
    cases hPe : P.eval Surface.code.body fuel rho E with
    | none =>
        have := hPtot rho E; rw [hPe] at this; simp at this
    | some pv =>
        cases pv with
        | false =>
            rw [SFormula.eval, hPe]; rfl
        | true =>
            rw [SFormula.eval, hPe]
            simp [bind, Option.bind, SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval,
              hvalid rho E hPe])

/-! ### `Term.eval` of the recursive-cell guards → the matching `Nat` selector.

The `*GuardTA` terms are byte-for-byte the arity-general restatements of the
keystone `*Guard` terms, so their evaluation lemmas reuse the identical `simp only`
normalization (cf. `interiorCellGuardT_eval_gen`, `topCellGuard_eval_gen`, …). -/

private theorem band3_ite_formA (a b c : Bool) :
    (if a = true then (if b = true then some c else some false) else some false)
      = some (a && (b && c)) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem bulkGuardTA_eval {fuel arity d kv : Nat} {dT kT : Term arity .nat} (rho : Env arity)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv) :
    Term.eval Surface.code.body fuel (bulkGuardTA dT kT) rho
      = some (decide (kv < (d - 1) * (d - 1))) := by
  simp only [bulkGuardTA, bulkCountTA, dm1TA, Term.eval, hdv, hkv,
    Option.bind, Option.bind_eq_bind]

theorem interiorCellGuardTA_eval {fuel arity d kv : Nat} {dT kT : Term arity .nat} (rho : Env arity)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv) :
    Term.eval Surface.code.body fuel (interiorCellGuardTA dT kT) rho
      = some (isInteriorCell d kv) := by
  simp only [interiorCellGuardTA, band4, band3, le, rTA, cTA, lastCellTA, dm1TA, Term.eval,
    hdv, hkv, Option.bind, Option.bind_eq_bind,
    isInteriorCell, cellR, cellC, cellLastCell]
  rcases Bool.eq_false_or_eq_true (decide (1 ≤ kv / (d-1))) with h|h <;>
    rcases Bool.eq_false_or_eq_true (decide (kv / (d-1) < d-1-1)) with h2|h2 <;>
    rcases Bool.eq_false_or_eq_true (decide (1 ≤ kv % (d-1))) with h3|h3 <;>
    simp [h, h2, h3]

theorem insideGuardTA_eval {fuel arity d qv : Nat} {dT qT : Term arity .nat} (rho : Env arity)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hqv : Term.eval Surface.code.body fuel qT rho = some qv) :
    Term.eval Surface.code.body fuel (insideGuardTA dT qT) rho
      = some (isInside d qv) := by
  simp only [insideGuardTA, band4, band3, le, rowTA, colTA, dm1TA, Term.eval,
    hdv, hqv, Option.bind, Option.bind_eq_bind,
    isInside, cellRow, cellCol]
  rcases Bool.eq_false_or_eq_true (decide (1 ≤ qv / d)) with h|h <;>
    rcases Bool.eq_false_or_eq_true (decide (qv / d < d-1)) with h2|h2 <;>
    rcases Bool.eq_false_or_eq_true (decide (1 ≤ qv % d)) with h3|h3 <;>
    simp [h, h2, h3]

theorem topCellGuardTA_eval {fuel arity d kv : Nat} {dT kT : Term arity .nat} (rho : Env arity)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv) :
    Term.eval Surface.code.body fuel (topCellGuardTA dT kT) rho = some (isTopCell d kv) := by
  simp only [topCellGuardTA, band3, topBTA, rTA, cTA, recInnerHalfTA, recInnerDm1TA, innerDm1TA,
    innerDTA, dm1TA, Term.eval, hdv, hkv, Option.bind, Option.bind_eq_bind,
    isTopCell, cellR, cellC, cellInnerHalf]
  exact band3_ite_formA _ _ _

theorem rightCellGuardTA_eval {fuel arity d kv : Nat} {dT kT : Term arity .nat} (rho : Env arity)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv) :
    Term.eval Surface.code.body fuel (rightCellGuardTA dT kT) rho = some (isRightCell d kv) := by
  simp only [rightCellGuardTA, band3, rightBTA, rTA, cTA, lastCellTA, recInnerHalfTA, recInnerDm1TA,
    innerDm1TA, innerDTA, dm1TA, Term.eval, hdv, hkv, Option.bind, Option.bind_eq_bind,
    isRightCell, cellR, cellC, cellLastCell, cellInnerHalf]
  exact band3_ite_formA _ _ _

theorem leftCellGuardTA_eval {fuel arity d kv : Nat} {dT kT : Term arity .nat} (rho : Env arity)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv) :
    Term.eval Surface.code.body fuel (leftCellGuardTA dT kT) rho = some (isLeftCell d kv) := by
  simp only [leftCellGuardTA, band3, leftBTA, rTA, cTA, recInnerHalfTA, recInnerDm1TA, innerDm1TA,
    innerDTA, dm1TA, Term.eval, hdv, hkv, Option.bind, Option.bind_eq_bind,
    isLeftCell, cellR, cellC, cellInnerHalf]
  exact band3_ite_formA _ _ _

theorem bottomCellGuardTA_eval {fuel arity d kv : Nat} {dT kT : Term arity .nat} (rho : Env arity)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv) :
    Term.eval Surface.code.body fuel (bottomCellGuardTA dT kT) rho = some (isBottomCell d kv) := by
  simp only [bottomCellGuardTA, band3, bottomBTA, rTA, cTA, lastCellTA, recInnerHalfTA, recInnerDm1TA,
    innerDm1TA, innerDTA, dm1TA, Term.eval, hdv, hkv, Option.bind, Option.bind_eq_bind,
    isBottomCell, cellR, cellC, cellLastCell, cellInnerHalf]
  exact band3_ite_formA _ _ _

/-! ### `Term.eval` of the base-entry (flat classifier) guards.

These map each `baseLeafTreeTA` guard to the matching `surfaceCellPauli` branch
condition (as a decidable `Bool`).  `baseBulkBandGuardTA → inBulkBand`,
`baseKindGuardTA → (bulkKind = Z)`, and the class / band guards to the boundary
strip conditions. -/

theorem baseBulkBandGuardTA_eval {fuel arity d kv qv : Nat} {dT kT qT : Term arity .nat}
    (rho : Env arity)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : Term.eval Surface.code.body fuel qT rho = some qv) :
    Term.eval Surface.code.body fuel (baseBulkBandGuardTA dT kT qT) rho
      = some (baseBulkBandVal d kv qv) := by
  simp only [baseBulkBandGuardTA, band3, orEqSucc, bulkCountTA, dm1TA, Term.eval, hdv, hkv, hqv,
    Option.bind, Option.bind_eq_bind, baseBulkBandVal, cellRow, cellCol, cellR, cellC]
  by_cases h1 : qv / d = kv / (d-1) <;> by_cases h2 : qv % d = kv % (d-1) <;>
    simp [h1, h2] <;> (try split) <;> simp_all <;> (try split) <;> simp_all

theorem baseKindGuardTA_eval {fuel arity d kv : Nat} {dT kT : Term arity .nat} (rho : Env arity)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv) :
    Term.eval Surface.code.body fuel (baseKindGuardTA dT kT) rho
      = some (baseKindVal d kv) := by
  simp only [baseKindGuardTA, dm1TA, Term.eval, hdv, hkv, Option.bind, Option.bind_eq_bind,
    baseKindVal, cellR, cellC]

theorem topClassGuardTA_eval {fuel arity d kv : Nat} {dT kT : Term arity .nat} (rho : Env arity)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv) :
    Term.eval Surface.code.body fuel (topClassGuardTA dT kT) rho
      = some (topClassVal d kv) := by
  simp only [topClassGuardTA, baseBTA, baseHalfTA, bulkCountTA, dm1TA, Term.eval, hdv, hkv,
    Option.bind, Option.bind_eq_bind, topClassVal]

theorem rightClassGuardTA_eval {fuel arity d kv : Nat} {dT kT : Term arity .nat} (rho : Env arity)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv) :
    Term.eval Surface.code.body fuel (rightClassGuardTA dT kT) rho
      = some (rightClassVal d kv) := by
  simp only [rightClassGuardTA, baseBTA, baseHalfTA, bulkCountTA, dm1TA, Term.eval, hdv, hkv,
    Option.bind, Option.bind_eq_bind, rightClassVal]

theorem leftClassGuardTA_eval {fuel arity d kv : Nat} {dT kT : Term arity .nat} (rho : Env arity)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv) :
    Term.eval Surface.code.body fuel (leftClassGuardTA dT kT) rho
      = some (leftClassVal d kv) := by
  simp only [leftClassGuardTA, baseBTA, baseHalfTA, bulkCountTA, dm1TA, Term.eval, hdv, hkv,
    Option.bind, Option.bind_eq_bind, leftClassVal]

theorem topBandGuardTA_eval {fuel arity d kv qv : Nat} {dT kT qT : Term arity .nat} (rho : Env arity)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : Term.eval Surface.code.body fuel qT rho = some qv) :
    Term.eval Surface.code.body fuel (topBandGuardTA dT kT qT) rho
      = some (topBandVal d kv qv) := by
  simp only [topBandGuardTA, band3, orEqSucc, baseBTA, bulkCountTA, dm1TA, Term.eval, hdv, hkv, hqv,
    Option.bind, Option.bind_eq_bind, topBandVal, cellRow, cellCol]
  by_cases h1 : kv < d*d - 1 <;> by_cases h2 : qv / d = 0 <;>
    simp [h1, h2] <;> split <;> simp_all

theorem rightBandGuardTA_eval {fuel arity d kv qv : Nat} {dT kT qT : Term arity .nat} (rho : Env arity)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : Term.eval Surface.code.body fuel qT rho = some qv) :
    Term.eval Surface.code.body fuel (rightBandGuardTA dT kT qT) rho
      = some (rightBandVal d kv qv) := by
  simp only [rightBandGuardTA, orEqSucc, baseBTA, baseHalfTA, bulkCountTA, dm1TA, Term.eval,
    hdv, hkv, hqv, Option.bind, Option.bind_eq_bind, rightBandVal, cellRow, cellCol]
  by_cases h1 : qv % d = d-1 <;> simp [h1] <;> split <;> simp_all

theorem leftBandGuardTA_eval {fuel arity d kv qv : Nat} {dT kT qT : Term arity .nat} (rho : Env arity)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : Term.eval Surface.code.body fuel qT rho = some qv) :
    Term.eval Surface.code.body fuel (leftBandGuardTA dT kT qT) rho
      = some (leftBandVal d kv qv) := by
  simp only [leftBandGuardTA, orEqPair, baseBTA, baseHalfTA, bulkCountTA, dm1TA, Term.eval,
    hdv, hkv, hqv, Option.bind, Option.bind_eq_bind, leftBandVal, cellRow, cellCol]
  by_cases h1 : qv % d = 0 <;> simp [h1] <;> split <;> simp_all

theorem bottomBandGuardTA_eval {fuel arity d kv qv : Nat} {dT kT qT : Term arity .nat} (rho : Env arity)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : Term.eval Surface.code.body fuel qT rho = some qv) :
    Term.eval Surface.code.body fuel (bottomBandGuardTA dT kT qT) rho
      = some (bottomBandVal d kv qv) := by
  simp only [bottomBandGuardTA, orEqPair, baseBTA, baseHalfTA, bulkCountTA, dm1TA, Term.eval,
    hdv, hkv, hqv, Option.bind, Option.bind_eq_bind, bottomBandVal, cellRow, cellCol]
  by_cases h1 : qv / d = d-1 <;> simp [h1] <;> split <;> simp_all

/-! ### `Term.eval` of the inner stabilizer-index / qubit terms (arity-general).

Each promoted inner index `*KTA` / inner qubit `innerQTA`, fed the eval certs for
`dT`/`kT`/`qT`, evaluates to its `Nat`-level counterpart (`innerInteriorK`,
`innerTopK`, …, `innerQval`).  Arity-general restatements of the keystone
`interiorKT_evalsTo_gen` / `innerQT_evalsTo_gen` / `*KT_evalsTo_gen`. -/

theorem interiorKTA_evalsTo {fuel arity d kv : Nat} {dT kT : Term arity .nat} (rho : Env arity)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv) :
    Term.eval Surface.code.body fuel (interiorKTA dT kT) rho = some (innerInteriorK d kv) := by
  simp only [interiorKTA, innerDm1TA, innerDTA, rTA, cTA, dm1TA, Term.eval, hdv, hkv,
    Option.bind, Option.bind_eq_bind]
  rfl

theorem innerQTA_evalsTo {fuel arity d qv : Nat} {dT qT : Term arity .nat} (rho : Env arity)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hqv : Term.eval Surface.code.body fuel qT rho = some qv) :
    Term.eval Surface.code.body fuel (innerQTA dT qT) rho = some (innerQval d qv) := by
  simp only [innerQTA, innerDTA, rowTA, colTA, Term.eval, hdv, hqv,
    Option.bind, Option.bind_eq_bind]
  rfl

theorem topKTA_evalsTo {fuel arity d kv : Nat} {dT kT : Term arity .nat} (rho : Env arity)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv) :
    Term.eval Surface.code.body fuel (topKTA dT kT) rho = some (innerTopK d kv) := by
  simp only [topKTA, recInnerBulkTA, recInnerDm1TA, innerDm1TA, topBTA, cTA, innerDTA, dm1TA,
    innerTopK, cellC, Term.eval, hdv, hkv, Option.bind, Option.bind_eq_bind]

theorem rightKTA_evalsTo {fuel arity d kv : Nat} {dT kT : Term arity .nat} (rho : Env arity)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv) :
    Term.eval Surface.code.body fuel (rightKTA dT kT) rho = some (innerRightK d kv) := by
  simp only [rightKTA, recInnerBulkTA, recInnerDm1TA, innerDm1TA, recInnerHalfTA, rightBTA, rTA,
    innerDTA, dm1TA, innerRightK, cellR, cellInnerHalf, Term.eval, hdv, hkv, Option.bind,
    Option.bind_eq_bind]

theorem leftKTA_evalsTo {fuel arity d kv : Nat} {dT kT : Term arity .nat} (rho : Env arity)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv) :
    Term.eval Surface.code.body fuel (leftKTA dT kT) rho = some (innerLeftK d kv) := by
  simp only [leftKTA, recInnerBulkTA, recInnerDm1TA, innerDm1TA, recInnerHalfTA, leftBTA, rTA,
    innerDTA, dm1TA, innerLeftK, cellR, cellInnerHalf, Term.eval, hdv, hkv, Option.bind,
    Option.bind_eq_bind]

theorem bottomKTA_evalsTo {fuel arity d kv : Nat} {dT kT : Term arity .nat} (rho : Env arity)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv) :
    Term.eval Surface.code.body fuel (bottomKTA dT kT) rho = some (innerBottomK d kv) := by
  simp only [bottomKTA, recInnerBulkTA, recInnerDm1TA, innerDm1TA, recInnerHalfTA, bottomBTA, cTA,
    innerDTA, dm1TA, innerBottomK, cellC, cellInnerHalf, Term.eval, hdv, hkv, Option.bind,
    Option.bind_eq_bind]

/-! ### `Term.eval` of the promoted-not-inside boundary outer guards. -/

theorem topOuterGuardTA_eval {fuel arity d kv qv : Nat} {dT kT qT : Term arity .nat} (rho : Env arity)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : Term.eval Surface.code.body fuel qT rho = some qv) :
    Term.eval Surface.code.body fuel (topOuterGuardTA dT kT qT) rho = some (topOuterVal d kv qv) := by
  simp only [topOuterGuardTA, orEqSucc, rowTA, colTA, cTA, dm1TA, Term.eval, hdv, hkv, hqv,
    Option.bind, Option.bind_eq_bind, topOuterVal, cellRow, cellCol, cellC]
  by_cases h1 : qv / d = 0 <;> simp [h1] <;> split <;> simp_all

theorem rightOuterGuardTA_eval {fuel arity d kv qv : Nat} {dT kT qT : Term arity .nat} (rho : Env arity)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : Term.eval Surface.code.body fuel qT rho = some qv) :
    Term.eval Surface.code.body fuel (rightOuterGuardTA dT kT qT) rho = some (rightOuterVal d kv qv) := by
  simp only [rightOuterGuardTA, orEqSucc, rowTA, colTA, rTA, dm1TA, Term.eval, hdv, hkv, hqv,
    Option.bind, Option.bind_eq_bind, rightOuterVal, cellRow, cellCol, cellR]
  by_cases h1 : qv % d = d-1 <;> simp [h1] <;> split <;> simp_all

theorem leftOuterGuardTA_eval {fuel arity d kv qv : Nat} {dT kT qT : Term arity .nat} (rho : Env arity)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : Term.eval Surface.code.body fuel qT rho = some qv) :
    Term.eval Surface.code.body fuel (leftOuterGuardTA dT kT qT) rho = some (leftOuterVal d kv qv) := by
  simp only [leftOuterGuardTA, orEqSucc, rowTA, colTA, rTA, dm1TA, Term.eval, hdv, hkv, hqv,
    Option.bind, Option.bind_eq_bind, leftOuterVal, cellRow, cellCol, cellR]
  by_cases h1 : qv % d = 0 <;> simp [h1] <;> split <;> simp_all

theorem bottomOuterGuardTA_eval {fuel arity d kv qv : Nat} {dT kT qT : Term arity .nat} (rho : Env arity)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : Term.eval Surface.code.body fuel qT rho = some qv) :
    Term.eval Surface.code.body fuel (bottomOuterGuardTA dT kT qT) rho = some (bottomOuterVal d kv qv) := by
  simp only [bottomOuterGuardTA, orEqSucc, rowTA, colTA, cTA, dm1TA, Term.eval, hdv, hkv, hqv,
    Option.bind, Option.bind_eq_bind, bottomOuterVal, cellRow, cellCol, cellC]
  by_cases h1 : qv / d = d-1 <;> simp [h1] <;> split <;> simp_all

/-! ## (B) `baseLeafTreeTA` reduces to the `surfaceCellPauli` literal

At a concrete `(kv, qv)` (eval certs) and a distance `d`, the flat classifier tree
`baseLeafTreeTA dT kT qT` equals the Pauli literal `surfaceCellPauli d kv qv`, by
selecting its `ite` branches through the guard facts.  `surfaceCellPauli` and
`baseLeafTreeTA` share the identical branch structure, so each Nat-level case picks
the matching path and the leaf literal is `surfaceCellPauli`'s own. -/

private def pauliLitEqA {fuel arity : Nat} (p : Pauli) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (SC.closed (.pauliLit (arity := arity) p)) (SC.closed (.pauliLit p))) :=
  PureFamilyDerivA.eqPauliRefl _

def baseLeafTreeTA_resolveA {fuel arity d kv qv : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hdv : ∀ (rho : Env arity), Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : ∀ (rho : Env arity), Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : ∀ (rho : Env arity), Term.eval Surface.code.body fuel qT rho = some qv) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT))
        (SC.closed (.pauliLit (surfaceCellPauli d kv qv)))) := by
  -- Guard facts at `(kv, qv)`.
  have gBulk := cellGuardA_of (b := decide (kv < (d-1)*(d-1)))
    (bulkGuardTA_pure hd hk) (fun rho => bulkGuardTA_eval rho (hdv rho) (hkv rho))
  by_cases hbulk : kv < (d-1)*(d-1)
  · -- bulk index: select the bulk then-branch.
    have hbulkD : decide (kv < (d-1)*(d-1)) = true := by simp [hbulk]
    rw [hbulkD] at gBulk
    have gBand := cellGuardA_of (b := baseBulkBandVal d kv qv)
      (baseBulkBandGuardTA_pure hd hk hq) (fun rho => baseBulkBandGuardTA_eval rho (hdv rho) (hkv rho) (hqv rho))
    refine PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectThen _ _ _ gBulk) ?_
    by_cases hband : baseBulkBandVal d kv qv = true
    · rw [hband] at gBand
      have gKind := cellGuardA_of (b := baseKindVal d kv)
        (baseKindGuardTA_pure hd hk) (fun rho => baseKindGuardTA_eval rho (hdv rho) (hkv rho))
      have hbb : inBulkBand d kv qv = true := by
        simpa only [baseBulkBandVal, inBulkBand, Bool.and_assoc] using hband
      by_cases hkind : baseKindVal d kv = true
      · rw [hkind] at gKind
        refine PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.pauliIteSelectThen _ _ _ gBand)
          (PureFamilyDerivA.eqPauliTrans _ _ _
            (PureFamilyDerivA.pauliIteSelectThen _ _ _ gKind) ?_)
        have : surfaceCellPauli d kv qv = Pauli.Z := by
          have hkz : (cellR d kv + cellC d kv) % 2 = 0 := by simpa [baseKindVal] using hkind
          simp only [surfaceCellPauli, if_pos hbulk, hbb, if_true, bulkKind, if_pos hkz]
        rw [this]; exact PureFamilyDerivA.eqPauliRefl _
      · have hkindF : baseKindVal d kv = false := by simpa using hkind
        rw [hkindF] at gKind
        refine PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.pauliIteSelectThen _ _ _ gBand)
          (PureFamilyDerivA.eqPauliTrans _ _ _
            (PureFamilyDerivA.pauliIteSelectElse _ _ _ gKind) ?_)
        have : surfaceCellPauli d kv qv = Pauli.X := by
          have hkz : ¬ (cellR d kv + cellC d kv) % 2 = 0 := by simpa [baseKindVal] using hkindF
          simp only [surfaceCellPauli, if_pos hbulk, hbb, if_true, bulkKind, if_neg hkz]
        rw [this]; exact PureFamilyDerivA.eqPauliRefl _
    · have hbandF : baseBulkBandVal d kv qv = false := by simpa using hband
      rw [hbandF] at gBand
      have hbb : inBulkBand d kv qv = false := by
        simpa only [baseBulkBandVal, inBulkBand, Bool.and_assoc] using hbandF
      refine PureFamilyDerivA.eqPauliTrans _ _ _
        (PureFamilyDerivA.pauliIteSelectElse _ _ _ gBand) ?_
      have : surfaceCellPauli d kv qv = Pauli.I := by
        simp only [surfaceCellPauli, if_pos hbulk, hbb, Bool.false_eq_true, if_false]
      rw [this]; exact PureFamilyDerivA.eqPauliRefl _
  · -- boundary index: select the bulk else-branch.
    have hbulkF : decide (kv < (d-1)*(d-1)) = false := by simp [hbulk]
    rw [hbulkF] at gBulk
    refine PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectElse _ _ _ gBulk) ?_
    -- now classify into top/right/left/bottom strips.
    have gTopClass := cellGuardA_of (b := topClassVal d kv)
      (topClassGuardTA_pure hd hk) (fun rho => topClassGuardTA_eval rho (hdv rho) (hkv rho))
    by_cases htc : topClassVal d kv = true
    · rw [htc] at gTopClass
      have htcN : kv - (d-1)*(d-1) < (d-1)/2 := by simpa [topClassVal] using htc
      have gTopBand := cellGuardA_of (b := topBandVal d kv qv)
        (topBandGuardTA_pure hd hk hq) (fun rho => topBandGuardTA_eval rho (hdv rho) (hkv rho) (hqv rho))
      refine PureFamilyDerivA.eqPauliTrans _ _ _
        (PureFamilyDerivA.pauliIteSelectThen _ _ _ gTopClass) ?_
      by_cases htb : topBandVal d kv qv = true
      · rw [htb] at gTopBand
        refine PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.pauliIteSelectThen _ _ _ gTopBand) ?_
        have : surfaceCellPauli d kv qv = Pauli.X := by
          have hh := htb
          simp only [topBandVal, cellRow, cellCol] at hh
          simp only [surfaceCellPauli, if_neg hbulk, if_pos htcN, Bool.and_assoc, hh, if_true]
        rw [this]; exact PureFamilyDerivA.eqPauliRefl _
      · have htbF : topBandVal d kv qv = false := by simpa using htb
        rw [htbF] at gTopBand
        refine PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.pauliIteSelectElse _ _ _ gTopBand) ?_
        have : surfaceCellPauli d kv qv = Pauli.I := by
          have hh := htbF
          simp only [topBandVal, cellRow, cellCol] at hh
          simp only [surfaceCellPauli, if_neg hbulk, if_pos htcN, Bool.and_assoc, hh,
            Bool.false_eq_true, if_false]
        rw [this]; exact PureFamilyDerivA.eqPauliRefl _
    · have htcF : topClassVal d kv = false := by simpa using htc
      rw [htcF] at gTopClass
      have htcN : ¬ kv - (d-1)*(d-1) < (d-1)/2 := by simpa [topClassVal] using htcF
      refine PureFamilyDerivA.eqPauliTrans _ _ _
        (PureFamilyDerivA.pauliIteSelectElse _ _ _ gTopClass) ?_
      have gRightClass := cellGuardA_of (b := rightClassVal d kv)
        (rightClassGuardTA_pure hd hk) (fun rho => rightClassGuardTA_eval rho (hdv rho) (hkv rho))
      by_cases hrc : rightClassVal d kv = true
      · rw [hrc] at gRightClass
        have hrcN : kv - (d-1)*(d-1) < 2*((d-1)/2) := by simpa [rightClassVal] using hrc
        have gRightBand := cellGuardA_of (b := rightBandVal d kv qv)
          (rightBandGuardTA_pure hd hk hq) (fun rho => rightBandGuardTA_eval rho (hdv rho) (hkv rho) (hqv rho))
        refine PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.pauliIteSelectThen _ _ _ gRightClass) ?_
        by_cases hrb : rightBandVal d kv qv = true
        · rw [hrb] at gRightBand
          refine PureFamilyDerivA.eqPauliTrans _ _ _
            (PureFamilyDerivA.pauliIteSelectThen _ _ _ gRightBand) ?_
          have : surfaceCellPauli d kv qv = Pauli.Z := by
            have := hrb
            simp only [rightBandVal, cellRow, cellCol] at this
            simp only [surfaceCellPauli, if_neg hbulk, if_neg htcN, if_pos hrcN, this, if_true]
          rw [this]; exact PureFamilyDerivA.eqPauliRefl _
        · have hrbF : rightBandVal d kv qv = false := by simpa using hrb
          rw [hrbF] at gRightBand
          refine PureFamilyDerivA.eqPauliTrans _ _ _
            (PureFamilyDerivA.pauliIteSelectElse _ _ _ gRightBand) ?_
          have : surfaceCellPauli d kv qv = Pauli.I := by
            have := hrbF
            simp only [rightBandVal, cellRow, cellCol] at this
            simp only [surfaceCellPauli, if_neg hbulk, if_neg htcN, if_pos hrcN, this,
              Bool.false_eq_true, if_false]
          rw [this]; exact PureFamilyDerivA.eqPauliRefl _
      · have hrcF : rightClassVal d kv = false := by simpa using hrc
        rw [hrcF] at gRightClass
        have hrcN : ¬ kv - (d-1)*(d-1) < 2*((d-1)/2) := by simpa [rightClassVal] using hrcF
        refine PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.pauliIteSelectElse _ _ _ gRightClass) ?_
        have gLeftClass := cellGuardA_of (b := leftClassVal d kv)
          (leftClassGuardTA_pure hd hk) (fun rho => leftClassGuardTA_eval rho (hdv rho) (hkv rho))
        by_cases hlc : leftClassVal d kv = true
        · rw [hlc] at gLeftClass
          have hlcN : kv - (d-1)*(d-1) < 3*((d-1)/2) := by simpa [leftClassVal] using hlc
          have gLeftBand := cellGuardA_of (b := leftBandVal d kv qv)
            (leftBandGuardTA_pure hd hk hq) (fun rho => leftBandGuardTA_eval rho (hdv rho) (hkv rho) (hqv rho))
          refine PureFamilyDerivA.eqPauliTrans _ _ _
            (PureFamilyDerivA.pauliIteSelectThen _ _ _ gLeftClass) ?_
          by_cases hlb : leftBandVal d kv qv = true
          · rw [hlb] at gLeftBand
            refine PureFamilyDerivA.eqPauliTrans _ _ _
              (PureFamilyDerivA.pauliIteSelectThen _ _ _ gLeftBand) ?_
            have : surfaceCellPauli d kv qv = Pauli.Z := by
              have := hlb
              simp only [leftBandVal, cellRow, cellCol] at this
              simp only [surfaceCellPauli, if_neg hbulk, if_neg htcN, if_neg hrcN, if_pos hlcN, this, if_true]
            rw [this]; exact PureFamilyDerivA.eqPauliRefl _
          · have hlbF : leftBandVal d kv qv = false := by simpa using hlb
            rw [hlbF] at gLeftBand
            refine PureFamilyDerivA.eqPauliTrans _ _ _
              (PureFamilyDerivA.pauliIteSelectElse _ _ _ gLeftBand) ?_
            have : surfaceCellPauli d kv qv = Pauli.I := by
              have := hlbF
              simp only [leftBandVal, cellRow, cellCol] at this
              simp only [surfaceCellPauli, if_neg hbulk, if_neg htcN, if_neg hrcN, if_pos hlcN, this,
                Bool.false_eq_true, if_false]
            rw [this]; exact PureFamilyDerivA.eqPauliRefl _
        · have hlcF : leftClassVal d kv = false := by simpa using hlc
          rw [hlcF] at gLeftClass
          have hlcN : ¬ kv - (d-1)*(d-1) < 3*((d-1)/2) := by simpa [leftClassVal] using hlcF
          have gBottomBand := cellGuardA_of (b := bottomBandVal d kv qv)
            (bottomBandGuardTA_pure hd hk hq) (fun rho => bottomBandGuardTA_eval rho (hdv rho) (hkv rho) (hqv rho))
          refine PureFamilyDerivA.eqPauliTrans _ _ _
            (PureFamilyDerivA.pauliIteSelectElse _ _ _ gLeftClass) ?_
          by_cases hbb' : bottomBandVal d kv qv = true
          · rw [hbb'] at gBottomBand
            refine PureFamilyDerivA.eqPauliTrans _ _ _
              (PureFamilyDerivA.pauliIteSelectThen _ _ _ gBottomBand) ?_
            have : surfaceCellPauli d kv qv = Pauli.X := by
              have := hbb'
              simp only [bottomBandVal, cellRow, cellCol] at this
              simp only [surfaceCellPauli, if_neg hbulk, if_neg htcN, if_neg hrcN, if_neg hlcN, this, if_true]
            rw [this]; exact PureFamilyDerivA.eqPauliRefl _
          · have hbbF : bottomBandVal d kv qv = false := by simpa using hbb'
            rw [hbbF] at gBottomBand
            refine PureFamilyDerivA.eqPauliTrans _ _ _
              (PureFamilyDerivA.pauliIteSelectElse _ _ _ gBottomBand) ?_
            have : surfaceCellPauli d kv qv = Pauli.I := by
              have := hbbF
              simp only [bottomBandVal, cellRow, cellCol] at this
              simp only [surfaceCellPauli, if_neg hbulk, if_neg htcN, if_neg hrcN, if_neg hlcN, this,
                Bool.false_eq_true, if_false]
            rw [this]; exact PureFamilyDerivA.eqPauliRefl _

/-! ## (C) `rowSymTreeA` reduces to the `recLeaf` literal

By structural recursion on the distance index `m`.  Base case (`m = 0`):
`rowSymTreeA 0 = baseLeafTreeTA`, resolved by (B) and `recLeaf 0 = surfaceCellPauli`.
Recursive case (`m + 1`): `rowSymTreeA (m+1) = recLeafTreeTA` with the five inner
subtrees `rowSymTreeA m …`; case on the Nat classification of `(kv, qv)` exactly as
`recLeaf (m+1)` does.  Recursing inside-cells use the IH; promoted-not-inside cells
use the outer guard reduction; bulk-fallback / out-of-bulk use (B).

`recInnerDTA D.dT = innerDTA D.dT = (DistAtA.pred D).dT` definitionally, so the IH
at `D.pred` resolves every inner subtree. -/

/-- Reduce a promoted-not-inside `ite outerGuard kindLit I` to the
`surfaceCellPauli` literal, given the outer guard's `Nat` value and the matching
`surfaceCellPauli_*Cell_notInside` rewrite. -/
private def outerLeafReduceA {fuel arity : Nat} {kindP : Pauli} {ov : Bool}
    {og : Term arity .bool} {scp : Pauli}
    (gOuter : PureFamilyDerivA Surface.code.body fuel (.eqBool (SC.closed og) (SC.b ov)))
    (hsc : scp = (if ov then kindP else Pauli.I)) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (SC.closed (.ite og (.pauliLit kindP) (.pauliLit Pauli.I)))
        (SC.closed (.pauliLit scp))) := by
  cases ov with
  | true =>
      refine PureFamilyDerivA.eqPauliTrans _ _ _ (PureFamilyDerivA.pauliIteSelectThen _ _ _ gOuter) ?_
      rw [show scp = kindP from by simpa using hsc]; exact PureFamilyDerivA.eqPauliRefl _
  | false =>
      refine PureFamilyDerivA.eqPauliTrans _ _ _ (PureFamilyDerivA.pauliIteSelectElse _ _ _ gOuter) ?_
      rw [show scp = Pauli.I from by simpa using hsc]; exact PureFamilyDerivA.eqPauliRefl _

def rowSymTreeA_resolveA {fuel arity : Nat} :
    (m : Nat) → (D : DistAtA arity m) → (kT qT : Term arity .nat) → (kv qv : Nat) →
    SFormula.PureNatTerm kT → SFormula.PureNatTerm qT →
    (∀ (rho : Env arity), Term.eval Surface.code.body fuel kT rho = some kv) →
    (∀ (rho : Env arity), Term.eval Surface.code.body fuel qT rho = some qv) →
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (SC.closed (rowSymTreeA m D.dT kT qT))
        (SC.closed (.pauliLit (recLeaf m kv qv))))
  | 0, D, kT, qT, kv, qv, hk, hq, hkv, hqv => by
      have h := baseLeafTreeTA_resolveA (d := oddDistance 0) D.pure hk hq
        (fun rho => D.evalsTo rho) hkv hqv
      simpa only [rowSymTreeA, recLeaf] using h
  | m + 1, D, kT, qT, kv, qv, hk, hq, hkv, hqv => by
      set d := oddDistance (m + 1) with hd_def
      have hodd : d % 2 = 1 := by rw [hd_def]; simp only [oddDistance]; omega
      have ih : ∀ (kT' qT' : Term arity .nat) (kv' qv' : Nat),
          SFormula.PureNatTerm kT' → SFormula.PureNatTerm qT' →
          (∀ (rho : Env arity), Term.eval Surface.code.body fuel kT' rho = some kv') →
          (∀ (rho : Env arity), Term.eval Surface.code.body fuel qT' rho = some qv') →
          PureFamilyDerivA Surface.code.body fuel
            (.eqPauli (SC.closed (rowSymTreeA m (innerDTA D.dT) kT' qT'))
              (SC.closed (.pauliLit (recLeaf m kv' qv')))) := by
        intro kT' qT' kv' qv' hk' hq' hkv' hqv'
        have := rowSymTreeA_resolveA m (DistAtA.pred D) kT' qT' kv' qv' hk' hq' hkv' hqv'
        simpa only [DistAtA.pred] using this
      simp only [rowSymTreeA, recLeafTreeTA, recInnerDTA]
      have gBulk := cellGuardA_of (b := decide (kv < (d-1)*(d-1)))
        (bulkGuardTA_pure D.pure hk) (fun rho => bulkGuardTA_eval rho (D.evalsTo rho) (hkv rho))
      by_cases hbulk : kv < (d-1)*(d-1)
      · have hbulkD : decide (kv < (d-1)*(d-1)) = true := by simp [hbulk]
        rw [hbulkD] at gBulk
        refine PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.pauliIteSelectThen _ _ _ gBulk) ?_
        have gInt := cellGuardA_of (b := isInteriorCell d kv)
          (interiorCellGuardTA_pure D.pure hk) (fun rho => interiorCellGuardTA_eval rho (D.evalsTo rho) (hkv rho))
        by_cases hint : isInteriorCell d kv = true
        · rw [hint] at gInt
          refine PureFamilyDerivA.eqPauliTrans _ _ _
            (PureFamilyDerivA.pauliIteSelectThen _ _ _ gInt) ?_
          have gIns := cellGuardA_of (b := isInside d qv)
            (insideGuardTA_pure D.pure hq) (fun rho => insideGuardTA_eval rho (D.evalsTo rho) (hqv rho))
          by_cases hin : isInside d qv = true
          · rw [hin] at gIns
            refine PureFamilyDerivA.eqPauliTrans _ _ _
              (PureFamilyDerivA.pauliIteSelectThen _ _ _ gIns) ?_
            have hleaf : recLeaf (m + 1) kv qv = recLeaf m (innerInteriorK d kv) (innerQval d qv) := by
              simp only [recLeaf, ← hd_def, if_pos hbulk, hint, hin, if_true]
            rw [hleaf]
            exact ih (interiorKTA D.dT kT) (innerQTA D.dT qT) (innerInteriorK d kv) (innerQval d qv)
              (interiorKTA_pure D.pure hk) (innerQTA_pure D.pure hq)
              (fun rho => interiorKTA_evalsTo rho (D.evalsTo rho) (hkv rho))
              (fun rho => innerQTA_evalsTo rho (D.evalsTo rho) (hqv rho))
          · have hinF : isInside d qv = false := by simpa using hin
            rw [hinF] at gIns
            refine PureFamilyDerivA.eqPauliTrans _ _ _
              (PureFamilyDerivA.pauliIteSelectElse _ _ _ gIns) ?_
            have hleaf : recLeaf (m + 1) kv qv = Pauli.I := by
              simp only [recLeaf, ← hd_def, if_pos hbulk, hint, if_true, hinF,
                Bool.false_eq_true, if_false]
            rw [hleaf]; exact PureFamilyDerivA.eqPauliRefl _
        · have hintF : isInteriorCell d kv = false := by simpa using hint
          rw [hintF] at gInt
          refine PureFamilyDerivA.eqPauliTrans _ _ _
            (PureFamilyDerivA.pauliIteSelectElse _ _ _ gInt) ?_
          have gTop := cellGuardA_of (b := isTopCell d kv)
            (topCellGuardTA_pure D.pure hk) (fun rho => topCellGuardTA_eval rho (D.evalsTo rho) (hkv rho))
          by_cases htop : isTopCell d kv = true
          · rw [htop] at gTop
            refine PureFamilyDerivA.eqPauliTrans _ _ _
              (PureFamilyDerivA.pauliIteSelectThen _ _ _ gTop) ?_
            have gIns := cellGuardA_of (b := isInside d qv)
              (insideGuardTA_pure D.pure hq) (fun rho => insideGuardTA_eval rho (D.evalsTo rho) (hqv rho))
            by_cases hin : isInside d qv = true
            · rw [hin] at gIns
              refine PureFamilyDerivA.eqPauliTrans _ _ _
                (PureFamilyDerivA.pauliIteSelectThen _ _ _ gIns) ?_
              have hleaf : recLeaf (m + 1) kv qv = recLeaf m (innerTopK d kv) (innerQval d qv) := by
                simp only [recLeaf, ← hd_def, if_pos hbulk, hintF, htop, hin,
                  Bool.false_eq_true, if_false, if_true]
              rw [hleaf]
              exact ih (topKTA D.dT kT) (innerQTA D.dT qT) (innerTopK d kv) (innerQval d qv)
                (topKTA_pure D.pure hk) (innerQTA_pure D.pure hq)
                (fun rho => topKTA_evalsTo rho (D.evalsTo rho) (hkv rho))
                (fun rho => innerQTA_evalsTo rho (D.evalsTo rho) (hqv rho))
            · have hinF : isInside d qv = false := by simpa using hin
              rw [hinF] at gIns
              refine PureFamilyDerivA.eqPauliTrans _ _ _
                (PureFamilyDerivA.pauliIteSelectElse _ _ _ gIns) ?_
              have hleaf : recLeaf (m + 1) kv qv = surfaceCellPauli d kv qv := by
                simp only [recLeaf, ← hd_def, if_pos hbulk, hintF, htop, hinF,
                  Bool.false_eq_true, if_false, if_true]
              rw [hleaf]
              exact outerLeafReduceA
                (cellGuardA_of (b := topOuterVal d kv qv) (topOuterGuardTA_pure D.pure hk hq)
                  (fun rho => topOuterGuardTA_eval rho (D.evalsTo rho) (hkv rho) (hqv rho)))
                (surfaceCellPauli_topCell_notInside htop hinF)
          · have htopF : isTopCell d kv = false := by simpa using htop
            rw [htopF] at gTop
            refine PureFamilyDerivA.eqPauliTrans _ _ _
              (PureFamilyDerivA.pauliIteSelectElse _ _ _ gTop) ?_
            have gRight := cellGuardA_of (b := isRightCell d kv)
              (rightCellGuardTA_pure D.pure hk) (fun rho => rightCellGuardTA_eval rho (D.evalsTo rho) (hkv rho))
            by_cases hright : isRightCell d kv = true
            · rw [hright] at gRight
              refine PureFamilyDerivA.eqPauliTrans _ _ _
                (PureFamilyDerivA.pauliIteSelectThen _ _ _ gRight) ?_
              have gIns := cellGuardA_of (b := isInside d qv)
                (insideGuardTA_pure D.pure hq) (fun rho => insideGuardTA_eval rho (D.evalsTo rho) (hqv rho))
              by_cases hin : isInside d qv = true
              · rw [hin] at gIns
                refine PureFamilyDerivA.eqPauliTrans _ _ _
                  (PureFamilyDerivA.pauliIteSelectThen _ _ _ gIns) ?_
                have hleaf : recLeaf (m + 1) kv qv = recLeaf m (innerRightK d kv) (innerQval d qv) := by
                  simp only [recLeaf, ← hd_def, if_pos hbulk, hintF, htopF, hright, hin,
                    Bool.false_eq_true, if_false, if_true]
                rw [hleaf]
                exact ih (rightKTA D.dT kT) (innerQTA D.dT qT) (innerRightK d kv) (innerQval d qv)
                  (rightKTA_pure D.pure hk) (innerQTA_pure D.pure hq)
                  (fun rho => rightKTA_evalsTo rho (D.evalsTo rho) (hkv rho))
                  (fun rho => innerQTA_evalsTo rho (D.evalsTo rho) (hqv rho))
              · have hinF : isInside d qv = false := by simpa using hin
                rw [hinF] at gIns
                refine PureFamilyDerivA.eqPauliTrans _ _ _
                  (PureFamilyDerivA.pauliIteSelectElse _ _ _ gIns) ?_
                have hleaf : recLeaf (m + 1) kv qv = surfaceCellPauli d kv qv := by
                  simp only [recLeaf, ← hd_def, if_pos hbulk, hintF, htopF, hright, hinF,
                    Bool.false_eq_true, if_false, if_true]
                rw [hleaf]
                exact outerLeafReduceA
                  (cellGuardA_of (b := rightOuterVal d kv qv) (rightOuterGuardTA_pure D.pure hk hq)
                    (fun rho => rightOuterGuardTA_eval rho (D.evalsTo rho) (hkv rho) (hqv rho)))
                  (surfaceCellPauli_rightCell_notInside hright hinF hodd)
            · have hrightF : isRightCell d kv = false := by simpa using hright
              rw [hrightF] at gRight
              refine PureFamilyDerivA.eqPauliTrans _ _ _
                (PureFamilyDerivA.pauliIteSelectElse _ _ _ gRight) ?_
              have gLeft := cellGuardA_of (b := isLeftCell d kv)
                (leftCellGuardTA_pure D.pure hk) (fun rho => leftCellGuardTA_eval rho (D.evalsTo rho) (hkv rho))
              by_cases hleft : isLeftCell d kv = true
              · rw [hleft] at gLeft
                refine PureFamilyDerivA.eqPauliTrans _ _ _
                  (PureFamilyDerivA.pauliIteSelectThen _ _ _ gLeft) ?_
                have gIns := cellGuardA_of (b := isInside d qv)
                  (insideGuardTA_pure D.pure hq) (fun rho => insideGuardTA_eval rho (D.evalsTo rho) (hqv rho))
                by_cases hin : isInside d qv = true
                · rw [hin] at gIns
                  refine PureFamilyDerivA.eqPauliTrans _ _ _
                    (PureFamilyDerivA.pauliIteSelectThen _ _ _ gIns) ?_
                  have hleaf : recLeaf (m + 1) kv qv = recLeaf m (innerLeftK d kv) (innerQval d qv) := by
                    simp only [recLeaf, ← hd_def, if_pos hbulk, hintF, htopF, hrightF, hleft, hin,
                      Bool.false_eq_true, if_false, if_true]
                  rw [hleaf]
                  exact ih (leftKTA D.dT kT) (innerQTA D.dT qT) (innerLeftK d kv) (innerQval d qv)
                    (leftKTA_pure D.pure hk) (innerQTA_pure D.pure hq)
                    (fun rho => leftKTA_evalsTo rho (D.evalsTo rho) (hkv rho))
                    (fun rho => innerQTA_evalsTo rho (D.evalsTo rho) (hqv rho))
                · have hinF : isInside d qv = false := by simpa using hin
                  rw [hinF] at gIns
                  refine PureFamilyDerivA.eqPauliTrans _ _ _
                    (PureFamilyDerivA.pauliIteSelectElse _ _ _ gIns) ?_
                  have hleaf : recLeaf (m + 1) kv qv = surfaceCellPauli d kv qv := by
                    simp only [recLeaf, ← hd_def, if_pos hbulk, hintF, htopF, hrightF, hleft, hinF,
                      Bool.false_eq_true, if_false, if_true]
                  rw [hleaf]
                  exact outerLeafReduceA
                    (cellGuardA_of (b := leftOuterVal d kv qv) (leftOuterGuardTA_pure D.pure hk hq)
                      (fun rho => leftOuterGuardTA_eval rho (D.evalsTo rho) (hkv rho) (hqv rho)))
                    (surfaceCellPauli_leftCell_notInside hleft hinF)
              · have hleftF : isLeftCell d kv = false := by simpa using hleft
                rw [hleftF] at gLeft
                refine PureFamilyDerivA.eqPauliTrans _ _ _
                  (PureFamilyDerivA.pauliIteSelectElse _ _ _ gLeft) ?_
                have gBottom := cellGuardA_of (b := isBottomCell d kv)
                  (bottomCellGuardTA_pure D.pure hk) (fun rho => bottomCellGuardTA_eval rho (D.evalsTo rho) (hkv rho))
                by_cases hbottom : isBottomCell d kv = true
                · rw [hbottom] at gBottom
                  refine PureFamilyDerivA.eqPauliTrans _ _ _
                    (PureFamilyDerivA.pauliIteSelectThen _ _ _ gBottom) ?_
                  have gIns := cellGuardA_of (b := isInside d qv)
                    (insideGuardTA_pure D.pure hq) (fun rho => insideGuardTA_eval rho (D.evalsTo rho) (hqv rho))
                  by_cases hin : isInside d qv = true
                  · rw [hin] at gIns
                    refine PureFamilyDerivA.eqPauliTrans _ _ _
                      (PureFamilyDerivA.pauliIteSelectThen _ _ _ gIns) ?_
                    have hleaf : recLeaf (m + 1) kv qv = recLeaf m (innerBottomK d kv) (innerQval d qv) := by
                      simp only [recLeaf, ← hd_def, if_pos hbulk, hintF, htopF, hrightF, hleftF, hbottom, hin,
                        Bool.false_eq_true, if_false, if_true]
                    rw [hleaf]
                    exact ih (bottomKTA D.dT kT) (innerQTA D.dT qT) (innerBottomK d kv) (innerQval d qv)
                      (bottomKTA_pure D.pure hk) (innerQTA_pure D.pure hq)
                      (fun rho => bottomKTA_evalsTo rho (D.evalsTo rho) (hkv rho))
                      (fun rho => innerQTA_evalsTo rho (D.evalsTo rho) (hqv rho))
                  · have hinF : isInside d qv = false := by simpa using hin
                    rw [hinF] at gIns
                    refine PureFamilyDerivA.eqPauliTrans _ _ _
                      (PureFamilyDerivA.pauliIteSelectElse _ _ _ gIns) ?_
                    have hleaf : recLeaf (m + 1) kv qv = surfaceCellPauli d kv qv := by
                      simp only [recLeaf, ← hd_def, if_pos hbulk, hintF, htopF, hrightF, hleftF, hbottom, hinF,
                        Bool.false_eq_true, if_false, if_true]
                    rw [hleaf]
                    exact outerLeafReduceA
                      (cellGuardA_of (b := bottomOuterVal d kv qv) (bottomOuterGuardTA_pure D.pure hk hq)
                        (fun rho => bottomOuterGuardTA_eval rho (D.evalsTo rho) (hkv rho) (hqv rho)))
                      (surfaceCellPauli_bottomCell_notInside hbottom hinF hodd)
                · have hbottomF : isBottomCell d kv = false := by simpa using hbottom
                  rw [hbottomF] at gBottom
                  refine PureFamilyDerivA.eqPauliTrans _ _ _
                    (PureFamilyDerivA.pauliIteSelectElse _ _ _ gBottom) ?_
                  have hleaf : recLeaf (m + 1) kv qv = surfaceCellPauli d kv qv := by
                    simp only [recLeaf, ← hd_def, if_pos hbulk, hintF, htopF, hrightF, hleftF, hbottomF,
                      Bool.false_eq_true, if_false]
                  rw [hleaf]
                  exact baseLeafTreeTA_resolveA (d := d) D.pure hk hq (fun rho => D.evalsTo rho) hkv hqv
      · have hbulkF : decide (kv < (d-1)*(d-1)) = false := by simp [hbulk]
        rw [hbulkF] at gBulk
        refine PureFamilyDerivA.eqPauliTrans _ _ _
          (PureFamilyDerivA.pauliIteSelectElse _ _ _ gBulk) ?_
        have hleaf : recLeaf (m + 1) kv qv = surfaceCellPauli d kv qv := by
          simp only [recLeaf, ← hd_def, if_neg hbulk]
        rw [hleaf]
        exact baseLeafTreeTA_resolveA (d := d) D.pure hk hq (fun rho => D.evalsTo rho) hkv hqv

/-! ## The flat bridge

`rowSymTreeFlatBridge`: at a concrete stabilizer index `kv` / qubit `qv` (carried
by pure terms `kT`/`qT` with eval certificates) and a distance `dT` evaluating to
`oddDistance m`, the recursive resolved row-entry tree `rowSymTreeA m dT kT qT`
equals the flat base-entry classifier `baseLeafTreeTA dT kT qT`, as a pure
object-logic `PureFamilyDerivA` `eqPauli` derivation.

Composition: `rowSymTreeA = pauliLit (recLeaf m kv qv)` by (C); the literal is
rewritten by the Nat-level global self-similarity `recLeaf m kv qv =
surfaceCellPauli (oddDistance m) kv qv`; and `pauliLit (surfaceCellPauli …) =
baseLeafTreeTA` by (B) (symm).  This pays the recursion exactly once, yielding the
flat, recursion-free row-entry equality. -/
def rowSymTreeFlatBridge {fuel arity : Nat}
    (m : Nat) (D : DistAtA arity m) (kT qT : Term arity .nat) (kv qv : Nat)
    (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hkv : ∀ (rho : Env arity), Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : ∀ (rho : Env arity), Term.eval Surface.code.body fuel qT rho = some qv) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (SC.closed (rowSymTreeA m D.dT kT qT))
        (SC.closed (baseLeafTreeTA D.dT kT qT))) := by
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (rowSymTreeA_resolveA m D kT qT kv qv hk hq hkv hqv) ?_
  -- rewrite the literal `recLeaf m kv qv` to `surfaceCellPauli (oddDistance m) kv qv`.
  rw [recLeaf_eq_surfaceCellPauli m kv qv]
  -- and `pauliLit (surfaceCellPauli …) = baseLeafTreeTA` by (B), symm.
  exact PureFamilyDerivA.eqPauliSymm _ _
    (baseLeafTreeTA_resolveA (d := oddDistance m) D.pure hk hq (fun rho => D.evalsTo rho) hkv hqv)

/-- Literal-distance specialisation: the flat bridge at the canonical literal
distance `oddDistance m` (`DistAtA.lit`). -/
def rowSymTreeFlatBridge_lit {fuel arity : Nat}
    (m : Nat) (kT qT : Term arity .nat) (kv qv : Nat)
    (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hkv : ∀ (rho : Env arity), Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : ∀ (rho : Env arity), Term.eval Surface.code.body fuel qT rho = some qv) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (SC.closed (rowSymTreeA m (DistAtA.lit arity m).dT kT qT))
        (SC.closed (baseLeafTreeTA (DistAtA.lit arity m).dT kT qT))) :=
  rowSymTreeFlatBridge m (DistAtA.lit arity m) kT qT kv qv hk hq hkv hqv

/-! ## The SYMBOLIC flat bridge

`rowSymTreeFlatBridgeSym` proves the same flat-bridge equality but with `kT`, `qT`
**arbitrary pure terms** (in particular the object-logic bound variable `.var 0`),
not fixed concrete values.  The only distance constraint is `DistAtA` (so `D.dT`
evaluates to `oddDistance m`).  This is the form the symbolic-distance consumers
need (a flat, recursion-free row entry at a symbolic stabilizer index).

The recursion mirrors `rowSymTreeA_resolveA`, but the cell-kind dispatch is the
**object-logic** `SFormula.Deriv.boolCases` (no `by_cases` on a concrete `kv`),
exactly as in `recRowConvergeA` / `recEntryMasterD`.

Mechanism (`m + 1`):
* `rowSymTreeA (m+1) D.dT kT qT = recLeafTreeTA D.dT kT qT (sub₁ … sub₅)` where
  `subN = rowSymTreeA m (inner) (innerK) (innerQ)`.
* The five recursing inside-cells are flattened by the **IH**
  `rowSymTreeFlatBridgeSym m D.pred …` to `baseLeafTreeTA (inner)`.
* The remaining per-leaf self-similarity (`baseLeafTreeTA inner = outer leaf`) is
  the genuine SelfSim content — see the helper lemmas below. -/

/-! ### `recLeafTreeTA` leaf reductions (Deriv-level, re-derived locally)

Re-statements of the private `recLeaf*` reductions of
`SurfaceRowCharacterizationSymbolic.lean`, reducing `recLeafTreeTA … subs` to the
selected leaf given the cell guards as `SFormula.Deriv` premises.  Built directly
from the `*GuardTA` guard terms via `pauliIteSelectThen/Else`. -/

def recLeafIntS {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b true)))
    (hInside : SFormula.Deriv Γ (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b true))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (recLeafTreeTA dT kT qT pInt pTop pRight pLeft pBottom)) (SC.closed pInt)) :=
  SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectThen _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectThen _ _ _ hInterior)
      (SFormula.Deriv.pauliIteSelectThen _ _ _ hInside))

def recLeafIntIS {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b true)))
    (hInside : SFormula.Deriv Γ (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b false))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (recLeafTreeTA dT kT qT pInt pTop pRight pLeft pBottom))
        (SC.closed (.pauliLit Pauli.I))) :=
  SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectThen _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectThen _ _ _ hInterior)
      (SFormula.Deriv.pauliIteSelectElse _ _ _ hInside))

def recLeafTopS {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : SFormula.Deriv Γ (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b true)))
    (hInside : SFormula.Deriv Γ (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b true))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (recLeafTreeTA dT kT qT pInt pTop pRight pLeft pBottom)) (SC.closed pTop)) :=
  SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectThen _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectElse _ _ _ hInterior)
      (SFormula.Deriv.eqPauliTrans _ _ _
        (SFormula.Deriv.pauliIteSelectThen _ _ _ hTop)
        (SFormula.Deriv.pauliIteSelectThen _ _ _ hInside)))

def recLeafTopNIS {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : SFormula.Deriv Γ (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b true)))
    (hInside : SFormula.Deriv Γ (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b false))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (recLeafTreeTA dT kT qT pInt pTop pRight pLeft pBottom))
        (SC.closed (.ite (topOuterGuardTA dT kT qT) (.pauliLit Pauli.X) (.pauliLit Pauli.I)))) :=
  SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectThen _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectElse _ _ _ hInterior)
      (SFormula.Deriv.eqPauliTrans _ _ _
        (SFormula.Deriv.pauliIteSelectThen _ _ _ hTop)
        (SFormula.Deriv.pauliIteSelectElse _ _ _ hInside)))

def recLeafRightS {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : SFormula.Deriv Γ (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b false)))
    (hRight : SFormula.Deriv Γ (.eqBool (SC.closed (rightCellGuardTA dT kT)) (SC.b true)))
    (hInside : SFormula.Deriv Γ (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b true))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (recLeafTreeTA dT kT qT pInt pTop pRight pLeft pBottom)) (SC.closed pRight)) :=
  SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectThen _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectElse _ _ _ hInterior)
      (SFormula.Deriv.eqPauliTrans _ _ _
        (SFormula.Deriv.pauliIteSelectElse _ _ _ hTop)
        (SFormula.Deriv.eqPauliTrans _ _ _
          (SFormula.Deriv.pauliIteSelectThen _ _ _ hRight)
          (SFormula.Deriv.pauliIteSelectThen _ _ _ hInside))))

def recLeafRightNIS {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : SFormula.Deriv Γ (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b false)))
    (hRight : SFormula.Deriv Γ (.eqBool (SC.closed (rightCellGuardTA dT kT)) (SC.b true)))
    (hInside : SFormula.Deriv Γ (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b false))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (recLeafTreeTA dT kT qT pInt pTop pRight pLeft pBottom))
        (SC.closed (.ite (rightOuterGuardTA dT kT qT) (.pauliLit Pauli.Z) (.pauliLit Pauli.I)))) :=
  SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectThen _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectElse _ _ _ hInterior)
      (SFormula.Deriv.eqPauliTrans _ _ _
        (SFormula.Deriv.pauliIteSelectElse _ _ _ hTop)
        (SFormula.Deriv.eqPauliTrans _ _ _
          (SFormula.Deriv.pauliIteSelectThen _ _ _ hRight)
          (SFormula.Deriv.pauliIteSelectElse _ _ _ hInside))))

def recLeafLeftS {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : SFormula.Deriv Γ (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b false)))
    (hRight : SFormula.Deriv Γ (.eqBool (SC.closed (rightCellGuardTA dT kT)) (SC.b false)))
    (hLeft : SFormula.Deriv Γ (.eqBool (SC.closed (leftCellGuardTA dT kT)) (SC.b true)))
    (hInside : SFormula.Deriv Γ (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b true))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (recLeafTreeTA dT kT qT pInt pTop pRight pLeft pBottom)) (SC.closed pLeft)) :=
  SFormula.Deriv.eqPauliTrans _ _ _
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

def recLeafLeftNIS {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : SFormula.Deriv Γ (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b false)))
    (hRight : SFormula.Deriv Γ (.eqBool (SC.closed (rightCellGuardTA dT kT)) (SC.b false)))
    (hLeft : SFormula.Deriv Γ (.eqBool (SC.closed (leftCellGuardTA dT kT)) (SC.b true)))
    (hInside : SFormula.Deriv Γ (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b false))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (recLeafTreeTA dT kT qT pInt pTop pRight pLeft pBottom))
        (SC.closed (.ite (leftOuterGuardTA dT kT qT) (.pauliLit Pauli.Z) (.pauliLit Pauli.I)))) :=
  SFormula.Deriv.eqPauliTrans _ _ _
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

def recLeafBottomS {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : SFormula.Deriv Γ (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b false)))
    (hRight : SFormula.Deriv Γ (.eqBool (SC.closed (rightCellGuardTA dT kT)) (SC.b false)))
    (hLeft : SFormula.Deriv Γ (.eqBool (SC.closed (leftCellGuardTA dT kT)) (SC.b false)))
    (hBottom : SFormula.Deriv Γ (.eqBool (SC.closed (bottomCellGuardTA dT kT)) (SC.b true)))
    (hInside : SFormula.Deriv Γ (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b true))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (recLeafTreeTA dT kT qT pInt pTop pRight pLeft pBottom)) (SC.closed pBottom)) :=
  SFormula.Deriv.eqPauliTrans _ _ _
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

def recLeafBottomNIS {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
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
        (SC.closed (.ite (bottomOuterGuardTA dT kT qT) (.pauliLit Pauli.X) (.pauliLit Pauli.I)))) :=
  SFormula.Deriv.eqPauliTrans _ _ _
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

def recLeafFallbackS {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : SFormula.Deriv Γ (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b false)))
    (hRight : SFormula.Deriv Γ (.eqBool (SC.closed (rightCellGuardTA dT kT)) (SC.b false)))
    (hLeft : SFormula.Deriv Γ (.eqBool (SC.closed (leftCellGuardTA dT kT)) (SC.b false)))
    (hBottom : SFormula.Deriv Γ (.eqBool (SC.closed (bottomCellGuardTA dT kT)) (SC.b false))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (recLeafTreeTA dT kT qT pInt pTop pRight pLeft pBottom))
        (SC.closed (baseLeafTreeTA dT kT qT))) :=
  SFormula.Deriv.eqPauliTrans _ _ _
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

def recLeafBoundaryS {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (recLeafTreeTA dT kT qT pInt pTop pRight pLeft pBottom))
        (SC.closed (baseLeafTreeTA dT kT qT))) :=
  SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk

/-! ### `baseLeafTreeTA` leaf reductions (Deriv-level, re-derived locally)

Re-statements of the private `leaf*` reductions, reducing `baseLeafTreeTA dT kT qT`
to its selected leaf given the cell-class / band guards as `SFormula.Deriv`
premises.  Built directly via `pauliIteSelectThen/Else`. -/

def baseLeafZS {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hBand : SFormula.Deriv Γ (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)))
    (hKind : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b true))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.closed (.pauliLit Pauli.Z))) :=
  SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectThen _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectThen _ _ _ hBand)
      (SFormula.Deriv.pauliIteSelectThen _ _ _ hKind))

def baseLeafXS {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hBand : SFormula.Deriv Γ (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)))
    (hKind : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b false))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.closed (.pauliLit Pauli.X))) :=
  SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectThen _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectThen _ _ _ hBand)
      (SFormula.Deriv.pauliIteSelectElse _ _ _ hKind))

def baseLeafBulkIS {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hBand : SFormula.Deriv Γ (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.closed (.pauliLit Pauli.I))) :=
  SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectThen _ _ _ hBulk)
    (SFormula.Deriv.pauliIteSelectElse _ _ _ hBand)

/-! #### Boundary-strip `baseLeafTreeTA` reducers (the not-bulk else branch).

When `bulkGuardTA = false` the flat classifier enters its four-strip else branch:
`ite topClass (ite topBand X I) (ite rightClass (ite rightBand Z I) (ite leftClass
(ite leftBand Z I) (ite bottomBand X I)))`.  Each reducer below selects the matching
strip + band branch, given the cell-class and band guards as `Deriv` premises.  Used
to reduce the INNER `baseLeafTreeTA` (whose mapped index is a boundary cell of the
inner code) to its strip literal in the boundary `flatStep*` leaves. -/

def baseLeafTopXS {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b true)))
    (hTopBand : SFormula.Deriv Γ (.eqBool (SC.closed (topBandGuardTA dT kT qT)) (SC.b true))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.closed (.pauliLit Pauli.X))) :=
  SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectThen _ _ _ hTopClass)
      (SFormula.Deriv.pauliIteSelectThen _ _ _ hTopBand))

def baseLeafTopIS {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b true)))
    (hTopBand : SFormula.Deriv Γ (.eqBool (SC.closed (topBandGuardTA dT kT qT)) (SC.b false))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.closed (.pauliLit Pauli.I))) :=
  SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectThen _ _ _ hTopClass)
      (SFormula.Deriv.pauliIteSelectElse _ _ _ hTopBand))

def baseLeafRightZS {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false)))
    (hRightClass : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b true)))
    (hRightBand : SFormula.Deriv Γ (.eqBool (SC.closed (rightBandGuardTA dT kT qT)) (SC.b true))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.closed (.pauliLit Pauli.Z))) :=
  SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectElse _ _ _ hTopClass)
      (SFormula.Deriv.eqPauliTrans _ _ _
        (SFormula.Deriv.pauliIteSelectThen _ _ _ hRightClass)
        (SFormula.Deriv.pauliIteSelectThen _ _ _ hRightBand)))

def baseLeafRightIS {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false)))
    (hRightClass : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b true)))
    (hRightBand : SFormula.Deriv Γ (.eqBool (SC.closed (rightBandGuardTA dT kT qT)) (SC.b false))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.closed (.pauliLit Pauli.I))) :=
  SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectElse _ _ _ hTopClass)
      (SFormula.Deriv.eqPauliTrans _ _ _
        (SFormula.Deriv.pauliIteSelectThen _ _ _ hRightClass)
        (SFormula.Deriv.pauliIteSelectElse _ _ _ hRightBand)))

def baseLeafLeftZS {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false)))
    (hRightClass : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b false)))
    (hLeftClass : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA dT kT)) (SC.b true)))
    (hLeftBand : SFormula.Deriv Γ (.eqBool (SC.closed (leftBandGuardTA dT kT qT)) (SC.b true))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.closed (.pauliLit Pauli.Z))) :=
  SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectElse _ _ _ hTopClass)
      (SFormula.Deriv.eqPauliTrans _ _ _
        (SFormula.Deriv.pauliIteSelectElse _ _ _ hRightClass)
        (SFormula.Deriv.eqPauliTrans _ _ _
          (SFormula.Deriv.pauliIteSelectThen _ _ _ hLeftClass)
          (SFormula.Deriv.pauliIteSelectThen _ _ _ hLeftBand))))

def baseLeafLeftIS {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false)))
    (hRightClass : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b false)))
    (hLeftClass : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA dT kT)) (SC.b true)))
    (hLeftBand : SFormula.Deriv Γ (.eqBool (SC.closed (leftBandGuardTA dT kT qT)) (SC.b false))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.closed (.pauliLit Pauli.I))) :=
  SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectElse _ _ _ hTopClass)
      (SFormula.Deriv.eqPauliTrans _ _ _
        (SFormula.Deriv.pauliIteSelectElse _ _ _ hRightClass)
        (SFormula.Deriv.eqPauliTrans _ _ _
          (SFormula.Deriv.pauliIteSelectThen _ _ _ hLeftClass)
          (SFormula.Deriv.pauliIteSelectElse _ _ _ hLeftBand))))

def baseLeafBottomXS {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false)))
    (hRightClass : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b false)))
    (hLeftClass : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA dT kT)) (SC.b false)))
    (hBottomBand : SFormula.Deriv Γ (.eqBool (SC.closed (bottomBandGuardTA dT kT qT)) (SC.b true))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.closed (.pauliLit Pauli.X))) :=
  SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectElse _ _ _ hTopClass)
      (SFormula.Deriv.eqPauliTrans _ _ _
        (SFormula.Deriv.pauliIteSelectElse _ _ _ hRightClass)
        (SFormula.Deriv.eqPauliTrans _ _ _
          (SFormula.Deriv.pauliIteSelectElse _ _ _ hLeftClass)
          (SFormula.Deriv.pauliIteSelectThen _ _ _ hBottomBand))))

def baseLeafBottomIS {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false)))
    (hRightClass : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b false)))
    (hLeftClass : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA dT kT)) (SC.b false)))
    (hBottomBand : SFormula.Deriv Γ (.eqBool (SC.closed (bottomBandGuardTA dT kT qT)) (SC.b false))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.closed (.pauliLit Pauli.I))) :=
  SFormula.Deriv.eqPauliTrans _ _ _
    (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _
      (SFormula.Deriv.pauliIteSelectElse _ _ _ hTopClass)
      (SFormula.Deriv.eqPauliTrans _ _ _
        (SFormula.Deriv.pauliIteSelectElse _ _ _ hRightClass)
        (SFormula.Deriv.eqPauliTrans _ _ _
          (SFormula.Deriv.pauliIteSelectElse _ _ _ hLeftClass)
          (SFormula.Deriv.pauliIteSelectElse _ _ _ hBottomBand))))

/-! ### Nat-level inner↔outer classifier-guard correspondences

The genuine SelfSim content of the symbolic flat bridge, isolated at the `Nat`
level (full `omega`/`simp` power).  Under each cell-kind + inside context at
distance `d = 2M+3` (so the inner code is `2M+1`), the inner flat classifier's
guard `Val`s correspond to the outer ones.  These restate the internal `hKind` /
`hBand` / bulk facts of `SurfaceSelfSimNat.lean` as standalone Nat lemmas, used by
the object-level leaves below via `arithBool` implications.

The interior block: inner is bulk, inner band-membership = outer band-membership,
inner kind = outer kind. -/

/-- `a * n + b < n * n` whenever `a < n` and `b < n` (local copy of the private
grid-linearization bound in `SurfaceSelfSimNat.lean`). -/
private theorem cellLinIndexLt' {a b n : Nat} (ha : a < n) (hb : b < n) :
    a * n + b < n * n := by
  have h1 : a + 1 ≤ n := ha
  have h2 : (a + 1) * n ≤ n * n := Nat.mul_le_mul_right _ h1
  have h3 : a * n + n = (a + 1) * n := by rw [Nat.succ_mul]
  omega

/-- Interior: the inner interior cell is a bulk cell of the inner `2M+1` code. -/
private theorem interiorInnerBulkNat (M k q : Nat)
    (hI : isInteriorCell (2*M+3) k = true)
    (hIn : isInside (2*M+3) q = true) :
    decide (innerInteriorK (2*M+3) k < (2*M+1-1)*(2*M+1-1)) = true := by
  simp only [isInteriorCell, cellLastCell, cellR, cellC, Bool.and_eq_true,
    decide_eq_true_eq] at hI
  obtain ⟨hr1, hr2, hc1, hc2⟩ := hI
  simp only [show 2 * M + 3 - 1 = 2 * M + 2 from by omega,
      show 2 * M + 2 - 1 = 2 * M + 1 from by omega] at hr1 hr2 hc1 hc2
  simp only [innerInteriorK, cellR, cellC, show 2 * M + 3 - 1 = 2 * M + 2 from by omega,
    show 2 * M + 3 - 2 - 1 = 2 * M from by omega, show 2 * M + 1 - 1 = 2 * M from by omega,
    decide_eq_true_eq]
  exact cellLinIndexLt' (by omega) (by omega)

/-- Interior: inner band-membership equals outer band-membership. -/
private theorem interiorBandCorrNat (M k q : Nat)
    (hI : isInteriorCell (2*M+3) k = true)
    (hIn : isInside (2*M+3) q = true) :
    baseBulkBandVal (2*M+1) (innerInteriorK (2*M+3) k) (innerQval (2*M+3) q)
      = baseBulkBandVal (2*M+3) k q := by
  simp only [isInteriorCell, isInside, cellLastCell, cellR, cellC, cellRow, cellCol,
    Bool.and_eq_true, decide_eq_true_eq] at hI hIn
  obtain ⟨hr1, hr2, hc1, hc2⟩ := hI
  obtain ⟨hrow1, hrow2, hcol1, hcol2⟩ := hIn
  simp only [show 2 * M + 3 - 1 = 2 * M + 2 from by omega,
      show 2 * M + 2 - 1 = 2 * M + 1 from by omega] at hr1 hr2 hc1 hc2 hrow2 hcol2
  set r := k / (2 * M + 2) with hr
  set c := k % (2 * M + 2) with hc
  set row := q / (2 * M + 3) with hrowdef
  set col := q % (2 * M + 3) with hcoldef
  have hK : innerInteriorK (2 * M + 3) k = (r - 1) * (2 * M) + (c - 1) := by
    unfold innerInteriorK
    simp only [cellR, cellC, show 2 * M + 3 - 1 = 2 * M + 2 from by omega,
      show 2 * M + 3 - 2 - 1 = 2 * M from by omega, ← hr, ← hc]
  have hQ : innerQval (2 * M + 3) q = (row - 1) * (2 * M + 1) + (col - 1) := by
    unfold innerQval
    simp only [cellRow, cellCol, show 2 * M + 3 - 2 = 2 * M + 1 from by omega,
      ← hrowdef, ← hcoldef]
  rw [hK, hQ]
  have hKR : ((r - 1) * (2 * M) + (c - 1)) / (2 * M) = r - 1 := by
    rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), Nat.add_zero]
  have hKC : ((r - 1) * (2 * M) + (c - 1)) % (2 * M) = c - 1 := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  have hQR : ((row - 1) * (2 * M + 1) + (col - 1)) / (2 * M + 1) = row - 1 := by
    rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), Nat.add_zero]
  have hQC : ((row - 1) * (2 * M + 1) + (col - 1)) % (2 * M + 1) = col - 1 := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  have hKbulk : (r - 1) * (2 * M) + (c - 1) < 2 * M * (2 * M) :=
    cellLinIndexLt' (by omega) (by omega)
  have hkbulk : k < (2 * M + 2) * (2 * M + 2) := by
    have hk : k = r * (2 * M + 2) + c := by
      rw [hr, hc, Nat.mul_comm]; exact (Nat.div_add_mod k (2 * M + 2)).symm
    rw [hk]
    exact cellLinIndexLt' (by omega) (by omega)
  unfold baseBulkBandVal
  simp only [cellRow, cellCol, cellR, cellC,
    show 2 * M + 1 - 1 = 2 * M from by omega,
    show 2 * M + 3 - 1 = 2 * M + 2 from by omega,
    hKR, hKC, hQR, hQC, ← hr, ← hc, ← hrowdef, ← hcoldef]
  simp only [show (row - 1 = r - 1) = (row = r) from by simp only [eq_iff_iff]; omega,
      show (row - 1 = r - 1 + 1) = (row = r + 1) from by simp only [eq_iff_iff]; omega,
      show (col - 1 = c - 1) = (col = c) from by simp only [eq_iff_iff]; omega,
      show (col - 1 = c - 1 + 1) = (col = c + 1) from by simp only [eq_iff_iff]; omega,
      decide_eq_true hKbulk, decide_eq_true hkbulk]

/-- Interior: inner kind equals outer kind (parity preserved). -/
private theorem interiorKindCorrNat (M k q : Nat)
    (hI : isInteriorCell (2*M+3) k = true)
    (hIn : isInside (2*M+3) q = true) :
    baseKindVal (2*M+1) (innerInteriorK (2*M+3) k) = baseKindVal (2*M+3) k := by
  simp only [isInteriorCell, cellLastCell, cellR, cellC, Bool.and_eq_true,
    decide_eq_true_eq] at hI
  obtain ⟨hr1, hr2, hc1, hc2⟩ := hI
  simp only [show 2 * M + 3 - 1 = 2 * M + 2 from by omega,
      show 2 * M + 2 - 1 = 2 * M + 1 from by omega] at hr1 hr2 hc1 hc2
  set r := k / (2 * M + 2) with hr
  set c := k % (2 * M + 2) with hc
  have hK : innerInteriorK (2 * M + 3) k = (r - 1) * (2 * M) + (c - 1) := by
    unfold innerInteriorK
    simp only [cellR, cellC, show 2 * M + 3 - 1 = 2 * M + 2 from by omega,
      show 2 * M + 3 - 2 - 1 = 2 * M from by omega, ← hr, ← hc]
  rw [hK]
  have hKR : ((r - 1) * (2 * M) + (c - 1)) / (2 * M) = r - 1 := by
    rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), Nat.add_zero]
  have hKC : ((r - 1) * (2 * M) + (c - 1)) % (2 * M) = c - 1 := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  unfold baseKindVal
  simp only [cellR, cellC, show 2 * M + 1 - 1 = 2 * M from by omega,
    show 2 * M + 3 - 1 = 2 * M + 2 from by omega, hKR, hKC, ← hr, ← hc]
  have hpar : (r - 1 + (c - 1)) % 2 = (r + c) % 2 := by omega
  rw [hpar]

/-! ### Top promoted-boundary inner↔outer correspondences

Under the top-cell ∧ inside context at distance `d = 2M+3`, the mapped inner index
`innerTopK` is a boundary (top-strip) cell of the inner `2M+1` code, NOT a bulk cell.
So the inner flat classifier reduces through `bulkGuardTA inner = false`,
`topClassGuardTA inner = true`, `ite (topBandGuardTA inner) X I`; the outer through
`baseBulkBandGuardTA outer`, `baseKindGuardTA outer` (= false, since a top cell is
X-kind).  The four facts below pin those values; all extracted from `topSelfSimNat`'s
internal computation. -/

/-- Top context: extract `r = 0`, `c = 2tb+1`, `tb < M`, `1 ≤ row,col < 2M+2`,
where `tb = (c-1)/2`, `c = k % (2M+2)`, `row = q/(2M+3)`, `col = q%(2M+3)`. -/
private theorem topCtx (M k q : Nat)
    (hT : isTopCell (2*M+3) k = true) (hIn : isInside (2*M+3) q = true) :
    k / (2*M+2) = 0 ∧ k % (2*M+2) = 2*((k % (2*M+2) - 1)/2) + 1 ∧
      (k % (2*M+2) - 1)/2 < M ∧ k = k % (2*M+2) ∧
      1 ≤ q / (2*M+3) ∧ q / (2*M+3) < 2*M+2 ∧ 1 ≤ q % (2*M+3) ∧ q % (2*M+3) < 2*M+2 := by
  simp only [isTopCell, isInside, cellInnerHalf, cellR, cellC, cellRow, cellCol,
    Bool.and_eq_true, decide_eq_true_eq] at hT hIn
  obtain ⟨hr0, hcEq, htb⟩ := hT
  obtain ⟨hrow1, hrow2, hcol1, hcol2⟩ := hIn
  simp only [show 2 * M + 3 - 1 = 2 * M + 2 from by omega,
      show 2 * M + 3 - 2 = 2 * M + 1 from by omega,
      show 2 * M + 1 - 1 = 2 * M from by omega] at hr0 hcEq htb hrow2 hcol2
  have hklt : k < 2 * M + 2 := by
    have := (Nat.div_eq_zero_iff (a := k) (b := 2 * M + 2)).mp hr0; omega
  have htbm : (k % (2*M+2) - 1)/2 < M := by
    rw [Nat.mul_div_cancel_left M (by omega : 0 < 2)] at htb; exact htb
  exact ⟨hr0, hcEq, htbm, (Nat.mod_eq_of_lt hklt).symm, hrow1, hrow2, hcol1, hcol2⟩

/-- Top: inner index is NOT bulk (`bulkGuardTA inner = false`). -/
private theorem topInnerBulkFalseNat (M k q : Nat)
    (hT : isTopCell (2*M+3) k = true) (hIn : isInside (2*M+3) q = true) :
    decide (innerTopK (2*M+3) k < (2*M+1-1)*(2*M+1-1)) = false := by
  obtain ⟨hr0, hcEq, htbm, hkc, _, _, _, _⟩ := topCtx M k q hT hIn
  simp only [innerTopK, cellC, show 2 * M + 3 - 2 - 1 = 2 * M from by omega,
    show 2 * M + 3 - 1 = 2 * M + 2 from by omega, show 2 * M + 1 - 1 = 2 * M from by omega,
    decide_eq_false_iff_not, Nat.not_lt]
  omega

/-- Top: inner index is in the top class of the inner code (`topClassVal inner = true`). -/
private theorem topInnerClassTrueNat (M k q : Nat)
    (hT : isTopCell (2*M+3) k = true) (hIn : isInside (2*M+3) q = true) :
    topClassVal (2*M+1) (innerTopK (2*M+3) k) = true := by
  obtain ⟨hr0, hcEq, htbm, hkc, _, _, _, _⟩ := topCtx M k q hT hIn
  simp only [topClassVal, innerTopK, cellC, show 2 * M + 3 - 2 - 1 = 2 * M from by omega,
    show 2 * M + 3 - 1 = 2 * M + 2 from by omega, show 2 * M + 1 - 1 = 2 * M from by omega,
    decide_eq_true_eq]
  omega

/-- Top: a top cell has odd `r+c` parity, so the outer bulk kind is `X`
(`baseKindVal outer = false`). -/
private theorem topKindFalseNat (M k q : Nat)
    (hT : isTopCell (2*M+3) k = true) (hIn : isInside (2*M+3) q = true) :
    baseKindVal (2*M+3) k = false := by
  obtain ⟨hr0, hcEq, htbm, hkc, _, _, _, _⟩ := topCtx M k q hT hIn
  simp only [baseKindVal, cellR, cellC, show 2 * M + 3 - 1 = 2 * M + 2 from by omega,
    hr0, decide_eq_false_iff_not]
  omega

/-- Top: inner top band membership equals outer bulk band membership. -/
private theorem topBandCorrNat (M k q : Nat)
    (hT : isTopCell (2*M+3) k = true) (hIn : isInside (2*M+3) q = true) :
    topBandVal (2*M+1) (innerTopK (2*M+3) k) (innerQval (2*M+3) q)
      = baseBulkBandVal (2*M+3) k q := by
  obtain ⟨hr0, hcEq, htbm, hkc, hrow1, hrow2, hcol1, hcol2⟩ := topCtx M k q hT hIn
  set c := k % (2 * M + 2) with hc
  set row := q / (2 * M + 3) with hrowdef
  set col := q % (2 * M + 3) with hcoldef
  set tb := (c - 1) / 2 with htbdef
  have hK : innerTopK (2 * M + 3) k = 2 * M * (2 * M) + tb := by
    simp only [innerTopK, cellC, show 2 * M + 3 - 2 - 1 = 2 * M from by omega,
      show 2 * M + 3 - 1 = 2 * M + 2 from by omega, ← hc, ← htbdef]
  have hQ : innerQval (2 * M + 3) q = (row - 1) * (2 * M + 1) + (col - 1) := by
    simp only [innerQval, cellRow, cellCol, show 2 * M + 3 - 2 = 2 * M + 1 from by omega,
      ← hrowdef, ← hcoldef]
  rw [hK, hQ]
  have hQR : ((row - 1) * (2 * M + 1) + (col - 1)) / (2 * M + 1) = row - 1 := by
    rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), Nat.add_zero]
  have hQC : ((row - 1) * (2 * M + 1) + (col - 1)) % (2 * M + 1) = col - 1 := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  have hk'lt : 2 * M * (2 * M) + tb < (2 * M + 1) * (2 * M + 1) - 1 := by
    have h2 : (2 * M + 1) * (2 * M + 1) = 2 * M * (2 * M) + 2 * M + (2 * M + 1) := by
      rw [Nat.add_one_mul, Nat.mul_add_one]
    omega
  have hkbulk : k < (2 * M + 2) * (2 * M + 2) := by
    have h2 : 2 * M + 2 ≤ (2 * M + 2) * (2 * M + 2) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hbprime : (2 * M * (2 * M) + tb) - (2 * M + 1 - 1) * (2 * M + 1 - 1) = tb := by
    simp only [show 2 * M + 1 - 1 = 2 * M from by omega]; omega
  simp only [topBandVal, baseBulkBandVal, cellRow, cellCol, cellR, cellC,
    show 2 * M + 1 - 1 = 2 * M from by omega, show 2 * M + 3 - 1 = 2 * M + 2 from by omega,
    hQR, hQC, hr0, ← hc, hcEq, ← hrowdef, ← hcoldef,
    decide_eq_true hk'lt, decide_eq_true hkbulk, Bool.true_and, Bool.and_true]
  simp only [show 2 * M * (2 * M) + tb - 2 * M * (2 * M) = tb from by omega]
  simp only [show (row - 1 = 0) = (row = 1) from by simp only [eq_iff_iff]; omega,
      show (col - 1 = 2 * tb) = (col = 2 * tb + 1) from by simp only [eq_iff_iff]; omega,
      show (col - 1 = 2 * tb + 1) = (col = 2 * tb + 1 + 1) from by simp only [eq_iff_iff]; omega,
      show (row = 0) = False from eq_false (by omega),
      show (row = 0 + 1) = (row = 1) from by simp only [Nat.zero_add],
      decide_false, Bool.false_or]

/-! ### Right promoted-boundary inner↔outer correspondences (from `rightSelfSimNat`). -/

/-- Right context: `c = 2M+1`, `r = 2rb+1`, `rb < M`, `1 ≤ row,col < 2M+2`. -/
private theorem rightCtx (M k q : Nat)
    (hR : isRightCell (2*M+3) k = true) (hIn : isInside (2*M+3) q = true) :
    k % (2*M+2) = 2*M+1 ∧ k / (2*M+2) = 2*((k / (2*M+2) - 1)/2) + 1 ∧
      (k / (2*M+2) - 1)/2 < M ∧ k = k / (2*M+2) * (2*M+2) + k % (2*M+2) ∧
      1 ≤ q / (2*M+3) ∧ q / (2*M+3) < 2*M+2 ∧ 1 ≤ q % (2*M+3) ∧ q % (2*M+3) < 2*M+2 := by
  simp only [isRightCell, isInside, cellLastCell, cellInnerHalf, cellR, cellC, cellRow, cellCol,
    Bool.and_eq_true, decide_eq_true_eq] at hR hIn
  obtain ⟨hcEq, hrEq, hrb⟩ := hR
  obtain ⟨hrow1, hrow2, hcol1, hcol2⟩ := hIn
  simp only [show 2 * M + 3 - 1 = 2 * M + 2 from by omega,
      show 2 * M + 3 - 2 = 2 * M + 1 from by omega,
      show 2 * M + 1 - 1 = 2 * M from by omega] at hcEq hrEq hrb hrow2 hcol2
  have hrbm : (k / (2*M+2) - 1)/2 < M := by
    rw [Nat.mul_div_cancel_left M (by omega : 0 < 2)] at hrb; exact hrb
  have hkdm : k = k / (2*M+2) * (2*M+2) + k % (2*M+2) := by
    rw [Nat.mul_comm]; exact (Nat.div_add_mod k (2 * M + 2)).symm
  exact ⟨by omega, hrEq, hrbm, hkdm, hrow1, hrow2, hcol1, hcol2⟩

private theorem rightInnerBulkFalseNat (M k q : Nat)
    (hR : isRightCell (2*M+3) k = true) (hIn : isInside (2*M+3) q = true) :
    decide (innerRightK (2*M+3) k < (2*M+1-1)*(2*M+1-1)) = false := by
  obtain ⟨hcEq, hrEq, hrbm, _, _, _, _, _⟩ := rightCtx M k q hR hIn
  simp only [innerRightK, cellR, cellInnerHalf, show 2 * M + 3 - 2 = 2 * M + 1 from by omega,
    show 2 * M + 1 - 1 = 2 * M from by omega, show 2 * M + 3 - 1 = 2 * M + 2 from by omega,
    Nat.mul_div_cancel_left M (by omega : 0 < 2), decide_eq_false_iff_not, Nat.not_lt]
  omega

private theorem rightInnerTopClassFalseNat (M k q : Nat)
    (hR : isRightCell (2*M+3) k = true) (hIn : isInside (2*M+3) q = true) :
    topClassVal (2*M+1) (innerRightK (2*M+3) k) = false := by
  obtain ⟨hcEq, hrEq, hrbm, _, _, _, _, _⟩ := rightCtx M k q hR hIn
  simp only [topClassVal, innerRightK, cellR, cellInnerHalf,
    show 2 * M + 3 - 2 = 2 * M + 1 from by omega, show 2 * M + 1 - 1 = 2 * M from by omega,
    show 2 * M + 3 - 1 = 2 * M + 2 from by omega, Nat.mul_div_cancel_left M (by omega : 0 < 2),
    decide_eq_false_iff_not, Nat.not_lt]
  omega

private theorem rightInnerClassTrueNat (M k q : Nat)
    (hR : isRightCell (2*M+3) k = true) (hIn : isInside (2*M+3) q = true) :
    rightClassVal (2*M+1) (innerRightK (2*M+3) k) = true := by
  obtain ⟨hcEq, hrEq, hrbm, _, _, _, _, _⟩ := rightCtx M k q hR hIn
  simp only [rightClassVal, innerRightK, cellR, cellInnerHalf,
    show 2 * M + 3 - 2 = 2 * M + 1 from by omega, show 2 * M + 1 - 1 = 2 * M from by omega,
    show 2 * M + 3 - 1 = 2 * M + 2 from by omega, Nat.mul_div_cancel_left M (by omega : 0 < 2),
    decide_eq_true_eq]
  omega

private theorem rightKindTrueNat (M k q : Nat)
    (hR : isRightCell (2*M+3) k = true) (hIn : isInside (2*M+3) q = true) :
    baseKindVal (2*M+3) k = true := by
  obtain ⟨hcEq, hrEq, hrbm, _, _, _, _, _⟩ := rightCtx M k q hR hIn
  simp only [baseKindVal, cellR, cellC, show 2 * M + 3 - 1 = 2 * M + 2 from by omega,
    decide_eq_true_eq]
  omega

private theorem rightBandCorrNat (M k q : Nat)
    (hR : isRightCell (2*M+3) k = true) (hIn : isInside (2*M+3) q = true) :
    rightBandVal (2*M+1) (innerRightK (2*M+3) k) (innerQval (2*M+3) q)
      = baseBulkBandVal (2*M+3) k q := by
  obtain ⟨hcEq, hrEq, hrbm, hkdm, hrow1, hrow2, hcol1, hcol2⟩ := rightCtx M k q hR hIn
  set r := k / (2 * M + 2) with hr
  set row := q / (2 * M + 3) with hrowdef
  set col := q % (2 * M + 3) with hcoldef
  set rb := (r - 1) / 2 with hrbdef
  have hK : innerRightK (2 * M + 3) k = 2 * M * (2 * M) + (M + rb) := by
    simp only [innerRightK, cellR, cellInnerHalf, show 2 * M + 3 - 2 = 2 * M + 1 from by omega,
      show 2 * M + 1 - 1 = 2 * M from by omega, show 2 * M + 3 - 1 = 2 * M + 2 from by omega,
      ← hr, ← hrbdef, Nat.mul_div_cancel_left M (by omega : 0 < 2)]
  have hQ : innerQval (2 * M + 3) q = (row - 1) * (2 * M + 1) + (col - 1) := by
    simp only [innerQval, cellRow, cellCol, show 2 * M + 3 - 2 = 2 * M + 1 from by omega,
      ← hrowdef, ← hcoldef]
  rw [hK, hQ]
  have hQR : ((row - 1) * (2 * M + 1) + (col - 1)) / (2 * M + 1) = row - 1 := by
    rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), Nat.add_zero]
  have hQC : ((row - 1) * (2 * M + 1) + (col - 1)) % (2 * M + 1) = col - 1 := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  have hkbulk : k < (2 * M + 2) * (2 * M + 2) := by
    rw [hkdm, hcEq]; exact cellLinIndexLt' (by omega) (by omega)
  have hbprime : (2 * M * (2 * M) + (M + rb)) - (2 * M + 1 - 1) * (2 * M + 1 - 1) = M + rb := by
    simp only [show 2 * M + 1 - 1 = 2 * M from by omega]; omega
  have hhalf : (2 * M + 1 - 1) / 2 = M := by
    simp only [show 2 * M + 1 - 1 = 2 * M from by omega, Nat.mul_div_cancel_left M (by omega : 0 < 2)]
  have hbbR : M + rb - (2 * M + 1 - 1)/2 = rb := by rw [hhalf]; omega
  simp only [rightBandVal, baseBulkBandVal, cellRow, cellCol, cellR, cellC,
    show 2 * M + 3 - 1 = 2 * M + 2 from by omega,
    hQR, hQC, ← hr, hcEq, ← hrowdef, ← hcoldef, hbprime, hbbR,
    decide_eq_true hkbulk, Bool.and_true]
  rw [show 2 * M + 1 - 1 = 2 * M from by omega, hrEq]
  simp only [show (col - 1 = 2 * M) = (col = 2 * M + 1) from by simp only [eq_iff_iff]; omega,
      show (row - 1 = 2 * rb) = (row = 2 * rb + 1) from by simp only [eq_iff_iff]; omega,
      show (row - 1 = 2 * rb + 1) = (row = 2 * rb + 1 + 1) from by simp only [eq_iff_iff]; omega,
      show (col = 2 * M + 1 + 1) = False from eq_false (by omega),
      decide_false, Bool.or_false, Bool.and_comm]

/-! ### Left promoted-boundary inner↔outer correspondences (from `leftSelfSimNat`). -/

/-- Left context: `c = 0`, `r = 2lb+2`, `lb < M`, `1 ≤ row,col < 2M+2`. -/
private theorem leftCtx (M k q : Nat)
    (hL : isLeftCell (2*M+3) k = true) (hIn : isInside (2*M+3) q = true) :
    k % (2*M+2) = 0 ∧ k / (2*M+2) = 2*((k / (2*M+2) - 2)/2) + 2 ∧
      (k / (2*M+2) - 2)/2 < M ∧ k = k / (2*M+2) * (2*M+2) + k % (2*M+2) ∧
      1 ≤ q / (2*M+3) ∧ q / (2*M+3) < 2*M+2 ∧ 1 ≤ q % (2*M+3) ∧ q % (2*M+3) < 2*M+2 := by
  simp only [isLeftCell, isInside, cellInnerHalf, cellR, cellC, cellRow, cellCol,
    Bool.and_eq_true, decide_eq_true_eq] at hL hIn
  obtain ⟨hcEq, hrEq, hlb⟩ := hL
  obtain ⟨hrow1, hrow2, hcol1, hcol2⟩ := hIn
  simp only [show 2 * M + 3 - 1 = 2 * M + 2 from by omega,
      show 2 * M + 3 - 2 = 2 * M + 1 from by omega,
      show 2 * M + 1 - 1 = 2 * M from by omega] at hcEq hrEq hlb hrow2 hcol2
  have hlbm : (k / (2*M+2) - 2)/2 < M := by
    rw [Nat.mul_div_cancel_left M (by omega : 0 < 2)] at hlb; exact hlb
  have hkdm : k = k / (2*M+2) * (2*M+2) + k % (2*M+2) := by
    rw [Nat.mul_comm]; exact (Nat.div_add_mod k (2 * M + 2)).symm
  exact ⟨hcEq, hrEq, hlbm, hkdm, hrow1, hrow2, hcol1, hcol2⟩

private theorem leftInnerBulkFalseNat (M k q : Nat)
    (hL : isLeftCell (2*M+3) k = true) (hIn : isInside (2*M+3) q = true) :
    decide (innerLeftK (2*M+3) k < (2*M+1-1)*(2*M+1-1)) = false := by
  obtain ⟨hcEq, hrEq, hlbm, _, _, _, _, _⟩ := leftCtx M k q hL hIn
  simp only [innerLeftK, cellR, cellInnerHalf, show 2 * M + 3 - 2 = 2 * M + 1 from by omega,
    show 2 * M + 1 - 1 = 2 * M from by omega, show 2 * M + 3 - 1 = 2 * M + 2 from by omega,
    Nat.mul_div_cancel_left M (by omega : 0 < 2), decide_eq_false_iff_not, Nat.not_lt]
  omega

private theorem leftInnerTopClassFalseNat (M k q : Nat)
    (hL : isLeftCell (2*M+3) k = true) (hIn : isInside (2*M+3) q = true) :
    topClassVal (2*M+1) (innerLeftK (2*M+3) k) = false := by
  obtain ⟨hcEq, hrEq, hlbm, _, _, _, _, _⟩ := leftCtx M k q hL hIn
  simp only [topClassVal, innerLeftK, cellR, cellInnerHalf,
    show 2 * M + 3 - 2 = 2 * M + 1 from by omega, show 2 * M + 1 - 1 = 2 * M from by omega,
    show 2 * M + 3 - 1 = 2 * M + 2 from by omega, Nat.mul_div_cancel_left M (by omega : 0 < 2),
    decide_eq_false_iff_not, Nat.not_lt]
  omega

private theorem leftInnerRightClassFalseNat (M k q : Nat)
    (hL : isLeftCell (2*M+3) k = true) (hIn : isInside (2*M+3) q = true) :
    rightClassVal (2*M+1) (innerLeftK (2*M+3) k) = false := by
  obtain ⟨hcEq, hrEq, hlbm, _, _, _, _, _⟩ := leftCtx M k q hL hIn
  simp only [rightClassVal, innerLeftK, cellR, cellInnerHalf,
    show 2 * M + 3 - 2 = 2 * M + 1 from by omega, show 2 * M + 1 - 1 = 2 * M from by omega,
    show 2 * M + 3 - 1 = 2 * M + 2 from by omega, Nat.mul_div_cancel_left M (by omega : 0 < 2),
    decide_eq_false_iff_not, Nat.not_lt]
  omega

private theorem leftInnerClassTrueNat (M k q : Nat)
    (hL : isLeftCell (2*M+3) k = true) (hIn : isInside (2*M+3) q = true) :
    leftClassVal (2*M+1) (innerLeftK (2*M+3) k) = true := by
  obtain ⟨hcEq, hrEq, hlbm, _, _, _, _, _⟩ := leftCtx M k q hL hIn
  simp only [leftClassVal, innerLeftK, cellR, cellInnerHalf,
    show 2 * M + 3 - 2 = 2 * M + 1 from by omega, show 2 * M + 1 - 1 = 2 * M from by omega,
    show 2 * M + 3 - 1 = 2 * M + 2 from by omega, Nat.mul_div_cancel_left M (by omega : 0 < 2),
    decide_eq_true_eq]
  omega

private theorem leftKindTrueNat (M k q : Nat)
    (hL : isLeftCell (2*M+3) k = true) (hIn : isInside (2*M+3) q = true) :
    baseKindVal (2*M+3) k = true := by
  obtain ⟨hcEq, hrEq, hlbm, _, _, _, _, _⟩ := leftCtx M k q hL hIn
  simp only [baseKindVal, cellR, cellC, show 2 * M + 3 - 1 = 2 * M + 2 from by omega,
    hcEq, decide_eq_true_eq]
  omega

private theorem leftBandCorrNat (M k q : Nat)
    (hL : isLeftCell (2*M+3) k = true) (hIn : isInside (2*M+3) q = true) :
    leftBandVal (2*M+1) (innerLeftK (2*M+3) k) (innerQval (2*M+3) q)
      = baseBulkBandVal (2*M+3) k q := by
  obtain ⟨hcEq, hrEq, hlbm, hkdm, hrow1, hrow2, hcol1, hcol2⟩ := leftCtx M k q hL hIn
  set r := k / (2 * M + 2) with hr
  set row := q / (2 * M + 3) with hrowdef
  set col := q % (2 * M + 3) with hcoldef
  set lb := (r - 2) / 2 with hlbdef
  have hK : innerLeftK (2 * M + 3) k = 2 * M * (2 * M) + (2 * M + lb) := by
    simp only [innerLeftK, cellR, cellInnerHalf, show 2 * M + 3 - 2 = 2 * M + 1 from by omega,
      show 2 * M + 1 - 1 = 2 * M from by omega, show 2 * M + 3 - 1 = 2 * M + 2 from by omega,
      ← hr, ← hlbdef, Nat.mul_div_cancel_left M (by omega : 0 < 2)]
  have hQ : innerQval (2 * M + 3) q = (row - 1) * (2 * M + 1) + (col - 1) := by
    simp only [innerQval, cellRow, cellCol, show 2 * M + 3 - 2 = 2 * M + 1 from by omega,
      ← hrowdef, ← hcoldef]
  rw [hK, hQ]
  have hQR : ((row - 1) * (2 * M + 1) + (col - 1)) / (2 * M + 1) = row - 1 := by
    rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), Nat.add_zero]
  have hQC : ((row - 1) * (2 * M + 1) + (col - 1)) % (2 * M + 1) = col - 1 := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  have hkbulk : k < (2 * M + 2) * (2 * M + 2) := by
    rw [hkdm, hcEq]
    exact cellLinIndexLt' (by rw [hrEq]; omega) (by omega)
  have hbprime : (2 * M * (2 * M) + (2 * M + lb)) - (2 * M + 1 - 1) * (2 * M + 1 - 1) = 2 * M + lb := by
    simp only [show 2 * M + 1 - 1 = 2 * M from by omega]; omega
  have hhalf : (2 * M + 1 - 1) / 2 = M := by
    simp only [show 2 * M + 1 - 1 = 2 * M from by omega, Nat.mul_div_cancel_left M (by omega : 0 < 2)]
  have hbbL : 2 * M + lb - 2 * ((2 * M + 1 - 1)/2) = lb := by rw [hhalf]; omega
  simp only [leftBandVal, baseBulkBandVal, cellRow, cellCol, cellR, cellC,
    show 2 * M + 3 - 1 = 2 * M + 2 from by omega,
    hQR, hQC, ← hr, hcEq, ← hrowdef, ← hcoldef, hbprime, hbbL,
    decide_eq_true hkbulk, Bool.and_true]
  rw [hrEq]
  simp only [show (col - 1 = 0) = (col = 1) from by simp only [eq_iff_iff]; omega,
      show (row - 1 = 2 * lb + 1) = (row = 2 * lb + 2) from by simp only [eq_iff_iff]; omega,
      show (row - 1 = 2 * lb + 2) = (row = 2 * lb + 2 + 1) from by simp only [eq_iff_iff]; omega,
      show (col = 0) = False from eq_false (by omega),
      show (col = 0 + 1) = (col = 1) from by simp only [Nat.zero_add],
      decide_false, Bool.false_or, Bool.and_comm]

/-! ### Bottom promoted-boundary inner↔outer correspondences (from `bottomSelfSimNat`). -/

/-- Bottom context: `r = 2M+1`, `c = 2bb+2`, `bb < M`, `1 ≤ row,col < 2M+2`. -/
private theorem bottomCtx (M k q : Nat)
    (hB : isBottomCell (2*M+3) k = true) (hIn : isInside (2*M+3) q = true) :
    k / (2*M+2) = 2*M+1 ∧ k % (2*M+2) = 2*((k % (2*M+2) - 2)/2) + 2 ∧
      (k % (2*M+2) - 2)/2 < M ∧ k = k / (2*M+2) * (2*M+2) + k % (2*M+2) ∧
      1 ≤ q / (2*M+3) ∧ q / (2*M+3) < 2*M+2 ∧ 1 ≤ q % (2*M+3) ∧ q % (2*M+3) < 2*M+2 := by
  simp only [isBottomCell, isInside, cellLastCell, cellInnerHalf, cellR, cellC, cellRow, cellCol,
    Bool.and_eq_true, decide_eq_true_eq] at hB hIn
  obtain ⟨hrEq, hcEq, hbb⟩ := hB
  obtain ⟨hrow1, hrow2, hcol1, hcol2⟩ := hIn
  simp only [show 2 * M + 3 - 1 = 2 * M + 2 from by omega,
      show 2 * M + 3 - 2 = 2 * M + 1 from by omega,
      show 2 * M + 1 - 1 = 2 * M from by omega] at hrEq hcEq hbb hrow2 hcol2
  have hbbm : (k % (2*M+2) - 2)/2 < M := by
    rw [Nat.mul_div_cancel_left M (by omega : 0 < 2)] at hbb; exact hbb
  have hkdm : k = k / (2*M+2) * (2*M+2) + k % (2*M+2) := by
    rw [Nat.mul_comm]; exact (Nat.div_add_mod k (2 * M + 2)).symm
  exact ⟨by omega, hcEq, hbbm, hkdm, hrow1, hrow2, hcol1, hcol2⟩

private theorem bottomInnerBulkFalseNat (M k q : Nat)
    (hB : isBottomCell (2*M+3) k = true) (hIn : isInside (2*M+3) q = true) :
    decide (innerBottomK (2*M+3) k < (2*M+1-1)*(2*M+1-1)) = false := by
  obtain ⟨hrEq, hcEq, hbbm, _, _, _, _, _⟩ := bottomCtx M k q hB hIn
  simp only [innerBottomK, cellC, cellInnerHalf, show 2 * M + 3 - 2 = 2 * M + 1 from by omega,
    show 2 * M + 1 - 1 = 2 * M from by omega, show 2 * M + 3 - 1 = 2 * M + 2 from by omega,
    Nat.mul_div_cancel_left M (by omega : 0 < 2), decide_eq_false_iff_not, Nat.not_lt]
  omega

private theorem bottomInnerTopClassFalseNat (M k q : Nat)
    (hB : isBottomCell (2*M+3) k = true) (hIn : isInside (2*M+3) q = true) :
    topClassVal (2*M+1) (innerBottomK (2*M+3) k) = false := by
  obtain ⟨hrEq, hcEq, hbbm, _, _, _, _, _⟩ := bottomCtx M k q hB hIn
  simp only [topClassVal, innerBottomK, cellC, cellInnerHalf,
    show 2 * M + 3 - 2 = 2 * M + 1 from by omega, show 2 * M + 1 - 1 = 2 * M from by omega,
    show 2 * M + 3 - 1 = 2 * M + 2 from by omega, Nat.mul_div_cancel_left M (by omega : 0 < 2),
    decide_eq_false_iff_not, Nat.not_lt]
  omega

private theorem bottomInnerRightClassFalseNat (M k q : Nat)
    (hB : isBottomCell (2*M+3) k = true) (hIn : isInside (2*M+3) q = true) :
    rightClassVal (2*M+1) (innerBottomK (2*M+3) k) = false := by
  obtain ⟨hrEq, hcEq, hbbm, _, _, _, _, _⟩ := bottomCtx M k q hB hIn
  simp only [rightClassVal, innerBottomK, cellC, cellInnerHalf,
    show 2 * M + 3 - 2 = 2 * M + 1 from by omega, show 2 * M + 1 - 1 = 2 * M from by omega,
    show 2 * M + 3 - 1 = 2 * M + 2 from by omega, Nat.mul_div_cancel_left M (by omega : 0 < 2),
    decide_eq_false_iff_not, Nat.not_lt]
  omega

private theorem bottomInnerLeftClassFalseNat (M k q : Nat)
    (hB : isBottomCell (2*M+3) k = true) (hIn : isInside (2*M+3) q = true) :
    leftClassVal (2*M+1) (innerBottomK (2*M+3) k) = false := by
  obtain ⟨hrEq, hcEq, hbbm, _, _, _, _, _⟩ := bottomCtx M k q hB hIn
  simp only [leftClassVal, innerBottomK, cellC, cellInnerHalf,
    show 2 * M + 3 - 2 = 2 * M + 1 from by omega, show 2 * M + 1 - 1 = 2 * M from by omega,
    show 2 * M + 3 - 1 = 2 * M + 2 from by omega, Nat.mul_div_cancel_left M (by omega : 0 < 2),
    decide_eq_false_iff_not, Nat.not_lt]
  omega

private theorem bottomKindFalseNat (M k q : Nat)
    (hB : isBottomCell (2*M+3) k = true) (hIn : isInside (2*M+3) q = true) :
    baseKindVal (2*M+3) k = false := by
  obtain ⟨hrEq, hcEq, hbbm, _, _, _, _, _⟩ := bottomCtx M k q hB hIn
  simp only [baseKindVal, cellR, cellC, show 2 * M + 3 - 1 = 2 * M + 2 from by omega,
    hrEq, decide_eq_false_iff_not]
  omega

private theorem bottomBandCorrNat (M k q : Nat)
    (hB : isBottomCell (2*M+3) k = true) (hIn : isInside (2*M+3) q = true) :
    bottomBandVal (2*M+1) (innerBottomK (2*M+3) k) (innerQval (2*M+3) q)
      = baseBulkBandVal (2*M+3) k q := by
  obtain ⟨hrEq, hcEq, hbbm, hkdm, hrow1, hrow2, hcol1, hcol2⟩ := bottomCtx M k q hB hIn
  set c := k % (2 * M + 2) with hc
  set row := q / (2 * M + 3) with hrowdef
  set col := q % (2 * M + 3) with hcoldef
  set bb := (c - 2) / 2 with hbbdef
  have hK : innerBottomK (2 * M + 3) k = 2 * M * (2 * M) + (3 * M + bb) := by
    simp only [innerBottomK, cellC, cellInnerHalf, show 2 * M + 3 - 2 = 2 * M + 1 from by omega,
      show 2 * M + 1 - 1 = 2 * M from by omega, show 2 * M + 3 - 1 = 2 * M + 2 from by omega,
      ← hc, ← hbbdef, Nat.mul_div_cancel_left M (by omega : 0 < 2)]
  have hQ : innerQval (2 * M + 3) q = (row - 1) * (2 * M + 1) + (col - 1) := by
    simp only [innerQval, cellRow, cellCol, show 2 * M + 3 - 2 = 2 * M + 1 from by omega,
      ← hrowdef, ← hcoldef]
  rw [hK, hQ]
  have hQR : ((row - 1) * (2 * M + 1) + (col - 1)) / (2 * M + 1) = row - 1 := by
    rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), Nat.add_zero]
  have hQC : ((row - 1) * (2 * M + 1) + (col - 1)) % (2 * M + 1) = col - 1 := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  have hkbulk : k < (2 * M + 2) * (2 * M + 2) := by
    rw [hkdm, hrEq]; exact cellLinIndexLt' (by omega) (by rw [hcEq]; omega)
  have hbprime : (2 * M * (2 * M) + (3 * M + bb)) - (2 * M + 1 - 1) * (2 * M + 1 - 1) = 3 * M + bb := by
    simp only [show 2 * M + 1 - 1 = 2 * M from by omega]; omega
  have hhalf : (2 * M + 1 - 1) / 2 = M := by
    simp only [show 2 * M + 1 - 1 = 2 * M from by omega, Nat.mul_div_cancel_left M (by omega : 0 < 2)]
  have hbbB : 3 * M + bb - 3 * ((2 * M + 1 - 1)/2) = bb := by rw [hhalf]; omega
  simp only [bottomBandVal, baseBulkBandVal, cellRow, cellCol, cellR, cellC,
    show 2 * M + 3 - 1 = 2 * M + 2 from by omega,
    hQR, hQC, hrEq, ← hc, hcEq, ← hrowdef, ← hcoldef, hbprime, hbbB,
    decide_eq_true hkbulk, Bool.and_true]
  rw [show 2 * M + 1 - 1 = 2 * M from by omega]
  simp only [show (row - 1 = 2 * M) = (row = 2 * M + 1) from by simp only [eq_iff_iff]; omega,
      show (col - 1 = 2 * bb + 1) = (col = 2 * bb + 2) from by simp only [eq_iff_iff]; omega,
      show (col - 1 = 2 * bb + 2) = (col = 2 * bb + 2 + 1) from by simp only [eq_iff_iff]; omega,
      show (row = 2 * M + 1 + 1) = False from eq_false (by omega),
      decide_false, Bool.or_false]

/-! ### Per-cell self-similarity leaf equalities  (the remaining SelfSim content)

These are the genuine single-step self-similarity content of the symbolic flat
bridge.  Each states, under the recursive-entry cell guards (supplied as
`SFormula.Deriv` premises by the master `recFlatMasterD` dispatch), that the
IH-flattened inner leaf `baseLeafTreeTA (inner)` equals the flat outer classifier
`baseLeafTreeTA dT kT qT`.

Both sides are closed pure Pauli `ite`-trees; they evaluate (by the Nat-level
single-step self-similarity of `SurfaceSelfSimNat.lean`) to the SAME
`surfaceCellPauli` value *in the relevant guard context*:

* `flatStepInterior`     ← `interiorSelfSimNat`     (`surfaceCellPauli inner = surfaceCellPauli outer`)
* `flatStepTop`          ← `topSelfSimNat`
* `flatStepRight`        ← `rightSelfSimNat`
* `flatStepLeft`         ← `leftSelfSimNat`
* `flatStepBottom`       ← `bottomSelfSimNat`
* `flatStepInteriorNI`   ← `interiorNotInsideNat`   (interior ∧ ¬inside ⇒ `inBulkBand = false` ⇒ `I`)
* `flatStep{Top,Right,Left,Bottom}NI` ← `surfaceCellPauli_{top,right,left,bottom}Cell_notInside`

**Why these are NOT one-line `pauliIteSelect` reductions.**  At a SYMBOLIC index the
two sides use *distinct guard families* (inner: `bulkGuardTA inner /
baseBulkBandGuardTA inner / …`; outer: `baseBulkBandGuardTA dT kT qT /
topClassGuardTA dT kT / …`).  The master's cell-kind `boolCases` context supplies
the OUTER recursive-entry guards as object hypotheses (`eqBool … = b true/false`).
To reduce `baseLeafTreeTA inner` and `baseLeafTreeTA outer` to matching literals one
must establish the corresponding INNER/OUTER classifier-guard *correspondences*
(e.g. interior ∧ inside ⇒ `baseBulkBandGuardTA inner` ↔ `baseBulkBandGuardTA outer`,
and the inner/outer `baseKind` parity match), and discharge the inconsistent guard
combinations.  These correspondences ARE provable at THIS layer — they are
environment-uniform closed-bool *implications* over `(k, q)` that hold because
`D.dT` evaluates to the FIXED `oddDistance (m+1)` (so each `*SelfSimNat` becomes a
uniform Nat tautology), hence discharged by `PureFamilyDerivA.arithBool` and folded
into the `cut` premise alongside the IH-leaf equalities.  Mechanising the full set
of guard-correspondence `arithBool` facts + their boolean combination inside the
`boolCases` head is the object-level analogue of all of `SurfaceSelfSimNat.lean`
threaded through both guard families — a sizeable development left as the remaining
step; see the honest-notes section at the end of the file.

The headline `rowSymTreeFlatBridgeSym` / `rowEntryFlatSym` below are otherwise fully
built (base case + IH flatten + master dispatch), so the bridge is complete modulo
exactly these ten single-step self-similarity leaves. -/

/-- The interior leaf's correspondence-premise: the three interior-cell guards
hold (bulk ∧ interiorCell ∧ inside).  All five inner↔outer guard implications below
share this antecedent. -/
private def interiorPbase {arity : Nat} (dT kT qT : Term arity .nat) : SFormula arity :=
  .and (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true))
    (.and (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b true))
      (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b true)))

def flatStepInterior {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b true)))
    (hInside : SFormula.Deriv Γ (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b true)))
    -- inner-bulk correspondence: inner cell is bulk.
    (hImpBulk : SFormula.Deriv Γ
      (.imp (interiorPbase dT kT qT)
        (.eqBool (SC.closed (bulkGuardTA (innerDTA dT) (interiorKTA dT kT))) (SC.b true))))
    -- inner-band correspondence (true / false outer-band cases).
    (hImpBandT : SFormula.Deriv Γ
      (.imp (.and (interiorPbase dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)))
        (.eqBool (SC.closed (baseBulkBandGuardTA (innerDTA dT) (interiorKTA dT kT) (innerQTA dT qT)))
          (SC.b true))))
    (hImpBandF : SFormula.Deriv Γ
      (.imp (.and (interiorPbase dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false)))
        (.eqBool (SC.closed (baseBulkBandGuardTA (innerDTA dT) (interiorKTA dT kT) (innerQTA dT qT)))
          (SC.b false))))
    -- inner-kind correspondence (true / false outer-kind cases).
    (hImpKindT : SFormula.Deriv Γ
      (.imp (.and (interiorPbase dT kT qT)
              (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b true)))
        (.eqBool (SC.closed (baseKindGuardTA (innerDTA dT) (interiorKTA dT kT))) (SC.b true))))
    (hImpKindF : SFormula.Deriv Γ
      (.imp (.and (interiorPbase dT kT qT)
              (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b false)))
        (.eqBool (SC.closed (baseKindGuardTA (innerDTA dT) (interiorKTA dT kT))) (SC.b false)))) :
    SFormula.Deriv Γ
      (.eqPauli
        (SC.closed (baseLeafTreeTA (innerDTA dT) (interiorKTA dT kT) (innerQTA dT qT)))
        (SC.closed (baseLeafTreeTA dT kT qT))) := by
  have hPbase : SFormula.Deriv Γ (interiorPbase dT kT qT) :=
    SFormula.Deriv.andIntro hBulk (SFormula.Deriv.andIntro hInterior hInside)
  -- inner is bulk.
  have hInnerBulk := SFormula.Deriv.mp hImpBulk hPbase
  -- case on the OUTER band guard.
  refine SFormula.Deriv.boolCases (SC.closed (baseBulkBandGuardTA dT kT qT)) _ ?_ ?_
  · -- outer band = true; further case on the OUTER kind guard.
    refine SFormula.Deriv.boolCases (SC.closed (baseKindGuardTA dT kT)) _ ?_ ?_
    · -- outer kind = true → both sides Z
      have hOBandT : SFormula.Deriv (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b true)
              :: .eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true) :: Γ)
          (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)) :=
        .hyp (by right; left)
      have hOKindT : SFormula.Deriv (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b true)
              :: .eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true) :: Γ)
          (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b true)) := .assumption
      have wkP := SFormula.Deriv.contextWeakening
        (Δ := (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b true)
                :: .eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true) :: Γ))
        (by intro C hC; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC)) hPbase
      have wkBulk := SFormula.Deriv.contextWeakening
        (Δ := (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b true)
                :: .eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true) :: Γ))
        (by intro C hC; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC)) hBulk
      have hInnerBulk' := SFormula.Deriv.contextWeakening
        (Δ := (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b true)
                :: .eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true) :: Γ))
        (by intro C hC; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC)) hInnerBulk
      have hInnerBand := SFormula.Deriv.mp
        (SFormula.Deriv.contextWeakening
          (Δ := (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b true)
                  :: .eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true) :: Γ))
          (by intro C hC; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC)) hImpBandT)
        (SFormula.Deriv.andIntro wkP hOBandT)
      have hInnerKind := SFormula.Deriv.mp
        (SFormula.Deriv.contextWeakening
          (Δ := (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b true)
                  :: .eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true) :: Γ))
          (by intro C hC; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC)) hImpKindT)
        (SFormula.Deriv.andIntro wkP hOKindT)
      have lhsZ := baseLeafZS (innerDTA dT) (interiorKTA dT kT) (innerQTA dT qT) hInnerBulk' hInnerBand hInnerKind
      have rhsZ := baseLeafZS dT kT qT wkBulk hOBandT hOKindT
      exact SFormula.Deriv.eqPauliTrans _ _ _ lhsZ (SFormula.Deriv.eqPauliSymm _ _ rhsZ)
    · -- outer kind = false → both sides X
      have hOBandT : SFormula.Deriv (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b false)
              :: .eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true) :: Γ)
          (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)) :=
        .hyp (by right; left)
      have hOKindF : SFormula.Deriv (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b false)
              :: .eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true) :: Γ)
          (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b false)) := .assumption
      have wkP := SFormula.Deriv.contextWeakening
        (Δ := (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b false)
                :: .eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true) :: Γ))
        (by intro C hC; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC)) hPbase
      have wkBulk := SFormula.Deriv.contextWeakening
        (Δ := (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b false)
                :: .eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true) :: Γ))
        (by intro C hC; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC)) hBulk
      have hInnerBulk' := SFormula.Deriv.contextWeakening
        (Δ := (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b false)
                :: .eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true) :: Γ))
        (by intro C hC; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC)) hInnerBulk
      have hInnerBand := SFormula.Deriv.mp
        (SFormula.Deriv.contextWeakening
          (Δ := (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b false)
                  :: .eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true) :: Γ))
          (by intro C hC; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC)) hImpBandT)
        (SFormula.Deriv.andIntro wkP hOBandT)
      have hInnerKind := SFormula.Deriv.mp
        (SFormula.Deriv.contextWeakening
          (Δ := (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b false)
                  :: .eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true) :: Γ))
          (by intro C hC; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC)) hImpKindF)
        (SFormula.Deriv.andIntro wkP hOKindF)
      have lhsX := baseLeafXS (innerDTA dT) (interiorKTA dT kT) (innerQTA dT qT) hInnerBulk' hInnerBand hInnerKind
      have rhsX := baseLeafXS dT kT qT wkBulk hOBandT hOKindF
      exact SFormula.Deriv.eqPauliTrans _ _ _ lhsX (SFormula.Deriv.eqPauliSymm _ _ rhsX)
  · -- outer band = false → both sides I
    have hOBandF : SFormula.Deriv (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false) :: Γ)
        (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false)) := .assumption
    have wkP := SFormula.Deriv.contextWeakening
      (Δ := (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false) :: Γ))
      (by intro C hC; exact List.mem_cons_of_mem _ hC) hPbase
    have wkBulk := SFormula.Deriv.contextWeakening
      (Δ := (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false) :: Γ))
      (by intro C hC; exact List.mem_cons_of_mem _ hC) hBulk
    have hInnerBulk' := SFormula.Deriv.contextWeakening
      (Δ := (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false) :: Γ))
      (by intro C hC; exact List.mem_cons_of_mem _ hC) hInnerBulk
    have hInnerBand := SFormula.Deriv.mp
      (SFormula.Deriv.contextWeakening
        (Δ := (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false) :: Γ))
        (by intro C hC; exact List.mem_cons_of_mem _ hC) hImpBandF)
      (SFormula.Deriv.andIntro wkP hOBandF)
    have lhsI := baseLeafBulkIS (innerDTA dT) (interiorKTA dT kT) (innerQTA dT qT) hInnerBulk' hInnerBand
    have rhsI := baseLeafBulkIS dT kT qT wkBulk hOBandF
    exact SFormula.Deriv.eqPauliTrans _ _ _ lhsI (SFormula.Deriv.eqPauliSymm _ _ rhsI)

/-! ### Interior leaf correspondence facts (the five `arithBool` implications)

Built from a `DistAtA arity (m+1)` witness (so the outer `dT` evaluates to
`oddDistance (m+1) = 2(m+1)+3`), discharged by `impGuardA_of` whose validity
certificate is the matching `interior*Nat` correspondence at the concrete `(kv,qv)`
extracted from the pure terms `kT`/`qT`. -/

/-- `interiorPbase` is in the arithmetic-boolean fragment whenever `dT`/`kT`/`qT`
are pure. -/
private theorem interiorPbase_frag {arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    arithBoolFragment (interiorPbase dT kT qT) = true := by
  simp only [interiorPbase, arithBoolFragment, ArithBoolFragment.formula, ArithBoolFragment.sterm,
    SC.closed, SC.b, ArithBoolFragment.term,
    pureTerm_in_fragment (bulkGuardTA_pure hd hk),
    pureTerm_in_fragment (interiorCellGuardTA_pure hd hk),
    pureTerm_in_fragment (insideGuardTA_pure hd hq), Bool.and_self]

/-- Extract the three interior-cell Nat facts from `interiorPbase.eval = some true`
at the concrete `(kv, qv)` carried by the pure terms.  `d = oddDistance (m+1)`. -/
private theorem interiorPbase_extract {fuel arity m kv qv : Nat} {kT qT : Term arity .nat}
    (D : DistAtA arity (m + 1)) (rho : Env arity) (E : PartialStabilizer)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : Term.eval Surface.code.body fuel qT rho = some qv)
    (hPe : (interiorPbase D.dT kT qT).eval Surface.code.body fuel rho E = some true) :
    isInteriorCell (oddDistance (m + 1)) kv = true ∧
      isInside (oddDistance (m + 1)) qv = true := by
  simp only [interiorPbase, SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval, bind, Option.bind,
    bulkGuardTA_eval rho (D.evalsTo rho) hkv,
    interiorCellGuardTA_eval rho (D.evalsTo rho) hkv,
    insideGuardTA_eval rho (D.evalsTo rho) hqv] at hPe
  by_cases hI : isInteriorCell (oddDistance (m + 1)) kv = true <;>
    by_cases hIn : isInside (oddDistance (m + 1)) qv = true <;>
    simp_all

/-- `interiorPbase` always evaluates to `some _` (its atoms are pure bool guards). -/
private theorem interiorPbase_tot {fuel arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (rho : Env arity) (E : PartialStabilizer) :
    ((interiorPbase dT kT qT).eval Surface.code.body fuel rho E).isSome = true := by
  obtain ⟨b1, h1⟩ := (bulkGuardTA_pure hd hk).eval_total Surface.code.body fuel rho
  obtain ⟨b2, h2⟩ := (interiorCellGuardTA_pure hd hk).eval_total Surface.code.body fuel rho
  obtain ⟨b3, h3⟩ := (insideGuardTA_pure hd hq).eval_total Surface.code.body fuel rho
  simp only [interiorPbase, SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval, bind, Option.bind,
    h1, h2, h3]
  cases b1 <;> cases b2 <;> cases b3 <;> simp

/-- Totality for `interiorPbase ∧ (extra pure-bool guard)`. -/
private theorem interiorPbaseAnd_tot {fuel arity : Nat} {dT kT qT : Term arity .nat}
    {g : Term arity .bool} (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT)
    (hq : SFormula.PureNatTerm qT) (hg : SFormula.PureBoolTerm g) (v : Bool)
    (rho : Env arity) (E : PartialStabilizer) :
    (((interiorPbase dT kT qT).and (.eqBool (SC.closed g) (SC.b v))).eval
      Surface.code.body fuel rho E).isSome = true := by
  obtain ⟨bg, hgv⟩ := hg.eval_total Surface.code.body fuel rho
  have hbase := interiorPbase_tot (fuel := fuel) hd hk hq rho E
  cases hbe : (interiorPbase dT kT qT).eval Surface.code.body fuel rho E with
  | none => rw [hbe] at hbase; simp at hbase
  | some bb =>
      cases bb <;>
        simp [SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval, bind, Option.bind, hbe, hgv]

/-- The interior inner-bulk correspondence implication. -/
private def interiorImpBulk {fuel arity m : Nat} {kT qT : Term arity .nat}
    (D : DistAtA arity (m + 1)) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    PureFamilyDerivA Surface.code.body fuel
      (.imp (interiorPbase D.dT kT qT)
        (.eqBool (SC.closed (bulkGuardTA (innerDTA D.dT) (interiorKTA D.dT kT))) (SC.b true))) :=
  impGuardA_of (interiorPbase_frag D.pure hk hq)
    (bulkGuardTA_pure (innerDTA_pure D.pure) (interiorKTA_pure D.pure hk))
    (fun rho E => interiorPbase_tot D.pure hk hq rho E)
    (by
      intro rho E hPe
      obtain ⟨kv, hkv⟩ := hk.eval_total Surface.code.body fuel rho
      obtain ⟨qv, hqv⟩ := hq.eval_total Surface.code.body fuel rho
      obtain ⟨hI, hIn⟩ := interiorPbase_extract D rho E hkv hqv hPe
      have hdInner : Term.eval Surface.code.body fuel (innerDTA D.dT) rho
          = some (2 * (m + 1) + 1) := by
        rw [innerDTA, Term.eval, Term.eval, D.evalsTo rho]
        simp [Option.bind, Option.bind_eq_bind, Option.some.injEq, oddDistance]
      have hkInner : Term.eval Surface.code.body fuel (interiorKTA D.dT kT) rho
          = some (innerInteriorK (2 * (m + 1) + 3) kv) := by
        have := interiorKTA_evalsTo (d := oddDistance (m + 1)) rho (D.evalsTo rho) hkv
        simpa only [oddDistance] using this
      rw [bulkGuardTA_eval rho hdInner hkInner]
      have hM := interiorInnerBulkNat (m + 1) kv qv (by simpa [oddDistance] using hI)
        (by simpa [oddDistance] using hIn)
      simpa using hM)

/-- The interior inner-band correspondence implication (parametric in the outer-band
boolean `v`). -/
private def interiorImpBand {fuel arity m : Nat} {kT qT : Term arity .nat} (v : Bool)
    (D : DistAtA arity (m + 1)) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    PureFamilyDerivA Surface.code.body fuel
      (.imp (.and (interiorPbase D.dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA D.dT kT qT)) (SC.b v)))
        (.eqBool (SC.closed (baseBulkBandGuardTA (innerDTA D.dT) (interiorKTA D.dT kT) (innerQTA D.dT qT)))
          (SC.b v))) :=
  impGuardA_of
    (by
      simp only [arithBoolFragment, ArithBoolFragment.formula]
      rw [show ArithBoolFragment.formula (interiorPbase D.dT kT qT) = true from
            interiorPbase_frag D.pure hk hq]
      simp [ArithBoolFragment.sterm, SC.closed, SC.b, ArithBoolFragment.term,
        pureTerm_in_fragment (baseBulkBandGuardTA_pure D.pure hk hq)])
    (baseBulkBandGuardTA_pure (innerDTA_pure D.pure) (interiorKTA_pure D.pure hk)
      (innerQTA_pure D.pure hq))
    (fun rho E => interiorPbaseAnd_tot D.pure hk hq (baseBulkBandGuardTA_pure D.pure hk hq) v rho E)
    (by
      intro rho E hPe
      obtain ⟨kv, hkv⟩ := hk.eval_total Surface.code.body fuel rho
      obtain ⟨qv, hqv⟩ := hq.eval_total Surface.code.body fuel rho
      -- split the conjunction premise
      rw [SFormula.eval] at hPe
      have hbase := interiorPbase_tot (fuel := fuel) D.pure hk hq rho E
      cases hbe : (interiorPbase D.dT kT qT).eval Surface.code.body fuel rho E with
      | none => rw [hbe] at hbase; simp at hbase
      | some bb =>
          cases bb with
          | false => rw [hbe] at hPe; simp at hPe
          | true =>
              rw [hbe] at hPe
              simp only [SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval,
                bind, Option.bind, baseBulkBandGuardTA_eval rho (D.evalsTo rho) hkv hqv,
                Option.some.injEq, decide_eq_true_eq, if_true] at hPe
              obtain ⟨hI, hIn⟩ := interiorPbase_extract D rho E hkv hqv hbe
              have hdInner : Term.eval Surface.code.body fuel (innerDTA D.dT) rho
                  = some (2 * (m + 1) + 1) := by
                rw [innerDTA, Term.eval, Term.eval, D.evalsTo rho]
                simp [Option.bind, Option.bind_eq_bind, Option.some.injEq, oddDistance]
              have hkInner : Term.eval Surface.code.body fuel (interiorKTA D.dT kT) rho
                  = some (innerInteriorK (2 * (m + 1) + 3) kv) := by
                have := interiorKTA_evalsTo (d := oddDistance (m + 1)) rho (D.evalsTo rho) hkv
                simpa only [oddDistance] using this
              have hqInner : Term.eval Surface.code.body fuel (innerQTA D.dT qT) rho
                  = some (innerQval (2 * (m + 1) + 3) qv) := by
                have := innerQTA_evalsTo (d := oddDistance (m + 1)) rho (D.evalsTo rho) hqv
                simpa only [oddDistance] using this
              rw [baseBulkBandGuardTA_eval rho hdInner hkInner hqInner]
              have hcorr := interiorBandCorrNat (m + 1) kv qv
                (by simpa [oddDistance] using hI) (by simpa [oddDistance] using hIn)
              rw [hcorr, show (2 * (m + 1) + 3) = oddDistance (m + 1) from rfl, hPe])

/-- The interior inner-kind correspondence implication (parametric in `v`). -/
private def interiorImpKind {fuel arity m : Nat} {kT qT : Term arity .nat} (v : Bool)
    (D : DistAtA arity (m + 1)) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    PureFamilyDerivA Surface.code.body fuel
      (.imp (.and (interiorPbase D.dT kT qT)
              (.eqBool (SC.closed (baseKindGuardTA D.dT kT)) (SC.b v)))
        (.eqBool (SC.closed (baseKindGuardTA (innerDTA D.dT) (interiorKTA D.dT kT))) (SC.b v))) :=
  impGuardA_of
    (by
      simp only [arithBoolFragment, ArithBoolFragment.formula]
      rw [show ArithBoolFragment.formula (interiorPbase D.dT kT qT) = true from
            interiorPbase_frag D.pure hk hq]
      simp [ArithBoolFragment.sterm, SC.closed, SC.b, ArithBoolFragment.term,
        pureTerm_in_fragment (baseKindGuardTA_pure D.pure hk)])
    (baseKindGuardTA_pure (innerDTA_pure D.pure) (interiorKTA_pure D.pure hk))
    (fun rho E => interiorPbaseAnd_tot D.pure hk hq (baseKindGuardTA_pure D.pure hk) v rho E)
    (by
      intro rho E hPe
      obtain ⟨kv, hkv⟩ := hk.eval_total Surface.code.body fuel rho
      obtain ⟨qv, hqv⟩ := hq.eval_total Surface.code.body fuel rho
      rw [SFormula.eval] at hPe
      have hbase := interiorPbase_tot (fuel := fuel) D.pure hk hq rho E
      cases hbe : (interiorPbase D.dT kT qT).eval Surface.code.body fuel rho E with
      | none => rw [hbe] at hbase; simp at hbase
      | some bb =>
          cases bb with
          | false => rw [hbe] at hPe; simp at hPe
          | true =>
              rw [hbe] at hPe
              simp only [SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval,
                bind, Option.bind, baseKindGuardTA_eval rho (D.evalsTo rho) hkv,
                Option.some.injEq, decide_eq_true_eq, if_true] at hPe
              obtain ⟨hI, hIn⟩ := interiorPbase_extract D rho E hkv hqv hbe
              have hdInner : Term.eval Surface.code.body fuel (innerDTA D.dT) rho
                  = some (2 * (m + 1) + 1) := by
                rw [innerDTA, Term.eval, Term.eval, D.evalsTo rho]
                simp [Option.bind, Option.bind_eq_bind, Option.some.injEq, oddDistance]
              have hkInner : Term.eval Surface.code.body fuel (interiorKTA D.dT kT) rho
                  = some (innerInteriorK (2 * (m + 1) + 3) kv) := by
                have := interiorKTA_evalsTo (d := oddDistance (m + 1)) rho (D.evalsTo rho) hkv
                simpa only [oddDistance] using this
              rw [baseKindGuardTA_eval rho hdInner hkInner]
              have hcorr := interiorKindCorrNat (m + 1) kv qv
                (by simpa [oddDistance] using hI) (by simpa [oddDistance] using hIn)
              rw [hcorr, show (2 * (m + 1) + 3) = oddDistance (m + 1) from rfl, hPe])

/-- The interior-not-inside leaf's correspondence-premise (`inside = false`). -/
private def interiorPbaseNI {arity : Nat} (dT kT qT : Term arity .nat) : SFormula arity :=
  .and (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true))
    (.and (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b true))
      (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b false)))

/-- Interior, not inside: the outer bulk band is empty (`baseBulkBandVal = false`). -/
private theorem interiorNI_bandFalseNat (M k q : Nat)
    (hI : isInteriorCell (2*M+3) k = true)
    (hIn : isInside (2*M+3) q = false) :
    baseBulkBandVal (2*M+3) k q = false := by
  have hbb := interiorNotInsideNat M k q hI hIn
  simpa only [baseBulkBandVal, inBulkBand, Bool.and_assoc] using hbb

/-- `interiorPbaseNI` is in the arithmetic-boolean fragment. -/
private theorem interiorPbaseNI_frag {arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    arithBoolFragment (interiorPbaseNI dT kT qT) = true := by
  simp only [interiorPbaseNI, arithBoolFragment, ArithBoolFragment.formula, ArithBoolFragment.sterm,
    SC.closed, SC.b, ArithBoolFragment.term,
    pureTerm_in_fragment (bulkGuardTA_pure hd hk),
    pureTerm_in_fragment (interiorCellGuardTA_pure hd hk),
    pureTerm_in_fragment (insideGuardTA_pure hd hq), Bool.and_self]

/-- `interiorPbaseNI` always evaluates to `some _`. -/
private theorem interiorPbaseNI_tot {fuel arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (rho : Env arity) (E : PartialStabilizer) :
    ((interiorPbaseNI dT kT qT).eval Surface.code.body fuel rho E).isSome = true := by
  obtain ⟨b1, h1⟩ := (bulkGuardTA_pure hd hk).eval_total Surface.code.body fuel rho
  obtain ⟨b2, h2⟩ := (interiorCellGuardTA_pure hd hk).eval_total Surface.code.body fuel rho
  obtain ⟨b3, h3⟩ := (insideGuardTA_pure hd hq).eval_total Surface.code.body fuel rho
  simp only [interiorPbaseNI, SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval, bind,
    Option.bind, h1, h2, h3]
  cases b1 <;> cases b2 <;> cases b3 <;> simp

/-- The interior-not-inside band-false correspondence implication. -/
private def interiorImpBandNI {fuel arity m : Nat} {kT qT : Term arity .nat}
    (D : DistAtA arity (m + 1)) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    PureFamilyDerivA Surface.code.body fuel
      (.imp (interiorPbaseNI D.dT kT qT)
        (.eqBool (SC.closed (baseBulkBandGuardTA D.dT kT qT)) (SC.b false))) :=
  impGuardA_of (interiorPbaseNI_frag D.pure hk hq)
    (baseBulkBandGuardTA_pure D.pure hk hq)
    (fun rho E => interiorPbaseNI_tot D.pure hk hq rho E)
    (by
      intro rho E hPe
      obtain ⟨kv, hkv⟩ := hk.eval_total Surface.code.body fuel rho
      obtain ⟨qv, hqv⟩ := hq.eval_total Surface.code.body fuel rho
      -- extract interior = true, inside = false from the premise.
      have hII : isInteriorCell (oddDistance (m + 1)) kv = true ∧
          isInside (oddDistance (m + 1)) qv = false := by
        simp only [interiorPbaseNI, SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval,
          bind, Option.bind, bulkGuardTA_eval rho (D.evalsTo rho) hkv,
          interiorCellGuardTA_eval rho (D.evalsTo rho) hkv,
          insideGuardTA_eval rho (D.evalsTo rho) hqv] at hPe
        by_cases hI : isInteriorCell (oddDistance (m + 1)) kv = true <;>
          by_cases hIn : isInside (oddDistance (m + 1)) qv = true <;> simp_all
      obtain ⟨hI, hIn⟩ := hII
      rw [baseBulkBandGuardTA_eval rho (D.evalsTo rho) hkv hqv]
      have := interiorNI_bandFalseNat (m + 1) kv qv (by simpa [oddDistance] using hI)
        (by simpa [oddDistance] using hIn)
      simpa [oddDistance] using this)

/-! ### Top promoted-boundary inside leaf: premise + correspondence implications -/

/-- Top-inside leaf correspondence premise: `bulk ∧ ¬interiorCell ∧ topCell ∧ inside`. -/
private def topPbase {arity : Nat} (dT kT qT : Term arity .nat) : SFormula arity :=
  .and (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true))
    (.and (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false))
      (.and (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b true))
        (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b true))))

private theorem topPbase_frag {arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    arithBoolFragment (topPbase dT kT qT) = true := by
  simp only [topPbase, arithBoolFragment, ArithBoolFragment.formula, ArithBoolFragment.sterm,
    SC.closed, SC.b, ArithBoolFragment.term,
    pureTerm_in_fragment (bulkGuardTA_pure hd hk),
    pureTerm_in_fragment (interiorCellGuardTA_pure hd hk),
    pureTerm_in_fragment (topCellGuardTA_pure hd hk),
    pureTerm_in_fragment (insideGuardTA_pure hd hq), Bool.and_self]

private theorem topPbase_tot {fuel arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (rho : Env arity) (E : PartialStabilizer) :
    ((topPbase dT kT qT).eval Surface.code.body fuel rho E).isSome = true := by
  obtain ⟨b1, h1⟩ := (bulkGuardTA_pure hd hk).eval_total Surface.code.body fuel rho
  obtain ⟨b2, h2⟩ := (interiorCellGuardTA_pure hd hk).eval_total Surface.code.body fuel rho
  obtain ⟨b3, h3⟩ := (topCellGuardTA_pure hd hk).eval_total Surface.code.body fuel rho
  obtain ⟨b4, h4⟩ := (insideGuardTA_pure hd hq).eval_total Surface.code.body fuel rho
  simp only [topPbase, SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval, bind, Option.bind,
    h1, h2, h3, h4]
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> simp

private theorem topPbaseAnd_tot {fuel arity : Nat} {dT kT qT : Term arity .nat}
    {g : Term arity .bool} (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT)
    (hq : SFormula.PureNatTerm qT) (hg : SFormula.PureBoolTerm g) (v : Bool)
    (rho : Env arity) (E : PartialStabilizer) :
    (((topPbase dT kT qT).and (.eqBool (SC.closed g) (SC.b v))).eval
      Surface.code.body fuel rho E).isSome = true := by
  obtain ⟨bg, hgv⟩ := hg.eval_total Surface.code.body fuel rho
  have hbase := topPbase_tot (fuel := fuel) hd hk hq rho E
  cases hbe : (topPbase dT kT qT).eval Surface.code.body fuel rho E with
  | none => rw [hbe] at hbase; simp at hbase
  | some bb =>
      cases bb <;>
        simp [SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval, bind, Option.bind, hbe, hgv]

/-- Extract the top-cell + inside Nat facts from `topPbase.eval = some true`. -/
private theorem topPbase_extract {fuel arity m kv qv : Nat} {kT qT : Term arity .nat}
    (D : DistAtA arity (m + 1)) (rho : Env arity) (E : PartialStabilizer)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : Term.eval Surface.code.body fuel qT rho = some qv)
    (hPe : (topPbase D.dT kT qT).eval Surface.code.body fuel rho E = some true) :
    isTopCell (oddDistance (m + 1)) kv = true ∧ isInside (oddDistance (m + 1)) qv = true := by
  simp only [topPbase, SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval, bind, Option.bind,
    bulkGuardTA_eval rho (D.evalsTo rho) hkv,
    interiorCellGuardTA_eval rho (D.evalsTo rho) hkv,
    topCellGuardTA_eval rho (D.evalsTo rho) hkv,
    insideGuardTA_eval rho (D.evalsTo rho) hqv] at hPe
  by_cases hT : isTopCell (oddDistance (m + 1)) kv = true <;>
    by_cases hIn : isInside (oddDistance (m + 1)) qv = true <;> simp_all

/-- The top inner stab index `topKTA` evaluates inside the inner `2(m+1)+1` code. -/
private theorem topInner_evals {fuel arity m kv : Nat} {kT : Term arity .nat}
    (D : DistAtA arity (m + 1)) (rho : Env arity)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv) :
    Term.eval Surface.code.body fuel (innerDTA D.dT) rho = some (2 * (m + 1) + 1) ∧
      Term.eval Surface.code.body fuel (topKTA D.dT kT) rho
        = some (innerTopK (2 * (m + 1) + 3) kv) := by
  refine ⟨?_, ?_⟩
  · rw [innerDTA, Term.eval, Term.eval, D.evalsTo rho]
    simp [Option.bind, Option.bind_eq_bind, oddDistance]
  · have := topKTA_evalsTo (d := oddDistance (m + 1)) rho (D.evalsTo rho) hkv
    simpa only [oddDistance] using this

/-- Top context-only correspondence: `kindF ∧ innerBulkF ∧ innerClassT`. -/
private def topImpCtx {fuel arity m : Nat} {kT qT : Term arity .nat}
    (D : DistAtA arity (m + 1)) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    PureFamilyDerivA Surface.code.body fuel
      (.imp (topPbase D.dT kT qT)
        (.and (.eqBool (SC.closed (baseKindGuardTA D.dT kT)) (SC.b false))
          (.and (.eqBool (SC.closed (bulkGuardTA (recInnerDTA D.dT) (topKTA D.dT kT))) (SC.b false))
            (.eqBool (SC.closed (topClassGuardTA (recInnerDTA D.dT) (topKTA D.dT kT))) (SC.b true))))) := by
  refine PureFamilyDerivA.arithBool _ ?_ ?_
  · simp only [arithBoolFragment, ArithBoolFragment.formula]
    rw [show ArithBoolFragment.formula (topPbase D.dT kT qT) = true from topPbase_frag D.pure hk hq]
    simp [ArithBoolFragment.sterm, SC.closed, SC.b, ArithBoolFragment.term, recInnerDTA,
      pureTerm_in_fragment (baseKindGuardTA_pure D.pure hk),
      pureTerm_in_fragment (bulkGuardTA_pure (innerDTA_pure D.pure) (topKTA_pure D.pure hk)),
      pureTerm_in_fragment (topClassGuardTA_pure (innerDTA_pure D.pure) (topKTA_pure D.pure hk))]
  · intro rho E
    cases hPe : (topPbase D.dT kT qT).eval Surface.code.body fuel rho E with
    | none => have := topPbase_tot (fuel := fuel) D.pure hk hq rho E; rw [hPe] at this; simp at this
    | some pv =>
        cases pv with
        | false => rw [SFormula.eval, hPe]; rfl
        | true =>
            rw [SFormula.eval, hPe]
            obtain ⟨kv, hkv⟩ := hk.eval_total Surface.code.body fuel rho
            obtain ⟨qv, hqv⟩ := hq.eval_total Surface.code.body fuel rho
            obtain ⟨hT, hIn⟩ := topPbase_extract D rho E hkv hqv hPe
            obtain ⟨hdInner, hkInner⟩ := topInner_evals D rho hkv
            have hT' := (by simpa [oddDistance] using hT : isTopCell (2*(m+1)+3) kv = true)
            have hIn' := (by simpa [oddDistance] using hIn : isInside (2*(m+1)+3) qv = true)
            have hkindF := topKindFalseNat (m+1) kv qv hT' hIn'
            have hbf := topInnerBulkFalseNat (m+1) kv qv hT' hIn'
            have hct := topInnerClassTrueNat (m+1) kv qv hT' hIn'
            simp only [oddDistance] at hkindF
            simp only [show (2*(m+1)+1) - 1 = 2*(m+1) from by omega] at hbf
            simp only [SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval, bind, Option.bind,
              baseKindGuardTA_eval rho (D.evalsTo rho) hkv, recInnerDTA,
              bulkGuardTA_eval rho hdInner hkInner,
              topClassGuardTA_eval rho hdInner hkInner, oddDistance,
              show (2*(m+1)+1) - 1 = 2*(m+1) from by omega, hkindF, hbf, hct]
            simp

/-- Top band correspondence (parametric in the outer band boolean `v`). -/
private def topImpBand {fuel arity m : Nat} {kT qT : Term arity .nat} (v : Bool)
    (D : DistAtA arity (m + 1)) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    PureFamilyDerivA Surface.code.body fuel
      (.imp (.and (topPbase D.dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA D.dT kT qT)) (SC.b v)))
        (.eqBool (SC.closed (topBandGuardTA (recInnerDTA D.dT) (topKTA D.dT kT) (innerQTA D.dT qT)))
          (SC.b v))) := by
  refine impGuardA_of ?_ ?_ ?_ ?_
  · simp only [arithBoolFragment, ArithBoolFragment.formula]
    rw [show ArithBoolFragment.formula (topPbase D.dT kT qT) = true from topPbase_frag D.pure hk hq]
    simp [ArithBoolFragment.sterm, SC.closed, SC.b, ArithBoolFragment.term,
      pureTerm_in_fragment (baseBulkBandGuardTA_pure D.pure hk hq)]
  · exact topBandGuardTA_pure (innerDTA_pure D.pure) (topKTA_pure D.pure hk) (innerQTA_pure D.pure hq)
  · exact fun rho E => topPbaseAnd_tot D.pure hk hq (baseBulkBandGuardTA_pure D.pure hk hq) v rho E
  · intro rho E hPe
    obtain ⟨kv, hkv⟩ := hk.eval_total Surface.code.body fuel rho
    obtain ⟨qv, hqv⟩ := hq.eval_total Surface.code.body fuel rho
    rw [SFormula.eval] at hPe
    have hbase := topPbase_tot (fuel := fuel) D.pure hk hq rho E
    cases hbe : (topPbase D.dT kT qT).eval Surface.code.body fuel rho E with
    | none => rw [hbe] at hbase; simp at hbase
    | some bb =>
        cases bb with
        | false => rw [hbe] at hPe; simp at hPe
        | true =>
            rw [hbe] at hPe
            simp only [SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval,
              bind, Option.bind, baseBulkBandGuardTA_eval rho (D.evalsTo rho) hkv hqv,
              Option.some.injEq, decide_eq_true_eq, if_true] at hPe
            obtain ⟨hT, hIn⟩ := topPbase_extract D rho E hkv hqv hbe
            obtain ⟨hdInner, hkInner⟩ := topInner_evals D rho hkv
            have hqInner : Term.eval Surface.code.body fuel (innerQTA D.dT qT) rho
                = some (innerQval (2 * (m + 1) + 3) qv) := by
              have := innerQTA_evalsTo (d := oddDistance (m + 1)) rho (D.evalsTo rho) hqv
              simpa only [oddDistance] using this
            have hT' := (by simpa [oddDistance] using hT : isTopCell (2*(m+1)+3) kv = true)
            have hIn' := (by simpa [oddDistance] using hIn : isInside (2*(m+1)+3) qv = true)
            rw [show recInnerDTA D.dT = innerDTA D.dT from rfl,
              topBandGuardTA_eval rho hdInner hkInner hqInner]
            have hcorr := topBandCorrNat (m + 1) kv qv hT' hIn'
            rw [hcorr, show (2 * (m + 1) + 3) = oddDistance (m + 1) from rfl, hPe]

def flatStepTop {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : SFormula.Deriv Γ (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b true)))
    (hInside : SFormula.Deriv Γ (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b true)))
    (hImpCtx : SFormula.Deriv Γ
      (.imp (topPbase dT kT qT)
        (.and (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b false))
          (.and (.eqBool (SC.closed (bulkGuardTA (recInnerDTA dT) (topKTA dT kT))) (SC.b false))
            (.eqBool (SC.closed (topClassGuardTA (recInnerDTA dT) (topKTA dT kT))) (SC.b true))))))
    (hImpBandT : SFormula.Deriv Γ
      (.imp (.and (topPbase dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)))
        (.eqBool (SC.closed (topBandGuardTA (recInnerDTA dT) (topKTA dT kT) (innerQTA dT qT)))
          (SC.b true))))
    (hImpBandF : SFormula.Deriv Γ
      (.imp (.and (topPbase dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false)))
        (.eqBool (SC.closed (topBandGuardTA (recInnerDTA dT) (topKTA dT kT) (innerQTA dT qT)))
          (SC.b false)))) :
    SFormula.Deriv Γ
      (.eqPauli
        (SC.closed (baseLeafTreeTA (recInnerDTA dT) (topKTA dT kT) (innerQTA dT qT)))
        (SC.closed (baseLeafTreeTA dT kT qT))) := by
  have hPbase : SFormula.Deriv Γ (topPbase dT kT qT) :=
    SFormula.Deriv.andIntro hBulk (SFormula.Deriv.andIntro hInterior
      (SFormula.Deriv.andIntro hTop hInside))
  have hCtx := SFormula.Deriv.mp hImpCtx hPbase
  have hKindF := SFormula.Deriv.andElimLeft hCtx
  have hInnerBulkF := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hCtx)
  have hInnerClassT := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hCtx)
  -- case on the OUTER band guard.
  refine SFormula.Deriv.boolCases (SC.closed (baseBulkBandGuardTA dT kT qT)) _ ?_ ?_
  · -- outer band = true → both sides X
    set Δ := (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true) :: Γ) with hΔ
    have hsub : ∀ C, C ∈ Γ → C ∈ Δ := by intro C hC; exact List.mem_cons_of_mem _ hC
    have hOBandT : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)) :=
      .assumption
    have wkBulk := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hBulk
    have wkKindF := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hKindF
    have wkInnerBulkF := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hInnerBulkF
    have wkInnerClassT := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hInnerClassT
    have wkPbase := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hPbase
    have hInnerBand := SFormula.Deriv.mp
      (SFormula.Deriv.contextWeakening (Δ := Δ) hsub hImpBandT)
      (SFormula.Deriv.andIntro wkPbase hOBandT)
    have lhsX := baseLeafTopXS (recInnerDTA dT) (topKTA dT kT) (innerQTA dT qT)
      wkInnerBulkF wkInnerClassT hInnerBand
    have rhsX := baseLeafXS dT kT qT wkBulk hOBandT wkKindF
    exact SFormula.Deriv.eqPauliTrans _ _ _ lhsX (SFormula.Deriv.eqPauliSymm _ _ rhsX)
  · -- outer band = false → both sides I
    set Δ := (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false) :: Γ) with hΔ
    have hsub : ∀ C, C ∈ Γ → C ∈ Δ := by intro C hC; exact List.mem_cons_of_mem _ hC
    have hOBandF : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false)) :=
      .assumption
    have wkInnerBulkF := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hInnerBulkF
    have wkInnerClassT := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hInnerClassT
    have wkBulk := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hBulk
    have wkPbase := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hPbase
    have hInnerBand := SFormula.Deriv.mp
      (SFormula.Deriv.contextWeakening (Δ := Δ) hsub hImpBandF)
      (SFormula.Deriv.andIntro wkPbase hOBandF)
    have lhsI := baseLeafTopIS (recInnerDTA dT) (topKTA dT kT) (innerQTA dT qT)
      wkInnerBulkF wkInnerClassT hInnerBand
    have rhsI := baseLeafBulkIS dT kT qT wkBulk hOBandF
    exact SFormula.Deriv.eqPauliTrans _ _ _ lhsI (SFormula.Deriv.eqPauliSymm _ _ rhsI)

/-! ### Right promoted-boundary inside leaf: premise + correspondence implications -/

/-- Right-inside premise: `bulk ∧ ¬interior ∧ ¬top ∧ right ∧ inside`. -/
private def rightPbase {arity : Nat} (dT kT qT : Term arity .nat) : SFormula arity :=
  .and (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true))
    (.and (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false))
      (.and (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b false))
        (.and (.eqBool (SC.closed (rightCellGuardTA dT kT)) (SC.b true))
          (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b true)))))

private theorem rightPbase_frag {arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    arithBoolFragment (rightPbase dT kT qT) = true := by
  simp only [rightPbase, arithBoolFragment, ArithBoolFragment.formula, ArithBoolFragment.sterm,
    SC.closed, SC.b, ArithBoolFragment.term,
    pureTerm_in_fragment (bulkGuardTA_pure hd hk),
    pureTerm_in_fragment (interiorCellGuardTA_pure hd hk),
    pureTerm_in_fragment (topCellGuardTA_pure hd hk),
    pureTerm_in_fragment (rightCellGuardTA_pure hd hk),
    pureTerm_in_fragment (insideGuardTA_pure hd hq), Bool.and_self]

private theorem rightPbase_tot {fuel arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (rho : Env arity) (E : PartialStabilizer) :
    ((rightPbase dT kT qT).eval Surface.code.body fuel rho E).isSome = true := by
  obtain ⟨b1, h1⟩ := (bulkGuardTA_pure hd hk).eval_total Surface.code.body fuel rho
  obtain ⟨b2, h2⟩ := (interiorCellGuardTA_pure hd hk).eval_total Surface.code.body fuel rho
  obtain ⟨b3, h3⟩ := (topCellGuardTA_pure hd hk).eval_total Surface.code.body fuel rho
  obtain ⟨b4, h4⟩ := (rightCellGuardTA_pure hd hk).eval_total Surface.code.body fuel rho
  obtain ⟨b5, h5⟩ := (insideGuardTA_pure hd hq).eval_total Surface.code.body fuel rho
  simp only [rightPbase, SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval, bind, Option.bind,
    h1, h2, h3, h4, h5]
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> simp

private theorem rightPbaseAnd_tot {fuel arity : Nat} {dT kT qT : Term arity .nat}
    {g : Term arity .bool} (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT)
    (hq : SFormula.PureNatTerm qT) (hg : SFormula.PureBoolTerm g) (v : Bool)
    (rho : Env arity) (E : PartialStabilizer) :
    (((rightPbase dT kT qT).and (.eqBool (SC.closed g) (SC.b v))).eval
      Surface.code.body fuel rho E).isSome = true := by
  obtain ⟨bg, hgv⟩ := hg.eval_total Surface.code.body fuel rho
  have hbase := rightPbase_tot (fuel := fuel) hd hk hq rho E
  cases hbe : (rightPbase dT kT qT).eval Surface.code.body fuel rho E with
  | none => rw [hbe] at hbase; simp at hbase
  | some bb =>
      cases bb <;>
        simp [SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval, bind, Option.bind, hbe, hgv]

private theorem rightPbase_extract {fuel arity m kv qv : Nat} {kT qT : Term arity .nat}
    (D : DistAtA arity (m + 1)) (rho : Env arity) (E : PartialStabilizer)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : Term.eval Surface.code.body fuel qT rho = some qv)
    (hPe : (rightPbase D.dT kT qT).eval Surface.code.body fuel rho E = some true) :
    isRightCell (oddDistance (m + 1)) kv = true ∧ isInside (oddDistance (m + 1)) qv = true := by
  simp only [rightPbase, SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval, bind, Option.bind,
    bulkGuardTA_eval rho (D.evalsTo rho) hkv,
    interiorCellGuardTA_eval rho (D.evalsTo rho) hkv,
    topCellGuardTA_eval rho (D.evalsTo rho) hkv,
    rightCellGuardTA_eval rho (D.evalsTo rho) hkv,
    insideGuardTA_eval rho (D.evalsTo rho) hqv] at hPe
  by_cases hR : isRightCell (oddDistance (m + 1)) kv = true <;>
    by_cases hIn : isInside (oddDistance (m + 1)) qv = true <;> simp_all

private theorem rightInner_evals {fuel arity m kv : Nat} {kT : Term arity .nat}
    (D : DistAtA arity (m + 1)) (rho : Env arity)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv) :
    Term.eval Surface.code.body fuel (innerDTA D.dT) rho = some (2 * (m + 1) + 1) ∧
      Term.eval Surface.code.body fuel (rightKTA D.dT kT) rho
        = some (innerRightK (2 * (m + 1) + 3) kv) := by
  refine ⟨?_, ?_⟩
  · rw [innerDTA, Term.eval, Term.eval, D.evalsTo rho]
    simp [Option.bind, Option.bind_eq_bind, oddDistance]
  · have := rightKTA_evalsTo (d := oddDistance (m + 1)) rho (D.evalsTo rho) hkv
    simpa only [oddDistance] using this

/-- Right context-only correspondence: `kindT ∧ innerBulkF ∧ innerTopClassF ∧ innerRightClassT`. -/
private def rightImpCtx {fuel arity m : Nat} {kT qT : Term arity .nat}
    (D : DistAtA arity (m + 1)) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    PureFamilyDerivA Surface.code.body fuel
      (.imp (rightPbase D.dT kT qT)
        (.and (.eqBool (SC.closed (baseKindGuardTA D.dT kT)) (SC.b true))
          (.and (.eqBool (SC.closed (bulkGuardTA (recInnerDTA D.dT) (rightKTA D.dT kT))) (SC.b false))
            (.and (.eqBool (SC.closed (topClassGuardTA (recInnerDTA D.dT) (rightKTA D.dT kT))) (SC.b false))
              (.eqBool (SC.closed (rightClassGuardTA (recInnerDTA D.dT) (rightKTA D.dT kT))) (SC.b true)))))) := by
  refine PureFamilyDerivA.arithBool _ ?_ ?_
  · simp only [arithBoolFragment, ArithBoolFragment.formula]
    rw [show ArithBoolFragment.formula (rightPbase D.dT kT qT) = true from rightPbase_frag D.pure hk hq]
    simp [ArithBoolFragment.sterm, SC.closed, SC.b, ArithBoolFragment.term, recInnerDTA,
      pureTerm_in_fragment (baseKindGuardTA_pure D.pure hk),
      pureTerm_in_fragment (bulkGuardTA_pure (innerDTA_pure D.pure) (rightKTA_pure D.pure hk)),
      pureTerm_in_fragment (topClassGuardTA_pure (innerDTA_pure D.pure) (rightKTA_pure D.pure hk)),
      pureTerm_in_fragment (rightClassGuardTA_pure (innerDTA_pure D.pure) (rightKTA_pure D.pure hk))]
  · intro rho E
    cases hPe : (rightPbase D.dT kT qT).eval Surface.code.body fuel rho E with
    | none => have := rightPbase_tot (fuel := fuel) D.pure hk hq rho E; rw [hPe] at this; simp at this
    | some pv =>
        cases pv with
        | false => rw [SFormula.eval, hPe]; rfl
        | true =>
            rw [SFormula.eval, hPe]
            obtain ⟨kv, hkv⟩ := hk.eval_total Surface.code.body fuel rho
            obtain ⟨qv, hqv⟩ := hq.eval_total Surface.code.body fuel rho
            obtain ⟨hR, hIn⟩ := rightPbase_extract D rho E hkv hqv hPe
            obtain ⟨hdInner, hkInner⟩ := rightInner_evals D rho hkv
            have hR' := (by simpa [oddDistance] using hR : isRightCell (2*(m+1)+3) kv = true)
            have hIn' := (by simpa [oddDistance] using hIn : isInside (2*(m+1)+3) qv = true)
            have hkindT := rightKindTrueNat (m+1) kv qv hR' hIn'
            have hbf := rightInnerBulkFalseNat (m+1) kv qv hR' hIn'
            have htcf := rightInnerTopClassFalseNat (m+1) kv qv hR' hIn'
            have hrct := rightInnerClassTrueNat (m+1) kv qv hR' hIn'
            simp only [oddDistance] at hkindT
            simp only [show (2*(m+1)+1) - 1 = 2*(m+1) from by omega] at hbf
            simp only [SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval, bind, Option.bind,
              baseKindGuardTA_eval rho (D.evalsTo rho) hkv, recInnerDTA,
              bulkGuardTA_eval rho hdInner hkInner,
              topClassGuardTA_eval rho hdInner hkInner,
              rightClassGuardTA_eval rho hdInner hkInner, oddDistance,
              show (2*(m+1)+1) - 1 = 2*(m+1) from by omega, hkindT, hbf, htcf, hrct]
            simp

private def rightImpBand {fuel arity m : Nat} {kT qT : Term arity .nat} (v : Bool)
    (D : DistAtA arity (m + 1)) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    PureFamilyDerivA Surface.code.body fuel
      (.imp (.and (rightPbase D.dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA D.dT kT qT)) (SC.b v)))
        (.eqBool (SC.closed (rightBandGuardTA (recInnerDTA D.dT) (rightKTA D.dT kT) (innerQTA D.dT qT)))
          (SC.b v))) := by
  refine impGuardA_of ?_ ?_ ?_ ?_
  · simp only [arithBoolFragment, ArithBoolFragment.formula]
    rw [show ArithBoolFragment.formula (rightPbase D.dT kT qT) = true from rightPbase_frag D.pure hk hq]
    simp [ArithBoolFragment.sterm, SC.closed, SC.b, ArithBoolFragment.term,
      pureTerm_in_fragment (baseBulkBandGuardTA_pure D.pure hk hq)]
  · exact rightBandGuardTA_pure (innerDTA_pure D.pure) (rightKTA_pure D.pure hk) (innerQTA_pure D.pure hq)
  · exact fun rho E => rightPbaseAnd_tot D.pure hk hq (baseBulkBandGuardTA_pure D.pure hk hq) v rho E
  · intro rho E hPe
    obtain ⟨kv, hkv⟩ := hk.eval_total Surface.code.body fuel rho
    obtain ⟨qv, hqv⟩ := hq.eval_total Surface.code.body fuel rho
    rw [SFormula.eval] at hPe
    have hbase := rightPbase_tot (fuel := fuel) D.pure hk hq rho E
    cases hbe : (rightPbase D.dT kT qT).eval Surface.code.body fuel rho E with
    | none => rw [hbe] at hbase; simp at hbase
    | some bb =>
        cases bb with
        | false => rw [hbe] at hPe; simp at hPe
        | true =>
            rw [hbe] at hPe
            simp only [SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval,
              bind, Option.bind, baseBulkBandGuardTA_eval rho (D.evalsTo rho) hkv hqv,
              Option.some.injEq, decide_eq_true_eq, if_true] at hPe
            obtain ⟨hR, hIn⟩ := rightPbase_extract D rho E hkv hqv hbe
            obtain ⟨hdInner, hkInner⟩ := rightInner_evals D rho hkv
            have hqInner : Term.eval Surface.code.body fuel (innerQTA D.dT qT) rho
                = some (innerQval (2 * (m + 1) + 3) qv) := by
              have := innerQTA_evalsTo (d := oddDistance (m + 1)) rho (D.evalsTo rho) hqv
              simpa only [oddDistance] using this
            have hR' := (by simpa [oddDistance] using hR : isRightCell (2*(m+1)+3) kv = true)
            have hIn' := (by simpa [oddDistance] using hIn : isInside (2*(m+1)+3) qv = true)
            rw [show recInnerDTA D.dT = innerDTA D.dT from rfl,
              rightBandGuardTA_eval rho hdInner hkInner hqInner]
            have hcorr := rightBandCorrNat (m + 1) kv qv hR' hIn'
            rw [hcorr, show (2 * (m + 1) + 3) = oddDistance (m + 1) from rfl, hPe]

def flatStepRight {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : SFormula.Deriv Γ (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b false)))
    (hRight : SFormula.Deriv Γ (.eqBool (SC.closed (rightCellGuardTA dT kT)) (SC.b true)))
    (hInside : SFormula.Deriv Γ (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b true)))
    (hImpCtx : SFormula.Deriv Γ
      (.imp (rightPbase dT kT qT)
        (.and (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b true))
          (.and (.eqBool (SC.closed (bulkGuardTA (recInnerDTA dT) (rightKTA dT kT))) (SC.b false))
            (.and (.eqBool (SC.closed (topClassGuardTA (recInnerDTA dT) (rightKTA dT kT))) (SC.b false))
              (.eqBool (SC.closed (rightClassGuardTA (recInnerDTA dT) (rightKTA dT kT))) (SC.b true)))))))
    (hImpBandT : SFormula.Deriv Γ
      (.imp (.and (rightPbase dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)))
        (.eqBool (SC.closed (rightBandGuardTA (recInnerDTA dT) (rightKTA dT kT) (innerQTA dT qT)))
          (SC.b true))))
    (hImpBandF : SFormula.Deriv Γ
      (.imp (.and (rightPbase dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false)))
        (.eqBool (SC.closed (rightBandGuardTA (recInnerDTA dT) (rightKTA dT kT) (innerQTA dT qT)))
          (SC.b false)))) :
    SFormula.Deriv Γ
      (.eqPauli
        (SC.closed (baseLeafTreeTA (recInnerDTA dT) (rightKTA dT kT) (innerQTA dT qT)))
        (SC.closed (baseLeafTreeTA dT kT qT))) := by
  have hPbase : SFormula.Deriv Γ (rightPbase dT kT qT) :=
    SFormula.Deriv.andIntro hBulk (SFormula.Deriv.andIntro hInterior
      (SFormula.Deriv.andIntro hTop (SFormula.Deriv.andIntro hRight hInside)))
  have hCtx := SFormula.Deriv.mp hImpCtx hPbase
  have hKindT := SFormula.Deriv.andElimLeft hCtx
  have hInnerBulkF := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hCtx)
  have hInnerTopClassF := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight hCtx))
  have hInnerRightClassT := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight hCtx))
  refine SFormula.Deriv.boolCases (SC.closed (baseBulkBandGuardTA dT kT qT)) _ ?_ ?_
  · -- outer band = true → both sides Z
    set Δ := (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true) :: Γ) with hΔ
    have hsub : ∀ C, C ∈ Γ → C ∈ Δ := by intro C hC; exact List.mem_cons_of_mem _ hC
    have hOBandT : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)) :=
      .assumption
    have wkBulk := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hBulk
    have wkKindT := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hKindT
    have wkInnerBulkF := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hInnerBulkF
    have wkInnerTopClassF := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hInnerTopClassF
    have wkInnerRightClassT := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hInnerRightClassT
    have wkPbase := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hPbase
    have hInnerBand := SFormula.Deriv.mp
      (SFormula.Deriv.contextWeakening (Δ := Δ) hsub hImpBandT)
      (SFormula.Deriv.andIntro wkPbase hOBandT)
    have lhsZ := baseLeafRightZS (recInnerDTA dT) (rightKTA dT kT) (innerQTA dT qT)
      wkInnerBulkF wkInnerTopClassF wkInnerRightClassT hInnerBand
    have rhsZ := baseLeafZS dT kT qT wkBulk hOBandT wkKindT
    exact SFormula.Deriv.eqPauliTrans _ _ _ lhsZ (SFormula.Deriv.eqPauliSymm _ _ rhsZ)
  · -- outer band = false → both sides I
    set Δ := (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false) :: Γ) with hΔ
    have hsub : ∀ C, C ∈ Γ → C ∈ Δ := by intro C hC; exact List.mem_cons_of_mem _ hC
    have hOBandF : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false)) :=
      .assumption
    have wkInnerBulkF := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hInnerBulkF
    have wkInnerTopClassF := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hInnerTopClassF
    have wkInnerRightClassT := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hInnerRightClassT
    have wkBulk := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hBulk
    have wkPbase := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hPbase
    have hInnerBand := SFormula.Deriv.mp
      (SFormula.Deriv.contextWeakening (Δ := Δ) hsub hImpBandF)
      (SFormula.Deriv.andIntro wkPbase hOBandF)
    have lhsI := baseLeafRightIS (recInnerDTA dT) (rightKTA dT kT) (innerQTA dT qT)
      wkInnerBulkF wkInnerTopClassF wkInnerRightClassT hInnerBand
    have rhsI := baseLeafBulkIS dT kT qT wkBulk hOBandF
    exact SFormula.Deriv.eqPauliTrans _ _ _ lhsI (SFormula.Deriv.eqPauliSymm _ _ rhsI)

/-! ### Left promoted-boundary inside leaf: premise + correspondence implications -/

/-- Left-inside premise: `bulk ∧ ¬interior ∧ ¬top ∧ ¬right ∧ left ∧ inside`. -/
private def leftPbase {arity : Nat} (dT kT qT : Term arity .nat) : SFormula arity :=
  .and (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true))
    (.and (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false))
      (.and (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b false))
        (.and (.eqBool (SC.closed (rightCellGuardTA dT kT)) (SC.b false))
          (.and (.eqBool (SC.closed (leftCellGuardTA dT kT)) (SC.b true))
            (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b true))))))

private theorem leftPbase_frag {arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    arithBoolFragment (leftPbase dT kT qT) = true := by
  simp only [leftPbase, arithBoolFragment, ArithBoolFragment.formula, ArithBoolFragment.sterm,
    SC.closed, SC.b, ArithBoolFragment.term,
    pureTerm_in_fragment (bulkGuardTA_pure hd hk),
    pureTerm_in_fragment (interiorCellGuardTA_pure hd hk),
    pureTerm_in_fragment (topCellGuardTA_pure hd hk),
    pureTerm_in_fragment (rightCellGuardTA_pure hd hk),
    pureTerm_in_fragment (leftCellGuardTA_pure hd hk),
    pureTerm_in_fragment (insideGuardTA_pure hd hq), Bool.and_self]

private theorem leftPbase_tot {fuel arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (rho : Env arity) (E : PartialStabilizer) :
    ((leftPbase dT kT qT).eval Surface.code.body fuel rho E).isSome = true := by
  obtain ⟨b1, h1⟩ := (bulkGuardTA_pure hd hk).eval_total Surface.code.body fuel rho
  obtain ⟨b2, h2⟩ := (interiorCellGuardTA_pure hd hk).eval_total Surface.code.body fuel rho
  obtain ⟨b3, h3⟩ := (topCellGuardTA_pure hd hk).eval_total Surface.code.body fuel rho
  obtain ⟨b4, h4⟩ := (rightCellGuardTA_pure hd hk).eval_total Surface.code.body fuel rho
  obtain ⟨b5, h5⟩ := (leftCellGuardTA_pure hd hk).eval_total Surface.code.body fuel rho
  obtain ⟨b6, h6⟩ := (insideGuardTA_pure hd hq).eval_total Surface.code.body fuel rho
  simp only [leftPbase, SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval, bind, Option.bind,
    h1, h2, h3, h4, h5, h6]
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> simp

private theorem leftPbaseAnd_tot {fuel arity : Nat} {dT kT qT : Term arity .nat}
    {g : Term arity .bool} (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT)
    (hq : SFormula.PureNatTerm qT) (hg : SFormula.PureBoolTerm g) (v : Bool)
    (rho : Env arity) (E : PartialStabilizer) :
    (((leftPbase dT kT qT).and (.eqBool (SC.closed g) (SC.b v))).eval
      Surface.code.body fuel rho E).isSome = true := by
  obtain ⟨bg, hgv⟩ := hg.eval_total Surface.code.body fuel rho
  have hbase := leftPbase_tot (fuel := fuel) hd hk hq rho E
  cases hbe : (leftPbase dT kT qT).eval Surface.code.body fuel rho E with
  | none => rw [hbe] at hbase; simp at hbase
  | some bb =>
      cases bb <;>
        simp [SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval, bind, Option.bind, hbe, hgv]

private theorem leftPbase_extract {fuel arity m kv qv : Nat} {kT qT : Term arity .nat}
    (D : DistAtA arity (m + 1)) (rho : Env arity) (E : PartialStabilizer)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : Term.eval Surface.code.body fuel qT rho = some qv)
    (hPe : (leftPbase D.dT kT qT).eval Surface.code.body fuel rho E = some true) :
    isLeftCell (oddDistance (m + 1)) kv = true ∧ isInside (oddDistance (m + 1)) qv = true := by
  simp only [leftPbase, SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval, bind, Option.bind,
    bulkGuardTA_eval rho (D.evalsTo rho) hkv,
    interiorCellGuardTA_eval rho (D.evalsTo rho) hkv,
    topCellGuardTA_eval rho (D.evalsTo rho) hkv,
    rightCellGuardTA_eval rho (D.evalsTo rho) hkv,
    leftCellGuardTA_eval rho (D.evalsTo rho) hkv,
    insideGuardTA_eval rho (D.evalsTo rho) hqv] at hPe
  by_cases hL : isLeftCell (oddDistance (m + 1)) kv = true <;>
    by_cases hIn : isInside (oddDistance (m + 1)) qv = true <;> simp_all

private theorem leftInner_evals {fuel arity m kv : Nat} {kT : Term arity .nat}
    (D : DistAtA arity (m + 1)) (rho : Env arity)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv) :
    Term.eval Surface.code.body fuel (innerDTA D.dT) rho = some (2 * (m + 1) + 1) ∧
      Term.eval Surface.code.body fuel (leftKTA D.dT kT) rho
        = some (innerLeftK (2 * (m + 1) + 3) kv) := by
  refine ⟨?_, ?_⟩
  · rw [innerDTA, Term.eval, Term.eval, D.evalsTo rho]
    simp [Option.bind, Option.bind_eq_bind, oddDistance]
  · have := leftKTA_evalsTo (d := oddDistance (m + 1)) rho (D.evalsTo rho) hkv
    simpa only [oddDistance] using this

/-- Left context-only: `kindT ∧ innerBulkF ∧ innerTopClassF ∧ innerRightClassF ∧ innerLeftClassT`. -/
private def leftImpCtx {fuel arity m : Nat} {kT qT : Term arity .nat}
    (D : DistAtA arity (m + 1)) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    PureFamilyDerivA Surface.code.body fuel
      (.imp (leftPbase D.dT kT qT)
        (.and (.eqBool (SC.closed (baseKindGuardTA D.dT kT)) (SC.b true))
          (.and (.eqBool (SC.closed (bulkGuardTA (recInnerDTA D.dT) (leftKTA D.dT kT))) (SC.b false))
            (.and (.eqBool (SC.closed (topClassGuardTA (recInnerDTA D.dT) (leftKTA D.dT kT))) (SC.b false))
              (.and (.eqBool (SC.closed (rightClassGuardTA (recInnerDTA D.dT) (leftKTA D.dT kT))) (SC.b false))
                (.eqBool (SC.closed (leftClassGuardTA (recInnerDTA D.dT) (leftKTA D.dT kT))) (SC.b true))))))) := by
  refine PureFamilyDerivA.arithBool _ ?_ ?_
  · simp only [arithBoolFragment, ArithBoolFragment.formula]
    rw [show ArithBoolFragment.formula (leftPbase D.dT kT qT) = true from leftPbase_frag D.pure hk hq]
    simp [ArithBoolFragment.sterm, SC.closed, SC.b, ArithBoolFragment.term, recInnerDTA,
      pureTerm_in_fragment (baseKindGuardTA_pure D.pure hk),
      pureTerm_in_fragment (bulkGuardTA_pure (innerDTA_pure D.pure) (leftKTA_pure D.pure hk)),
      pureTerm_in_fragment (topClassGuardTA_pure (innerDTA_pure D.pure) (leftKTA_pure D.pure hk)),
      pureTerm_in_fragment (rightClassGuardTA_pure (innerDTA_pure D.pure) (leftKTA_pure D.pure hk)),
      pureTerm_in_fragment (leftClassGuardTA_pure (innerDTA_pure D.pure) (leftKTA_pure D.pure hk))]
  · intro rho E
    cases hPe : (leftPbase D.dT kT qT).eval Surface.code.body fuel rho E with
    | none => have := leftPbase_tot (fuel := fuel) D.pure hk hq rho E; rw [hPe] at this; simp at this
    | some pv =>
        cases pv with
        | false => rw [SFormula.eval, hPe]; rfl
        | true =>
            rw [SFormula.eval, hPe]
            obtain ⟨kv, hkv⟩ := hk.eval_total Surface.code.body fuel rho
            obtain ⟨qv, hqv⟩ := hq.eval_total Surface.code.body fuel rho
            obtain ⟨hL, hIn⟩ := leftPbase_extract D rho E hkv hqv hPe
            obtain ⟨hdInner, hkInner⟩ := leftInner_evals D rho hkv
            have hL' := (by simpa [oddDistance] using hL : isLeftCell (2*(m+1)+3) kv = true)
            have hIn' := (by simpa [oddDistance] using hIn : isInside (2*(m+1)+3) qv = true)
            have hkindT := leftKindTrueNat (m+1) kv qv hL' hIn'
            have hbf := leftInnerBulkFalseNat (m+1) kv qv hL' hIn'
            have htcf := leftInnerTopClassFalseNat (m+1) kv qv hL' hIn'
            have hrcf := leftInnerRightClassFalseNat (m+1) kv qv hL' hIn'
            have hlct := leftInnerClassTrueNat (m+1) kv qv hL' hIn'
            simp only [oddDistance] at hkindT
            simp only [show (2*(m+1)+1) - 1 = 2*(m+1) from by omega] at hbf
            simp only [SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval, bind, Option.bind,
              baseKindGuardTA_eval rho (D.evalsTo rho) hkv, recInnerDTA,
              bulkGuardTA_eval rho hdInner hkInner,
              topClassGuardTA_eval rho hdInner hkInner,
              rightClassGuardTA_eval rho hdInner hkInner,
              leftClassGuardTA_eval rho hdInner hkInner, oddDistance,
              show (2*(m+1)+1) - 1 = 2*(m+1) from by omega, hkindT, hbf, htcf, hrcf, hlct]
            simp

private def leftImpBand {fuel arity m : Nat} {kT qT : Term arity .nat} (v : Bool)
    (D : DistAtA arity (m + 1)) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    PureFamilyDerivA Surface.code.body fuel
      (.imp (.and (leftPbase D.dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA D.dT kT qT)) (SC.b v)))
        (.eqBool (SC.closed (leftBandGuardTA (recInnerDTA D.dT) (leftKTA D.dT kT) (innerQTA D.dT qT)))
          (SC.b v))) := by
  refine impGuardA_of ?_ ?_ ?_ ?_
  · simp only [arithBoolFragment, ArithBoolFragment.formula]
    rw [show ArithBoolFragment.formula (leftPbase D.dT kT qT) = true from leftPbase_frag D.pure hk hq]
    simp [ArithBoolFragment.sterm, SC.closed, SC.b, ArithBoolFragment.term,
      pureTerm_in_fragment (baseBulkBandGuardTA_pure D.pure hk hq)]
  · exact leftBandGuardTA_pure (innerDTA_pure D.pure) (leftKTA_pure D.pure hk) (innerQTA_pure D.pure hq)
  · exact fun rho E => leftPbaseAnd_tot D.pure hk hq (baseBulkBandGuardTA_pure D.pure hk hq) v rho E
  · intro rho E hPe
    obtain ⟨kv, hkv⟩ := hk.eval_total Surface.code.body fuel rho
    obtain ⟨qv, hqv⟩ := hq.eval_total Surface.code.body fuel rho
    rw [SFormula.eval] at hPe
    have hbase := leftPbase_tot (fuel := fuel) D.pure hk hq rho E
    cases hbe : (leftPbase D.dT kT qT).eval Surface.code.body fuel rho E with
    | none => rw [hbe] at hbase; simp at hbase
    | some bb =>
        cases bb with
        | false => rw [hbe] at hPe; simp at hPe
        | true =>
            rw [hbe] at hPe
            simp only [SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval,
              bind, Option.bind, baseBulkBandGuardTA_eval rho (D.evalsTo rho) hkv hqv,
              Option.some.injEq, decide_eq_true_eq, if_true] at hPe
            obtain ⟨hL, hIn⟩ := leftPbase_extract D rho E hkv hqv hbe
            obtain ⟨hdInner, hkInner⟩ := leftInner_evals D rho hkv
            have hqInner : Term.eval Surface.code.body fuel (innerQTA D.dT qT) rho
                = some (innerQval (2 * (m + 1) + 3) qv) := by
              have := innerQTA_evalsTo (d := oddDistance (m + 1)) rho (D.evalsTo rho) hqv
              simpa only [oddDistance] using this
            have hL' := (by simpa [oddDistance] using hL : isLeftCell (2*(m+1)+3) kv = true)
            have hIn' := (by simpa [oddDistance] using hIn : isInside (2*(m+1)+3) qv = true)
            rw [show recInnerDTA D.dT = innerDTA D.dT from rfl,
              leftBandGuardTA_eval rho hdInner hkInner hqInner]
            have hcorr := leftBandCorrNat (m + 1) kv qv hL' hIn'
            rw [hcorr, show (2 * (m + 1) + 3) = oddDistance (m + 1) from rfl, hPe]

def flatStepLeft {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : SFormula.Deriv Γ (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b false)))
    (hRight : SFormula.Deriv Γ (.eqBool (SC.closed (rightCellGuardTA dT kT)) (SC.b false)))
    (hLeft : SFormula.Deriv Γ (.eqBool (SC.closed (leftCellGuardTA dT kT)) (SC.b true)))
    (hInside : SFormula.Deriv Γ (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b true)))
    (hImpCtx : SFormula.Deriv Γ
      (.imp (leftPbase dT kT qT)
        (.and (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b true))
          (.and (.eqBool (SC.closed (bulkGuardTA (recInnerDTA dT) (leftKTA dT kT))) (SC.b false))
            (.and (.eqBool (SC.closed (topClassGuardTA (recInnerDTA dT) (leftKTA dT kT))) (SC.b false))
              (.and (.eqBool (SC.closed (rightClassGuardTA (recInnerDTA dT) (leftKTA dT kT))) (SC.b false))
                (.eqBool (SC.closed (leftClassGuardTA (recInnerDTA dT) (leftKTA dT kT))) (SC.b true))))))))
    (hImpBandT : SFormula.Deriv Γ
      (.imp (.and (leftPbase dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)))
        (.eqBool (SC.closed (leftBandGuardTA (recInnerDTA dT) (leftKTA dT kT) (innerQTA dT qT)))
          (SC.b true))))
    (hImpBandF : SFormula.Deriv Γ
      (.imp (.and (leftPbase dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false)))
        (.eqBool (SC.closed (leftBandGuardTA (recInnerDTA dT) (leftKTA dT kT) (innerQTA dT qT)))
          (SC.b false)))) :
    SFormula.Deriv Γ
      (.eqPauli
        (SC.closed (baseLeafTreeTA (recInnerDTA dT) (leftKTA dT kT) (innerQTA dT qT)))
        (SC.closed (baseLeafTreeTA dT kT qT))) := by
  have hPbase : SFormula.Deriv Γ (leftPbase dT kT qT) :=
    SFormula.Deriv.andIntro hBulk (SFormula.Deriv.andIntro hInterior
      (SFormula.Deriv.andIntro hTop (SFormula.Deriv.andIntro hRight
        (SFormula.Deriv.andIntro hLeft hInside))))
  have hCtx := SFormula.Deriv.mp hImpCtx hPbase
  have hKindT := SFormula.Deriv.andElimLeft hCtx
  have hInnerBulkF := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hCtx)
  have hInnerTopClassF := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight hCtx))
  have hInnerRightClassF := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hCtx)))
  have hInnerLeftClassT := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hCtx)))
  refine SFormula.Deriv.boolCases (SC.closed (baseBulkBandGuardTA dT kT qT)) _ ?_ ?_
  · -- outer band = true → both sides Z
    set Δ := (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true) :: Γ) with hΔ
    have hsub : ∀ C, C ∈ Γ → C ∈ Δ := by intro C hC; exact List.mem_cons_of_mem _ hC
    have hOBandT : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)) :=
      .assumption
    have wkBulk := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hBulk
    have wkKindT := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hKindT
    have wkInnerBulkF := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hInnerBulkF
    have wkInnerTopClassF := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hInnerTopClassF
    have wkInnerRightClassF := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hInnerRightClassF
    have wkInnerLeftClassT := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hInnerLeftClassT
    have wkPbase := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hPbase
    have hInnerBand := SFormula.Deriv.mp
      (SFormula.Deriv.contextWeakening (Δ := Δ) hsub hImpBandT)
      (SFormula.Deriv.andIntro wkPbase hOBandT)
    have lhsZ := baseLeafLeftZS (recInnerDTA dT) (leftKTA dT kT) (innerQTA dT qT)
      wkInnerBulkF wkInnerTopClassF wkInnerRightClassF wkInnerLeftClassT hInnerBand
    have rhsZ := baseLeafZS dT kT qT wkBulk hOBandT wkKindT
    exact SFormula.Deriv.eqPauliTrans _ _ _ lhsZ (SFormula.Deriv.eqPauliSymm _ _ rhsZ)
  · -- outer band = false → both sides I
    set Δ := (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false) :: Γ) with hΔ
    have hsub : ∀ C, C ∈ Γ → C ∈ Δ := by intro C hC; exact List.mem_cons_of_mem _ hC
    have hOBandF : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false)) :=
      .assumption
    have wkInnerBulkF := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hInnerBulkF
    have wkInnerTopClassF := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hInnerTopClassF
    have wkInnerRightClassF := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hInnerRightClassF
    have wkInnerLeftClassT := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hInnerLeftClassT
    have wkBulk := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hBulk
    have wkPbase := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hPbase
    have hInnerBand := SFormula.Deriv.mp
      (SFormula.Deriv.contextWeakening (Δ := Δ) hsub hImpBandF)
      (SFormula.Deriv.andIntro wkPbase hOBandF)
    have lhsI := baseLeafLeftIS (recInnerDTA dT) (leftKTA dT kT) (innerQTA dT qT)
      wkInnerBulkF wkInnerTopClassF wkInnerRightClassF wkInnerLeftClassT hInnerBand
    have rhsI := baseLeafBulkIS dT kT qT wkBulk hOBandF
    exact SFormula.Deriv.eqPauliTrans _ _ _ lhsI (SFormula.Deriv.eqPauliSymm _ _ rhsI)

/-! ### Bottom promoted-boundary inside leaf: premise + correspondence implications -/

/-- Bottom-inside premise: `bulk ∧ ¬interior ∧ ¬top ∧ ¬right ∧ ¬left ∧ bottom ∧ inside`. -/
private def bottomPbase {arity : Nat} (dT kT qT : Term arity .nat) : SFormula arity :=
  .and (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true))
    (.and (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false))
      (.and (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b false))
        (.and (.eqBool (SC.closed (rightCellGuardTA dT kT)) (SC.b false))
          (.and (.eqBool (SC.closed (leftCellGuardTA dT kT)) (SC.b false))
            (.and (.eqBool (SC.closed (bottomCellGuardTA dT kT)) (SC.b true))
              (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b true)))))))

private theorem bottomPbase_frag {arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    arithBoolFragment (bottomPbase dT kT qT) = true := by
  simp only [bottomPbase, arithBoolFragment, ArithBoolFragment.formula, ArithBoolFragment.sterm,
    SC.closed, SC.b, ArithBoolFragment.term,
    pureTerm_in_fragment (bulkGuardTA_pure hd hk),
    pureTerm_in_fragment (interiorCellGuardTA_pure hd hk),
    pureTerm_in_fragment (topCellGuardTA_pure hd hk),
    pureTerm_in_fragment (rightCellGuardTA_pure hd hk),
    pureTerm_in_fragment (leftCellGuardTA_pure hd hk),
    pureTerm_in_fragment (bottomCellGuardTA_pure hd hk),
    pureTerm_in_fragment (insideGuardTA_pure hd hq), Bool.and_self]

private theorem bottomPbase_tot {fuel arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (rho : Env arity) (E : PartialStabilizer) :
    ((bottomPbase dT kT qT).eval Surface.code.body fuel rho E).isSome = true := by
  obtain ⟨b1, h1⟩ := (bulkGuardTA_pure hd hk).eval_total Surface.code.body fuel rho
  obtain ⟨b2, h2⟩ := (interiorCellGuardTA_pure hd hk).eval_total Surface.code.body fuel rho
  obtain ⟨b3, h3⟩ := (topCellGuardTA_pure hd hk).eval_total Surface.code.body fuel rho
  obtain ⟨b4, h4⟩ := (rightCellGuardTA_pure hd hk).eval_total Surface.code.body fuel rho
  obtain ⟨b5, h5⟩ := (leftCellGuardTA_pure hd hk).eval_total Surface.code.body fuel rho
  obtain ⟨b6, h6⟩ := (bottomCellGuardTA_pure hd hk).eval_total Surface.code.body fuel rho
  obtain ⟨b7, h7⟩ := (insideGuardTA_pure hd hq).eval_total Surface.code.body fuel rho
  simp only [bottomPbase, SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval, bind, Option.bind,
    h1, h2, h3, h4, h5, h6, h7]
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;> simp

private theorem bottomPbaseAnd_tot {fuel arity : Nat} {dT kT qT : Term arity .nat}
    {g : Term arity .bool} (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT)
    (hq : SFormula.PureNatTerm qT) (hg : SFormula.PureBoolTerm g) (v : Bool)
    (rho : Env arity) (E : PartialStabilizer) :
    (((bottomPbase dT kT qT).and (.eqBool (SC.closed g) (SC.b v))).eval
      Surface.code.body fuel rho E).isSome = true := by
  obtain ⟨bg, hgv⟩ := hg.eval_total Surface.code.body fuel rho
  have hbase := bottomPbase_tot (fuel := fuel) hd hk hq rho E
  cases hbe : (bottomPbase dT kT qT).eval Surface.code.body fuel rho E with
  | none => rw [hbe] at hbase; simp at hbase
  | some bb =>
      cases bb <;>
        simp [SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval, bind, Option.bind, hbe, hgv]

private theorem bottomPbase_extract {fuel arity m kv qv : Nat} {kT qT : Term arity .nat}
    (D : DistAtA arity (m + 1)) (rho : Env arity) (E : PartialStabilizer)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : Term.eval Surface.code.body fuel qT rho = some qv)
    (hPe : (bottomPbase D.dT kT qT).eval Surface.code.body fuel rho E = some true) :
    isBottomCell (oddDistance (m + 1)) kv = true ∧ isInside (oddDistance (m + 1)) qv = true := by
  simp only [bottomPbase, SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval, bind, Option.bind,
    bulkGuardTA_eval rho (D.evalsTo rho) hkv,
    interiorCellGuardTA_eval rho (D.evalsTo rho) hkv,
    topCellGuardTA_eval rho (D.evalsTo rho) hkv,
    rightCellGuardTA_eval rho (D.evalsTo rho) hkv,
    leftCellGuardTA_eval rho (D.evalsTo rho) hkv,
    bottomCellGuardTA_eval rho (D.evalsTo rho) hkv,
    insideGuardTA_eval rho (D.evalsTo rho) hqv] at hPe
  by_cases hB : isBottomCell (oddDistance (m + 1)) kv = true <;>
    by_cases hIn : isInside (oddDistance (m + 1)) qv = true <;> simp_all

private theorem bottomInner_evals {fuel arity m kv : Nat} {kT : Term arity .nat}
    (D : DistAtA arity (m + 1)) (rho : Env arity)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv) :
    Term.eval Surface.code.body fuel (innerDTA D.dT) rho = some (2 * (m + 1) + 1) ∧
      Term.eval Surface.code.body fuel (bottomKTA D.dT kT) rho
        = some (innerBottomK (2 * (m + 1) + 3) kv) := by
  refine ⟨?_, ?_⟩
  · rw [innerDTA, Term.eval, Term.eval, D.evalsTo rho]
    simp [Option.bind, Option.bind_eq_bind, oddDistance]
  · have := bottomKTA_evalsTo (d := oddDistance (m + 1)) rho (D.evalsTo rho) hkv
    simpa only [oddDistance] using this

/-- Bottom context-only: `kindF ∧ innerBulkF ∧ innerTopClassF ∧ innerRightClassF ∧ innerLeftClassF`. -/
private def bottomImpCtx {fuel arity m : Nat} {kT qT : Term arity .nat}
    (D : DistAtA arity (m + 1)) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    PureFamilyDerivA Surface.code.body fuel
      (.imp (bottomPbase D.dT kT qT)
        (.and (.eqBool (SC.closed (baseKindGuardTA D.dT kT)) (SC.b false))
          (.and (.eqBool (SC.closed (bulkGuardTA (recInnerDTA D.dT) (bottomKTA D.dT kT))) (SC.b false))
            (.and (.eqBool (SC.closed (topClassGuardTA (recInnerDTA D.dT) (bottomKTA D.dT kT))) (SC.b false))
              (.and (.eqBool (SC.closed (rightClassGuardTA (recInnerDTA D.dT) (bottomKTA D.dT kT))) (SC.b false))
                (.eqBool (SC.closed (leftClassGuardTA (recInnerDTA D.dT) (bottomKTA D.dT kT))) (SC.b false))))))) := by
  refine PureFamilyDerivA.arithBool _ ?_ ?_
  · simp only [arithBoolFragment, ArithBoolFragment.formula]
    rw [show ArithBoolFragment.formula (bottomPbase D.dT kT qT) = true from bottomPbase_frag D.pure hk hq]
    simp [ArithBoolFragment.sterm, SC.closed, SC.b, ArithBoolFragment.term, recInnerDTA,
      pureTerm_in_fragment (baseKindGuardTA_pure D.pure hk),
      pureTerm_in_fragment (bulkGuardTA_pure (innerDTA_pure D.pure) (bottomKTA_pure D.pure hk)),
      pureTerm_in_fragment (topClassGuardTA_pure (innerDTA_pure D.pure) (bottomKTA_pure D.pure hk)),
      pureTerm_in_fragment (rightClassGuardTA_pure (innerDTA_pure D.pure) (bottomKTA_pure D.pure hk)),
      pureTerm_in_fragment (leftClassGuardTA_pure (innerDTA_pure D.pure) (bottomKTA_pure D.pure hk))]
  · intro rho E
    cases hPe : (bottomPbase D.dT kT qT).eval Surface.code.body fuel rho E with
    | none => have := bottomPbase_tot (fuel := fuel) D.pure hk hq rho E; rw [hPe] at this; simp at this
    | some pv =>
        cases pv with
        | false => rw [SFormula.eval, hPe]; rfl
        | true =>
            rw [SFormula.eval, hPe]
            obtain ⟨kv, hkv⟩ := hk.eval_total Surface.code.body fuel rho
            obtain ⟨qv, hqv⟩ := hq.eval_total Surface.code.body fuel rho
            obtain ⟨hB, hIn⟩ := bottomPbase_extract D rho E hkv hqv hPe
            obtain ⟨hdInner, hkInner⟩ := bottomInner_evals D rho hkv
            have hB' := (by simpa [oddDistance] using hB : isBottomCell (2*(m+1)+3) kv = true)
            have hIn' := (by simpa [oddDistance] using hIn : isInside (2*(m+1)+3) qv = true)
            have hkindF := bottomKindFalseNat (m+1) kv qv hB' hIn'
            have hbf := bottomInnerBulkFalseNat (m+1) kv qv hB' hIn'
            have htcf := bottomInnerTopClassFalseNat (m+1) kv qv hB' hIn'
            have hrcf := bottomInnerRightClassFalseNat (m+1) kv qv hB' hIn'
            have hlcf := bottomInnerLeftClassFalseNat (m+1) kv qv hB' hIn'
            simp only [oddDistance] at hkindF
            simp only [show (2*(m+1)+1) - 1 = 2*(m+1) from by omega] at hbf
            simp only [SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval, bind, Option.bind,
              baseKindGuardTA_eval rho (D.evalsTo rho) hkv, recInnerDTA,
              bulkGuardTA_eval rho hdInner hkInner,
              topClassGuardTA_eval rho hdInner hkInner,
              rightClassGuardTA_eval rho hdInner hkInner,
              leftClassGuardTA_eval rho hdInner hkInner, oddDistance,
              show (2*(m+1)+1) - 1 = 2*(m+1) from by omega, hkindF, hbf, htcf, hrcf, hlcf]
            simp

private def bottomImpBand {fuel arity m : Nat} {kT qT : Term arity .nat} (v : Bool)
    (D : DistAtA arity (m + 1)) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    PureFamilyDerivA Surface.code.body fuel
      (.imp (.and (bottomPbase D.dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA D.dT kT qT)) (SC.b v)))
        (.eqBool (SC.closed (bottomBandGuardTA (recInnerDTA D.dT) (bottomKTA D.dT kT) (innerQTA D.dT qT)))
          (SC.b v))) := by
  refine impGuardA_of ?_ ?_ ?_ ?_
  · simp only [arithBoolFragment, ArithBoolFragment.formula]
    rw [show ArithBoolFragment.formula (bottomPbase D.dT kT qT) = true from bottomPbase_frag D.pure hk hq]
    simp [ArithBoolFragment.sterm, SC.closed, SC.b, ArithBoolFragment.term,
      pureTerm_in_fragment (baseBulkBandGuardTA_pure D.pure hk hq)]
  · exact bottomBandGuardTA_pure (innerDTA_pure D.pure) (bottomKTA_pure D.pure hk) (innerQTA_pure D.pure hq)
  · exact fun rho E => bottomPbaseAnd_tot D.pure hk hq (baseBulkBandGuardTA_pure D.pure hk hq) v rho E
  · intro rho E hPe
    obtain ⟨kv, hkv⟩ := hk.eval_total Surface.code.body fuel rho
    obtain ⟨qv, hqv⟩ := hq.eval_total Surface.code.body fuel rho
    rw [SFormula.eval] at hPe
    have hbase := bottomPbase_tot (fuel := fuel) D.pure hk hq rho E
    cases hbe : (bottomPbase D.dT kT qT).eval Surface.code.body fuel rho E with
    | none => rw [hbe] at hbase; simp at hbase
    | some bb =>
        cases bb with
        | false => rw [hbe] at hPe; simp at hPe
        | true =>
            rw [hbe] at hPe
            simp only [SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval,
              bind, Option.bind, baseBulkBandGuardTA_eval rho (D.evalsTo rho) hkv hqv,
              Option.some.injEq, decide_eq_true_eq, if_true] at hPe
            obtain ⟨hB, hIn⟩ := bottomPbase_extract D rho E hkv hqv hbe
            obtain ⟨hdInner, hkInner⟩ := bottomInner_evals D rho hkv
            have hqInner : Term.eval Surface.code.body fuel (innerQTA D.dT qT) rho
                = some (innerQval (2 * (m + 1) + 3) qv) := by
              have := innerQTA_evalsTo (d := oddDistance (m + 1)) rho (D.evalsTo rho) hqv
              simpa only [oddDistance] using this
            have hB' := (by simpa [oddDistance] using hB : isBottomCell (2*(m+1)+3) kv = true)
            have hIn' := (by simpa [oddDistance] using hIn : isInside (2*(m+1)+3) qv = true)
            rw [show recInnerDTA D.dT = innerDTA D.dT from rfl,
              bottomBandGuardTA_eval rho hdInner hkInner hqInner]
            have hcorr := bottomBandCorrNat (m + 1) kv qv hB' hIn'
            rw [hcorr, show (2 * (m + 1) + 3) = oddDistance (m + 1) from rfl, hPe]

def flatStepBottom {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : SFormula.Deriv Γ (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b false)))
    (hRight : SFormula.Deriv Γ (.eqBool (SC.closed (rightCellGuardTA dT kT)) (SC.b false)))
    (hLeft : SFormula.Deriv Γ (.eqBool (SC.closed (leftCellGuardTA dT kT)) (SC.b false)))
    (hBottom : SFormula.Deriv Γ (.eqBool (SC.closed (bottomCellGuardTA dT kT)) (SC.b true)))
    (hInside : SFormula.Deriv Γ (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b true)))
    (hImpCtx : SFormula.Deriv Γ
      (.imp (bottomPbase dT kT qT)
        (.and (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b false))
          (.and (.eqBool (SC.closed (bulkGuardTA (recInnerDTA dT) (bottomKTA dT kT))) (SC.b false))
            (.and (.eqBool (SC.closed (topClassGuardTA (recInnerDTA dT) (bottomKTA dT kT))) (SC.b false))
              (.and (.eqBool (SC.closed (rightClassGuardTA (recInnerDTA dT) (bottomKTA dT kT))) (SC.b false))
                (.eqBool (SC.closed (leftClassGuardTA (recInnerDTA dT) (bottomKTA dT kT))) (SC.b false))))))))
    (hImpBandT : SFormula.Deriv Γ
      (.imp (.and (bottomPbase dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)))
        (.eqBool (SC.closed (bottomBandGuardTA (recInnerDTA dT) (bottomKTA dT kT) (innerQTA dT qT)))
          (SC.b true))))
    (hImpBandF : SFormula.Deriv Γ
      (.imp (.and (bottomPbase dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false)))
        (.eqBool (SC.closed (bottomBandGuardTA (recInnerDTA dT) (bottomKTA dT kT) (innerQTA dT qT)))
          (SC.b false)))) :
    SFormula.Deriv Γ
      (.eqPauli
        (SC.closed (baseLeafTreeTA (recInnerDTA dT) (bottomKTA dT kT) (innerQTA dT qT)))
        (SC.closed (baseLeafTreeTA dT kT qT))) := by
  have hPbase : SFormula.Deriv Γ (bottomPbase dT kT qT) :=
    SFormula.Deriv.andIntro hBulk (SFormula.Deriv.andIntro hInterior
      (SFormula.Deriv.andIntro hTop (SFormula.Deriv.andIntro hRight
        (SFormula.Deriv.andIntro hLeft (SFormula.Deriv.andIntro hBottom hInside)))))
  have hCtx := SFormula.Deriv.mp hImpCtx hPbase
  have hKindF := SFormula.Deriv.andElimLeft hCtx
  have hInnerBulkF := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hCtx)
  have hInnerTopClassF := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight hCtx))
  have hInnerRightClassF := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hCtx)))
  have hInnerLeftClassF := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hCtx)))
  refine SFormula.Deriv.boolCases (SC.closed (baseBulkBandGuardTA dT kT qT)) _ ?_ ?_
  · -- outer band = true → both sides X
    set Δ := (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true) :: Γ) with hΔ
    have hsub : ∀ C, C ∈ Γ → C ∈ Δ := by intro C hC; exact List.mem_cons_of_mem _ hC
    have hOBandT : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)) :=
      .assumption
    have wkBulk := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hBulk
    have wkKindF := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hKindF
    have wkInnerBulkF := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hInnerBulkF
    have wkInnerTopClassF := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hInnerTopClassF
    have wkInnerRightClassF := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hInnerRightClassF
    have wkInnerLeftClassF := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hInnerLeftClassF
    have wkPbase := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hPbase
    have hInnerBand := SFormula.Deriv.mp
      (SFormula.Deriv.contextWeakening (Δ := Δ) hsub hImpBandT)
      (SFormula.Deriv.andIntro wkPbase hOBandT)
    have lhsX := baseLeafBottomXS (recInnerDTA dT) (bottomKTA dT kT) (innerQTA dT qT)
      wkInnerBulkF wkInnerTopClassF wkInnerRightClassF wkInnerLeftClassF hInnerBand
    have rhsX := baseLeafXS dT kT qT wkBulk hOBandT wkKindF
    exact SFormula.Deriv.eqPauliTrans _ _ _ lhsX (SFormula.Deriv.eqPauliSymm _ _ rhsX)
  · -- outer band = false → both sides I
    set Δ := (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false) :: Γ) with hΔ
    have hsub : ∀ C, C ∈ Γ → C ∈ Δ := by intro C hC; exact List.mem_cons_of_mem _ hC
    have hOBandF : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false)) :=
      .assumption
    have wkInnerBulkF := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hInnerBulkF
    have wkInnerTopClassF := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hInnerTopClassF
    have wkInnerRightClassF := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hInnerRightClassF
    have wkInnerLeftClassF := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hInnerLeftClassF
    have wkBulk := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hBulk
    have wkPbase := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hPbase
    have hInnerBand := SFormula.Deriv.mp
      (SFormula.Deriv.contextWeakening (Δ := Δ) hsub hImpBandF)
      (SFormula.Deriv.andIntro wkPbase hOBandF)
    have lhsI := baseLeafBottomIS (recInnerDTA dT) (bottomKTA dT kT) (innerQTA dT qT)
      wkInnerBulkF wkInnerTopClassF wkInnerRightClassF wkInnerLeftClassF hInnerBand
    have rhsI := baseLeafBulkIS dT kT qT wkBulk hOBandF
    exact SFormula.Deriv.eqPauliTrans _ _ _ lhsI (SFormula.Deriv.eqPauliSymm _ _ rhsI)

/-! ### Non-recursing promoted-not-inside leaf equalities

When a promoted-boundary cell is NOT inside, the recursive entry produces the
outer-ring `ite outerGuard kind I` form (e.g. `ite topOuter X I`).  The flat
classifier `baseLeafTreeTA` produces the corresponding boundary-band leaf.  Like
the inside leaves, relating the two distinct guard families is SelfSim content;
isolated here.  Interior-not-inside resolves directly to `I` on the recursive
side, but the flat side's leaf there is also `I` only under the matching outer
guards, so it is isolated too. -/

/-! ### Promoted-not-inside boundary Nat correspondences

Under cell ∧ ¬inside, the outer bulk band membership equals the boundary outer-ring
membership, and the outer bulk kind is the cell's fixed kind.  Derived from the bulk
form of `surfaceCellPauli` combined with `surfaceCellPauli_*Cell_notInside`. -/

/-- Generic: from the two `surfaceCellPauli` forms (bulk band/kind and the
`notInside` outer-ring) conclude `band = outer`, given the cell kind is `kindP ≠ I`
and the cell is a bulk cell. -/
private theorem band_eq_outer_of_forms {bandV outerV : Bool} {kindP : Pauli}
    (hkindNeI : kindP ≠ Pauli.I)
    (hform : (if bandV then kindP else Pauli.I) = (if outerV then kindP else Pauli.I)) :
    bandV = outerV := by
  cases bandV <;> cases outerV <;> simp_all

/-- Top NI: outer band membership equals the top outer-ring membership. -/
private theorem topNI_bandEqOuterNat (M k q : Nat)
    (hT : isTopCell (2*M+3) k = true) (hInF : isInside (2*M+3) q = false) :
    baseBulkBandVal (2*M+3) k q = topOuterVal (2*M+3) k q := by
  -- top cell is bulk and X-kind; the bulk form of surfaceCellPauli is `ite band X I`,
  -- and the notInside form is `ite topOuter X I`.
  have hbulk : k < (2*M+3-1)*(2*M+3-1) := by
    simp only [isTopCell, cellR, cellC, cellLastCell, cellInnerHalf, Bool.and_eq_true,
      decide_eq_true_eq] at hT
    obtain ⟨hr, hc, htb⟩ := hT
    have hklt : k < 2*M+2 := by
      have := (Nat.div_eq_zero_iff (a := k) (b := 2*M+2)).mp (by simpa [show 2*M+3-1 = 2*M+2 from by omega] using hr)
      omega
    have : 2*M+2 ≤ (2*M+3-1)*(2*M+3-1) := by
      rw [show 2*M+3-1 = 2*M+2 from by omega]; exact Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hkindX : baseKindVal (2*M+3) k = false := by
    simp only [isTopCell, cellR, cellC, cellInnerHalf, Bool.and_eq_true,
      decide_eq_true_eq] at hT
    obtain ⟨hr, hc, htb⟩ := hT
    simp only [baseKindVal, cellR, cellC, show 2*M+3-1 = 2*M+2 from by omega,
      decide_eq_false_iff_not]
    simp only [show 2*M+3-1 = 2*M+2 from by omega] at hr hc; omega
  -- bulk form
  have hbulkForm : surfaceCellPauli (2*M+3) k q
      = (if baseBulkBandVal (2*M+3) k q then Pauli.X else Pauli.I) := by
    simp only [surfaceCellPauli, if_pos hbulk, baseBulkBandVal, inBulkBand, bulkKind, cellRow,
      cellCol, cellR, cellC, Bool.and_assoc]
    have : ¬ (k / (2*M+3-1) + k % (2*M+3-1)) % 2 = 0 := by
      simp only [baseKindVal, cellR, cellC, decide_eq_false_iff_not] at hkindX; exact hkindX
    by_cases hb : (decide (q / (2*M+3) = k / (2*M+3-1)) || decide (q / (2*M+3) = k / (2*M+3-1) + 1)) &&
        ((decide (q % (2*M+3) = k % (2*M+3-1)) || decide (q % (2*M+3) = k % (2*M+3-1) + 1)) &&
          decide (k < (2*M+3-1)*(2*M+3-1))) = true <;>
      simp only [hb, if_pos, if_neg, this] <;> simp_all
  have houterForm := surfaceCellPauli_topCell_notInside hT hInF
  rw [hbulkForm] at houterForm
  exact band_eq_outer_of_forms (by decide) houterForm

/-- Top NI: the outer bulk kind is `X` (a top cell has odd parity). -/
private theorem topNI_kindFalseNat (M k : Nat) (hT : isTopCell (2*M+3) k = true) :
    baseKindVal (2*M+3) k = false := by
  simp only [isTopCell, cellR, cellC, cellInnerHalf, Bool.and_eq_true, decide_eq_true_eq] at hT
  obtain ⟨hr, hc, htb⟩ := hT
  simp only [baseKindVal, cellR, cellC, show 2*M+3-1 = 2*M+2 from by omega, decide_eq_false_iff_not]
  simp only [show 2*M+3-1 = 2*M+2 from by omega] at hr hc; omega

/-- Right NI: outer band membership equals the right outer-ring membership. -/
private theorem rightNI_bandEqOuterNat (M k q : Nat)
    (hR : isRightCell (2*M+3) k = true) (hInF : isInside (2*M+3) q = false) :
    baseBulkBandVal (2*M+3) k q = rightOuterVal (2*M+3) k q := by
  have hodd : (2*M+3) % 2 = 1 := by omega
  have hbulk : k < (2*M+3-1)*(2*M+3-1) := by
    simp only [isRightCell, cellR, cellC, cellLastCell, cellInnerHalf, Bool.and_eq_true,
      decide_eq_true_eq] at hR
    obtain ⟨hc, hr, hrb⟩ := hR
    have hkdm : k = k/(2*M+2)*(2*M+2) + k%(2*M+2) := by
      rw [Nat.mul_comm]; exact (Nat.div_add_mod k (2*M+2)).symm
    have hc2 : k % (2*M+2) = 2*M+1 := by
      simp only [show 2*M+3-1 = 2*M+2 from by omega] at hc; omega
    have hr2 : k / (2*M+2) < 2*M+2 := by
      simp only [show 2*M+3-1 = 2*M+2 from by omega, show 2*M+3-2 = 2*M+1 from by omega,
        show 2*M+1-1 = 2*M from by omega] at hr hrb
      rw [Nat.mul_div_cancel_left M (by omega : 0 < 2)] at hrb; omega
    rw [show 2*M+3-1 = 2*M+2 from by omega, hkdm, hc2]
    exact cellLinIndexLt' hr2 (by omega)
  have hkindZ : ¬ baseKindVal (2*M+3) k = false := by
    simp only [isRightCell, cellR, cellC, cellLastCell, cellInnerHalf, Bool.and_eq_true,
      decide_eq_true_eq] at hR
    obtain ⟨hc, hr, hrb⟩ := hR
    simp only [baseKindVal, cellR, cellC, show 2*M+3-1 = 2*M+2 from by omega,
      decide_eq_false_iff_not, not_not]
    simp only [show 2*M+3-1 = 2*M+2 from by omega] at hc hr; omega
  have hbulkForm : surfaceCellPauli (2*M+3) k q
      = (if baseBulkBandVal (2*M+3) k q then Pauli.Z else Pauli.I) := by
    simp only [surfaceCellPauli, if_pos hbulk, baseBulkBandVal, inBulkBand, bulkKind, cellRow,
      cellCol, cellR, cellC, Bool.and_assoc]
    have hkz : (k / (2*M+3-1) + k % (2*M+3-1)) % 2 = 0 := by
      simp only [baseKindVal, cellR, cellC, decide_eq_false_iff_not, not_not] at hkindZ; exact hkindZ
    by_cases hb : (decide (q / (2*M+3) = k / (2*M+3-1)) || decide (q / (2*M+3) = k / (2*M+3-1) + 1)) &&
        ((decide (q % (2*M+3) = k % (2*M+3-1)) || decide (q % (2*M+3) = k % (2*M+3-1) + 1)) &&
          decide (k < (2*M+3-1)*(2*M+3-1))) = true <;>
      simp only [hb, if_pos, if_neg, hkz] <;> simp_all
  have houterForm := surfaceCellPauli_rightCell_notInside hR hInF hodd
  rw [hbulkForm] at houterForm
  exact band_eq_outer_of_forms (by decide) houterForm

/-- Right NI: the outer bulk kind is `Z`. -/
private theorem rightNI_kindTrueNat (M k : Nat) (hR : isRightCell (2*M+3) k = true) :
    baseKindVal (2*M+3) k = true := by
  simp only [isRightCell, cellR, cellC, cellLastCell, cellInnerHalf, Bool.and_eq_true,
    decide_eq_true_eq] at hR
  obtain ⟨hc, hr, hrb⟩ := hR
  simp only [baseKindVal, cellR, cellC, show 2*M+3-1 = 2*M+2 from by omega, decide_eq_true_eq]
  simp only [show 2*M+3-1 = 2*M+2 from by omega] at hc hr; omega

/-- Left NI: outer band membership equals the left outer-ring membership. -/
private theorem leftNI_bandEqOuterNat (M k q : Nat)
    (hL : isLeftCell (2*M+3) k = true) (hInF : isInside (2*M+3) q = false) :
    baseBulkBandVal (2*M+3) k q = leftOuterVal (2*M+3) k q := by
  have hbulk : k < (2*M+3-1)*(2*M+3-1) := by
    simp only [isLeftCell, cellR, cellC, cellInnerHalf, Bool.and_eq_true, decide_eq_true_eq] at hL
    obtain ⟨hc, hr, hlb⟩ := hL
    have hkdm : k = k/(2*M+2)*(2*M+2) + k%(2*M+2) := by
      rw [Nat.mul_comm]; exact (Nat.div_add_mod k (2*M+2)).symm
    have hc2 : k % (2*M+2) = 0 := by simp only [show 2*M+3-1 = 2*M+2 from by omega] at hc; omega
    have hr2 : k / (2*M+2) < 2*M+2 := by
      simp only [show 2*M+3-1 = 2*M+2 from by omega, show 2*M+3-2 = 2*M+1 from by omega,
        show 2*M+1-1 = 2*M from by omega] at hr hlb
      rw [Nat.mul_div_cancel_left M (by omega : 0 < 2)] at hlb; omega
    rw [show 2*M+3-1 = 2*M+2 from by omega, hkdm, hc2]
    exact cellLinIndexLt' hr2 (by omega)
  have hkindZ : ¬ baseKindVal (2*M+3) k = false := by
    simp only [isLeftCell, cellR, cellC, cellInnerHalf, Bool.and_eq_true, decide_eq_true_eq] at hL
    obtain ⟨hc, hr, hlb⟩ := hL
    simp only [baseKindVal, cellR, cellC, show 2*M+3-1 = 2*M+2 from by omega,
      decide_eq_false_iff_not, not_not]
    simp only [show 2*M+3-1 = 2*M+2 from by omega] at hc hr; omega
  have hbulkForm : surfaceCellPauli (2*M+3) k q
      = (if baseBulkBandVal (2*M+3) k q then Pauli.Z else Pauli.I) := by
    simp only [surfaceCellPauli, if_pos hbulk, baseBulkBandVal, inBulkBand, bulkKind, cellRow,
      cellCol, cellR, cellC, Bool.and_assoc]
    have hkz : (k / (2*M+3-1) + k % (2*M+3-1)) % 2 = 0 := by
      simp only [baseKindVal, cellR, cellC, decide_eq_false_iff_not, not_not] at hkindZ; exact hkindZ
    by_cases hb : (decide (q / (2*M+3) = k / (2*M+3-1)) || decide (q / (2*M+3) = k / (2*M+3-1) + 1)) &&
        ((decide (q % (2*M+3) = k % (2*M+3-1)) || decide (q % (2*M+3) = k % (2*M+3-1) + 1)) &&
          decide (k < (2*M+3-1)*(2*M+3-1))) = true <;>
      simp only [hb, if_pos, if_neg, hkz] <;> simp_all
  have houterForm := surfaceCellPauli_leftCell_notInside hL hInF
  rw [hbulkForm] at houterForm
  exact band_eq_outer_of_forms (by decide) houterForm

/-- Left NI: the outer bulk kind is `Z`. -/
private theorem leftNI_kindTrueNat (M k : Nat) (hL : isLeftCell (2*M+3) k = true) :
    baseKindVal (2*M+3) k = true := by
  simp only [isLeftCell, cellR, cellC, cellInnerHalf, Bool.and_eq_true, decide_eq_true_eq] at hL
  obtain ⟨hc, hr, hlb⟩ := hL
  simp only [baseKindVal, cellR, cellC, show 2*M+3-1 = 2*M+2 from by omega, decide_eq_true_eq]
  simp only [show 2*M+3-1 = 2*M+2 from by omega] at hc hr; omega

/-- Bottom NI: outer band membership equals the bottom outer-ring membership. -/
private theorem bottomNI_bandEqOuterNat (M k q : Nat)
    (hB : isBottomCell (2*M+3) k = true) (hInF : isInside (2*M+3) q = false) :
    baseBulkBandVal (2*M+3) k q = bottomOuterVal (2*M+3) k q := by
  have hodd : (2*M+3) % 2 = 1 := by omega
  have hbulk : k < (2*M+3-1)*(2*M+3-1) := by
    simp only [isBottomCell, cellR, cellC, cellLastCell, cellInnerHalf, Bool.and_eq_true,
      decide_eq_true_eq] at hB
    obtain ⟨hr, hc, hbb⟩ := hB
    have hkdm : k = k/(2*M+2)*(2*M+2) + k%(2*M+2) := by
      rw [Nat.mul_comm]; exact (Nat.div_add_mod k (2*M+2)).symm
    have hr2 : k / (2*M+2) = 2*M+1 := by simp only [show 2*M+3-1 = 2*M+2 from by omega] at hr; omega
    have hc2 : k % (2*M+2) < 2*M+2 := Nat.mod_lt _ (by omega)
    rw [show 2*M+3-1 = 2*M+2 from by omega, hkdm, hr2]
    exact cellLinIndexLt' (by omega) hc2
  have hkindX : baseKindVal (2*M+3) k = false := by
    simp only [isBottomCell, cellR, cellC, cellLastCell, cellInnerHalf, Bool.and_eq_true,
      decide_eq_true_eq] at hB
    obtain ⟨hr, hc, hbb⟩ := hB
    simp only [baseKindVal, cellR, cellC, show 2*M+3-1 = 2*M+2 from by omega, decide_eq_false_iff_not]
    simp only [show 2*M+3-1 = 2*M+2 from by omega] at hr hc; omega
  have hbulkForm : surfaceCellPauli (2*M+3) k q
      = (if baseBulkBandVal (2*M+3) k q then Pauli.X else Pauli.I) := by
    simp only [surfaceCellPauli, if_pos hbulk, baseBulkBandVal, inBulkBand, bulkKind, cellRow,
      cellCol, cellR, cellC, Bool.and_assoc]
    have hkz : ¬ (k / (2*M+3-1) + k % (2*M+3-1)) % 2 = 0 := by
      simp only [baseKindVal, cellR, cellC, decide_eq_false_iff_not] at hkindX; exact hkindX
    by_cases hb : (decide (q / (2*M+3) = k / (2*M+3-1)) || decide (q / (2*M+3) = k / (2*M+3-1) + 1)) &&
        ((decide (q % (2*M+3) = k % (2*M+3-1)) || decide (q % (2*M+3) = k % (2*M+3-1) + 1)) &&
          decide (k < (2*M+3-1)*(2*M+3-1))) = true <;>
      simp only [hb, if_pos, if_neg, hkz] <;> simp_all
  have houterForm := surfaceCellPauli_bottomCell_notInside hB hInF hodd
  rw [hbulkForm] at houterForm
  exact band_eq_outer_of_forms (by decide) houterForm

/-- Bottom NI: the outer bulk kind is `X`. -/
private theorem bottomNI_kindFalseNat (M k : Nat) (hB : isBottomCell (2*M+3) k = true) :
    baseKindVal (2*M+3) k = false := by
  simp only [isBottomCell, cellR, cellC, cellLastCell, cellInnerHalf, Bool.and_eq_true,
    decide_eq_true_eq] at hB
  obtain ⟨hr, hc, hbb⟩ := hB
  simp only [baseKindVal, cellR, cellC, show 2*M+3-1 = 2*M+2 from by omega, decide_eq_false_iff_not]
  simp only [show 2*M+3-1 = 2*M+2 from by omega] at hr hc; omega

def flatStepInteriorNI {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b true)))
    (hInside : SFormula.Deriv Γ (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b false)))
    -- inner-band correspondence: under interior ∧ ¬inside the outer bulk band is empty.
    (hImpBandF : SFormula.Deriv Γ
      (.imp (interiorPbaseNI dT kT qT)
        (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false)))) :
    SFormula.Deriv Γ
      (.eqPauli (SC.closed (.pauliLit Pauli.I)) (SC.closed (baseLeafTreeTA dT kT qT))) := by
  have hPbase : SFormula.Deriv Γ (interiorPbaseNI dT kT qT) :=
    SFormula.Deriv.andIntro hBulk (SFormula.Deriv.andIntro hInterior hInside)
  have hOBandF := SFormula.Deriv.mp hImpBandF hPbase
  -- outer reduces to `I` (bulk = true, band = false); LHS is already `I`.
  exact SFormula.Deriv.eqPauliSymm _ _ (baseLeafBulkIS dT kT qT hBulk hOBandF)

/-! ### Top NI leaf: premise + correspondence implications -/

/-- Top NI premise: `bulk ∧ ¬interior ∧ top ∧ ¬inside`. -/
private def topPbaseNI {arity : Nat} (dT kT qT : Term arity .nat) : SFormula arity :=
  .and (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true))
    (.and (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false))
      (.and (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b true))
        (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b false))))

private theorem topPbaseNI_frag {arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    arithBoolFragment (topPbaseNI dT kT qT) = true := by
  simp only [topPbaseNI, arithBoolFragment, ArithBoolFragment.formula, ArithBoolFragment.sterm,
    SC.closed, SC.b, ArithBoolFragment.term,
    pureTerm_in_fragment (bulkGuardTA_pure hd hk),
    pureTerm_in_fragment (interiorCellGuardTA_pure hd hk),
    pureTerm_in_fragment (topCellGuardTA_pure hd hk),
    pureTerm_in_fragment (insideGuardTA_pure hd hq), Bool.and_self]

private theorem topPbaseNI_tot {fuel arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (rho : Env arity) (E : PartialStabilizer) :
    ((topPbaseNI dT kT qT).eval Surface.code.body fuel rho E).isSome = true := by
  obtain ⟨b1, h1⟩ := (bulkGuardTA_pure hd hk).eval_total Surface.code.body fuel rho
  obtain ⟨b2, h2⟩ := (interiorCellGuardTA_pure hd hk).eval_total Surface.code.body fuel rho
  obtain ⟨b3, h3⟩ := (topCellGuardTA_pure hd hk).eval_total Surface.code.body fuel rho
  obtain ⟨b4, h4⟩ := (insideGuardTA_pure hd hq).eval_total Surface.code.body fuel rho
  simp only [topPbaseNI, SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval, bind, Option.bind,
    h1, h2, h3, h4]
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> simp

private theorem topPbaseNIAnd_tot {fuel arity : Nat} {dT kT qT : Term arity .nat}
    {g : Term arity .bool} (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT)
    (hq : SFormula.PureNatTerm qT) (hg : SFormula.PureBoolTerm g) (v : Bool)
    (rho : Env arity) (E : PartialStabilizer) :
    (((topPbaseNI dT kT qT).and (.eqBool (SC.closed g) (SC.b v))).eval
      Surface.code.body fuel rho E).isSome = true := by
  obtain ⟨bg, hgv⟩ := hg.eval_total Surface.code.body fuel rho
  have hbase := topPbaseNI_tot (fuel := fuel) hd hk hq rho E
  cases hbe : (topPbaseNI dT kT qT).eval Surface.code.body fuel rho E with
  | none => rw [hbe] at hbase; simp at hbase
  | some bb =>
      cases bb <;>
        simp [SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval, bind, Option.bind, hbe, hgv]

private theorem topPbaseNI_extract {fuel arity m kv qv : Nat} {kT qT : Term arity .nat}
    (D : DistAtA arity (m + 1)) (rho : Env arity) (E : PartialStabilizer)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : Term.eval Surface.code.body fuel qT rho = some qv)
    (hPe : (topPbaseNI D.dT kT qT).eval Surface.code.body fuel rho E = some true) :
    isTopCell (oddDistance (m + 1)) kv = true ∧ isInside (oddDistance (m + 1)) qv = false := by
  simp only [topPbaseNI, SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval, bind, Option.bind,
    bulkGuardTA_eval rho (D.evalsTo rho) hkv,
    interiorCellGuardTA_eval rho (D.evalsTo rho) hkv,
    topCellGuardTA_eval rho (D.evalsTo rho) hkv,
    insideGuardTA_eval rho (D.evalsTo rho) hqv] at hPe
  by_cases hT : isTopCell (oddDistance (m + 1)) kv = true <;>
    by_cases hIn : isInside (oddDistance (m + 1)) qv = true <;> simp_all

/-- Top NI context: `baseKindGuardTA outer = false`. -/
private def topNIImpCtx {fuel arity m : Nat} {kT qT : Term arity .nat}
    (D : DistAtA arity (m + 1)) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    PureFamilyDerivA Surface.code.body fuel
      (.imp (topPbaseNI D.dT kT qT)
        (.eqBool (SC.closed (baseKindGuardTA D.dT kT)) (SC.b false))) := by
  refine impGuardA_of (topPbaseNI_frag D.pure hk hq) (baseKindGuardTA_pure D.pure hk)
    (fun rho E => topPbaseNI_tot D.pure hk hq rho E) ?_
  intro rho E hPe
  obtain ⟨kv, hkv⟩ := hk.eval_total Surface.code.body fuel rho
  obtain ⟨qv, hqv⟩ := hq.eval_total Surface.code.body fuel rho
  obtain ⟨hT, _⟩ := topPbaseNI_extract D rho E hkv hqv hPe
  rw [baseKindGuardTA_eval rho (D.evalsTo rho) hkv]
  have := topNI_kindFalseNat (m+1) kv (by simpa [oddDistance] using hT)
  simpa [oddDistance] using this

/-- Top NI band correspondence: `topOuterGuardTA = band`. -/
private def topNIImpBand {fuel arity m : Nat} {kT qT : Term arity .nat} (v : Bool)
    (D : DistAtA arity (m + 1)) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    PureFamilyDerivA Surface.code.body fuel
      (.imp (.and (topPbaseNI D.dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA D.dT kT qT)) (SC.b v)))
        (.eqBool (SC.closed (topOuterGuardTA D.dT kT qT)) (SC.b v))) := by
  refine impGuardA_of ?_ ?_ ?_ ?_
  · simp only [arithBoolFragment, ArithBoolFragment.formula]
    rw [show ArithBoolFragment.formula (topPbaseNI D.dT kT qT) = true from topPbaseNI_frag D.pure hk hq]
    simp [ArithBoolFragment.sterm, SC.closed, SC.b, ArithBoolFragment.term,
      pureTerm_in_fragment (baseBulkBandGuardTA_pure D.pure hk hq)]
  · exact topOuterGuardTA_pure D.pure hk hq
  · exact fun rho E => topPbaseNIAnd_tot D.pure hk hq (baseBulkBandGuardTA_pure D.pure hk hq) v rho E
  · intro rho E hPe
    obtain ⟨kv, hkv⟩ := hk.eval_total Surface.code.body fuel rho
    obtain ⟨qv, hqv⟩ := hq.eval_total Surface.code.body fuel rho
    rw [SFormula.eval] at hPe
    have hbase := topPbaseNI_tot (fuel := fuel) D.pure hk hq rho E
    cases hbe : (topPbaseNI D.dT kT qT).eval Surface.code.body fuel rho E with
    | none => rw [hbe] at hbase; simp at hbase
    | some bb =>
        cases bb with
        | false => rw [hbe] at hPe; simp at hPe
        | true =>
            rw [hbe] at hPe
            simp only [SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval,
              bind, Option.bind, baseBulkBandGuardTA_eval rho (D.evalsTo rho) hkv hqv,
              Option.some.injEq, decide_eq_true_eq, if_true] at hPe
            obtain ⟨hT, hInF⟩ := topPbaseNI_extract D rho E hkv hqv hbe
            rw [topOuterGuardTA_eval rho (D.evalsTo rho) hkv hqv]
            have hcorr := topNI_bandEqOuterNat (m + 1) kv qv
              (by simpa [oddDistance] using hT) (by simpa [oddDistance] using hInF)
            rw [show (oddDistance (m + 1)) = 2 * (m + 1) + 3 from rfl, ← hcorr,
              show (2 * (m + 1) + 3) = oddDistance (m + 1) from rfl, hPe]

def flatStepTopNI {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : SFormula.Deriv Γ (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b true)))
    (hInside : SFormula.Deriv Γ (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b false)))
    (hImpCtx : SFormula.Deriv Γ
      (.imp (topPbaseNI dT kT qT) (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b false))))
    (hImpBandT : SFormula.Deriv Γ
      (.imp (.and (topPbaseNI dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)))
        (.eqBool (SC.closed (topOuterGuardTA dT kT qT)) (SC.b true))))
    (hImpBandF : SFormula.Deriv Γ
      (.imp (.and (topPbaseNI dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false)))
        (.eqBool (SC.closed (topOuterGuardTA dT kT qT)) (SC.b false)))) :
    SFormula.Deriv Γ
      (.eqPauli
        (SC.closed (.ite (topOuterGuardTA dT kT qT) (.pauliLit Pauli.X) (.pauliLit Pauli.I)))
        (SC.closed (baseLeafTreeTA dT kT qT))) := by
  have hPbase : SFormula.Deriv Γ (topPbaseNI dT kT qT) :=
    SFormula.Deriv.andIntro hBulk (SFormula.Deriv.andIntro hInterior
      (SFormula.Deriv.andIntro hTop hInside))
  have hKindF := SFormula.Deriv.mp hImpCtx hPbase
  refine SFormula.Deriv.boolCases (SC.closed (baseBulkBandGuardTA dT kT qT)) _ ?_ ?_
  · set Δ := (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true) :: Γ) with hΔ
    have hsub : ∀ C, C ∈ Γ → C ∈ Δ := by intro C hC; exact List.mem_cons_of_mem _ hC
    have hOBandT : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)) :=
      .assumption
    have wkBulk := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hBulk
    have wkKindF := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hKindF
    have wkPbase := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hPbase
    have hOuterT := SFormula.Deriv.mp
      (SFormula.Deriv.contextWeakening (Δ := Δ) hsub hImpBandT)
      (SFormula.Deriv.andIntro wkPbase hOBandT)
    have lhsX : SFormula.Deriv Δ (.eqPauli
        (SC.closed (.ite (topOuterGuardTA dT kT qT) (.pauliLit Pauli.X) (.pauliLit Pauli.I)))
        (SC.closed (.pauliLit Pauli.X))) := SFormula.Deriv.pauliIteSelectThen _ _ _ hOuterT
    have rhsX := baseLeafXS dT kT qT wkBulk hOBandT wkKindF
    exact SFormula.Deriv.eqPauliTrans _ _ _ lhsX (SFormula.Deriv.eqPauliSymm _ _ rhsX)
  · set Δ := (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false) :: Γ) with hΔ
    have hsub : ∀ C, C ∈ Γ → C ∈ Δ := by intro C hC; exact List.mem_cons_of_mem _ hC
    have hOBandF : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false)) :=
      .assumption
    have wkBulk := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hBulk
    have wkPbase := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hPbase
    have hOuterF := SFormula.Deriv.mp
      (SFormula.Deriv.contextWeakening (Δ := Δ) hsub hImpBandF)
      (SFormula.Deriv.andIntro wkPbase hOBandF)
    have lhsI : SFormula.Deriv Δ (.eqPauli
        (SC.closed (.ite (topOuterGuardTA dT kT qT) (.pauliLit Pauli.X) (.pauliLit Pauli.I)))
        (SC.closed (.pauliLit Pauli.I))) := SFormula.Deriv.pauliIteSelectElse _ _ _ hOuterF
    have rhsI := baseLeafBulkIS dT kT qT wkBulk hOBandF
    exact SFormula.Deriv.eqPauliTrans _ _ _ lhsI (SFormula.Deriv.eqPauliSymm _ _ rhsI)

/-! ### Right NI leaf: premise + correspondence implications -/

private def rightPbaseNI {arity : Nat} (dT kT qT : Term arity .nat) : SFormula arity :=
  .and (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true))
    (.and (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false))
      (.and (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b false))
        (.and (.eqBool (SC.closed (rightCellGuardTA dT kT)) (SC.b true))
          (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b false)))))

private theorem rightPbaseNI_frag {arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    arithBoolFragment (rightPbaseNI dT kT qT) = true := by
  simp only [rightPbaseNI, arithBoolFragment, ArithBoolFragment.formula, ArithBoolFragment.sterm,
    SC.closed, SC.b, ArithBoolFragment.term,
    pureTerm_in_fragment (bulkGuardTA_pure hd hk),
    pureTerm_in_fragment (interiorCellGuardTA_pure hd hk),
    pureTerm_in_fragment (topCellGuardTA_pure hd hk),
    pureTerm_in_fragment (rightCellGuardTA_pure hd hk),
    pureTerm_in_fragment (insideGuardTA_pure hd hq), Bool.and_self]

private theorem rightPbaseNI_tot {fuel arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (rho : Env arity) (E : PartialStabilizer) :
    ((rightPbaseNI dT kT qT).eval Surface.code.body fuel rho E).isSome = true := by
  obtain ⟨b1, h1⟩ := (bulkGuardTA_pure hd hk).eval_total Surface.code.body fuel rho
  obtain ⟨b2, h2⟩ := (interiorCellGuardTA_pure hd hk).eval_total Surface.code.body fuel rho
  obtain ⟨b3, h3⟩ := (topCellGuardTA_pure hd hk).eval_total Surface.code.body fuel rho
  obtain ⟨b4, h4⟩ := (rightCellGuardTA_pure hd hk).eval_total Surface.code.body fuel rho
  obtain ⟨b5, h5⟩ := (insideGuardTA_pure hd hq).eval_total Surface.code.body fuel rho
  simp only [rightPbaseNI, SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval, bind, Option.bind,
    h1, h2, h3, h4, h5]
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> simp

private theorem rightPbaseNIAnd_tot {fuel arity : Nat} {dT kT qT : Term arity .nat}
    {g : Term arity .bool} (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT)
    (hq : SFormula.PureNatTerm qT) (hg : SFormula.PureBoolTerm g) (v : Bool)
    (rho : Env arity) (E : PartialStabilizer) :
    (((rightPbaseNI dT kT qT).and (.eqBool (SC.closed g) (SC.b v))).eval
      Surface.code.body fuel rho E).isSome = true := by
  obtain ⟨bg, hgv⟩ := hg.eval_total Surface.code.body fuel rho
  have hbase := rightPbaseNI_tot (fuel := fuel) hd hk hq rho E
  cases hbe : (rightPbaseNI dT kT qT).eval Surface.code.body fuel rho E with
  | none => rw [hbe] at hbase; simp at hbase
  | some bb =>
      cases bb <;>
        simp [SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval, bind, Option.bind, hbe, hgv]

private theorem rightPbaseNI_extract {fuel arity m kv qv : Nat} {kT qT : Term arity .nat}
    (D : DistAtA arity (m + 1)) (rho : Env arity) (E : PartialStabilizer)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : Term.eval Surface.code.body fuel qT rho = some qv)
    (hPe : (rightPbaseNI D.dT kT qT).eval Surface.code.body fuel rho E = some true) :
    isRightCell (oddDistance (m + 1)) kv = true ∧ isInside (oddDistance (m + 1)) qv = false := by
  simp only [rightPbaseNI, SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval, bind, Option.bind,
    bulkGuardTA_eval rho (D.evalsTo rho) hkv,
    interiorCellGuardTA_eval rho (D.evalsTo rho) hkv,
    topCellGuardTA_eval rho (D.evalsTo rho) hkv,
    rightCellGuardTA_eval rho (D.evalsTo rho) hkv,
    insideGuardTA_eval rho (D.evalsTo rho) hqv] at hPe
  by_cases hR : isRightCell (oddDistance (m + 1)) kv = true <;>
    by_cases hIn : isInside (oddDistance (m + 1)) qv = true <;> simp_all

private def rightNIImpCtx {fuel arity m : Nat} {kT qT : Term arity .nat}
    (D : DistAtA arity (m + 1)) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    PureFamilyDerivA Surface.code.body fuel
      (.imp (rightPbaseNI D.dT kT qT)
        (.eqBool (SC.closed (baseKindGuardTA D.dT kT)) (SC.b true))) := by
  refine impGuardA_of (rightPbaseNI_frag D.pure hk hq) (baseKindGuardTA_pure D.pure hk)
    (fun rho E => rightPbaseNI_tot D.pure hk hq rho E) ?_
  intro rho E hPe
  obtain ⟨kv, hkv⟩ := hk.eval_total Surface.code.body fuel rho
  obtain ⟨qv, hqv⟩ := hq.eval_total Surface.code.body fuel rho
  obtain ⟨hR, _⟩ := rightPbaseNI_extract D rho E hkv hqv hPe
  rw [baseKindGuardTA_eval rho (D.evalsTo rho) hkv]
  have := rightNI_kindTrueNat (m+1) kv (by simpa [oddDistance] using hR)
  simpa [oddDistance] using this

private def rightNIImpBand {fuel arity m : Nat} {kT qT : Term arity .nat} (v : Bool)
    (D : DistAtA arity (m + 1)) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    PureFamilyDerivA Surface.code.body fuel
      (.imp (.and (rightPbaseNI D.dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA D.dT kT qT)) (SC.b v)))
        (.eqBool (SC.closed (rightOuterGuardTA D.dT kT qT)) (SC.b v))) := by
  refine impGuardA_of ?_ ?_ ?_ ?_
  · simp only [arithBoolFragment, ArithBoolFragment.formula]
    rw [show ArithBoolFragment.formula (rightPbaseNI D.dT kT qT) = true from rightPbaseNI_frag D.pure hk hq]
    simp [ArithBoolFragment.sterm, SC.closed, SC.b, ArithBoolFragment.term,
      pureTerm_in_fragment (baseBulkBandGuardTA_pure D.pure hk hq)]
  · exact rightOuterGuardTA_pure D.pure hk hq
  · exact fun rho E => rightPbaseNIAnd_tot D.pure hk hq (baseBulkBandGuardTA_pure D.pure hk hq) v rho E
  · intro rho E hPe
    obtain ⟨kv, hkv⟩ := hk.eval_total Surface.code.body fuel rho
    obtain ⟨qv, hqv⟩ := hq.eval_total Surface.code.body fuel rho
    rw [SFormula.eval] at hPe
    have hbase := rightPbaseNI_tot (fuel := fuel) D.pure hk hq rho E
    cases hbe : (rightPbaseNI D.dT kT qT).eval Surface.code.body fuel rho E with
    | none => rw [hbe] at hbase; simp at hbase
    | some bb =>
        cases bb with
        | false => rw [hbe] at hPe; simp at hPe
        | true =>
            rw [hbe] at hPe
            simp only [SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval,
              bind, Option.bind, baseBulkBandGuardTA_eval rho (D.evalsTo rho) hkv hqv,
              Option.some.injEq, decide_eq_true_eq, if_true] at hPe
            obtain ⟨hR, hInF⟩ := rightPbaseNI_extract D rho E hkv hqv hbe
            rw [rightOuterGuardTA_eval rho (D.evalsTo rho) hkv hqv]
            have hcorr := rightNI_bandEqOuterNat (m + 1) kv qv
              (by simpa [oddDistance] using hR) (by simpa [oddDistance] using hInF)
            rw [show (oddDistance (m + 1)) = 2 * (m + 1) + 3 from rfl, ← hcorr,
              show (2 * (m + 1) + 3) = oddDistance (m + 1) from rfl, hPe]

def flatStepRightNI {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : SFormula.Deriv Γ (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b false)))
    (hRight : SFormula.Deriv Γ (.eqBool (SC.closed (rightCellGuardTA dT kT)) (SC.b true)))
    (hInside : SFormula.Deriv Γ (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b false)))
    (hImpCtx : SFormula.Deriv Γ
      (.imp (rightPbaseNI dT kT qT) (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b true))))
    (hImpBandT : SFormula.Deriv Γ
      (.imp (.and (rightPbaseNI dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)))
        (.eqBool (SC.closed (rightOuterGuardTA dT kT qT)) (SC.b true))))
    (hImpBandF : SFormula.Deriv Γ
      (.imp (.and (rightPbaseNI dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false)))
        (.eqBool (SC.closed (rightOuterGuardTA dT kT qT)) (SC.b false)))) :
    SFormula.Deriv Γ
      (.eqPauli
        (SC.closed (.ite (rightOuterGuardTA dT kT qT) (.pauliLit Pauli.Z) (.pauliLit Pauli.I)))
        (SC.closed (baseLeafTreeTA dT kT qT))) := by
  have hPbase : SFormula.Deriv Γ (rightPbaseNI dT kT qT) :=
    SFormula.Deriv.andIntro hBulk (SFormula.Deriv.andIntro hInterior
      (SFormula.Deriv.andIntro hTop (SFormula.Deriv.andIntro hRight hInside)))
  have hKindT := SFormula.Deriv.mp hImpCtx hPbase
  refine SFormula.Deriv.boolCases (SC.closed (baseBulkBandGuardTA dT kT qT)) _ ?_ ?_
  · set Δ := (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true) :: Γ) with hΔ
    have hsub : ∀ C, C ∈ Γ → C ∈ Δ := by intro C hC; exact List.mem_cons_of_mem _ hC
    have hOBandT : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)) :=
      .assumption
    have wkBulk := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hBulk
    have wkKindT := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hKindT
    have wkPbase := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hPbase
    have hOuterT := SFormula.Deriv.mp
      (SFormula.Deriv.contextWeakening (Δ := Δ) hsub hImpBandT)
      (SFormula.Deriv.andIntro wkPbase hOBandT)
    have lhsZ : SFormula.Deriv Δ (.eqPauli
        (SC.closed (.ite (rightOuterGuardTA dT kT qT) (.pauliLit Pauli.Z) (.pauliLit Pauli.I)))
        (SC.closed (.pauliLit Pauli.Z))) := SFormula.Deriv.pauliIteSelectThen _ _ _ hOuterT
    have rhsZ := baseLeafZS dT kT qT wkBulk hOBandT wkKindT
    exact SFormula.Deriv.eqPauliTrans _ _ _ lhsZ (SFormula.Deriv.eqPauliSymm _ _ rhsZ)
  · set Δ := (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false) :: Γ) with hΔ
    have hsub : ∀ C, C ∈ Γ → C ∈ Δ := by intro C hC; exact List.mem_cons_of_mem _ hC
    have hOBandF : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false)) :=
      .assumption
    have wkBulk := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hBulk
    have wkPbase := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hPbase
    have hOuterF := SFormula.Deriv.mp
      (SFormula.Deriv.contextWeakening (Δ := Δ) hsub hImpBandF)
      (SFormula.Deriv.andIntro wkPbase hOBandF)
    have lhsI : SFormula.Deriv Δ (.eqPauli
        (SC.closed (.ite (rightOuterGuardTA dT kT qT) (.pauliLit Pauli.Z) (.pauliLit Pauli.I)))
        (SC.closed (.pauliLit Pauli.I))) := SFormula.Deriv.pauliIteSelectElse _ _ _ hOuterF
    have rhsI := baseLeafBulkIS dT kT qT wkBulk hOBandF
    exact SFormula.Deriv.eqPauliTrans _ _ _ lhsI (SFormula.Deriv.eqPauliSymm _ _ rhsI)

/-! ### Left NI leaf: premise + correspondence implications -/

private def leftPbaseNI {arity : Nat} (dT kT qT : Term arity .nat) : SFormula arity :=
  .and (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true))
    (.and (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false))
      (.and (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b false))
        (.and (.eqBool (SC.closed (rightCellGuardTA dT kT)) (SC.b false))
          (.and (.eqBool (SC.closed (leftCellGuardTA dT kT)) (SC.b true))
            (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b false))))))

private theorem leftPbaseNI_frag {arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    arithBoolFragment (leftPbaseNI dT kT qT) = true := by
  simp only [leftPbaseNI, arithBoolFragment, ArithBoolFragment.formula, ArithBoolFragment.sterm,
    SC.closed, SC.b, ArithBoolFragment.term,
    pureTerm_in_fragment (bulkGuardTA_pure hd hk),
    pureTerm_in_fragment (interiorCellGuardTA_pure hd hk),
    pureTerm_in_fragment (topCellGuardTA_pure hd hk),
    pureTerm_in_fragment (rightCellGuardTA_pure hd hk),
    pureTerm_in_fragment (leftCellGuardTA_pure hd hk),
    pureTerm_in_fragment (insideGuardTA_pure hd hq), Bool.and_self]

private theorem leftPbaseNI_tot {fuel arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (rho : Env arity) (E : PartialStabilizer) :
    ((leftPbaseNI dT kT qT).eval Surface.code.body fuel rho E).isSome = true := by
  obtain ⟨b1, h1⟩ := (bulkGuardTA_pure hd hk).eval_total Surface.code.body fuel rho
  obtain ⟨b2, h2⟩ := (interiorCellGuardTA_pure hd hk).eval_total Surface.code.body fuel rho
  obtain ⟨b3, h3⟩ := (topCellGuardTA_pure hd hk).eval_total Surface.code.body fuel rho
  obtain ⟨b4, h4⟩ := (rightCellGuardTA_pure hd hk).eval_total Surface.code.body fuel rho
  obtain ⟨b5, h5⟩ := (leftCellGuardTA_pure hd hk).eval_total Surface.code.body fuel rho
  obtain ⟨b6, h6⟩ := (insideGuardTA_pure hd hq).eval_total Surface.code.body fuel rho
  simp only [leftPbaseNI, SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval, bind, Option.bind,
    h1, h2, h3, h4, h5, h6]
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> simp

private theorem leftPbaseNIAnd_tot {fuel arity : Nat} {dT kT qT : Term arity .nat}
    {g : Term arity .bool} (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT)
    (hq : SFormula.PureNatTerm qT) (hg : SFormula.PureBoolTerm g) (v : Bool)
    (rho : Env arity) (E : PartialStabilizer) :
    (((leftPbaseNI dT kT qT).and (.eqBool (SC.closed g) (SC.b v))).eval
      Surface.code.body fuel rho E).isSome = true := by
  obtain ⟨bg, hgv⟩ := hg.eval_total Surface.code.body fuel rho
  have hbase := leftPbaseNI_tot (fuel := fuel) hd hk hq rho E
  cases hbe : (leftPbaseNI dT kT qT).eval Surface.code.body fuel rho E with
  | none => rw [hbe] at hbase; simp at hbase
  | some bb =>
      cases bb <;>
        simp [SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval, bind, Option.bind, hbe, hgv]

private theorem leftPbaseNI_extract {fuel arity m kv qv : Nat} {kT qT : Term arity .nat}
    (D : DistAtA arity (m + 1)) (rho : Env arity) (E : PartialStabilizer)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : Term.eval Surface.code.body fuel qT rho = some qv)
    (hPe : (leftPbaseNI D.dT kT qT).eval Surface.code.body fuel rho E = some true) :
    isLeftCell (oddDistance (m + 1)) kv = true ∧ isInside (oddDistance (m + 1)) qv = false := by
  simp only [leftPbaseNI, SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval, bind, Option.bind,
    bulkGuardTA_eval rho (D.evalsTo rho) hkv,
    interiorCellGuardTA_eval rho (D.evalsTo rho) hkv,
    topCellGuardTA_eval rho (D.evalsTo rho) hkv,
    rightCellGuardTA_eval rho (D.evalsTo rho) hkv,
    leftCellGuardTA_eval rho (D.evalsTo rho) hkv,
    insideGuardTA_eval rho (D.evalsTo rho) hqv] at hPe
  by_cases hL : isLeftCell (oddDistance (m + 1)) kv = true <;>
    by_cases hIn : isInside (oddDistance (m + 1)) qv = true <;> simp_all

private def leftNIImpCtx {fuel arity m : Nat} {kT qT : Term arity .nat}
    (D : DistAtA arity (m + 1)) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    PureFamilyDerivA Surface.code.body fuel
      (.imp (leftPbaseNI D.dT kT qT)
        (.eqBool (SC.closed (baseKindGuardTA D.dT kT)) (SC.b true))) := by
  refine impGuardA_of (leftPbaseNI_frag D.pure hk hq) (baseKindGuardTA_pure D.pure hk)
    (fun rho E => leftPbaseNI_tot D.pure hk hq rho E) ?_
  intro rho E hPe
  obtain ⟨kv, hkv⟩ := hk.eval_total Surface.code.body fuel rho
  obtain ⟨qv, hqv⟩ := hq.eval_total Surface.code.body fuel rho
  obtain ⟨hL, _⟩ := leftPbaseNI_extract D rho E hkv hqv hPe
  rw [baseKindGuardTA_eval rho (D.evalsTo rho) hkv]
  have := leftNI_kindTrueNat (m+1) kv (by simpa [oddDistance] using hL)
  simpa [oddDistance] using this

private def leftNIImpBand {fuel arity m : Nat} {kT qT : Term arity .nat} (v : Bool)
    (D : DistAtA arity (m + 1)) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    PureFamilyDerivA Surface.code.body fuel
      (.imp (.and (leftPbaseNI D.dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA D.dT kT qT)) (SC.b v)))
        (.eqBool (SC.closed (leftOuterGuardTA D.dT kT qT)) (SC.b v))) := by
  refine impGuardA_of ?_ ?_ ?_ ?_
  · simp only [arithBoolFragment, ArithBoolFragment.formula]
    rw [show ArithBoolFragment.formula (leftPbaseNI D.dT kT qT) = true from leftPbaseNI_frag D.pure hk hq]
    simp [ArithBoolFragment.sterm, SC.closed, SC.b, ArithBoolFragment.term,
      pureTerm_in_fragment (baseBulkBandGuardTA_pure D.pure hk hq)]
  · exact leftOuterGuardTA_pure D.pure hk hq
  · exact fun rho E => leftPbaseNIAnd_tot D.pure hk hq (baseBulkBandGuardTA_pure D.pure hk hq) v rho E
  · intro rho E hPe
    obtain ⟨kv, hkv⟩ := hk.eval_total Surface.code.body fuel rho
    obtain ⟨qv, hqv⟩ := hq.eval_total Surface.code.body fuel rho
    rw [SFormula.eval] at hPe
    have hbase := leftPbaseNI_tot (fuel := fuel) D.pure hk hq rho E
    cases hbe : (leftPbaseNI D.dT kT qT).eval Surface.code.body fuel rho E with
    | none => rw [hbe] at hbase; simp at hbase
    | some bb =>
        cases bb with
        | false => rw [hbe] at hPe; simp at hPe
        | true =>
            rw [hbe] at hPe
            simp only [SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval,
              bind, Option.bind, baseBulkBandGuardTA_eval rho (D.evalsTo rho) hkv hqv,
              Option.some.injEq, decide_eq_true_eq, if_true] at hPe
            obtain ⟨hL, hInF⟩ := leftPbaseNI_extract D rho E hkv hqv hbe
            rw [leftOuterGuardTA_eval rho (D.evalsTo rho) hkv hqv]
            have hcorr := leftNI_bandEqOuterNat (m + 1) kv qv
              (by simpa [oddDistance] using hL) (by simpa [oddDistance] using hInF)
            rw [show (oddDistance (m + 1)) = 2 * (m + 1) + 3 from rfl, ← hcorr,
              show (2 * (m + 1) + 3) = oddDistance (m + 1) from rfl, hPe]

def flatStepLeftNI {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : SFormula.Deriv Γ (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b false)))
    (hRight : SFormula.Deriv Γ (.eqBool (SC.closed (rightCellGuardTA dT kT)) (SC.b false)))
    (hLeft : SFormula.Deriv Γ (.eqBool (SC.closed (leftCellGuardTA dT kT)) (SC.b true)))
    (hInside : SFormula.Deriv Γ (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b false)))
    (hImpCtx : SFormula.Deriv Γ
      (.imp (leftPbaseNI dT kT qT) (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b true))))
    (hImpBandT : SFormula.Deriv Γ
      (.imp (.and (leftPbaseNI dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)))
        (.eqBool (SC.closed (leftOuterGuardTA dT kT qT)) (SC.b true))))
    (hImpBandF : SFormula.Deriv Γ
      (.imp (.and (leftPbaseNI dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false)))
        (.eqBool (SC.closed (leftOuterGuardTA dT kT qT)) (SC.b false)))) :
    SFormula.Deriv Γ
      (.eqPauli
        (SC.closed (.ite (leftOuterGuardTA dT kT qT) (.pauliLit Pauli.Z) (.pauliLit Pauli.I)))
        (SC.closed (baseLeafTreeTA dT kT qT))) := by
  have hPbase : SFormula.Deriv Γ (leftPbaseNI dT kT qT) :=
    SFormula.Deriv.andIntro hBulk (SFormula.Deriv.andIntro hInterior
      (SFormula.Deriv.andIntro hTop (SFormula.Deriv.andIntro hRight
        (SFormula.Deriv.andIntro hLeft hInside))))
  have hKindT := SFormula.Deriv.mp hImpCtx hPbase
  refine SFormula.Deriv.boolCases (SC.closed (baseBulkBandGuardTA dT kT qT)) _ ?_ ?_
  · set Δ := (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true) :: Γ) with hΔ
    have hsub : ∀ C, C ∈ Γ → C ∈ Δ := by intro C hC; exact List.mem_cons_of_mem _ hC
    have hOBandT : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)) :=
      .assumption
    have wkBulk := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hBulk
    have wkKindT := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hKindT
    have wkPbase := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hPbase
    have hOuterT := SFormula.Deriv.mp
      (SFormula.Deriv.contextWeakening (Δ := Δ) hsub hImpBandT)
      (SFormula.Deriv.andIntro wkPbase hOBandT)
    have lhsZ : SFormula.Deriv Δ (.eqPauli
        (SC.closed (.ite (leftOuterGuardTA dT kT qT) (.pauliLit Pauli.Z) (.pauliLit Pauli.I)))
        (SC.closed (.pauliLit Pauli.Z))) := SFormula.Deriv.pauliIteSelectThen _ _ _ hOuterT
    have rhsZ := baseLeafZS dT kT qT wkBulk hOBandT wkKindT
    exact SFormula.Deriv.eqPauliTrans _ _ _ lhsZ (SFormula.Deriv.eqPauliSymm _ _ rhsZ)
  · set Δ := (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false) :: Γ) with hΔ
    have hsub : ∀ C, C ∈ Γ → C ∈ Δ := by intro C hC; exact List.mem_cons_of_mem _ hC
    have hOBandF : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false)) :=
      .assumption
    have wkBulk := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hBulk
    have wkPbase := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hPbase
    have hOuterF := SFormula.Deriv.mp
      (SFormula.Deriv.contextWeakening (Δ := Δ) hsub hImpBandF)
      (SFormula.Deriv.andIntro wkPbase hOBandF)
    have lhsI : SFormula.Deriv Δ (.eqPauli
        (SC.closed (.ite (leftOuterGuardTA dT kT qT) (.pauliLit Pauli.Z) (.pauliLit Pauli.I)))
        (SC.closed (.pauliLit Pauli.I))) := SFormula.Deriv.pauliIteSelectElse _ _ _ hOuterF
    have rhsI := baseLeafBulkIS dT kT qT wkBulk hOBandF
    exact SFormula.Deriv.eqPauliTrans _ _ _ lhsI (SFormula.Deriv.eqPauliSymm _ _ rhsI)

/-! ### Bottom NI leaf: premise + correspondence implications -/

private def bottomPbaseNI {arity : Nat} (dT kT qT : Term arity .nat) : SFormula arity :=
  .and (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true))
    (.and (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false))
      (.and (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b false))
        (.and (.eqBool (SC.closed (rightCellGuardTA dT kT)) (SC.b false))
          (.and (.eqBool (SC.closed (leftCellGuardTA dT kT)) (SC.b false))
            (.and (.eqBool (SC.closed (bottomCellGuardTA dT kT)) (SC.b true))
              (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b false)))))))

private theorem bottomPbaseNI_frag {arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    arithBoolFragment (bottomPbaseNI dT kT qT) = true := by
  simp only [bottomPbaseNI, arithBoolFragment, ArithBoolFragment.formula, ArithBoolFragment.sterm,
    SC.closed, SC.b, ArithBoolFragment.term,
    pureTerm_in_fragment (bulkGuardTA_pure hd hk),
    pureTerm_in_fragment (interiorCellGuardTA_pure hd hk),
    pureTerm_in_fragment (topCellGuardTA_pure hd hk),
    pureTerm_in_fragment (rightCellGuardTA_pure hd hk),
    pureTerm_in_fragment (leftCellGuardTA_pure hd hk),
    pureTerm_in_fragment (bottomCellGuardTA_pure hd hk),
    pureTerm_in_fragment (insideGuardTA_pure hd hq), Bool.and_self]

private theorem bottomPbaseNI_tot {fuel arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (rho : Env arity) (E : PartialStabilizer) :
    ((bottomPbaseNI dT kT qT).eval Surface.code.body fuel rho E).isSome = true := by
  obtain ⟨b1, h1⟩ := (bulkGuardTA_pure hd hk).eval_total Surface.code.body fuel rho
  obtain ⟨b2, h2⟩ := (interiorCellGuardTA_pure hd hk).eval_total Surface.code.body fuel rho
  obtain ⟨b3, h3⟩ := (topCellGuardTA_pure hd hk).eval_total Surface.code.body fuel rho
  obtain ⟨b4, h4⟩ := (rightCellGuardTA_pure hd hk).eval_total Surface.code.body fuel rho
  obtain ⟨b5, h5⟩ := (leftCellGuardTA_pure hd hk).eval_total Surface.code.body fuel rho
  obtain ⟨b6, h6⟩ := (bottomCellGuardTA_pure hd hk).eval_total Surface.code.body fuel rho
  obtain ⟨b7, h7⟩ := (insideGuardTA_pure hd hq).eval_total Surface.code.body fuel rho
  simp only [bottomPbaseNI, SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval, bind, Option.bind,
    h1, h2, h3, h4, h5, h6, h7]
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;> simp

private theorem bottomPbaseNIAnd_tot {fuel arity : Nat} {dT kT qT : Term arity .nat}
    {g : Term arity .bool} (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT)
    (hq : SFormula.PureNatTerm qT) (hg : SFormula.PureBoolTerm g) (v : Bool)
    (rho : Env arity) (E : PartialStabilizer) :
    (((bottomPbaseNI dT kT qT).and (.eqBool (SC.closed g) (SC.b v))).eval
      Surface.code.body fuel rho E).isSome = true := by
  obtain ⟨bg, hgv⟩ := hg.eval_total Surface.code.body fuel rho
  have hbase := bottomPbaseNI_tot (fuel := fuel) hd hk hq rho E
  cases hbe : (bottomPbaseNI dT kT qT).eval Surface.code.body fuel rho E with
  | none => rw [hbe] at hbase; simp at hbase
  | some bb =>
      cases bb <;>
        simp [SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval, bind, Option.bind, hbe, hgv]

private theorem bottomPbaseNI_extract {fuel arity m kv qv : Nat} {kT qT : Term arity .nat}
    (D : DistAtA arity (m + 1)) (rho : Env arity) (E : PartialStabilizer)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : Term.eval Surface.code.body fuel qT rho = some qv)
    (hPe : (bottomPbaseNI D.dT kT qT).eval Surface.code.body fuel rho E = some true) :
    isBottomCell (oddDistance (m + 1)) kv = true ∧ isInside (oddDistance (m + 1)) qv = false := by
  simp only [bottomPbaseNI, SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval, bind, Option.bind,
    bulkGuardTA_eval rho (D.evalsTo rho) hkv,
    interiorCellGuardTA_eval rho (D.evalsTo rho) hkv,
    topCellGuardTA_eval rho (D.evalsTo rho) hkv,
    rightCellGuardTA_eval rho (D.evalsTo rho) hkv,
    leftCellGuardTA_eval rho (D.evalsTo rho) hkv,
    bottomCellGuardTA_eval rho (D.evalsTo rho) hkv,
    insideGuardTA_eval rho (D.evalsTo rho) hqv] at hPe
  by_cases hB : isBottomCell (oddDistance (m + 1)) kv = true <;>
    by_cases hIn : isInside (oddDistance (m + 1)) qv = true <;> simp_all

private def bottomNIImpCtx {fuel arity m : Nat} {kT qT : Term arity .nat}
    (D : DistAtA arity (m + 1)) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    PureFamilyDerivA Surface.code.body fuel
      (.imp (bottomPbaseNI D.dT kT qT)
        (.eqBool (SC.closed (baseKindGuardTA D.dT kT)) (SC.b false))) := by
  refine impGuardA_of (bottomPbaseNI_frag D.pure hk hq) (baseKindGuardTA_pure D.pure hk)
    (fun rho E => bottomPbaseNI_tot D.pure hk hq rho E) ?_
  intro rho E hPe
  obtain ⟨kv, hkv⟩ := hk.eval_total Surface.code.body fuel rho
  obtain ⟨qv, hqv⟩ := hq.eval_total Surface.code.body fuel rho
  obtain ⟨hB, _⟩ := bottomPbaseNI_extract D rho E hkv hqv hPe
  rw [baseKindGuardTA_eval rho (D.evalsTo rho) hkv]
  have := bottomNI_kindFalseNat (m+1) kv (by simpa [oddDistance] using hB)
  simpa [oddDistance] using this

private def bottomNIImpBand {fuel arity m : Nat} {kT qT : Term arity .nat} (v : Bool)
    (D : DistAtA arity (m + 1)) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    PureFamilyDerivA Surface.code.body fuel
      (.imp (.and (bottomPbaseNI D.dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA D.dT kT qT)) (SC.b v)))
        (.eqBool (SC.closed (bottomOuterGuardTA D.dT kT qT)) (SC.b v))) := by
  refine impGuardA_of ?_ ?_ ?_ ?_
  · simp only [arithBoolFragment, ArithBoolFragment.formula]
    rw [show ArithBoolFragment.formula (bottomPbaseNI D.dT kT qT) = true from bottomPbaseNI_frag D.pure hk hq]
    simp [ArithBoolFragment.sterm, SC.closed, SC.b, ArithBoolFragment.term,
      pureTerm_in_fragment (baseBulkBandGuardTA_pure D.pure hk hq)]
  · exact bottomOuterGuardTA_pure D.pure hk hq
  · exact fun rho E => bottomPbaseNIAnd_tot D.pure hk hq (baseBulkBandGuardTA_pure D.pure hk hq) v rho E
  · intro rho E hPe
    obtain ⟨kv, hkv⟩ := hk.eval_total Surface.code.body fuel rho
    obtain ⟨qv, hqv⟩ := hq.eval_total Surface.code.body fuel rho
    rw [SFormula.eval] at hPe
    have hbase := bottomPbaseNI_tot (fuel := fuel) D.pure hk hq rho E
    cases hbe : (bottomPbaseNI D.dT kT qT).eval Surface.code.body fuel rho E with
    | none => rw [hbe] at hbase; simp at hbase
    | some bb =>
        cases bb with
        | false => rw [hbe] at hPe; simp at hPe
        | true =>
            rw [hbe] at hPe
            simp only [SFormula.eval, STerm.eval, SC.closed, SC.b, Term.eval,
              bind, Option.bind, baseBulkBandGuardTA_eval rho (D.evalsTo rho) hkv hqv,
              Option.some.injEq, decide_eq_true_eq, if_true] at hPe
            obtain ⟨hB, hInF⟩ := bottomPbaseNI_extract D rho E hkv hqv hbe
            rw [bottomOuterGuardTA_eval rho (D.evalsTo rho) hkv hqv]
            have hcorr := bottomNI_bandEqOuterNat (m + 1) kv qv
              (by simpa [oddDistance] using hB) (by simpa [oddDistance] using hInF)
            rw [show (oddDistance (m + 1)) = 2 * (m + 1) + 3 from rfl, ← hcorr,
              show (2 * (m + 1) + 3) = oddDistance (m + 1) from rfl, hPe]

def flatStepBottomNI {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hInterior : SFormula.Deriv Γ (.eqBool (SC.closed (interiorCellGuardTA dT kT)) (SC.b false)))
    (hTop : SFormula.Deriv Γ (.eqBool (SC.closed (topCellGuardTA dT kT)) (SC.b false)))
    (hRight : SFormula.Deriv Γ (.eqBool (SC.closed (rightCellGuardTA dT kT)) (SC.b false)))
    (hLeft : SFormula.Deriv Γ (.eqBool (SC.closed (leftCellGuardTA dT kT)) (SC.b false)))
    (hBottom : SFormula.Deriv Γ (.eqBool (SC.closed (bottomCellGuardTA dT kT)) (SC.b true)))
    (hInside : SFormula.Deriv Γ (.eqBool (SC.closed (insideGuardTA dT qT)) (SC.b false)))
    (hImpCtx : SFormula.Deriv Γ
      (.imp (bottomPbaseNI dT kT qT) (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b false))))
    (hImpBandT : SFormula.Deriv Γ
      (.imp (.and (bottomPbaseNI dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)))
        (.eqBool (SC.closed (bottomOuterGuardTA dT kT qT)) (SC.b true))))
    (hImpBandF : SFormula.Deriv Γ
      (.imp (.and (bottomPbaseNI dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false)))
        (.eqBool (SC.closed (bottomOuterGuardTA dT kT qT)) (SC.b false)))) :
    SFormula.Deriv Γ
      (.eqPauli
        (SC.closed (.ite (bottomOuterGuardTA dT kT qT) (.pauliLit Pauli.X) (.pauliLit Pauli.I)))
        (SC.closed (baseLeafTreeTA dT kT qT))) := by
  have hPbase : SFormula.Deriv Γ (bottomPbaseNI dT kT qT) :=
    SFormula.Deriv.andIntro hBulk (SFormula.Deriv.andIntro hInterior
      (SFormula.Deriv.andIntro hTop (SFormula.Deriv.andIntro hRight
        (SFormula.Deriv.andIntro hLeft (SFormula.Deriv.andIntro hBottom hInside)))))
  have hKindF := SFormula.Deriv.mp hImpCtx hPbase
  refine SFormula.Deriv.boolCases (SC.closed (baseBulkBandGuardTA dT kT qT)) _ ?_ ?_
  · set Δ := (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true) :: Γ) with hΔ
    have hsub : ∀ C, C ∈ Γ → C ∈ Δ := by intro C hC; exact List.mem_cons_of_mem _ hC
    have hOBandT : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)) :=
      .assumption
    have wkBulk := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hBulk
    have wkKindF := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hKindF
    have wkPbase := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hPbase
    have hOuterT := SFormula.Deriv.mp
      (SFormula.Deriv.contextWeakening (Δ := Δ) hsub hImpBandT)
      (SFormula.Deriv.andIntro wkPbase hOBandT)
    have lhsX : SFormula.Deriv Δ (.eqPauli
        (SC.closed (.ite (bottomOuterGuardTA dT kT qT) (.pauliLit Pauli.X) (.pauliLit Pauli.I)))
        (SC.closed (.pauliLit Pauli.X))) := SFormula.Deriv.pauliIteSelectThen _ _ _ hOuterT
    have rhsX := baseLeafXS dT kT qT wkBulk hOBandT wkKindF
    exact SFormula.Deriv.eqPauliTrans _ _ _ lhsX (SFormula.Deriv.eqPauliSymm _ _ rhsX)
  · set Δ := (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false) :: Γ) with hΔ
    have hsub : ∀ C, C ∈ Γ → C ∈ Δ := by intro C hC; exact List.mem_cons_of_mem _ hC
    have hOBandF : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false)) :=
      .assumption
    have wkBulk := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hBulk
    have wkPbase := SFormula.Deriv.contextWeakening (Δ := Δ) hsub hPbase
    have hOuterF := SFormula.Deriv.mp
      (SFormula.Deriv.contextWeakening (Δ := Δ) hsub hImpBandF)
      (SFormula.Deriv.andIntro wkPbase hOBandF)
    have lhsI : SFormula.Deriv Δ (.eqPauli
        (SC.closed (.ite (bottomOuterGuardTA dT kT qT) (.pauliLit Pauli.X) (.pauliLit Pauli.I)))
        (SC.closed (.pauliLit Pauli.I))) := SFormula.Deriv.pauliIteSelectElse _ _ _ hOuterF
    have rhsI := baseLeafBulkIS dT kT qT wkBulk hOBandF
    exact SFormula.Deriv.eqPauliTrans _ _ _ lhsI (SFormula.Deriv.eqPauliSymm _ _ rhsI)

/-! ### The recursive-case master self-similarity dispatch

A single `SFormula.Deriv` reducing `recLeafTreeTA dT kT qT (baseLeafTreeTA inner₁)
… (baseLeafTreeTA inner₅)` (the IH-flattened recursive leaf tree) to the flat
classifier `baseLeafTreeTA dT kT qT`, by `boolCases` on every cell guard.  Each
recursing branch composes the `recLeaf*S` reduction (giving the IH-flattened inner
leaf) with the matching `flatStep*` self-similarity equality.  The fallback /
boundary branches reduce both sides to `baseLeafTreeTA` directly. -/
def recFlatMasterD {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    -- the five IH-leaf equalities: `rowSymTreeA m inner = baseLeafTreeTA inner`
    (hLeqInt : SFormula.Deriv Γ
      (.eqPauli (SC.closed pInt)
        (SC.closed (baseLeafTreeTA (innerDTA dT) (interiorKTA dT kT) (innerQTA dT qT)))))
    (hLeqTop : SFormula.Deriv Γ
      (.eqPauli (SC.closed pTop)
        (SC.closed (baseLeafTreeTA (recInnerDTA dT) (topKTA dT kT) (innerQTA dT qT)))))
    (hLeqRight : SFormula.Deriv Γ
      (.eqPauli (SC.closed pRight)
        (SC.closed (baseLeafTreeTA (recInnerDTA dT) (rightKTA dT kT) (innerQTA dT qT)))))
    (hLeqLeft : SFormula.Deriv Γ
      (.eqPauli (SC.closed pLeft)
        (SC.closed (baseLeafTreeTA (recInnerDTA dT) (leftKTA dT kT) (innerQTA dT qT)))))
    (hLeqBottom : SFormula.Deriv Γ
      (.eqPauli (SC.closed pBottom)
        (SC.closed (baseLeafTreeTA (recInnerDTA dT) (bottomKTA dT kT) (innerQTA dT qT)))))
    -- interior leaf correspondence implications (threaded from `rowSymTreeFlatBridgeSym`).
    (hImpBulk : SFormula.Deriv Γ
      (.imp (interiorPbase dT kT qT)
        (.eqBool (SC.closed (bulkGuardTA (innerDTA dT) (interiorKTA dT kT))) (SC.b true))))
    (hImpBandT : SFormula.Deriv Γ
      (.imp (.and (interiorPbase dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)))
        (.eqBool (SC.closed (baseBulkBandGuardTA (innerDTA dT) (interiorKTA dT kT) (innerQTA dT qT)))
          (SC.b true))))
    (hImpBandF : SFormula.Deriv Γ
      (.imp (.and (interiorPbase dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false)))
        (.eqBool (SC.closed (baseBulkBandGuardTA (innerDTA dT) (interiorKTA dT kT) (innerQTA dT qT)))
          (SC.b false))))
    (hImpKindT : SFormula.Deriv Γ
      (.imp (.and (interiorPbase dT kT qT)
              (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b true)))
        (.eqBool (SC.closed (baseKindGuardTA (innerDTA dT) (interiorKTA dT kT))) (SC.b true))))
    (hImpKindF : SFormula.Deriv Γ
      (.imp (.and (interiorPbase dT kT qT)
              (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b false)))
        (.eqBool (SC.closed (baseKindGuardTA (innerDTA dT) (interiorKTA dT kT))) (SC.b false))))
    (hImpBandFNI : SFormula.Deriv Γ
      (.imp (interiorPbaseNI dT kT qT)
        (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false))))
    -- top inside leaf correspondence implications.
    (hTopImpCtx : SFormula.Deriv Γ
      (.imp (topPbase dT kT qT)
        (.and (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b false))
          (.and (.eqBool (SC.closed (bulkGuardTA (recInnerDTA dT) (topKTA dT kT))) (SC.b false))
            (.eqBool (SC.closed (topClassGuardTA (recInnerDTA dT) (topKTA dT kT))) (SC.b true))))))
    (hTopImpBandT : SFormula.Deriv Γ
      (.imp (.and (topPbase dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)))
        (.eqBool (SC.closed (topBandGuardTA (recInnerDTA dT) (topKTA dT kT) (innerQTA dT qT)))
          (SC.b true))))
    (hTopImpBandF : SFormula.Deriv Γ
      (.imp (.and (topPbase dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false)))
        (.eqBool (SC.closed (topBandGuardTA (recInnerDTA dT) (topKTA dT kT) (innerQTA dT qT)))
          (SC.b false))))
    -- right inside leaf correspondence implications.
    (hRightImpCtx : SFormula.Deriv Γ
      (.imp (rightPbase dT kT qT)
        (.and (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b true))
          (.and (.eqBool (SC.closed (bulkGuardTA (recInnerDTA dT) (rightKTA dT kT))) (SC.b false))
            (.and (.eqBool (SC.closed (topClassGuardTA (recInnerDTA dT) (rightKTA dT kT))) (SC.b false))
              (.eqBool (SC.closed (rightClassGuardTA (recInnerDTA dT) (rightKTA dT kT))) (SC.b true)))))))
    (hRightImpBandT : SFormula.Deriv Γ
      (.imp (.and (rightPbase dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)))
        (.eqBool (SC.closed (rightBandGuardTA (recInnerDTA dT) (rightKTA dT kT) (innerQTA dT qT)))
          (SC.b true))))
    (hRightImpBandF : SFormula.Deriv Γ
      (.imp (.and (rightPbase dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false)))
        (.eqBool (SC.closed (rightBandGuardTA (recInnerDTA dT) (rightKTA dT kT) (innerQTA dT qT)))
          (SC.b false))))
    -- left inside leaf correspondence implications.
    (hLeftImpCtx : SFormula.Deriv Γ
      (.imp (leftPbase dT kT qT)
        (.and (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b true))
          (.and (.eqBool (SC.closed (bulkGuardTA (recInnerDTA dT) (leftKTA dT kT))) (SC.b false))
            (.and (.eqBool (SC.closed (topClassGuardTA (recInnerDTA dT) (leftKTA dT kT))) (SC.b false))
              (.and (.eqBool (SC.closed (rightClassGuardTA (recInnerDTA dT) (leftKTA dT kT))) (SC.b false))
                (.eqBool (SC.closed (leftClassGuardTA (recInnerDTA dT) (leftKTA dT kT))) (SC.b true))))))))
    (hLeftImpBandT : SFormula.Deriv Γ
      (.imp (.and (leftPbase dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)))
        (.eqBool (SC.closed (leftBandGuardTA (recInnerDTA dT) (leftKTA dT kT) (innerQTA dT qT)))
          (SC.b true))))
    (hLeftImpBandF : SFormula.Deriv Γ
      (.imp (.and (leftPbase dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false)))
        (.eqBool (SC.closed (leftBandGuardTA (recInnerDTA dT) (leftKTA dT kT) (innerQTA dT qT)))
          (SC.b false))))
    -- bottom inside leaf correspondence implications.
    (hBottomImpCtx : SFormula.Deriv Γ
      (.imp (bottomPbase dT kT qT)
        (.and (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b false))
          (.and (.eqBool (SC.closed (bulkGuardTA (recInnerDTA dT) (bottomKTA dT kT))) (SC.b false))
            (.and (.eqBool (SC.closed (topClassGuardTA (recInnerDTA dT) (bottomKTA dT kT))) (SC.b false))
              (.and (.eqBool (SC.closed (rightClassGuardTA (recInnerDTA dT) (bottomKTA dT kT))) (SC.b false))
                (.eqBool (SC.closed (leftClassGuardTA (recInnerDTA dT) (bottomKTA dT kT))) (SC.b false))))))))
    (hBottomImpBandT : SFormula.Deriv Γ
      (.imp (.and (bottomPbase dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)))
        (.eqBool (SC.closed (bottomBandGuardTA (recInnerDTA dT) (bottomKTA dT kT) (innerQTA dT qT)))
          (SC.b true))))
    (hBottomImpBandF : SFormula.Deriv Γ
      (.imp (.and (bottomPbase dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false)))
        (.eqBool (SC.closed (bottomBandGuardTA (recInnerDTA dT) (bottomKTA dT kT) (innerQTA dT qT)))
          (SC.b false))))
    -- top NI leaf correspondence implications.
    (hTopNIImpCtx : SFormula.Deriv Γ
      (.imp (topPbaseNI dT kT qT) (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b false))))
    (hTopNIImpBandT : SFormula.Deriv Γ
      (.imp (.and (topPbaseNI dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)))
        (.eqBool (SC.closed (topOuterGuardTA dT kT qT)) (SC.b true))))
    (hTopNIImpBandF : SFormula.Deriv Γ
      (.imp (.and (topPbaseNI dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false)))
        (.eqBool (SC.closed (topOuterGuardTA dT kT qT)) (SC.b false))))
    -- right NI leaf correspondence implications.
    (hRightNIImpCtx : SFormula.Deriv Γ
      (.imp (rightPbaseNI dT kT qT) (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b true))))
    (hRightNIImpBandT : SFormula.Deriv Γ
      (.imp (.and (rightPbaseNI dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)))
        (.eqBool (SC.closed (rightOuterGuardTA dT kT qT)) (SC.b true))))
    (hRightNIImpBandF : SFormula.Deriv Γ
      (.imp (.and (rightPbaseNI dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false)))
        (.eqBool (SC.closed (rightOuterGuardTA dT kT qT)) (SC.b false))))
    -- left NI leaf correspondence implications.
    (hLeftNIImpCtx : SFormula.Deriv Γ
      (.imp (leftPbaseNI dT kT qT) (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b true))))
    (hLeftNIImpBandT : SFormula.Deriv Γ
      (.imp (.and (leftPbaseNI dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)))
        (.eqBool (SC.closed (leftOuterGuardTA dT kT qT)) (SC.b true))))
    (hLeftNIImpBandF : SFormula.Deriv Γ
      (.imp (.and (leftPbaseNI dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false)))
        (.eqBool (SC.closed (leftOuterGuardTA dT kT qT)) (SC.b false))))
    -- bottom NI leaf correspondence implications.
    (hBottomNIImpCtx : SFormula.Deriv Γ
      (.imp (bottomPbaseNI dT kT qT) (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b false))))
    (hBottomNIImpBandT : SFormula.Deriv Γ
      (.imp (.and (bottomPbaseNI dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)))
        (.eqBool (SC.closed (bottomOuterGuardTA dT kT qT)) (SC.b true))))
    (hBottomNIImpBandF : SFormula.Deriv Γ
      (.imp (.and (bottomPbaseNI dT kT qT)
              (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false)))
        (.eqBool (SC.closed (bottomOuterGuardTA dT kT qT)) (SC.b false)))) :
    SFormula.Deriv Γ
      (.eqPauli
        (SC.closed (recLeafTreeTA dT kT qT pInt pTop pRight pLeft pBottom))
        (SC.closed (baseLeafTreeTA dT kT qT))) := by
  -- `wkN` weakens a `Γ`-level IH-leaf equality into the deeper boolCases branch.
  refine SFormula.Deriv.boolCases (SC.closed (bulkGuardTA dT kT)) _ ?_ ?_
  · -- bulk = true
    refine SFormula.Deriv.boolCases (SC.closed (interiorCellGuardTA dT kT)) _ ?_ ?_
    · -- interiorCell = true
      refine SFormula.Deriv.boolCases (SC.closed (insideGuardTA dT qT)) _ ?_ ?_
      · -- inside = true → interior IH leaf, then SelfSim
        exact SFormula.Deriv.eqPauliTrans _ _ _
          (recLeafIntS dT kT qT _ _ _ _ _
            (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption)
          (SFormula.Deriv.eqPauliTrans _ _ _
            (SFormula.Deriv.contextWeakening (by intro C hC; simp_all) hLeqInt)
            (flatStepInterior dT kT qT (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption
              (SFormula.Deriv.contextWeakening (by intro C hC; simp_all) hImpBulk)
              (SFormula.Deriv.contextWeakening (by intro C hC; simp_all) hImpBandT)
              (SFormula.Deriv.contextWeakening (by intro C hC; simp_all) hImpBandF)
              (SFormula.Deriv.contextWeakening (by intro C hC; simp_all) hImpKindT)
              (SFormula.Deriv.contextWeakening (by intro C hC; simp_all) hImpKindF)))
      · -- inside = false → I, then SelfSim
        exact SFormula.Deriv.eqPauliTrans _ _ _
          (recLeafIntIS dT kT qT _ _ _ _ _
            (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption)
          (flatStepInteriorNI dT kT qT (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption
            (SFormula.Deriv.contextWeakening (by intro C hC; simp_all) hImpBandFNI))
    · -- interiorCell = false
      refine SFormula.Deriv.boolCases (SC.closed (topCellGuardTA dT kT)) _ ?_ ?_
      · -- topCell = true
        refine SFormula.Deriv.boolCases (SC.closed (insideGuardTA dT qT)) _ ?_ ?_
        · exact SFormula.Deriv.eqPauliTrans _ _ _
            (recLeafTopS dT kT qT _ _ _ _ _ (.hyp (by right; right; right; left))
              (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption)
            (SFormula.Deriv.eqPauliTrans _ _ _
              (SFormula.Deriv.contextWeakening (by intro C hC; simp_all) hLeqTop)
              (flatStepTop dT kT qT (.hyp (by right; right; right; left))
                (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption
                (SFormula.Deriv.contextWeakening (by intro C hC; simp_all) hTopImpCtx)
                (SFormula.Deriv.contextWeakening (by intro C hC; simp_all) hTopImpBandT)
                (SFormula.Deriv.contextWeakening (by intro C hC; simp_all) hTopImpBandF)))
        · exact SFormula.Deriv.eqPauliTrans _ _ _
            (recLeafTopNIS dT kT qT _ _ _ _ _ (.hyp (by right; right; right; left))
              (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption)
            (flatStepTopNI dT kT qT (.hyp (by right; right; right; left))
              (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption
              (SFormula.Deriv.contextWeakening (by intro C hC; simp_all) hTopNIImpCtx)
              (SFormula.Deriv.contextWeakening (by intro C hC; simp_all) hTopNIImpBandT)
              (SFormula.Deriv.contextWeakening (by intro C hC; simp_all) hTopNIImpBandF))
      · -- topCell = false
        refine SFormula.Deriv.boolCases (SC.closed (rightCellGuardTA dT kT)) _ ?_ ?_
        · -- rightCell = true
          refine SFormula.Deriv.boolCases (SC.closed (insideGuardTA dT qT)) _ ?_ ?_
          · exact SFormula.Deriv.eqPauliTrans _ _ _
              (recLeafRightS dT kT qT _ _ _ _ _ (.hyp (by right; right; right; right; left))
                (.hyp (by right; right; right; left)) (.hyp (by right; right; left)) (.hyp (by right; left))
                .assumption)
              (SFormula.Deriv.eqPauliTrans _ _ _
                (SFormula.Deriv.contextWeakening (by intro C hC; simp_all) hLeqRight)
                (flatStepRight dT kT qT (.hyp (by right; right; right; right; left))
                  (.hyp (by right; right; right; left)) (.hyp (by right; right; left)) (.hyp (by right; left))
                  .assumption
                  (SFormula.Deriv.contextWeakening (by intro C hC; simp_all) hRightImpCtx)
                  (SFormula.Deriv.contextWeakening (by intro C hC; simp_all) hRightImpBandT)
                  (SFormula.Deriv.contextWeakening (by intro C hC; simp_all) hRightImpBandF)))
          · exact SFormula.Deriv.eqPauliTrans _ _ _
              (recLeafRightNIS dT kT qT _ _ _ _ _ (.hyp (by right; right; right; right; left))
                (.hyp (by right; right; right; left)) (.hyp (by right; right; left)) (.hyp (by right; left))
                .assumption)
              (flatStepRightNI dT kT qT (.hyp (by right; right; right; right; left))
                (.hyp (by right; right; right; left)) (.hyp (by right; right; left)) (.hyp (by right; left))
                .assumption
                (SFormula.Deriv.contextWeakening (by intro C hC; simp_all) hRightNIImpCtx)
                (SFormula.Deriv.contextWeakening (by intro C hC; simp_all) hRightNIImpBandT)
                (SFormula.Deriv.contextWeakening (by intro C hC; simp_all) hRightNIImpBandF))
        · -- rightCell = false
          refine SFormula.Deriv.boolCases (SC.closed (leftCellGuardTA dT kT)) _ ?_ ?_
          · -- leftCell = true
            refine SFormula.Deriv.boolCases (SC.closed (insideGuardTA dT qT)) _ ?_ ?_
            · exact SFormula.Deriv.eqPauliTrans _ _ _
                (recLeafLeftS dT kT qT _ _ _ _ _ (.hyp (by right; right; right; right; right; left))
                  (.hyp (by right; right; right; right; left)) (.hyp (by right; right; right; left))
                  (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption)
                (SFormula.Deriv.eqPauliTrans _ _ _
                  (SFormula.Deriv.contextWeakening (by intro C hC; simp_all) hLeqLeft)
                  (flatStepLeft dT kT qT (.hyp (by right; right; right; right; right; left))
                    (.hyp (by right; right; right; right; left)) (.hyp (by right; right; right; left))
                    (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption
                    (SFormula.Deriv.contextWeakening (by intro C hC; simp_all) hLeftImpCtx)
                    (SFormula.Deriv.contextWeakening (by intro C hC; simp_all) hLeftImpBandT)
                    (SFormula.Deriv.contextWeakening (by intro C hC; simp_all) hLeftImpBandF)))
            · exact SFormula.Deriv.eqPauliTrans _ _ _
                (recLeafLeftNIS dT kT qT _ _ _ _ _ (.hyp (by right; right; right; right; right; left))
                  (.hyp (by right; right; right; right; left)) (.hyp (by right; right; right; left))
                  (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption)
                (flatStepLeftNI dT kT qT (.hyp (by right; right; right; right; right; left))
                  (.hyp (by right; right; right; right; left)) (.hyp (by right; right; right; left))
                  (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption
                  (SFormula.Deriv.contextWeakening (by intro C hC; simp_all) hLeftNIImpCtx)
                  (SFormula.Deriv.contextWeakening (by intro C hC; simp_all) hLeftNIImpBandT)
                  (SFormula.Deriv.contextWeakening (by intro C hC; simp_all) hLeftNIImpBandF))
          · -- leftCell = false
            refine SFormula.Deriv.boolCases (SC.closed (bottomCellGuardTA dT kT)) _ ?_ ?_
            · -- bottomCell = true
              refine SFormula.Deriv.boolCases (SC.closed (insideGuardTA dT qT)) _ ?_ ?_
              · exact SFormula.Deriv.eqPauliTrans _ _ _
                  (recLeafBottomS dT kT qT _ _ _ _ _
                    (.hyp (by right; right; right; right; right; right; left))
                    (.hyp (by right; right; right; right; right; left))
                    (.hyp (by right; right; right; right; left)) (.hyp (by right; right; right; left))
                    (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption)
                  (SFormula.Deriv.eqPauliTrans _ _ _
                    (SFormula.Deriv.contextWeakening (by intro C hC; simp_all) hLeqBottom)
                    (flatStepBottom dT kT qT
                      (.hyp (by right; right; right; right; right; right; left))
                      (.hyp (by right; right; right; right; right; left))
                      (.hyp (by right; right; right; right; left)) (.hyp (by right; right; right; left))
                      (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption
                      (SFormula.Deriv.contextWeakening (by intro C hC; simp_all) hBottomImpCtx)
                      (SFormula.Deriv.contextWeakening (by intro C hC; simp_all) hBottomImpBandT)
                      (SFormula.Deriv.contextWeakening (by intro C hC; simp_all) hBottomImpBandF)))
              · exact SFormula.Deriv.eqPauliTrans _ _ _
                  (recLeafBottomNIS dT kT qT _ _ _ _ _
                    (.hyp (by right; right; right; right; right; right; left))
                    (.hyp (by right; right; right; right; right; left))
                    (.hyp (by right; right; right; right; left)) (.hyp (by right; right; right; left))
                    (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption)
                  (flatStepBottomNI dT kT qT
                    (.hyp (by right; right; right; right; right; right; left))
                    (.hyp (by right; right; right; right; right; left))
                    (.hyp (by right; right; right; right; left)) (.hyp (by right; right; right; left))
                    (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption
                    (SFormula.Deriv.contextWeakening (by intro C hC; simp_all) hBottomNIImpCtx)
                    (SFormula.Deriv.contextWeakening (by intro C hC; simp_all) hBottomNIImpBandT)
                    (SFormula.Deriv.contextWeakening (by intro C hC; simp_all) hBottomNIImpBandF))
            · -- bottomCell = false → fallback baseLeafTreeTA on both sides
              exact recLeafFallbackS dT kT qT _ _ _ _ _
                (.hyp (by right; right; right; right; right; left))
                (.hyp (by right; right; right; right; left)) (.hyp (by right; right; right; left))
                (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption
  · -- bulk = false → boundary baseLeafTreeTA on both sides
    exact recLeafBoundaryS dT kT qT _ _ _ _ _ .assumption

/-! ### The symbolic flat bridge (structural recursion on `m`) -/

/-- **The SYMBOLIC flat bridge.**  At an *arbitrary* pure index `kT` / qubit `qT`
(in particular the object-logic bound variable `.var 0`) and a `DistAtA arity m`
distance witness (so `D.dT` evaluates to `oddDistance m`), the recursive resolved
row-entry tree `rowSymTreeA m D.dT kT qT` equals the flat base-entry classifier
`baseLeafTreeTA D.dT kT qT`, as a pure object-logic `PureFamilyDerivA` `eqPauli`
derivation.  No concrete `kv`/`qv` value is required. -/
def rowSymTreeFlatBridgeSym {fuel arity : Nat} :
    (m : Nat) → (D : DistAtA arity m) → (kT qT : Term arity .nat) →
    SFormula.PureNatTerm kT → SFormula.PureNatTerm qT →
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (SC.closed (rowSymTreeA m D.dT kT qT)) (SC.closed (baseLeafTreeTA D.dT kT qT)))
  | 0, D, kT, qT, _hk, _hq => by
      -- base: rowSymTreeA 0 = baseLeafTreeTA definitionally → reflexivity.
      simpa only [rowSymTreeA] using
        (PureFamilyDerivA.core (baseLeafSelfEq (Γ := []) D.dT kT qT)
          : PureFamilyDerivA Surface.code.body fuel
              (.eqPauli (SC.closed (baseLeafTreeTA D.dT kT qT)) (SC.closed (baseLeafTreeTA D.dT kT qT))))
  | m + 1, D, kT, qT, hk, hq => by
      -- step: flatten the five inner leaves by the IH, then the master self-sim dispatch.
      have ihInt := rowSymTreeFlatBridgeSym (fuel := fuel) m D.pred (interiorKTA D.dT kT) (innerQTA D.dT qT)
        (interiorKTA_pure D.pure hk) (innerQTA_pure D.pure hq)
      have ihTop := rowSymTreeFlatBridgeSym (fuel := fuel) m D.pred (topKTA D.dT kT) (innerQTA D.dT qT)
        (topKTA_pure D.pure hk) (innerQTA_pure D.pure hq)
      have ihRight := rowSymTreeFlatBridgeSym (fuel := fuel) m D.pred (rightKTA D.dT kT) (innerQTA D.dT qT)
        (rightKTA_pure D.pure hk) (innerQTA_pure D.pure hq)
      have ihLeft := rowSymTreeFlatBridgeSym (fuel := fuel) m D.pred (leftKTA D.dT kT) (innerQTA D.dT qT)
        (leftKTA_pure D.pure hk) (innerQTA_pure D.pure hq)
      have ihBottom := rowSymTreeFlatBridgeSym (fuel := fuel) m D.pred (bottomKTA D.dT kT) (innerQTA D.dT qT)
        (bottomKTA_pure D.pure hk) (innerQTA_pure D.pure hq)
      -- `D.pred.dT = innerDTA D.dT = recInnerDTA D.dT` definitionally.
      have hpredInt : PureFamilyDerivA Surface.code.body fuel
          (.eqPauli (SC.closed (rowSymTreeA m (innerDTA D.dT) (interiorKTA D.dT kT) (innerQTA D.dT qT)))
            (SC.closed (baseLeafTreeTA (innerDTA D.dT) (interiorKTA D.dT kT) (innerQTA D.dT qT)))) := by
        simpa only [DistAtA.pred] using ihInt
      have hpredTop : PureFamilyDerivA Surface.code.body fuel
          (.eqPauli (SC.closed (rowSymTreeA m (recInnerDTA D.dT) (topKTA D.dT kT) (innerQTA D.dT qT)))
            (SC.closed (baseLeafTreeTA (recInnerDTA D.dT) (topKTA D.dT kT) (innerQTA D.dT qT)))) := by
        simpa only [DistAtA.pred, recInnerDTA] using ihTop
      have hpredRight : PureFamilyDerivA Surface.code.body fuel
          (.eqPauli (SC.closed (rowSymTreeA m (recInnerDTA D.dT) (rightKTA D.dT kT) (innerQTA D.dT qT)))
            (SC.closed (baseLeafTreeTA (recInnerDTA D.dT) (rightKTA D.dT kT) (innerQTA D.dT qT)))) := by
        simpa only [DistAtA.pred, recInnerDTA] using ihRight
      have hpredLeft : PureFamilyDerivA Surface.code.body fuel
          (.eqPauli (SC.closed (rowSymTreeA m (recInnerDTA D.dT) (leftKTA D.dT kT) (innerQTA D.dT qT)))
            (SC.closed (baseLeafTreeTA (recInnerDTA D.dT) (leftKTA D.dT kT) (innerQTA D.dT qT)))) := by
        simpa only [DistAtA.pred, recInnerDTA] using ihLeft
      have hpredBottom : PureFamilyDerivA Surface.code.body fuel
          (.eqPauli (SC.closed (rowSymTreeA m (recInnerDTA D.dT) (bottomKTA D.dT kT) (innerQTA D.dT qT)))
            (SC.closed (baseLeafTreeTA (recInnerDTA D.dT) (bottomKTA D.dT kT) (innerQTA D.dT qT)))) := by
        simpa only [DistAtA.pred, recInnerDTA] using ihBottom
      -- the five flattened-leaf facts, folded into a conjunction, fed via `cut2`,
      -- then the master self-sim dispatch as the cut head (mechanism from `recRowConvergeA`).
      set Pi : SFormula arity :=
        .eqPauli (SC.closed (rowSymTreeA m (innerDTA D.dT) (interiorKTA D.dT kT) (innerQTA D.dT qT)))
          (SC.closed (baseLeafTreeTA (innerDTA D.dT) (interiorKTA D.dT kT) (innerQTA D.dT qT)))
      set Pt : SFormula arity :=
        .eqPauli (SC.closed (rowSymTreeA m (recInnerDTA D.dT) (topKTA D.dT kT) (innerQTA D.dT qT)))
          (SC.closed (baseLeafTreeTA (recInnerDTA D.dT) (topKTA D.dT kT) (innerQTA D.dT qT)))
      set Pr : SFormula arity :=
        .eqPauli (SC.closed (rowSymTreeA m (recInnerDTA D.dT) (rightKTA D.dT kT) (innerQTA D.dT qT)))
          (SC.closed (baseLeafTreeTA (recInnerDTA D.dT) (rightKTA D.dT kT) (innerQTA D.dT qT)))
      set Pl : SFormula arity :=
        .eqPauli (SC.closed (rowSymTreeA m (recInnerDTA D.dT) (leftKTA D.dT kT) (innerQTA D.dT qT)))
          (SC.closed (baseLeafTreeTA (recInnerDTA D.dT) (leftKTA D.dT kT) (innerQTA D.dT qT)))
      set Pb : SFormula arity :=
        .eqPauli (SC.closed (rowSymTreeA m (recInnerDTA D.dT) (bottomKTA D.dT kT) (innerQTA D.dT qT)))
          (SC.closed (baseLeafTreeTA (recInnerDTA D.dT) (bottomKTA D.dT kT) (innerQTA D.dT qT)))
      -- the five interior correspondence implications (built via `interiorImp*`).
      set Qbulk : SFormula arity :=
        .imp (interiorPbase D.dT kT qT)
          (.eqBool (SC.closed (bulkGuardTA (innerDTA D.dT) (interiorKTA D.dT kT))) (SC.b true))
      set QbandT : SFormula arity :=
        .imp (.and (interiorPbase D.dT kT qT)
                (.eqBool (SC.closed (baseBulkBandGuardTA D.dT kT qT)) (SC.b true)))
          (.eqBool (SC.closed (baseBulkBandGuardTA (innerDTA D.dT) (interiorKTA D.dT kT) (innerQTA D.dT qT)))
            (SC.b true))
      set QbandF : SFormula arity :=
        .imp (.and (interiorPbase D.dT kT qT)
                (.eqBool (SC.closed (baseBulkBandGuardTA D.dT kT qT)) (SC.b false)))
          (.eqBool (SC.closed (baseBulkBandGuardTA (innerDTA D.dT) (interiorKTA D.dT kT) (innerQTA D.dT qT)))
            (SC.b false))
      set QkindT : SFormula arity :=
        .imp (.and (interiorPbase D.dT kT qT)
                (.eqBool (SC.closed (baseKindGuardTA D.dT kT)) (SC.b true)))
          (.eqBool (SC.closed (baseKindGuardTA (innerDTA D.dT) (interiorKTA D.dT kT))) (SC.b true))
      set QkindF : SFormula arity :=
        .imp (.and (interiorPbase D.dT kT qT)
                (.eqBool (SC.closed (baseKindGuardTA D.dT kT)) (SC.b false)))
          (.eqBool (SC.closed (baseKindGuardTA (innerDTA D.dT) (interiorKTA D.dT kT))) (SC.b false))
      set QbandFNI : SFormula arity :=
        .imp (interiorPbaseNI D.dT kT qT)
          (.eqBool (SC.closed (baseBulkBandGuardTA D.dT kT qT)) (SC.b false))
      set TQctx : SFormula arity :=
        .imp (topPbase D.dT kT qT)
          (.and (.eqBool (SC.closed (baseKindGuardTA D.dT kT)) (SC.b false))
            (.and (.eqBool (SC.closed (bulkGuardTA (recInnerDTA D.dT) (topKTA D.dT kT))) (SC.b false))
              (.eqBool (SC.closed (topClassGuardTA (recInnerDTA D.dT) (topKTA D.dT kT))) (SC.b true))))
      set TQbandT : SFormula arity :=
        .imp (.and (topPbase D.dT kT qT)
                (.eqBool (SC.closed (baseBulkBandGuardTA D.dT kT qT)) (SC.b true)))
          (.eqBool (SC.closed (topBandGuardTA (recInnerDTA D.dT) (topKTA D.dT kT) (innerQTA D.dT qT)))
            (SC.b true))
      set TQbandF : SFormula arity :=
        .imp (.and (topPbase D.dT kT qT)
                (.eqBool (SC.closed (baseBulkBandGuardTA D.dT kT qT)) (SC.b false)))
          (.eqBool (SC.closed (topBandGuardTA (recInnerDTA D.dT) (topKTA D.dT kT) (innerQTA D.dT qT)))
            (SC.b false))
      set RQctx : SFormula arity :=
        .imp (rightPbase D.dT kT qT)
          (.and (.eqBool (SC.closed (baseKindGuardTA D.dT kT)) (SC.b true))
            (.and (.eqBool (SC.closed (bulkGuardTA (recInnerDTA D.dT) (rightKTA D.dT kT))) (SC.b false))
              (.and (.eqBool (SC.closed (topClassGuardTA (recInnerDTA D.dT) (rightKTA D.dT kT))) (SC.b false))
                (.eqBool (SC.closed (rightClassGuardTA (recInnerDTA D.dT) (rightKTA D.dT kT))) (SC.b true)))))
      set RQbandT : SFormula arity :=
        .imp (.and (rightPbase D.dT kT qT)
                (.eqBool (SC.closed (baseBulkBandGuardTA D.dT kT qT)) (SC.b true)))
          (.eqBool (SC.closed (rightBandGuardTA (recInnerDTA D.dT) (rightKTA D.dT kT) (innerQTA D.dT qT)))
            (SC.b true))
      set RQbandF : SFormula arity :=
        .imp (.and (rightPbase D.dT kT qT)
                (.eqBool (SC.closed (baseBulkBandGuardTA D.dT kT qT)) (SC.b false)))
          (.eqBool (SC.closed (rightBandGuardTA (recInnerDTA D.dT) (rightKTA D.dT kT) (innerQTA D.dT qT)))
            (SC.b false))
      set LQctx : SFormula arity :=
        .imp (leftPbase D.dT kT qT)
          (.and (.eqBool (SC.closed (baseKindGuardTA D.dT kT)) (SC.b true))
            (.and (.eqBool (SC.closed (bulkGuardTA (recInnerDTA D.dT) (leftKTA D.dT kT))) (SC.b false))
              (.and (.eqBool (SC.closed (topClassGuardTA (recInnerDTA D.dT) (leftKTA D.dT kT))) (SC.b false))
                (.and (.eqBool (SC.closed (rightClassGuardTA (recInnerDTA D.dT) (leftKTA D.dT kT))) (SC.b false))
                  (.eqBool (SC.closed (leftClassGuardTA (recInnerDTA D.dT) (leftKTA D.dT kT))) (SC.b true))))))
      set LQbandT : SFormula arity :=
        .imp (.and (leftPbase D.dT kT qT)
                (.eqBool (SC.closed (baseBulkBandGuardTA D.dT kT qT)) (SC.b true)))
          (.eqBool (SC.closed (leftBandGuardTA (recInnerDTA D.dT) (leftKTA D.dT kT) (innerQTA D.dT qT)))
            (SC.b true))
      set LQbandF : SFormula arity :=
        .imp (.and (leftPbase D.dT kT qT)
                (.eqBool (SC.closed (baseBulkBandGuardTA D.dT kT qT)) (SC.b false)))
          (.eqBool (SC.closed (leftBandGuardTA (recInnerDTA D.dT) (leftKTA D.dT kT) (innerQTA D.dT qT)))
            (SC.b false))
      set BQctx : SFormula arity :=
        .imp (bottomPbase D.dT kT qT)
          (.and (.eqBool (SC.closed (baseKindGuardTA D.dT kT)) (SC.b false))
            (.and (.eqBool (SC.closed (bulkGuardTA (recInnerDTA D.dT) (bottomKTA D.dT kT))) (SC.b false))
              (.and (.eqBool (SC.closed (topClassGuardTA (recInnerDTA D.dT) (bottomKTA D.dT kT))) (SC.b false))
                (.and (.eqBool (SC.closed (rightClassGuardTA (recInnerDTA D.dT) (bottomKTA D.dT kT))) (SC.b false))
                  (.eqBool (SC.closed (leftClassGuardTA (recInnerDTA D.dT) (bottomKTA D.dT kT))) (SC.b false))))))
      set BQbandT : SFormula arity :=
        .imp (.and (bottomPbase D.dT kT qT)
                (.eqBool (SC.closed (baseBulkBandGuardTA D.dT kT qT)) (SC.b true)))
          (.eqBool (SC.closed (bottomBandGuardTA (recInnerDTA D.dT) (bottomKTA D.dT kT) (innerQTA D.dT qT)))
            (SC.b true))
      set BQbandF : SFormula arity :=
        .imp (.and (bottomPbase D.dT kT qT)
                (.eqBool (SC.closed (baseBulkBandGuardTA D.dT kT qT)) (SC.b false)))
          (.eqBool (SC.closed (bottomBandGuardTA (recInnerDTA D.dT) (bottomKTA D.dT kT) (innerQTA D.dT qT)))
            (SC.b false))
      set TNQctx : SFormula arity :=
        .imp (topPbaseNI D.dT kT qT) (.eqBool (SC.closed (baseKindGuardTA D.dT kT)) (SC.b false))
      set TNQbandT : SFormula arity :=
        .imp (.and (topPbaseNI D.dT kT qT)
                (.eqBool (SC.closed (baseBulkBandGuardTA D.dT kT qT)) (SC.b true)))
          (.eqBool (SC.closed (topOuterGuardTA D.dT kT qT)) (SC.b true))
      set TNQbandF : SFormula arity :=
        .imp (.and (topPbaseNI D.dT kT qT)
                (.eqBool (SC.closed (baseBulkBandGuardTA D.dT kT qT)) (SC.b false)))
          (.eqBool (SC.closed (topOuterGuardTA D.dT kT qT)) (SC.b false))
      set RNQctx : SFormula arity :=
        .imp (rightPbaseNI D.dT kT qT) (.eqBool (SC.closed (baseKindGuardTA D.dT kT)) (SC.b true))
      set RNQbandT : SFormula arity :=
        .imp (.and (rightPbaseNI D.dT kT qT)
                (.eqBool (SC.closed (baseBulkBandGuardTA D.dT kT qT)) (SC.b true)))
          (.eqBool (SC.closed (rightOuterGuardTA D.dT kT qT)) (SC.b true))
      set RNQbandF : SFormula arity :=
        .imp (.and (rightPbaseNI D.dT kT qT)
                (.eqBool (SC.closed (baseBulkBandGuardTA D.dT kT qT)) (SC.b false)))
          (.eqBool (SC.closed (rightOuterGuardTA D.dT kT qT)) (SC.b false))
      set LNQctx : SFormula arity :=
        .imp (leftPbaseNI D.dT kT qT) (.eqBool (SC.closed (baseKindGuardTA D.dT kT)) (SC.b true))
      set LNQbandT : SFormula arity :=
        .imp (.and (leftPbaseNI D.dT kT qT)
                (.eqBool (SC.closed (baseBulkBandGuardTA D.dT kT qT)) (SC.b true)))
          (.eqBool (SC.closed (leftOuterGuardTA D.dT kT qT)) (SC.b true))
      set LNQbandF : SFormula arity :=
        .imp (.and (leftPbaseNI D.dT kT qT)
                (.eqBool (SC.closed (baseBulkBandGuardTA D.dT kT qT)) (SC.b false)))
          (.eqBool (SC.closed (leftOuterGuardTA D.dT kT qT)) (SC.b false))
      set BNQctx : SFormula arity :=
        .imp (bottomPbaseNI D.dT kT qT) (.eqBool (SC.closed (baseKindGuardTA D.dT kT)) (SC.b false))
      set BNQbandT : SFormula arity :=
        .imp (.and (bottomPbaseNI D.dT kT qT)
                (.eqBool (SC.closed (baseBulkBandGuardTA D.dT kT qT)) (SC.b true)))
          (.eqBool (SC.closed (bottomOuterGuardTA D.dT kT qT)) (SC.b true))
      set BNQbandF : SFormula arity :=
        .imp (.and (bottomPbaseNI D.dT kT qT)
                (.eqBool (SC.closed (baseBulkBandGuardTA D.dT kT qT)) (SC.b false)))
          (.eqBool (SC.closed (bottomOuterGuardTA D.dT kT qT)) (SC.b false))
      have hConj : PureFamilyDerivA Surface.code.body fuel
          (.and Pi (.and Pt (.and Pr (.and Pl (.and Pb
            (.and Qbulk (.and QbandT (.and QbandF (.and QkindT (.and QkindF (.and QbandFNI
              (.and TQctx (.and TQbandT (.and TQbandF
                (.and RQctx (.and RQbandT (.and RQbandF
                  (.and LQctx (.and LQbandT (.and LQbandF
                    (.and BQctx (.and BQbandT (.and BQbandF
                      (.and TNQctx (.and TNQbandT (.and TNQbandF
                        (.and RNQctx (.and RNQbandT (.and RNQbandF
                          (.and LNQctx (.and LNQbandT (.and LNQbandF
                            (.and BNQctx (.and BNQbandT BNQbandF)))))))))))))))))))))))))))))))))) :=
        PureFamilyDerivA.cut2
          (SFormula.Deriv.andIntro (SFormula.Deriv.hyp (by left)) (SFormula.Deriv.hyp (by right; left)))
          hpredInt
          (PureFamilyDerivA.cut2
            (SFormula.Deriv.andIntro (SFormula.Deriv.hyp (by left)) (SFormula.Deriv.hyp (by right; left)))
            hpredTop
            (PureFamilyDerivA.cut2
              (SFormula.Deriv.andIntro (SFormula.Deriv.hyp (by left)) (SFormula.Deriv.hyp (by right; left)))
              hpredRight
              (PureFamilyDerivA.cut2
                (SFormula.Deriv.andIntro (SFormula.Deriv.hyp (by left)) (SFormula.Deriv.hyp (by right; left)))
                hpredLeft
                (PureFamilyDerivA.cut2
                  (SFormula.Deriv.andIntro (SFormula.Deriv.hyp (by left)) (SFormula.Deriv.hyp (by right; left)))
                  hpredBottom
                  (PureFamilyDerivA.cut2
                    (SFormula.Deriv.andIntro (SFormula.Deriv.hyp (by left)) (SFormula.Deriv.hyp (by right; left)))
                    (interiorImpBulk D hk hq)
                    (PureFamilyDerivA.cut2
                      (SFormula.Deriv.andIntro (SFormula.Deriv.hyp (by left)) (SFormula.Deriv.hyp (by right; left)))
                      (interiorImpBand true D hk hq)
                      (PureFamilyDerivA.cut2
                        (SFormula.Deriv.andIntro (SFormula.Deriv.hyp (by left)) (SFormula.Deriv.hyp (by right; left)))
                        (interiorImpBand false D hk hq)
                        (PureFamilyDerivA.cut2
                          (SFormula.Deriv.andIntro (SFormula.Deriv.hyp (by left)) (SFormula.Deriv.hyp (by right; left)))
                          (interiorImpKind true D hk hq)
                          (PureFamilyDerivA.cut2
                            (SFormula.Deriv.andIntro (SFormula.Deriv.hyp (by left)) (SFormula.Deriv.hyp (by right; left)))
                            (interiorImpKind false D hk hq)
                            (PureFamilyDerivA.cut2
                              (SFormula.Deriv.andIntro (SFormula.Deriv.hyp (by left)) (SFormula.Deriv.hyp (by right; left)))
                              (interiorImpBandNI D hk hq)
                              (PureFamilyDerivA.cut2
                                (SFormula.Deriv.andIntro (SFormula.Deriv.hyp (by left)) (SFormula.Deriv.hyp (by right; left)))
                                (topImpCtx D hk hq)
                                (PureFamilyDerivA.cut2
                                  (SFormula.Deriv.andIntro (SFormula.Deriv.hyp (by left)) (SFormula.Deriv.hyp (by right; left)))
                                  (topImpBand true D hk hq)
                                  (PureFamilyDerivA.cut2
                                    (SFormula.Deriv.andIntro (SFormula.Deriv.hyp (by left)) (SFormula.Deriv.hyp (by right; left)))
                                    (topImpBand false D hk hq)
                                    (PureFamilyDerivA.cut2
                                      (SFormula.Deriv.andIntro (SFormula.Deriv.hyp (by left)) (SFormula.Deriv.hyp (by right; left)))
                                      (rightImpCtx D hk hq)
                                      (PureFamilyDerivA.cut2
                                        (SFormula.Deriv.andIntro (SFormula.Deriv.hyp (by left)) (SFormula.Deriv.hyp (by right; left)))
                                        (rightImpBand true D hk hq)
                                        (PureFamilyDerivA.cut2
                                          (SFormula.Deriv.andIntro (SFormula.Deriv.hyp (by left)) (SFormula.Deriv.hyp (by right; left)))
                                          (rightImpBand false D hk hq)
                                          (PureFamilyDerivA.cut2
                                            (SFormula.Deriv.andIntro (SFormula.Deriv.hyp (by left)) (SFormula.Deriv.hyp (by right; left)))
                                            (leftImpCtx D hk hq)
                                            (PureFamilyDerivA.cut2
                                              (SFormula.Deriv.andIntro (SFormula.Deriv.hyp (by left)) (SFormula.Deriv.hyp (by right; left)))
                                              (leftImpBand true D hk hq)
                                              (PureFamilyDerivA.cut2
                                                (SFormula.Deriv.andIntro (SFormula.Deriv.hyp (by left)) (SFormula.Deriv.hyp (by right; left)))
                                                (leftImpBand false D hk hq)
                                                (PureFamilyDerivA.cut2
                                                  (SFormula.Deriv.andIntro (SFormula.Deriv.hyp (by left)) (SFormula.Deriv.hyp (by right; left)))
                                                  (bottomImpCtx D hk hq)
                                                  (PureFamilyDerivA.cut2
                                                    (SFormula.Deriv.andIntro (SFormula.Deriv.hyp (by left)) (SFormula.Deriv.hyp (by right; left)))
                                                    (bottomImpBand true D hk hq)
                                                    (PureFamilyDerivA.cut2 (SFormula.Deriv.andIntro (SFormula.Deriv.hyp (by left)) (SFormula.Deriv.hyp (by right; left))) (bottomImpBand false D hk hq)
                                                      (PureFamilyDerivA.cut2 (SFormula.Deriv.andIntro (SFormula.Deriv.hyp (by left)) (SFormula.Deriv.hyp (by right; left))) (topNIImpCtx D hk hq)
                                                        (PureFamilyDerivA.cut2 (SFormula.Deriv.andIntro (SFormula.Deriv.hyp (by left)) (SFormula.Deriv.hyp (by right; left))) (topNIImpBand true D hk hq)
                                                          (PureFamilyDerivA.cut2 (SFormula.Deriv.andIntro (SFormula.Deriv.hyp (by left)) (SFormula.Deriv.hyp (by right; left))) (topNIImpBand false D hk hq)
                                                            (PureFamilyDerivA.cut2 (SFormula.Deriv.andIntro (SFormula.Deriv.hyp (by left)) (SFormula.Deriv.hyp (by right; left))) (rightNIImpCtx D hk hq)
                                                              (PureFamilyDerivA.cut2 (SFormula.Deriv.andIntro (SFormula.Deriv.hyp (by left)) (SFormula.Deriv.hyp (by right; left))) (rightNIImpBand true D hk hq)
                                                                (PureFamilyDerivA.cut2 (SFormula.Deriv.andIntro (SFormula.Deriv.hyp (by left)) (SFormula.Deriv.hyp (by right; left))) (rightNIImpBand false D hk hq)
                                                                  (PureFamilyDerivA.cut2 (SFormula.Deriv.andIntro (SFormula.Deriv.hyp (by left)) (SFormula.Deriv.hyp (by right; left))) (leftNIImpCtx D hk hq)
                                                                    (PureFamilyDerivA.cut2 (SFormula.Deriv.andIntro (SFormula.Deriv.hyp (by left)) (SFormula.Deriv.hyp (by right; left))) (leftNIImpBand true D hk hq)
                                                                      (PureFamilyDerivA.cut2 (SFormula.Deriv.andIntro (SFormula.Deriv.hyp (by left)) (SFormula.Deriv.hyp (by right; left))) (leftNIImpBand false D hk hq)
                                                                        (PureFamilyDerivA.cut2 (SFormula.Deriv.andIntro (SFormula.Deriv.hyp (by left)) (SFormula.Deriv.hyp (by right; left))) (bottomNIImpCtx D hk hq)
                                                                          (PureFamilyDerivA.cut2 (SFormula.Deriv.andIntro (SFormula.Deriv.hyp (by left)) (SFormula.Deriv.hyp (by right; left))) (bottomNIImpBand true D hk hq)
                                                                            (bottomNIImpBand false D hk hq))))))))))))))))))))))))))))))))))
      -- cut1: the head congruences the five `rowSymTreeA m …` leaves into
      -- `baseLeafTreeTA …` leaves (via the conjuncts), then runs the master dispatch.
      have hmain : PureFamilyDerivA Surface.code.body fuel
          (.eqPauli
            (SC.closed (recLeafTreeTA D.dT kT qT
              (rowSymTreeA m (innerDTA D.dT) (interiorKTA D.dT kT) (innerQTA D.dT qT))
              (rowSymTreeA m (recInnerDTA D.dT) (topKTA D.dT kT) (innerQTA D.dT qT))
              (rowSymTreeA m (recInnerDTA D.dT) (rightKTA D.dT kT) (innerQTA D.dT qT))
              (rowSymTreeA m (recInnerDTA D.dT) (leftKTA D.dT kT) (innerQTA D.dT qT))
              (rowSymTreeA m (recInnerDTA D.dT) (bottomKTA D.dT kT) (innerQTA D.dT qT))))
            (SC.closed (baseLeafTreeTA D.dT kT qT))) := by
        refine PureFamilyDerivA.cut1 ?_ hConj
        -- in the cut head the single hypothesis is the big right-nested conjunction of the
        -- five IH-leaf equalities + all correspondence implications; name each conjunct via
        -- `andElimLeft (andElimRight^i hyp)` (last conjunct is the deepest `andElimRight^…`).
        have H : SFormula.Deriv [_]
            (.and Pi (.and Pt (.and Pr (.and Pl (.and Pb
              (.and Qbulk (.and QbandT (.and QbandF (.and QkindT (.and QkindF (.and QbandFNI
                (.and TQctx (.and TQbandT (.and TQbandF
                  (.and RQctx (.and RQbandT (.and RQbandF
                    (.and LQctx (.and LQbandT (.and LQbandF
                      (.and BQctx (.and BQbandT (.and BQbandF
                        (.and TNQctx (.and TNQbandT (.and TNQbandF
                          (.and RNQctx (.and RNQbandT (.and RNQbandF
                            (.and LNQctx (.and LNQbandT (.and LNQbandF
                              (.and BNQctx (.and BNQbandT BNQbandF)))))))))))))))))))))))))))))))))) :=
          SFormula.Deriv.hyp (by left)
        have r1 := SFormula.Deriv.andElimRight H
        have r2 := SFormula.Deriv.andElimRight r1
        have r3 := SFormula.Deriv.andElimRight r2
        have r4 := SFormula.Deriv.andElimRight r3
        have r5 := SFormula.Deriv.andElimRight r4
        have r6 := SFormula.Deriv.andElimRight r5
        have r7 := SFormula.Deriv.andElimRight r6
        have r8 := SFormula.Deriv.andElimRight r7
        have r9 := SFormula.Deriv.andElimRight r8
        have r10 := SFormula.Deriv.andElimRight r9
        have r11 := SFormula.Deriv.andElimRight r10
        have r12 := SFormula.Deriv.andElimRight r11
        have r13 := SFormula.Deriv.andElimRight r12
        have r14 := SFormula.Deriv.andElimRight r13
        have r15 := SFormula.Deriv.andElimRight r14
        have r16 := SFormula.Deriv.andElimRight r15
        have r17 := SFormula.Deriv.andElimRight r16
        have r18 := SFormula.Deriv.andElimRight r17
        have r19 := SFormula.Deriv.andElimRight r18
        have r20 := SFormula.Deriv.andElimRight r19
        have r21 := SFormula.Deriv.andElimRight r20
        have r22 := SFormula.Deriv.andElimRight r21
        have r23 := SFormula.Deriv.andElimRight r22
        have r24 := SFormula.Deriv.andElimRight r23
        have r25 := SFormula.Deriv.andElimRight r24
        have r26 := SFormula.Deriv.andElimRight r25
        have r27 := SFormula.Deriv.andElimRight r26
        have r28 := SFormula.Deriv.andElimRight r27
        have r29 := SFormula.Deriv.andElimRight r28
        have r30 := SFormula.Deriv.andElimRight r29
        have r31 := SFormula.Deriv.andElimRight r30
        have r32 := SFormula.Deriv.andElimRight r31
        have r33 := SFormula.Deriv.andElimRight r32
        exact recFlatMasterD D.dT kT qT _ _ _ _ _
          (SFormula.Deriv.andElimLeft H)
          (SFormula.Deriv.andElimLeft r1)
          (SFormula.Deriv.andElimLeft r2)
          (SFormula.Deriv.andElimLeft r3)
          (SFormula.Deriv.andElimLeft r4)
          (SFormula.Deriv.andElimLeft r5)
          (SFormula.Deriv.andElimLeft r6)
          (SFormula.Deriv.andElimLeft r7)
          (SFormula.Deriv.andElimLeft r8)
          (SFormula.Deriv.andElimLeft r9)
          (SFormula.Deriv.andElimLeft r10)
          (SFormula.Deriv.andElimLeft r11)
          (SFormula.Deriv.andElimLeft r12)
          (SFormula.Deriv.andElimLeft r13)
          (SFormula.Deriv.andElimLeft r14)
          (SFormula.Deriv.andElimLeft r15)
          (SFormula.Deriv.andElimLeft r16)
          (SFormula.Deriv.andElimLeft r17)
          (SFormula.Deriv.andElimLeft r18)
          (SFormula.Deriv.andElimLeft r19)
          (SFormula.Deriv.andElimLeft r20)
          (SFormula.Deriv.andElimLeft r21)
          (SFormula.Deriv.andElimLeft r22)
          (SFormula.Deriv.andElimLeft r23)
          (SFormula.Deriv.andElimLeft r24)
          (SFormula.Deriv.andElimLeft r25)
          (SFormula.Deriv.andElimLeft r26)
          (SFormula.Deriv.andElimLeft r27)
          (SFormula.Deriv.andElimLeft r28)
          (SFormula.Deriv.andElimLeft r29)
          (SFormula.Deriv.andElimLeft r30)
          (SFormula.Deriv.andElimLeft r31)
          (SFormula.Deriv.andElimLeft r32)
          (SFormula.Deriv.andElimLeft r33)
          (SFormula.Deriv.andElimRight r33)
      simpa only [rowSymTreeA] using hmain

/-! ## Composition: the flat row entry at a symbolic index

`rowEntryFlatSym` composes the symbolic row characterization
`surfaceRowEntryCharSymbolicA` (`stabAt (recCall D.dT kT) qT = rowSymTreeA m`) with
the symbolic flat bridge (`rowSymTreeA m = baseLeafTreeTA`), giving the flat,
recursion-free row entry at a SYMBOLIC index `kT` / qubit `qT`.  This is the
deliverable the symbolic-distance consumers need. -/
def rowEntryFlatSym {fuel arity : Nat}
    (m : Nat) (D : DistAtA arity m) (kT qT : Term arity .nat)
    (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (.stabAt (SC.closed (.recCall D.dT kT)) (SC.closed qT))
        (SC.closed (baseLeafTreeTA D.dT kT qT))) :=
  PureFamilyDerivA.eqPauliTrans _ _ _
    (surfaceRowEntryCharSymbolicA m D kT qT hk hq)
    (rowSymTreeFlatBridgeSym m D kT qT hk hq)

#print axioms rowSymTreeFlatBridgeSym
#print axioms rowEntryFlatSym

/-! ## Honest notes on the symbolic flat bridge

* `rowSymTreeFlatBridgeSym` has the REQUIRED symbolic statement: `kT qT : Term arity
  .nat` are arbitrary pure terms (only `SFormula.PureNatTerm` purity certificates,
  no `evalsTo`-to-a-fixed-value hypothesis), so it applies at the object-logic bound
  variable `.var 0`.  The only distance constraint is `DistAtA arity m` (so `D.dT`
  evaluates to `oddDistance m` in every environment).  `rowEntryFlatSym` composes it
  with `surfaceRowEntryCharSymbolicA` to give the flat, recursion-free row entry at a
  symbolic index — the deliverable the symbolic-distance consumers need.

* The recursion machinery is fully built and sound:
  - base `m = 0`: `rowSymTreeA 0 = baseLeafTreeTA` definitionally, closed by
    `PureFamilyDerivA.core (baseLeafSelfEq …)`;
  - step `m + 1`: the five inner leaves `rowSymTreeA m (inner)` are flattened to
    `baseLeafTreeTA (inner)` by the IH (`rowSymTreeFlatBridgeSym m D.pred …`), folded
    into one conjunction via `cut2`, and dispatched by `recFlatMasterD` — an
    object-logic `SFormula.Deriv.boolCases` over every cell-kind guard (the same
    mechanism as `recEntryMasterD` / `recRowConvergeA`), NOT `by_cases` on a concrete
    `kv`.  No `native_decide`, `Formula.check`, `Formula.eval`-as-proof,
    `deriveTrue?`, `admit`, new `axiom`, `@[implemented_by]`, `unsafe`, or
    `checkedBoundFree` is used.

* The self-similarity-leaf mechanism is now FULLY BUILT for ALL TEN single-step
  self-similarity leaves (`flatStepInterior`, `flatStep{Top,Right,Left,Bottom}`, and
  the six `…NI` counterparts) — every leaf is `sorry`-free.  The route, realised
  concretely and uniformly:
  1. Nat-level inner↔outer classifier-guard *correspondences*, restating the internal
     `hKind`/`hBand`/bulk facts of `SurfaceSelfSimNat.lean` as standalone Nat lemmas:
     interior (`interiorInnerBulkNat` / `interiorBandCorrNat` / `interiorKindCorrNat`),
     top/right/left/bottom (`*InnerBulkFalseNat` / `*InnerClassTrueNat` / `*KindNat` /
     `*BandCorrNat`, extracted from `top/right/left/bottomSelfSimNat`), and the NI
     band↔outer-ring equalities (`{top,right,left,bottom}NI_bandEqOuterNat`, derived
     from the bulk form of `surfaceCellPauli` + `surfaceCellPauli_*Cell_notInside`).
  2. `impGuardA_of`: the implication analogue of `cellGuardA_of`, discharging an
     `arithBool` correspondence implication `imp P (eqBool (closed g) (b v))` from an
     `Env`-uniform validity certificate.
  3. Each leaf `boolCases` on the OUTER band guard and, in each branch, `mp`s the
     matching correspondence implication to obtain the INNER guard value, then reduces
     both sides to the SAME Pauli literal: inside leaves via `baseLeaf{Z,X,BulkI}S`
     (interior) or `baseLeaf{Top,Right,Left,Bottom}{X,Z,I}S` (the inner-code boundary
     strip, since a promoted-boundary cell maps to a boundary cell of the inner code);
     the NI leaves reduce the already-outer-ring `ite outerGuard kind I` LHS via
     `pauliIteSelect{Then,Else}` and the flat RHS via `baseLeaf{X,Z}S`/`baseLeafBulkIS`.
  4. Every correspondence implication is built in `rowSymTreeFlatBridgeSym` via the
     `*Imp*` / `*NIImp*` helpers, folded into the `cut` conjunction `hConj` (35 conjuncts:
     5 IH-leaf equalities + 30 correspondence implications), and threaded into
     `recFlatMasterD`'s boolCases context.
  No `native_decide`, `Formula.check`, `Formula.eval`-as-proof, `deriveTrue?`,
  `admit`, new `axiom`, `@[implemented_by]`, `unsafe`, or `checkedBoundFree` is used;
  `arithBool` (the sanctioned closed-bool GUARD mechanism) carries every guard
  correspondence; META `Nat` tactics (`omega`, `simp`, `decide`) discharge the
  standalone Nat correspondence lemmas only.

* The bridge is COMPLETE: `rowSymTreeFlatBridgeSym` and `rowEntryFlatSym` are
  `sorry`-free and axiom-clean (`#print axioms` reports
  `[propext, Classical.choice, Quot.sound]`). -/

end QHL.CodeLang.Surface.Verify
