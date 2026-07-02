import QStab.QHL.Verify.SurfaceRowsCommute.Setup
import QStab.QHL.Verify.SurfaceRowsCommute.Resolvers
import QStab.QHL.Verify.SurfaceRowsCommute.Assembly
import QStab.QHL.Verify.SurfaceRowsCommute.TypeClosers
import QStab.QHL.Verify.SurfaceRowsCommute.BulkTop
import QStab.QHL.Verify.SurfaceRowsCommute.BulkBottom
import QStab.QHL.Verify.SurfaceRowsCommute.BulkRight
import QStab.QHL.Verify.SurfaceRowsCommute.BulkLeft
import QStab.QHL.Verify.SurfaceRowsCommute.BulkBulkHV
import QStab.QHL.Verify.SurfaceRowsCommute.BulkBulkLU
import QStab.QHL.Verify.SurfaceRowsCommute.NonAdjacentBulk
import QStab.QHL.Verify.SurfaceRowsCommute.NonAdjacentBoundary
import QStab.QHL.Verify.SurfaceRowsCommute.Dispatchers
import QStab.QHL.Verify.SurfaceRowsCommute.Router
import QStab.QHL.Verify.SurfaceRowsCommute.Families

/-!
# Surface rows-commute (module index)

Barrel over the small single-concern files under `SurfaceRowsCommute/`: any two generated
stabilizer rows of the recursive Surface code commute.  Structure: setup/resolvers → headline
assembly → same/different-type closers → the overlap classes (bulk-top/bottom/right/left,
bulk-bulk H/V/HL/VU) → the non-adjacent pairs → the class-combo dispatchers → router → ∀∀ families.
-/

/-!
# Pairwise row commutation for the recursive Surface code (`∀ D`)

`rowsCommuteSym D : PureFamilyDerivA Surface.code.body (D.distance + 2)
  (closedSF (rowsCommuteOddF D))` — every pair of generated stabilizer rows
`codeRow d k1`, `codeRow d k2` commutes, for all `OddSurfaceDistance D`.

This is the third input (`rows`) to `codeLevelPureFromGeneratedRows`, alongside
the two normalizers `xNormCommuteSym` / `zNormCommuteSym`.

## Strategy (CSS, verified by `#eval` on `surfaceCellPauli`/`baseLeafTreeTA`)

The surface code is CSS: every generated row is uniformly X-type or Z-type.
Verified geometry (d = 3,5,7, exhaustive):
* each row is uniformly X or Z (0 mixed);
* two rows of the SAME type never anticommute at any qubit;
* two rows of DIFFERENT type anticommute exactly on `support(k1) ∩ support(k2)`,
  whose size is always 0 or 2 (the two shared corner qubits of two adjacent
  surface-code plaquettes).

The proof reuses the normalizer machinery (`SurfaceNormalizers.lean`):
`rowEntryFlatSym` resolves BOTH row entries to the flat `baseLeafTreeTA`
classifier, `commutesOfPointwise` discharges the same-type / non-overlapping
classes, and `commutesOfTwoAnti` with arithmetic `q0`/`q1` discharges the
overlapping X-vs-Z classes.

Prover-side only: no `native_decide` / `Formula.check` / `Formula.eval`-as-proof
/ `deriveTrue?` / `admit` / new `axiom` / `@[implemented_by]` / `unsafe` /
`checkedBoundFree`.
-/
