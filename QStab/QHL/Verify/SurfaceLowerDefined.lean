import QStab.QHL.Verify.SurfaceLowerDefined.Helpers
import QStab.QHL.Verify.SurfaceLowerDefined.RowColCut
import QStab.QHL.Verify.SurfaceLowerDefined.LogicalOp
import QStab.QHL.Verify.SurfaceLowerDefined.ParityProp
import QStab.QHL.Verify.SurfaceLowerDefined.BridgeNorms
import QStab.QHL.Verify.SurfaceLowerDefined.RowWeight
import QStab.QHL.Verify.SurfaceLowerDefined.ColWeight
import QStab.QHL.Verify.SurfaceLowerDefined.Assembly

/-!
# Surface-code distance lower bound — the *definedness* layer (module index)

This module is a **barrel**: it re-exports the small, single-concern files under
`SurfaceLowerDefined/` (built in this dependency order, which mirrors the proof's structure):

1. `Helpers`      — reusable FD / totality / cell-read building blocks;
2. `RowColCut`    — row/col cut definedness (cores 1-2, `rowCutNoX`/`colCutNoZ`);
3. `LogicalOp`    — logical-operator FDs + rule-truth `…_holds` lemmas;
4. `ParityProp`   — parity-propagation cores 4/4';
5. `BridgeNorms`  — bridge-factor normalisation cores;
6. `RowWeight`    — X/row weight-counting core 6;
7. `ColWeight`    — Z/col weight-counting core 6';
8. `Assembly`     — core 3 + the entry point `lowerDefinedAux`.

This module is the **plumbing** for the distance lower bound.  It contains no new mathematics
about the surface code: the distance *argument* lives entirely in the pure derivation tree
assembled in `SurfacePureAssembly` (`PureLowerClosedLeaves.lowerBound`).  What that tree needs,
and what this file supplies, is a single companion fact:

> every object-logic step in the tree is **computationally well-formed** — each stabilizer read,
> each product-fold, each (anti)commutation actually *evaluates* on a total partial stabilizer `E`.

Formally we discharge the `DefinedObligations` side-conditions (`FormulaDefined` / `DerivWF`) that
`PureForallStabDeriv.sound` demands before it will turn the tree into the semantic distance fact.
The evaluator is allowed to appear *here* precisely because these are definedness obligations, not
the distance claim itself (see the strict-purity contract in `SurfaceDistanceProver`).

## The backbone the tree encodes (what we are certifying is *defined*)

A logical operator of weight `< d` is impossible.  The tree shows this in two mirror halves:

* **X / rows.**  A nontrivial logical `X` anticommutes with the logical `Z` string.  The
  *cut → telescope → bridge* structure propagates that anticommutation into **every one of the `d`
  rows**, so each row is *occupied* (contains support); counting the `d` occupied rows gives
  weight `≥ d`.
* **Z / columns.**  The exact transpose: a nontrivial logical `Z` occupies every one of the `d`
  columns, giving weight `≥ d`.

`cut4` glues the two halves.  This file proves that each ingredient of that walk — the row/col
cut entries, the strip products, the bridge factorisations, the per-cell occupancy reads, and the
final weight-counting cover — is *defined* for every odd `d` and every total `E`.

## Reading guide: the X ↔ Z (row ↔ column) mirror

The surface code's transpose symmetry makes almost every lemma below one of a **row/`X`** and
**column/`Z`** pair (e.g. `rowCutLocal_WF` ↔ `colCutLocal_WF`,
`xParityPropRowsCore_WF` ↔ `zParityPropColsCore_WF`, `xRowsWeight_WF` ↔ `zColsWeight_WF`).  The
pair members are genuine mirror images, not copy-paste: their *orientation-independent* cores are
factored into shared, orientation-parameterised lemmas that both members call —

* `commutesUpTo_stabFold_FD` — a strip product-fold commutes with any total `E` (both the top-level
  and bridge-normaliser strip obligations, both orientations);
* `xCellReadDefined` / `zCellReadDefined` — the single per-cell occupancy read `stabAt (gridIdx …)`
  is defined because `E` is total (the leaf under *every* occupancy `FormulaDefined`);
* `stabFoldEval_total` / `partialStabilizerFold_total` — the fold of everywhere-total slots is
  everywhere-total.

## Entry point

`lowerDefinedAux` assembles the nine core well-formedness lemmas into the exact
`DefinedObligations` shape the prover's `lowerDefined` field consumes.
-/

