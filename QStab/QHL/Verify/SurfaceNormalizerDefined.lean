import QStab.QHL.Verify.SurfaceNormalizerDefined.Combinators
import QStab.QHL.Verify.SurfaceNormalizerDefined.PurePauliCerts
import QStab.QHL.Verify.SurfaceNormalizerDefined.BaseLeaf
import QStab.QHL.Verify.SurfaceNormalizerDefined.BaseMaster
import QStab.QHL.Verify.SurfaceNormalizerDefined.RecEval
import QStab.QHL.Verify.SurfaceNormalizerDefined.RecLeaf
import QStab.QHL.Verify.SurfaceNormalizerDefined.RecPeel
import QStab.QHL.Verify.SurfaceNormalizerDefined.RowSelect
import QStab.QHL.Verify.SurfaceNormalizerDefined.FlatBridge
import QStab.QHL.Verify.SurfaceNormalizerDefined.Commutators
import QStab.QHL.Verify.SurfaceNormalizerDefined.LeafHelpers
import QStab.QHL.Verify.SurfaceNormalizerDefined.ZMirror
import QStab.QHL.Verify.SurfaceNormalizerDefined.Classification

/-!
# Normalizer sub-tree definedness — module index

Barrel over the small single-concern files under `SurfaceNormalizerDefined/`, towards
`xNormScaffold_WF` / `zNormScaffold_WF` (definedness of the two logical-normalizer code-level
sub-trees).  Built bottom-up: combinators → base/rec leaves → peel infrastructure → row-select
→ flat-bridge → commutators → leaf helpers → per-`k` classification.  Original notes below.
-/

/-!
# `DerivWFA` for the two NORMALIZER code-level sub-trees (GROUP 2)

This file works towards `xNormScaffold_WF` / `zNormScaffold_WF`, the definedness
well-formedness witnesses for the symbolic `logicalX`/`logicalZ` normalizers
(`xNormCommuteSym` / `zNormCommuteSym`).  These are 2 of the 6 `codeLevel`
sub-trees consumed by the `codeLevelDefined` discharger through
`pfd_defined`/`pfda_defined`.

## Status (HONEST)

The reusable `DerivWFA`-combinator scaffolding is in place and the top-level walk
is reduced via the combinators to exactly two genuinely deep residuals:

* `rowEntryFlatSym_WF` — the flat row-entry totality.  `rowEntryFlatSym` composes
  `surfaceRowEntryCharSymbolicA` (recurses on `D.index`!) with
  `rowSymTreeFlatBridgeSym`.

  ### `m`-induction COLLAPSE (PROVEN)
  `surfaceRowEntryCharSymbolicA_WF` is the keystone's first conjunct.  Its `DerivWFA`
  is proved by a single `induction m` whose BODY IS SORRY-FREE: the BASE relays
  `baseRowConvergeA_WF`, the STEP relays the IH (the five inner sub-derivations'
  `DerivWFA`) through `recRowConvergeA_WF`.  No per-level multiplication of the leaf
  grind — the entire `m`-family reduces to the two FLAT (non-`m`-recursing) master
  helpers.  `recRowConvergeA_WF`'s `cut1`/`cut2` glue (relaying the five IH sub-
  derivations + the row-projection structure) is ALSO sorry-free.
  REMAINING (the genuine grind, flat in `m`): the two master cores'
  `DerivWF`/`DerivWFA` — `baseEntryMasterD` (base 7-level boolCases tree),
  `recEntryMasterD` (rec 7-level boolCases tree), and the `surfaceCodeRowSelectBase`
  / `surfaceCodeRowSelectRecursive` row-select sub-trees; plus the parallel
  `rowSymTreeFlatBridgeSym` / `recFlatMasterD` bridge induction.  Each is hundreds of
  LOC of bespoke closed-`Term.eval` discharge (the `baseLeafTreeTA` pauli-literal
  `ite`-trees are NOT `PureTerm`, so the uniform `…_closedPure` dischargers do not
  apply).  `rowEntryFlatSym_WF` now takes the row-projection witnesses (`hproj`,
  `hwit`) — the qubit-in-range side-data the binder range supplies in the consumers.
* the commutator leaves `commTwoAntiA` / `commTwoAntiB` / `commPointwiseSym` —
  each a deep `SFormula.Deriv` (with `colDispatchOnTrue` / `entryAtBound` /
  `logicalXOffColumnLocalCommutes` sub-trees).  Their `DerivWF` is large but does
  NOT recurse on `D.index`.  OPEN (residual #2).

Everything *between* these residuals (the cast/`allNatLtIntro`/`cut1`/`boolCases`
structure, the `pfdaAnd` bundle glue, AND the entire `m`-induction collapse) is
proved sorry-free below.
-/
