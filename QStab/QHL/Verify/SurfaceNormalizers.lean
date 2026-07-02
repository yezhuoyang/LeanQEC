import QStab.QHL.Verify.SurfaceNormalizers.XSetup
import QStab.QHL.Verify.SurfaceNormalizers.XLogicalXEntries
import QStab.QHL.Verify.SurfaceNormalizers.XGuards
import QStab.QHL.Verify.SurfaceNormalizers.XClassA
import QStab.QHL.Verify.SurfaceNormalizers.XClassB
import QStab.QHL.Verify.SurfaceNormalizers.XTop
import QStab.QHL.Verify.SurfaceNormalizers.ZSetup
import QStab.QHL.Verify.SurfaceNormalizers.ZClassA
import QStab.QHL.Verify.SurfaceNormalizers.ZClassB
import QStab.QHL.Verify.SurfaceNormalizers.ZTop

/-!
# Logical-normalizer consumers — module index

Barrel over the small single-concern files under `SurfaceNormalizers/`.  The two logical
operators normalise every generated row: the X half (`xNormScaffold`) then its row/column
transpose Z half (`zNormScaffold`), each = witness/off-support setup → guards → two-anti
classes (a)/(b) → top-level classification.  Original task notes below.
-/

/-!
# Logical-normalizer consumers (TASK B)

`xNorm` / `zNorm` : the two logical operators `logicalX` / `logicalZ` commute with
every generated stabilizer row of the recursive Surface code.  These are two of
the three inputs to `codeLevelPureFromGeneratedRows`.

Prover-side only: no new logic rules, no `native_decide` / `Formula.check` /
`deriveTrue?` / `admit` / axioms / oracles.

## State of TASK B (honest)

The CSS overlap structure (confirmed by `#eval` on the evaluator, NOT used in any
proof) is: a generated row anticommutes with `logicalX` at **exactly 0 or 2**
column-0 qubits — never odd — so commutation always holds.  Concretely for `d=3`
stabilizers 0,6 overlap at 2; for `d=5` stabilizers 0,8,20,21 overlap at 2; all
other rows overlap at 0.

The faithful, sorry-free row-entry characterization `surfaceRowEntryCharSymbolicA`
(TASK A) resolves the symbolic row entry to the guarded leaf tree `rowSymTreeA`.

### Progress in this file (axiom-clean `[propext, Quot.sound]`)

The `recCall` obstacle is fully discharged:

* `boundRowEntryPure` / `boundRowsResolved` — for *every* qubit `q < nQubits`,
  the bound-index generated row entry `stabAt (recCall (lift d) k) q` equals the
  recursion-free leaf tree `rowSymTreeA D.index (lift d) (lift k) q`.  Built
  directly from `surfaceRowEntryCharSymbolicA`, no new rule.

* `xNormScaffold` then `cut1`s `boundRowsResolved` in, so the remaining goal is a
  pure `SFormula.Deriv` derivation of
  `commutesUpTo n (recCall (lift d) (var 0)) (lift logicalX)` **with the
  resolved-row equality available as an `SFormula.Deriv` hypothesis** — i.e. with
  the `recCall` already eliminated to a literal `rowSymTreeA` tree (via
  `allNatLtElim` of the hypothesis at any qubit).  This is the precise frontier:
  a recursion-free parity statement on the resolved tree, where `boolCases` on the
  (purely arithmetic) cell guards is now legal.

### Partial progress landed (axiom-clean `[propext, Quot.sound]`, sorry-free)

The **off-support** half of each normalizer is now factored out into two
reusable, sorry-free lemmas:

* `logicalXOffColumnLocalCommutes` — at every qubit where the `logicalX` column
  guard `q mod d = 0` is `false`, the `logicalX` entry is `I`, so it locally
  commutes with *any* row entry there (via `localCommutesOfRightI` + the
  `else`-branch entry peel).  No parity content, no `recCall`, no oracle.
* `logicalZOffRowLocalCommutes` — the row/column transpose for `logicalZ`
  (`q / d = 0`).

These discharge the entire all-others premise *off* the relevant logical line,
for every recursion depth.

### Both normalizers fully closed (axiom-clean, sorry-free)

The **column-0 (resp. top-row) even-parity argument** is now fully mechanized for
every `D`: classify the bound stabilizer index `k = var 0` by its (purely
arithmetic) cell guards and supply, via `commutesOfTwoAnti`, the two
anticommuting qubits as functions of `k` (`commutesOfPointwise` for the
commuting classes).  `xNormCommuteSym` (`logicalX`, column 0) and its row/column
transpose `zNormCommuteSym` (`logicalZ`, row 0) discharge the per-`k` commutation
goal completely; `xNormScaffold := xNormCommuteSym` and
`zNormScaffold := zNormCommuteSym`.  Axiom-clean
`[propext, Classical.choice, Quot.sound]`, sorry-free.
-/
