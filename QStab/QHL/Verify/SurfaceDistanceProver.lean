import QStab.QHL.Verify.SurfaceRowCharacterizationSym
import QStab.QHL.Verify.SurfaceNormalizers
import QStab.QHL.Verify.SurfaceRowsCommute
import QStab.QHL.Verify.SurfaceBridges

/-!
# Surface-code distance — PROVER DELIVERABLE (fill in the gaps)

**STRICT-PURITY MODE.**  The distance proof must be a *pure derivation tree* built
only from the object-logic rules — the evaluator may appear only inside the
(already-proved) soundness lemmas, never in the distance proof.  Concretely, the
four witness fields are now **derivation trees** in `PureFamilyDeriv` /
`PureForallStabDeriv` (see `PureDeriv.lean`) plus their definedness
side-conditions — *not* `Formula.check = true` Booleans.

You (the prover) edit **only** this file, plus any *new* helper files you create.
You must:

  * replace every `sorry` in `proverWitness` with a genuine, fully general
    (`∀ D : OddSurfaceDistance`) derivation/proof;
  * keep the names/signatures of `proverWitness` and
    `surface_code_has_distance_d_for_all_odd_d` exactly as written.

You must **NOT**:

  * edit the contract, the audit, the kernel, `CodeSurface` definitions, or
    `PureDeriv.lean` / `CodeEvalHelpers.lean` (all FROZEN/trusted);
  * use `sorry`/`admit`/`native_decide`/any `axiom` (the audit rejects
    `sorryAx` / `Lean.ofReduceBool` / custom axioms);
  * use `Formula.check`, `Formula.eval`-as-the-distance-proof, `checkedBoundFree`,
    or `deriveTrue?` to establish a distance fact.  (The *derivation tree* carries
    the distance content; the evaluator only legitimately appears when discharging
    a **definedness** side-condition `…DefinedObligations`.)

## The building blocks (all proved, in `PureDeriv.lean`)

  * `PureFamilyDeriv cb fuel A` — pure tree of a closed `SFormula 0` fact `A`:
      - `.core (d : SFormula.Deriv [] A)` — any generic logic-rule derivation;
      - `.recUnfold n d k` — the recursion rule: proves
        `eqStabUpTo n (recCall d k) (codeSubst cb d k)` (unfold one level);
      - `.cut1..4` — compose with a generic `SFormula.Deriv [..] B`.
  * `PureForallStabDeriv cb fuel Q` — the `∀E` wrapper (`.intro body`).
  * `…DefinedObligations` — the side-conditions; soundness is `…sound`.

## Strategy

  * `lowerBound`: reuse the existing generic cut-commutation / parity / counting
    `SFormula.Deriv` derivations via `.core`; where the recursive Surface
    stabilizers appear, rewrite `recCall` to `codeSubst` with `.recUnfold` and
    descend, `cut`ting the pieces together.  Wrap with `.intro`.
  * `codeLevel`: a `PureFamilyDeriv` of `codeLevelSF D` — unfold the recursive
    stabilizers via `.recUnfold` down to base entries (handled by the generic
    `stabAtClosedIteLamEq*` rules in `.core`), then the `eqStab`/commute/weight
    algebra rules.  Induct on `D.index` to assemble the `O(d)`-deep tree.
  * `codeLevelDefined` / `lowerDefined`: discharge the definedness side-conditions
    (these *may* reason about `Term.eval` — they are about definedness, not the
    distance fact).  `recUnfold`'s obligation is `∃ sa, recCall@fuel = some sa ∧
    ∀ q<n, ∃ p, sa q = some p`, dischargeable since `fuel = …+2` covers the
    recursion depth for all `d`.
-/

namespace QHL.CodeLang.Surface.Verify.Prover

open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab
open QHL.CodeLang.Surface.Verify

/-- The parametric witness — **pure derivation trees**.  Every field is currently
`sorry`; each is a `∀ D` statement, so it cannot be closed at concrete distances. -/
def proverWitness : ParametricSurfaceWitness where
  codeLevel := fun D =>
    -- GOAL: ∀ D, PureFamilyDeriv code.body (D.distance+2) (codeLevelSF D)
    -- Assembled from three generated-row facts via the already-proved
    -- `codeLevelPureFromGeneratedRows`.  The three inputs are the parametric
    -- consumers: `rows` (pairwise row commutation), `xNorm`/`zNorm` (the two
    -- logical operators normalise every generated row).  These are the
    -- genuinely recursive, ∀-D obligations.
    -- `xNorm`/`zNorm` are now the PROVEN symbolic normalizers (`xNormScaffold` /
    -- `zNormScaffold`, axiom-clean ∀-D).  `rows` is wired to the real
    -- `rowsCommuteSym` (spine + same-type half proven; the two different-type
    -- overlap branches are its remaining gaps).  So `codeLevel`'s only residual is
    -- the `rows` overlap dispatcher.
    codeLevelPureFromGeneratedRows D
      (rows := rowsCommuteSym D) (xNorm := xNormScaffold D) (zNorm := zNormScaffold D)
  codeLevelDefined := by
    -- GOAL: ∀ D E, (codeLevel D).DefinedObligations E
    -- Discharge the tree's definedness side-conditions (recUnfold nodes need the
    -- recCall defined up to n; core nodes need the SFormula.Deriv definedness).
    sorry
  lowerBound := fun D =>
    -- GOAL: ∀ D, PureForallStabDeriv code.body (bridgeProofFuel D)
    --                                (distanceLowerBoundForallStabF D)
    -- Assembled from the six closed Surface leaves via the already-proved
    -- `PureLowerClosedLeaves.lowerBound`.  Four leaves are fully built
    -- (`rowStripRangePure`/`colStripRangePure`/`rowCutTelescopingPure`/
    -- `colCutTelescopingPure`); the two OPEN ones are the generated-row bridge
    -- equalities `rowBridgeGenerated`/`colBridgeGenerated`.
    PureLowerClosedLeaves.lowerBound
      { rowBridgeGenerated := rowBridgeGeneratedPure D
        rowStripIndexInRange := rowStripRangePure D
        rowCutTelescoping := rowCutTelescopingPure D
        colBridgeGenerated := colBridgeGeneratedPure D
        colStripIndexInRange := colStripRangePure D
        colCutTelescoping := colCutTelescopingPure D }
  lowerDefined := by
    -- GOAL: ∀ D E n, width.eval … = some n → TotalUpTo n E →
    --                  (lowerBound D).DefinedObligations E
    sorry

/-- **The final, parametric, faithful distance theorem.**

For *every* odd distance `d = 2*m + 3`, the recursively-defined Surface code has
code distance exactly `d` (faithful-semantics statement; see
`SurfaceDistanceSpec`), established as a **pure derivation tree**.  Once
`proverWitness` is `sorry`-free this theorem is axiom-clean and
`SurfaceDistanceAudit.lean` passes. -/
theorem surface_code_has_distance_d_for_all_odd_d :
    ∀ (D : OddSurfaceDistance), SurfaceDistanceSpec D :=
  accept proverWitness

end QHL.CodeLang.Surface.Verify.Prover
