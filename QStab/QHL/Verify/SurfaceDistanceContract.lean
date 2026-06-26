import QStab.QHL.CodeSurface
import QStab.QHL.Verify.PureDeriv

/-!
# Surface-code distance — cheat-proof, parametric verification contract

**THIS FILE IS THE TRUSTED VERIFICATION BOUNDARY.**  It must not be edited while
filling in the proof.  The prover supplies a `ParametricSurfaceWitness` (see
`SurfaceDistanceProver.lean`); neither this contract, the audit, nor the kernel
(`CodeLang` / `CodeStabBinder` / `CodeRules` / `CodeDerivation` / `CodeLogic` /
`CodeAlgebra` / `CodeNatArithmetic` / `PureDeriv`) nor the surface *definitions*
in `CodeSurface.lean` may change.

## What this contract guarantees

It pins the surface-code distance claim to a single **parametric** `Prop`,
`SurfaceDistanceSpec D`, quantified by `accept` over *every* odd distance
`d = D.distance = 2*D.index + 3`.  The specification is phrased entirely through
the kernel's executable semantics, which an independent audit verified to be a
*faithful* model of Pauli stabilizers:

  * `weightUpTo`  — genuine Hamming weight (proved equal to support cardinality),
  * `parityUpTo`  — genuine symplectic anti-commutation parity,
  * `none`-propagation makes an undefined entry *fail* rather than masking support.

## How `accept` discharges the spec — pure derivation trees only

`accept` reduces the spec to the witness by routing **only** through the
*structural* soundness theorems of the **pure**, evaluator-free derivation
system in `PureDeriv.lean`:

  * `PureFamilyDeriv.sound`        — structural induction on the derivation tree;
    every closed leaf is justified by a soundness lemma (the recursion-unfold
    rule `recUnfold` by the semantic lemma `recUnfold_sound`), never by running
    the evaluator at proof time;
  * `PureForallStabDeriv.sound`    — the `∀ E` wrapper over the above.

There is **no** appeal to the executable checker `Formula.check`, to
`Formula.check_sound`, or to the evaluation-based leaf `checkedBoundFree`.  The
witness obligations are *derivation trees plus their definedness side-conditions*
— pure logic objects — not `check = true` Boolean facts produced by executing the
evaluator.  `accept` performs no per-distance computation and adds no axiom.

## Why it cannot be cheated

* The conclusion is a `∀ D` `Prop`, so it can **not** be produced by `#eval`,
  `decide`, `native_decide`, or any `Option`-valued search — those yield `Bool`
  facts at *concrete* distances, not a proof of the universally-quantified `Prop`.
* The witness obligations are themselves `∀ D` statements over `code.body`, so
  they likewise cannot be discharged at finitely many distances.
* The companion audit (`SurfaceDistanceAudit.lean`) rejects any dependency on
  `sorryAx` (unproved / `sorry`), `Lean.ofReduceBool` (`native_decide`), or any
  custom `axiom`.

The only way to complete the proof is therefore a real, fully general, `∀ d`
Lean argument about the recursively-defined Surface AST, packaged as a pure
derivation tree.
-/

namespace QHL.CodeLang.Surface.Verify

open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

/-! ## An `E`-free `SFormula` encoding of closed code-level `Formula`s

`codeLevelSF` re-expresses the closed code-level facts (`surfaceCodeLevelOddF`)
in the stabilizer-binder syntax `SFormula 0`, with every term leaf wrapped in
`SC.closed`.  Because the wrapper carries an ordinary closed `Term`, the encoding
mentions **no** bound stabilizer variable; the soundness bridge `codeLevelSF_eval`
shows its `SFormula.eval … E` is independent of `E` and agrees on the nose with
the faithful `Formula.eval` of the original closed assertion.

The generic encoder `closedSF` is the structural inverse of `SFormula.instantiate`
restricted to all-`SC.closed` leaves: it is syntactically bound-free and
`instantiate E (closedSF F) = F` for every `E`, so the kernel's already-proved
`SFormula.eval_boundFree_instantiate` collapses its evaluation to `Formula.eval`. -/

/-- Encode a closed `Formula arity` as an `E`-free `SFormula arity`, wrapping each
    term leaf with `SC.closed` and recursing structurally under the finite
    natural binders.  No constructor mentions the distinguished stabilizer
    variable, so the result is syntactically bound-free. -/
def closedSF {arity : Nat} : Formula arity → SFormula arity
  | .top => .top
  | .bot => .bot
  | .eqNat a b => .eqNat (SC.closed a) (SC.closed b)
  | .eqBool a b => .eqBool (SC.closed a) (SC.closed b)
  | .eqPauli a b => .eqPauli (SC.closed a) (SC.closed b)
  | .eqStabUpTo n a b => .eqStabUpTo (SC.closed n) (SC.closed a) (SC.closed b)
  | .commutesUpTo n a b => .commutesUpTo (SC.closed n) (SC.closed a) (SC.closed b)
  | .weightLe n a w => .weightLe (SC.closed n) (SC.closed a) (SC.closed w)
  | .and A B => .and (closedSF A) (closedSF B)
  | .or A B => .or (closedSF A) (closedSF B)
  | .not A => .not (closedSF A)
  | .imp A B => .imp (closedSF A) (closedSF B)
  | .applyNat witness A => .applyNat (SC.closed witness) (closedSF A)
  | .allNatLt n A => .allNatLt (SC.closed n) (closedSF A)
  | .existsNatLt n A => .existsNatLt (SC.closed n) (closedSF A)

/-- Structural predicate: a `Formula` uses no explicit `applyNat` beta-redex.
The kernel's `SFormula.boundFree` deliberately excludes `applyNat` (its beta
reasoning lives in the symbolic derivation layer), so `closedSF` can only be
proved bound-free on this fragment.  The code-level facts inhabit it: they are
built from `and` / `not` / `commutesUpTo` / `weightLe` / `allNatLt` only. -/
def applyNatFree {arity : Nat} : Formula arity → Prop
  | .top => True
  | .bot => True
  | .eqNat _ _ => True
  | .eqBool _ _ => True
  | .eqPauli _ _ => True
  | .eqStabUpTo _ _ _ => True
  | .commutesUpTo _ _ _ => True
  | .weightLe _ _ _ => True
  | .and A B => applyNatFree A ∧ applyNatFree B
  | .or A B => applyNatFree A ∧ applyNatFree B
  | .not A => applyNatFree A
  | .imp A B => applyNatFree A ∧ applyNatFree B
  | .applyNat _ _ => False
  | .allNatLt _ A => applyNatFree A
  | .existsNatLt _ A => applyNatFree A

/-- `closedSF F` mentions no bound stabilizer variable, on the `applyNat`-free
    fragment.  (`SFormula.boundFree` excludes `applyNat`, so the hypothesis is
    necessary and not a weakening: the code-level facts satisfy it.) -/
theorem closedSF_boundFree {arity : Nat} (F : Formula arity) (hF : applyNatFree F) :
    (closedSF F).boundFree = true := by
  induction F with
  | top => rfl
  | bot => rfl
  | eqNat a b => rfl
  | eqBool a b => rfl
  | eqPauli a b => rfl
  | eqStabUpTo n a b => rfl
  | commutesUpTo n a b => rfl
  | weightLe n a w => rfl
  | and A B ihA ihB => simp [closedSF, SFormula.boundFree, ihA hF.1, ihB hF.2]
  | or A B ihA ihB => simp [closedSF, SFormula.boundFree, ihA hF.1, ihB hF.2]
  | not A ihA => simp [closedSF, SFormula.boundFree, ihA hF]
  | imp A B ihA ihB => simp [closedSF, SFormula.boundFree, ihA hF.1, ihB hF.2]
  | applyNat witness A _ => exact absurd hF (by simp [applyNatFree])
  | allNatLt n A ih =>
      simp [closedSF, SFormula.boundFree, SC.closed, STerm.boundFree, ih hF]
  | existsNatLt n A ih =>
      simp [closedSF, SFormula.boundFree, SC.closed, STerm.boundFree, ih hF]

/-- Instantiating the (absent) bound stabilizer in `closedSF F` by any closed
    term returns the original `Formula F`. -/
theorem closedSF_instantiate {arity : Nat} (E : Term arity .stab) (F : Formula arity) :
    (closedSF F).instantiate E = F := by
  induction F with
  | top => rfl
  | bot => rfl
  | eqNat a b => rfl
  | eqBool a b => rfl
  | eqPauli a b => rfl
  | eqStabUpTo n a b => rfl
  | commutesUpTo n a b => rfl
  | weightLe n a w => rfl
  | and A B ihA ihB => simp [closedSF, SFormula.instantiate, ihA, ihB]
  | or A B ihA ihB => simp [closedSF, SFormula.instantiate, ihA, ihB]
  | not A ihA => simp [closedSF, SFormula.instantiate, ihA]
  | imp A B ihA ihB => simp [closedSF, SFormula.instantiate, ihA, ihB]
  | applyNat witness A ih => simp [closedSF, SFormula.instantiate, SC.closed, STerm.instantiate, ih]
  | allNatLt n A ih => simp [closedSF, SFormula.instantiate, SC.closed, STerm.instantiate, ih]
  | existsNatLt n A ih => simp [closedSF, SFormula.instantiate, SC.closed, STerm.instantiate, ih]

/-- The code-level facts use no explicit `applyNat` beta-redex: they are built
from `and` / `not` / `commutesUpTo` / `weightLe` / `allNatLt` only.  This is the
side-condition under which `closedSF` is bound-free. -/
theorem surfaceCodeLevelOddF_applyNatFree (D : OddSurfaceDistance) :
    applyNatFree (surfaceCodeLevelOddF D) := by
  simp only [surfaceCodeLevelOddF, surfaceCodeLevelF, rowsCommuteF, logicalPairF,
    logicalWeightsF, weightExactF, Formula.codeRowsCommuteUpTo,
    Formula.logicalPairCandidateUpTo, Formula.normalizesCodeUpTo,
    Formula.anticommutesUpTo, applyNatFree]
  trivial

/-- **The `E`-free code-level encoding.**  Mirrors `surfaceCodeLevelOddF D`
(which is `.and (rowsCommuteF d) (.and (logicalPairF d) (logicalWeightsF d))`,
all closed `Formula`s) in the stabilizer-binder syntax with `SC.closed`-wrapped
closed terms, so it contains **no** bound stabilizer `E`. -/
def codeLevelSF (D : OddSurfaceDistance) : SFormula 0 :=
  closedSF (surfaceCodeLevelOddF D)

/-- **Bridge.**  The `E`-free encoding evaluates (independently of `E`) to exactly
the faithful `Formula.eval` of the original closed code-level assertion.  Routed
through the kernel's `SFormula.eval_boundFree_instantiate` together with the two
purely-structural facts `closedSF_boundFree` / `closedSF_instantiate`. -/
theorem codeLevelSF_eval (D : OddSurfaceDistance) (E : PartialStabilizer) :
    (codeLevelSF D).eval Surface.code.body (D.distance + 2) Env.empty E =
      Formula.eval Surface.code.body (D.distance + 2) (surfaceCodeLevelOddF D) Env.empty := by
  unfold codeLevelSF
  rw [SFormula.eval_boundFree_instantiate (closedSF (surfaceCodeLevelOddF D))
        (closedSF_boundFree _ (surfaceCodeLevelOddF_applyNatFree D))
        Surface.code.body (D.distance + 2) Env.empty E
        (Formula.closedStabilizer (.pauliLit Pauli.I)),
      closedSF_instantiate]

/-- **The faithful, parametric distance specification** for the recursive Surface
AST `Surface.code.body` at odd distance `d = D.distance`.

* `code-level` (first conjunct): the generated stabilizers commute, the logical
  operators `logicalX`/`logicalZ` normalize the stabilizer group and
  anti-commute with each other, and both have weight **exactly** `d`.  The
  exact-weight half is the distance **upper bound** (a weight-`d` logical
  exists).  Read off the faithful evaluator `Formula.eval` over `code.body`.

* `lower-bound` (second conjunct): for **every** Pauli string `E` total on the
  `d*d` physical qubits, if `E` normalizes all stabilizers and is a nontrivial
  logical (anti-commutes with `logicalZ`, resp. `logicalX`), then `E` has weight
  `≥ d`.  This is the `ForallStabFormula.holds` semantics — a genuine `∀ E`
  statement, not a check at a particular `E`.

Together they state that the recursive Surface code has code distance exactly
`d`. -/
def SurfaceDistanceSpec (D : OddSurfaceDistance) : Prop :=
  Formula.eval Surface.code.body (D.distance + 2)
      (surfaceCodeLevelOddF D) Env.empty = some true
  ∧
  (distanceLowerBoundForallStabF D).holds
      Surface.code.body (bridgeProofFuel D) Env.empty

/-- **The obligations the prover must discharge.**  Every field is quantified
over *all* odd distances `D : OddSurfaceDistance` (recall
`D.distance = 2*D.index + 3`), so none of them can be met by `#eval`/`decide` at
concrete distances.  The obligations are **pure derivation trees** (plus their
definedness side-conditions) — logic objects, not `Formula.check = true` Booleans
obtained by running the evaluator. -/
structure ParametricSurfaceWitness where
  /-- A **pure** family derivation of the `E`-free code-level facts at **every**
      distance.  Its only non-logical leaf is the recursion-unfold rule, whose
      soundness is the semantic lemma `recUnfold_sound`; no evaluator leaf. -/
  codeLevel :
    ∀ (D : OddSurfaceDistance),
      PureFamilyDeriv Surface.code.body (D.distance + 2) (codeLevelSF D)
  /-- The code-level derivation's definedness side-conditions hold at **every**
      distance (and for **every** stabilizer slot `E`, on which the closed facts
      do not actually depend). -/
  codeLevelDefined :
    ∀ (D : OddSurfaceDistance) (E : PartialStabilizer),
      (codeLevel D).DefinedObligations E
  /-- A **pure** universal-stabilizer derivation of the open-`E` lower-bound
      family at **every** distance, again with structural soundness only. -/
  lowerBound :
    ∀ (D : OddSurfaceDistance),
      PureForallStabDeriv Surface.code.body (bridgeProofFuel D)
        (distanceLowerBoundForallStabF D)
  /-- The lower-bound derivation's definedness side-conditions hold at **every**
      distance and for **every** total stabilizer `E`. -/
  lowerDefined :
    ∀ (D : OddSurfaceDistance) (E : PartialStabilizer) (n : Nat),
      (distanceLowerBoundForallStabF D).width.eval
          Surface.code.body (bridgeProofFuel D) Env.empty E = some n →
        TotalUpTo n E →
          (lowerBound D).DefinedObligations E

/-- **Acceptance theorem.**  Given the parametric witness, the recursive Surface
code satisfies the faithful distance specification at *every* odd distance
`d = 2*m + 3`.

Both conjuncts are discharged by the **structural** soundness of the pure,
evaluator-free derivation system:

* code-level: `PureFamilyDeriv.sound` produces `(codeLevelSF D).eval … E = some
  true`; the `E`-free bridge `codeLevelSF_eval` rewrites it to the spec's
  `Formula.eval … = some true` (the dummy slot `E` is irrelevant, the encoding
  being bound-free);
* lower-bound: `PureForallStabDeriv.sound` yields the `holds` directly.

It introduces no new axiom, runs no per-distance computation, and never touches
`Formula.check` / `Formula.check_sound` / `checkedBoundFree`. -/
theorem accept (W : ParametricSurfaceWitness) :
    ∀ (D : OddSurfaceDistance), SurfaceDistanceSpec D := by
  intro D
  refine ⟨?_, ?_⟩
  · -- A dummy total stabilizer slot; the code-level encoding is `E`-free, so the
    -- bridge eval below is independent of this choice.
    have hEval :=
      PureFamilyDeriv.sound (W.codeLevel D) (fun _ => some Pauli.I)
        (W.codeLevelDefined D (fun _ => some Pauli.I))
    rw [codeLevelSF_eval] at hEval
    exact hEval
  · exact PureForallStabDeriv.sound (W.lowerBound D) (W.lowerDefined D)

end QHL.CodeLang.Surface.Verify
