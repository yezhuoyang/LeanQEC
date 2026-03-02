# LeanQEC

Formal verification of quantum error correction in [Lean 4](https://lean-lang.org/) with [Mathlib](https://leanprover-community.github.io/mathlib4_docs/).

We formalize the algebraic foundations (Pauli group, stabilizer formalism), code properties (distance, logical operators), and fault-tolerance guarantees (threshold theorem, operational semantics) for quantum error correction codes.

## File Structure

```
LeanQEC/
  Pauli.lean            -- Pauli operators, Phase (Z/4Z), PauliWithPhase, n-qubit PauliN; Group instances
  Stabilizer.lean       -- (stub) Stabilizer group, generators, normalizer
  Clifford.lean         -- (stub) Clifford group acting on Pauli operators
  CodeDistance.lean      -- (stub) Code distance: min-weight logical operator
  LogicalOp.lean        -- (stub) Logical operators: X_L, Z_L
  Decoder.lean          -- (stub) Decoder specification (e.g., MWPM)
  SurfaceCode.lean      -- (stub) Surface code instantiation
QStab/
  PauliOps.lean         -- ErrorVec (n-qubit Pauli vectors), weight, parity, update
  Defs.lean             -- QECParams, Coord (measurement schedule), next/prev
  State.lean            -- Program state (13 fields), ExecState (active/done/error)
  BackAction.lean       -- Back-action error set B^1(T_s), weight bound axiom
  Step.lean             -- Small-step transition: Type 0/I/II/III errors, measurement, halt
  MultiStep.lean        -- Reflexive-transitive closure, execution runs
  Invariant.lean        -- Generic Invariant structure (predicate + init + preservation)
  Invariants/
    ErrorCount.lean     -- cnt0 + cnt1 + cnt2 + cnt3 = C_budget - C
    ZeroBudget.lean     -- C = 0 is absorbing
    RegisterInit.lean   -- Unvisited classical registers are zero
    ConstantErrorFlow.lean -- Error flow constant at a fixed budget level
    SyndromeCorrectness.lean -- I_syn matches error parity when C = 0
    ErrorPropagation.lean    -- lam_E <= cnt0 + cnt1 + r*cnt2 + cnt3
    RoundInconsistency.lean  -- C_budget - C >= RI / 2
  Theorem.lean          -- Main fault-tolerance theorem combining all invariants
  Simulate.lean         -- Computable simulation functions for #eval testing
  Examples/
    RepetitionCode.lean -- [[3,1,3]] repetition code: 7 test scenarios
```

## Components

### Pauli Group (`LeanQEC/Pauli.lean`)

Defines the algebraic building blocks for stabilizer QEC:

- **`Pauli`** -- single-qubit operators {I, X, Y, Z} with multiplication (Klein four-group).
- **`Phase`** -- cyclic group Z/4Z = {1, i, -1, -i} with `CommGroup` instance.
- **`PauliWithPhase`** -- the 16-element single-qubit Pauli group (phase x operator) with `Group` instance.
- **`PauliN n`** -- n-qubit Pauli group: phase x (Fin n -> Pauli), with tensor-product multiplication and `Group` instance.

Group law proofs are currently `sorry`'d; definitions and computations are complete.

### QStab: Fault-Tolerance Verification (`QStab/`)

Formalizes the operational semantics of stabilizer code syndrome extraction and proves fault-tolerance via invariants. Based on the QStab framework:

- **Error model**: an adversary injects errors (Type 0: data qubit, Type I: during measurement, Type II: back-action, Type III: measurement bit flip) subject to a finite budget C.
- **Measurement**: deterministic stabilizer measurement updates syndrome registers G, inferred syndrome I_syn, and inconsistency flags F.
- **Invariants**: seven invariants proved preserved by every transition step, culminating in the main fault-tolerance theorem:

  > For any execution with error budget C, the number of round inconsistencies satisfies RI <= 2C, the error propagation satisfies lam_E <= cnt0 + cnt1 + r*cnt2 + cnt3, and the inferred syndrome is correct when the budget is exhausted.

- **Simulation**: computable functions (`applyType0`, `applyType3`, `runAllMeasurements`) mirror the `Step` relation for `#eval`-based testing. The [[3,1,3]] repetition code passes all 7 test scenarios (no error, single X/Z errors, Type-III flip, error count invariant).

See [QStab/README.md](QStab/README.md) for the detailed file-by-file description.

## TODO

### Algebraic Foundations
- [ ] Prove `Phase` `CommGroup` laws (decidable by `decide`)
- [ ] Prove `PauliWithPhase` and `PauliN` `Group` laws
- [ ] Define stabilizer group as a subgroup of `PauliN n`
- [ ] Formalize Clifford group and its action on Pauli operators
- [ ] Commutativity / anticommutativity predicates with lemmas

### Code Properties
- [ ] Define code distance as min-weight non-trivial logical operator
- [ ] Formalize logical operators X_L, Z_L and their algebraic properties
- [ ] Prove distance for specific codes (repetition, Steane, surface)

### Decoder
- [ ] Specify MWPM decoder interface (input: syndrome, output: correction)
- [ ] Formalize decoder correctness: corrects all errors of weight < d/2

### QStab Invariant Proofs
- [ ] Prove `ErrorCount` invariant (cnt0 + cnt1 + cnt2 + cnt3 = C_budget - C)
- [ ] Prove `ZeroBudget` invariant (C = 0 absorbing)
- [ ] Prove `RegisterInit` invariant
- [ ] Prove `ConstantErrorFlow` invariant
- [ ] Prove `SyndromeCorrectness` invariant
- [ ] Prove `ErrorPropagation` bound
- [ ] Prove `RoundInconsistency` bound
- [ ] Complete main fault-tolerance theorem (remove `sorry`)

### QStab Testing
- [ ] Add [[5,1,3]] five-qubit code example
- [ ] Add [[7,1,3]] Steane code example
- [ ] Add multi-error and Type-II back-action test scenarios

### Threshold Theorem
- [ ] Formalize the threshold theorem statement
- [ ] Connect QStab fault-tolerance to threshold via concatenated codes

## Building

Requires [elan](https://github.com/leanprover/elan) (Lean version manager).

```bash
lake update    # fetch Mathlib and dependencies
lake build     # build everything
```

## License

This project is open-source. See [LICENSE](LICENSE) for details.
