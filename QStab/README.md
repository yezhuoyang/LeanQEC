# Formalization and verification of QStab

Lean 4 formalization of the operational semantics and invariant-based fault-tolerance proofs for stabilizer code syndrome extraction.

## Structure

| File | Description |
|---|---|
| `PauliOps.lean` | `ErrorVec` (n-qubit Pauli vectors), weight, parity, update |
| `Defs.lean` | `QECParams` (code parameters), `Coord` (measurement schedule), `next`/`prev` |
| `State.lean` | Program state σ (13 fields), `ExecState` (active/done/error), initial state |
| `BackAction.lean` | Back-action error set B¹(T_s), weight bound axiom |
| `Step.lean` | Small-step transition relation (Type0/I/II/III errors, measurement, halt, error) |
| `MultiStep.lean` | Reflexive-transitive closure, execution runs |
| `Invariant.lean` | Generic `Invariant` structure (predicate + init + preservation) |
| `Invariants/ErrorCount.lean` | λ₀ + λ₁ + λ₂ + λ₃ = C_budget − C |
| `Invariants/ZeroBudget.lean` | C = 0 is absorbing |
| `Invariants/RegisterInit.lean` | Unvisited classical registers are zero |
| `Invariants/ConstantErrorFlow.lean` | Error flow is constant at a fixed budget level |
| `Invariants/SyndromeCorrectness.lean` | Inferred syndrome matches error parity when budget exhausted |
| `Invariants/ErrorPropagation.lean` | λ₀ + λ₁ + r·λ₂ + λ₃ ≥ λ_E |
| `Invariants/RoundInconsistency.lean` | C_budget − C ≥ RI/2 |
| `Theorem.lean` | Main fault-tolerance theorem combining all invariants |

