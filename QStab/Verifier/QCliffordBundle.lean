import QStab.Verifier
import QStab.QClifford.Gate

/-!
# QCliffordFTBundle: gate-level fault-tolerance certificate (Phase 3 sketch)

This is the **target** language of the TAL-style bundle compiler
(`compileBundle : QStabFTBundle → QCliffordFTBundle`). A
`QCliffordFTBundle` is the gate-level analog of `QStabFTBundle`:

  * Source (QStab): scheme-agnostic, single `Step` relation,
    invariant on `State P`.
  * Target (QClifford): concrete gate-level circuit, per-gate
    Pauli propagation, invariant as a per-gate annotation.

The shape mirrors `QStabFTBundle` 1-to-1:

```
QCliffordFTBundle = ⟨nq, circuit, failure, gateInv, static, bridge⟩
```

## Status

**Phase 3 sketch (iter 10)** — structure only, no `verifyQClifford`
or soundness theorem yet. Concrete annotation type and per-gate
preservation rule are TODOs for iters 11+.

## Design intent

- `failure : ErrorVec nq → Prop` — what counts as failure on the
  final accumulated error after the circuit's Pauli propagation.
- `gateInv : (i : Fin (circuit.length + 1)) → ErrorVec nq → Prop` —
  per-gate-location annotation. Index `i = 0` is pre-circuit
  (identity error), index `i = circuit.length` is post-circuit.
- `static : Bool` — decidable side-condition (analog of the source-
  side `static`).
- `bridge` — ties `gateInv` and `static` to `¬ failure` on the
  post-circuit accumulated error.

The verifier walks the circuit once, checking each adjacent pair
`(gateInv i, gateInv (i+1))` against the gate's Pauli-propagation
rule. Linear in `circuit.length` — the TAL "per-instruction
typing rule" pattern.

## Compilation target

`compileBundle : QStabFTBundle → QCliffordFTBundle` (Phase 4)
will, given a source bundle:
1. Generate the gate-level circuit from `P : QECParams` via the
   verified compiler (`QStab.Compiler`).
2. Lift the source invariant `inv : Invariant P` to per-gate
   annotations.
3. Generate the per-gate preservation proofs from the source
   `inv.preservation`.
4. Preserve `static` and re-derive `bridge` at the gate level.
-/

namespace QStab.Verifier

open QStab QStab.QClifford

/-- Gate-level fault-tolerance certificate (Phase 3 sketch — to be
    refined as we work out the per-gate annotation discipline). -/
structure QCliffordFTBundle where
  /-- Number of qubits the circuit operates on. -/
  nq      : Nat
  /-- The gate-level circuit. -/
  circuit : Circuit nq
  /-- Failure predicate on the final accumulated error. -/
  failure : ErrorVec nq → Prop
  /-- Per-gate-location annotation. `gateInv 0` holds at the
      circuit's input (identity error); `gateInv circuit.length`
      holds after the final gate. -/
  gateInv : ∀ (i : Fin (circuit.length + 1)), ErrorVec nq → Prop
  /-- Decidable side-condition. -/
  static  : Bool
  /-- The bridge: static + post-circuit invariant ⇒ no failure on
      the final accumulated error.

      (Per-gate preservation will be a separate field once we settle
      the gate-level Pauli propagation API in iters 11+.) -/
  bridge  : static = true →
            ∀ E : ErrorVec nq,
              gateInv ⟨circuit.length, Nat.lt_succ_self _⟩ E →
              ¬ failure E

/-- The verifier (Phase 3 sketch — currently just returns `static`).
    A full per-gate check pass will be added once the annotation
    preservation rule is defined. -/
def verifyQClifford (b : QCliffordFTBundle) : Bool := b.static

/-- Trivial bundle: no qubits, empty circuit, no failure. Sanity
    check that the structure compiles. -/
def trivialQCliffordBundle : QCliffordFTBundle where
  nq      := 0
  circuit := []
  failure := fun _ => False
  gateInv := fun _ _ => True
  static  := true
  bridge  := fun _ _ _ hf => hf

end QStab.Verifier
