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

/-- Gate-level fault-tolerance certificate.

    Mirrors `QStabFTBundle` exactly but at the QClifford layer:
    the state is `ErrorState nq` (per-qubit Pauli + measurement
    flips) instead of `State P`, and the dynamic invariant is given
    by `invHolds` (a single predicate preserved by every gate
    transition, analog of `Invariant.holds`).

    The `preservation` field is the TAL-style per-instruction typing
    rule: for any gate `g` and pre-state `es` satisfying `invHolds`,
    the post-state `propagateGate g es` also satisfies `invHolds`.
    The verifier can then walk the circuit and inductively conclude
    that `invHolds` survives to the post-circuit state. -/
structure QCliffordFTBundle where
  /-- Number of qubits the circuit operates on. -/
  nq      : Nat
  /-- The gate-level circuit. -/
  circuit : Circuit nq
  /-- Failure predicate on the final accumulated error state. -/
  failure : ErrorState nq → Prop
  /-- Dynamic gate-level invariant (single predicate, preserved by
      every Pauli-propagation step). -/
  invHolds : ErrorState nq → Prop
  /-- Holds for the initial clean error state. -/
  init    : invHolds (ErrorState.clean nq)
  /-- Preserved by every gate's Pauli propagation. -/
  preservation : ∀ (g : Gate nq) (es : ErrorState nq),
                   invHolds es → invHolds (propagateGate g es)
  /-- Decidable side-condition. -/
  static  : Bool
  /-- The bridge: static + invariant on the final state ⇒ no failure. -/
  bridge  : static = true →
            ∀ es : ErrorState nq, invHolds es → ¬ failure es

/-- The verifier currently returns `static`. A full per-gate walk is
    unnecessary in the bundle's metatheory because `preservation` is
    a structural field — its mere existence as a Lean term proves the
    per-gate check. (A `walk` function returning `Bool` will be added
    for the *standalone tool* in Phase 5; it's just for ergonomics,
    not metatheory.) -/
def verifyQClifford (b : QCliffordFTBundle) : Bool := b.static

/-- The invariant survives the entire circuit: if `b.invHolds` holds
    at the start, it holds after propagating through any prefix of
    the circuit. This is the inductive lift of `preservation` to
    multi-gate sequences. -/
theorem QCliffordFTBundle.invHolds_propagate (b : QCliffordFTBundle)
    (gs : Circuit b.nq) (es : ErrorState b.nq) :
    b.invHolds es → b.invHolds (propagateCircuit gs es) := by
  induction gs generalizing es with
  | nil => intro h; exact h
  | cons g gs ih => intro h; exact ih _ (b.preservation g es h)

/-- **Generic soundness theorem** at the QClifford layer. If the
    verifier accepts the bundle, then for any prefix of the circuit
    starting from the clean state, the failure predicate fails on
    the propagated error state. -/
theorem verifyQClifford_sound (b : QCliffordFTBundle)
    (h : verifyQClifford b = true) :
    ∀ gs : Circuit b.nq,
      ¬ b.failure (propagateCircuit gs (ErrorState.clean b.nq)) := by
  intro gs
  have hinv : b.invHolds (propagateCircuit gs (ErrorState.clean b.nq)) :=
    b.invHolds_propagate gs _ b.init
  exact b.bridge h _ hinv

/-- Trivial bundle: no qubits, empty circuit, no failure. Sanity
    check that the structure compiles. -/
def trivialQCliffordBundle : QCliffordFTBundle where
  nq      := 0
  circuit := []
  failure := fun _ => False
  invHolds := fun _ => True
  init    := trivial
  preservation := fun _ _ _ => trivial
  static  := true
  bridge  := fun _ _ _ hf => hf

end QStab.Verifier
