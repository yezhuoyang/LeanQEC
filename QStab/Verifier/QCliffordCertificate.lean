import QStab.Verifier
import QStab.QClifford.Gate

/-!
# QCliffordFTCertificate: gate-level fault-tolerance certificate (Phase 3 sketch)

This is the **target** language of the TAL-style bundle compiler
(`compileCertificateTrivial : QStabFTCertificate → QCliffordFTCertificate`). A
`QCliffordFTCertificate` is the gate-level analog of `QStabFTCertificate`:

  * Source (QStab): scheme-agnostic, single `Step` relation,
    invariant on `State P`.
  * Target (QClifford): concrete gate-level circuit, per-gate
    Pauli propagation, invariant as a per-gate annotation.

The shape mirrors `QStabFTCertificate` 1-to-1:

```
QCliffordFTCertificate = ⟨nq, circuit, failure, gateInv, static, bridge⟩
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

`compileCertificateTrivial : QStabFTCertificate → QCliffordFTCertificate` (Phase 4)
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

    Mirrors `QStabFTCertificate` exactly but at the QClifford layer:
    the state is `ErrorState nq` (per-qubit Pauli + measurement
    flips) instead of `State P`, and the dynamic invariant is given
    by `invHolds` (a single predicate preserved by every gate
    transition, analog of `Invariant.holds`).

    The `preservation` field is the TAL-style per-instruction typing
    rule: for any gate `g` and pre-state `es` satisfying `invHolds`,
    the post-state `propagateGate g es` also satisfies `invHolds`.
    The verifier can then walk the circuit and inductively conclude
    that `invHolds` survives to the post-circuit state. -/
structure QCliffordFTCertificate where
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
  /-- Preserved by every gate's Pauli propagation, RESTRICTED to gates
      that appear in this bundle's `circuit`. (Iter 7: weakened from
      universal `∀ g` so that `liftReach`-style invHolds can satisfy
      the field — applying an arbitrary off-circuit gate would
      generally break circuit-prefix-reachability.) -/
  preservation : ∀ (g : Gate nq), g ∈ circuit →
                   ∀ (es : ErrorState nq),
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
def verifyQClifford (b : QCliffordFTCertificate) : Bool := b.static

/-- The invariant survives any sequence of gates drawn from
    `b.circuit`. Iter 7: weakened to require every propagated gate be
    a member of `b.circuit`; this is the natural shape needed by
    `liftReach`-style invariants. The original universal claim no
    longer holds when `invHolds` depends on circuit identity. -/
theorem QCliffordFTCertificate.invHolds_propagate (b : QCliffordFTCertificate)
    (gs : Circuit b.nq)
    (hgs : ∀ (g : Gate b.nq), g ∈ gs → g ∈ b.circuit)
    (es : ErrorState b.nq) :
    b.invHolds es → b.invHolds (propagateCircuit gs es) := by
  induction gs generalizing es with
  | nil => intro h; exact h
  | cons g gs ih =>
    intro h
    have hg : g ∈ b.circuit := hgs g List.mem_cons_self
    have hgs' : ∀ (g' : Gate b.nq), g' ∈ gs → g' ∈ b.circuit :=
      fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')
    exact ih hgs' _ (b.preservation g hg es h)

/-- **Generic soundness theorem** at the QClifford layer. If the
    verifier accepts the bundle, then for any sequence of gates `gs`
    drawn from `b.circuit`, propagating them from clean does not
    trigger `b.failure`. -/
theorem verifyQClifford_sound (b : QCliffordFTCertificate)
    (h : verifyQClifford b = true)
    (gs : Circuit b.nq)
    (hgs : ∀ (g : Gate b.nq), g ∈ gs → g ∈ b.circuit) :
    ¬ b.failure (propagateCircuit gs (ErrorState.clean b.nq)) := by
  have hinv : b.invHolds (propagateCircuit gs (ErrorState.clean b.nq)) :=
    b.invHolds_propagate gs hgs _ b.init
  exact b.bridge h _ hinv

/-- Trivial bundle: no qubits, empty circuit, no failure. Sanity
    check that the structure compiles. -/
def trivialQCliffordCertificate : QCliffordFTCertificate where
  nq      := 0
  circuit := []
  failure := fun _ => False
  invHolds := fun _ => True
  init    := trivial
  preservation := fun _ _ _ _ => trivial
  static  := true
  bridge  := fun _ _ _ hf => hf

/-- A small non-trivial bundle: 2 qubits, a single CNOT(0, 1) gate.
    Demonstrates the bundle structure works for circuits with actual
    Pauli propagation (not just empty lists). `invHolds` is still the
    trivial `True` predicate — the point of this example is to
    exercise the *structure*, not test rich invariants. -/
def cnotPairCertificate : QCliffordFTCertificate where
  nq      := 2
  circuit := [Gate.cnot 0 1 (by decide)]
  failure := fun _ => False
  invHolds := fun _ => True
  init    := trivial
  preservation := fun _ _ _ _ => trivial
  static  := true
  bridge  := fun _ _ _ hf => hf

/-- The CNOT-pair bundle's verifier accepts. -/
theorem cnotPair_verified : verifyQClifford cnotPairCertificate = true := rfl

/-- The corollary of generic soundness applied to `cnotPairCertificate`:
    no list of gates `gs` can produce a failure state when prepended
    to (well, propagated from) the clean state. (Failure is `False`
    here, so this is trivially true — but the chain of typeclass +
    propagation reasoning is real and exercises `propagateCircuit`.) -/
theorem cnotPair_no_failure :
    ¬ cnotPairCertificate.failure (propagateCircuit cnotPairCertificate.circuit
                                                (ErrorState.clean 2)) :=
  verifyQClifford_sound cnotPairCertificate cnotPair_verified
    cnotPairCertificate.circuit (fun _ hg => hg)

/-! ## Operational view: `runFinal` for the standalone tool

`runFinal b` evaluates the bundle's circuit on the clean error
state and returns the final `ErrorState`. This is what a standalone
verifier executable would compute. The associated soundness
corollary `runFinal_no_failure` connects this operational view
back to the bundle's failure predicate via the generic
`verifyQClifford_sound` theorem.

Phase 5 of the verifier project (standalone CLI tool) consumes
`runFinal` + `verifyQClifford` together: print the final state
and the pass/fail status. -/

/-- Operational entry point: propagate the bundle's circuit on the
    clean input. -/
def QCliffordFTCertificate.runFinal (b : QCliffordFTCertificate) : ErrorState b.nq :=
  propagateCircuit b.circuit (ErrorState.clean b.nq)

/-- **Operational soundness**: if the bundle verifies, the failure
    predicate fails on the result of executing the bundle's circuit
    on clean input. Specialization of `verifyQClifford_sound` to the
    bundle's own `circuit`. -/
theorem QCliffordFTCertificate.runFinal_no_failure (b : QCliffordFTCertificate)
    (h : verifyQClifford b = true) : ¬ b.failure b.runFinal :=
  verifyQClifford_sound b h b.circuit (fun _ hg => hg)

/-- Smoke test on the CNOT-pair bundle. -/
example : ¬ cnotPairCertificate.failure cnotPairCertificate.runFinal :=
  cnotPairCertificate.runFinal_no_failure cnotPair_verified

/-! ## Legacy retirement note

The previous `compileCertificateTrivial : QStabFTCertificate → QCliffordFTCertificate`
and `compileCertificate b spec h_n : QCliffordFTCertificate` lived here
prior to the legacy retirement pass. They built a QClifford bundle
whose `invHolds := liftReach (toCircuitX spec)` and
`failure := ∃ i < n, paulis i ≠ I` predicates were jointly VACUOUS
(every `liftReach` state is paulis-clean, so the failure predicate is
unsatisfiable — see audit memo `audit_compile_qstab_qclifford`).
The bundle therefore did not carry real fault-tolerance content.

The live fault-tolerance pipeline is

  * QClifford-native barrier `gate_level_tolerates` (see
    `QStab/QClifford/GateBarrier.lean`), and
  * the Phase A–E compileFT_auto / compile_sound infrastructure
    (`QStab/QHL/Compile/CompilationRules.lean` and
    `QStab/QHL/Compile/CompileSound.lean`).

`compileCertificate*` and the supporting `liftReach` machinery were
moved into `QStab/Compiler/Legacy/LiftInvariant.lean` and
`QStab/Compiler/Legacy/CompiledCertificates.lean` and removed from the
default lake build. -/

end QStab.Verifier
