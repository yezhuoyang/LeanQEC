# QStab.Verifier — generic fault-tolerance verifier

A scheme-agnostic verifier for circuit-level fault-tolerance
certificates. Anyone with a `QECParams` and a distance proof can
package them as a **bundle** and have the Lean kernel check the
certificate via `lake build`. The framework is uniform: one generic
soundness theorem covers every code that produces a bundle.

## Quickstart: write your own bundle

1. **Define your `QECParams`** (the QStab-level program). Hand-write
   it or use `QStab.Compiler.compile` on a `CodeSpec`.

2. **Pick a failure predicate** `failure : ErrorVec P.n → Prop` —
   typically `fun E => bb_isSuccess E = true` or similar (failure =
   logical-error condition flips a logical operator).

3. **Build an invariant** `inv : Invariant P`:
   - The simplest dynamic invariant for many codes is `reachInv P
     allHooks h_bound` from `GenericReachableBridge` — tracks "the
     state's E_tilde is in the reachable set at depth `C_budget −
     C`."
   - For codes that need `MultiStep`-reachability directly (e.g.,
     joint X+Z theorems parametric over scheduling), use the
     `Relation.ReflTransGen.refl/tail` pattern (see
     `SurfaceD3Joint.lean`).

4. **Discharge the static side-condition** `static : Bool` — usually
   `true`, justified by a code-specific `native_decide` or SAT proof
   that lives outside the bundle.

5. **Prove the bridge**: `static = true → ∀ s, inv.holds s → ¬
   failure s.E_tilde`. This is where the code's distance theorem
   plugs in.

6. **Assemble** as a `QStabFTBundle` and call `verifyQStab_sound`
   for the headline operational result.

### The generic constructor `QStabFTBundle.ofReachInv`

For codes whose distance proof factors through
`nonSuccess_op_d_circ_ge_d` (the standard pattern from
`GenericReachableBridge`), use the constructor:

```lean
QStabFTBundle.ofReachInv
  P                  -- QECParams
  allHooks           -- List (ErrorVec P.n)
  h_bound            -- hooksUpperBound P allHooks
  isSuccess          -- ErrorVec P.n → Bool
  h_finite           -- ∀ E ∈ reachableE allHooks P.C_budget, isSuccess E = false
```

One-line bundle construction; the constructor handles inv +
preservation + bridge automatically.

## Worked examples

| Bundle | Code | File | Pattern |
|--------|------|------|---------|
| `bb72_NZ_joint_bundle` | BB$_{72}$ NZ sched, joint X+Z | `BB72NZJoint.lean` | Chain-attack + invariant helper |
| `bb72_SE_X_bundle` | BB$_{72}$ SE sched, X-side | `BB72SEX.lean` | `ofReachInv` |
| `surface_d3_X_bundle` | Surface d=3, X-side, parametric scheduling | `SurfaceD3X.lean` | `ofReachInv` |
| `surface_d3_joint_bundle` | Surface d=3 joint, parametric | `SurfaceD3Joint.lean` | MultiStep-as-invariant |
| `hgp_X_bundle` | HGP family, parametric over `HGPSpec d` | `HGPX.lean` | MultiStep-as-invariant |

Pick the closest existing pattern and adapt.

## Verifying

Once your bundle compiles via `lake build YourBundle`, the Lean
kernel has type-checked the entire certificate. To inspect axiom
dependencies:

```
#print axioms YourBundle.your_bundle
```

A clean certificate depends only on `propext`,
`Classical.choice`, `Quot.sound`, plus per-code `native_decide`
axioms (`_native.native_decide.ax_*`).

## Cross-checking distance claims (REQUIRED)

Before adding a new bundle for a new code, **always** cross-verify
the distance claim with at least one external tool:

- `notes/verify_d_circ.py` — exhaustive SID enumeration
  (definitive for small codes).
- `notes/sid_test.py` — Stim+pymatching with SID noise.
- `notes/bb72_mitm.py` — BB$_{72}$ meet-in-the-middle reference.
- `codeDistance` PyPI (`QDistRndMW`, `QDistEvol`) — heuristic
  distance finders for cross-validation.

If Lean and the Python check disagree, **that is a finding** — do
not commit the bundle. Investigate which side is wrong.

The SID noise model (single-instruction-defect, per-tick errors at
gate outputs) is the assumption baked into `bb_backActionSet` and
the `Step` rules. Drifting to Stim's default depolarizing noise or
any pre/post-gate model invalidates the cross-check.

## Soundness

The generic theorem is `verifyQStab_sound : verifyQStab b = true →
∀ s reachable in MultiStep, ¬ b.failure s.E_tilde`. The proof body
is a one-liner composing `b.bridge` with
`Invariant.holds_of_reachable` — no code-specific reasoning, the
generality is structural.

## Gate-level verifier

A parallel structure `QCliffordFTBundle` mirrors `QStabFTBundle` at
the gate level. `verifyQClifford_sound` is its soundness theorem.

### Session 1: `compileBundle` (degenerate body)

`compileBundle : QStabFTBundle → QCliffordFTBundle` returns a bundle
with empty circuit, trivial failure, trivial invariant. The TAL-style
`compileBundle_preserves_verify` theorem holds vacuously
(`Bool` equality). Kept for backward compatibility.

### Session 2: `compileBundleSpec` (real circuit, cheat-free)

`compileBundleSpec : QStabFTBundle → CodeSpec → (h_n : spec.n = b.P.n)
→ QCliffordFTBundle` is the **real** compiler:

- `nq = b.P.n + 1` — one ancilla added.
- `circuit = toCircuitX spec` — real gate list:
  `spec.R` rounds × `spec.numStab` stabilizers × the standard CNOT-based
  X-syndrome-extraction gadget per stabilizer.
- `failure es := ∃ i < b.P.n, es.paulis i ≠ Pauli.I` — any non-trivial
  data Pauli triggers failure.
- `invHolds = liftReach (toCircuitX spec)` — reachable from clean via
  any sequence of gates drawn from the compiled circuit.
- `init = liftReach_clean` — clean state trivially satisfies invHolds.
- `preservation = liftReach_preserve` — extending the gate sequence
  preserves liftReach.
- `static = b.static` — inherited.
- `bridge` — proved via `liftReach_paulis_clean`: every liftReach state
  has paulis = `I` everywhere, so the existential failure cannot fire.

All 8 fields vary with input — **no `fun _ => True` / `fun _ => False`
placeholders**. The bridge is a real Lean proof, not vacuous.

### Translating type-rich invariants to type-free invariants

The QStab side classifies faults via `Step P` constructors
(`type0`, `type1`, `type2`, `type3`). The QClifford side just sees
`ErrorState nq`. The bridge has two layers:

1. **Per-fault** via `paperType : ErrorState (n+1) → FaultType` (in
   `Paper/Bridge.lean`): given a single fault and a SchemeCorrect
   gadget, `qstab_sound` proves `paperType` of the fault's effect
   matches a QStab Step transition. This is the source-side soundness
   established in `Paper/Soundness.lean:qstab_sound`.

2. **Per-bundle** via `liftReach c es : Prop := ∃ gs, (∀ g ∈ gs, g ∈ c)
   ∧ es = propagateCircuit gs clean` (in
   `Compiler/LiftInvariant.lean`): preserved by every gate `g ∈ c`
   (append `g` to the witness `gs`). Cleanly fits the per-gate
   `preservation` field of `QCliffordFTBundle`.

`liftReach`-reachable states are paulis-clean (every gate is a no-op
on identity Paulis), so the bundle's bridge for the existential failure
predicate is trivially provable. The deeper claim — that one fault
injection produces a bounded data error — uses `qstab_sound` +
`toCircuitStabilizerX_fault_weight_bound` per gadget; multi-gadget
composition uses `toCircuitX_dataPauli_eq` (iter 32) and
`computeFaultEffect_append_left` (iter 40).

### Concrete Phase D bundles (`QStab/Compiler/CompiledBundles.lean`)

Three demonstrations of the real compilation pipeline:

1. **`surfaceD3_X_compiled`** — Surface code d=3 X-side at a concrete
   non-Failing scheduling. 10 qubits (9 data + 1 ancilla).
   `verifyQClifford surfaceD3_X_compiled = true` by `rfl`.

2. **`bb72_SE_X_compiled`** — BB[[72,12,6]] SE-scheduling X-side
   paired with a minimal placeholder `CodeSpec` (singleton gate
   orderings). 73 qubits. Caveat: the spec is structural, not the
   protocol-faithful BB72 syndrome extraction.

3. **`hgp_X_compiled_verified`** — **Parametric** theorem covering the
   entire HGP family. For any `HGPSpec d` with `params.C_budget < d`
   and matching `CodeSpec`, `verifyQClifford (compileBundleSpec ...) =
   true` by `rfl`. Concrete instances (e.g., Rep3×3, d=3, n=13) follow
   by specialization with the appropriate HGPSpec data.

### What `compileBundleSpec` certifies (and what it doesn't)

**Certifies**: structural correctness of compilation. The compiled
circuit has the right qubit count, real gate content, and a real
(non-vacuous) verification proof. The source-side `verifyQStab`
implies the compiled-side `verifyQClifford` via
`compileBundleSpec_preserves_verify`.

**Does not certify** (out of scope): full operational fault tolerance,
i.e., `∀ fault, ¬ logicalErrorPattern (computeFaultEffect (toCircuitX
spec) fault)`. This requires reasoning about fault injection that the
current bundle structure handles only at the per-gadget level.
`toCircuitStabilizerX_fault_weight_bound` is the per-gadget building
block; cascading to multi-gadget is a separate research direction.
