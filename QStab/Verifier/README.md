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
The `compileBundle : QStabFTBundle → QCliffordFTBundle` function
exists with the TAL-style `compileBundle_preserves_verify`
theorem, but its body is currently degenerate (empty circuit,
trivial failure) — making it informative requires a verified
QStab→QClifford translation that is a separate research project.
