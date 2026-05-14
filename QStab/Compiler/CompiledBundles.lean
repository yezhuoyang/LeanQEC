import QStab.Verifier.QCliffordBundle
import QStab.Verifier.SurfaceD3X
import QStab.Verifier.BB72SEX
import QStab.Examples.CompilerTest

/-!
# `CompiledBundles` — Phase D concrete compileBundleSpec instances

Demonstrates session 2's `compileBundleSpec` on real source bundles
from `QStab.Verifier`. Each instance:

  1. Picks a source `QStabFTBundle` (X-side fault-tolerance proven).
  2. Picks a matching `CodeSpec` (gate ordering for compilation).
  3. Discharges `spec.n = b.P.n` (typically by `rfl`).
  4. Confirms `verifyQClifford` of the compiled bundle = true via the
     iter 37 cheat-free bridge.

Build success of `lake build QStab.Compiler.CompiledBundles` is the
end-to-end Phase D smoke test: real source-side fault-tolerance ⇒
real circuit-level compilation ⇒ real Lean verification.
-/

namespace QStab.Compiler.CompiledBundles

open QStab QStab.Verifier
  QStab.Verifier.SurfaceD3X
  QStab.Paper.SurfaceD3OperationalIffParam
  QStab.Paper.SurfaceD3Classification
  QStab.Examples.CompilerTest

/-! ## Surface code d=3 X-side

Source bundle: `surface_d3_X_bundle` instantiated at a concrete
non-Failing scheduling. Spec: `surfaceD3Spec` from `CompilerTest`.
Dimension match: both have `n = 9`. -/

/-- A concrete non-Failing Surface3Sched: `(0, 0, 0, 0)`.
    Non-Failing is checked by `decide`. -/
def surfaceD3_concrete_sched : Surface3Sched :=
  (⟨0, by omega⟩, ⟨0, by omega⟩, ⟨0, by omega⟩, ⟨0, by omega⟩)

/-- Surface d=3 X-side source bundle, concretely instantiated. -/
def surfaceD3_X_bundle_concrete : QStabFTBundle :=
  surface_d3_X_bundle surfaceD3_concrete_sched (by decide)

/-- The compiled QClifford bundle for Surface d=3 X-side. -/
def surfaceD3_X_compiled : QCliffordFTBundle :=
  compileBundleSpec surfaceD3_X_bundle_concrete surfaceD3Spec rfl

/-- **Phase D smoke test**: the compiled Surface d=3 X-side bundle
    passes QClifford verification. -/
theorem surfaceD3_X_compiled_verified :
    verifyQClifford surfaceD3_X_compiled = true := rfl

/-- The compiled bundle has the expected qubit count (9 data + 1 ancilla). -/
theorem surfaceD3_X_compiled_nq :
    surfaceD3_X_compiled.nq = 10 := rfl

/-! ## BB[[72,12,6]] SE-scheduling X-side

Source bundle: `bb72_SE_X_bundle`. We need a `CodeSpec` with `n = 72`.
Creating a minimal placeholder `bb72_minimal_spec` (the spec's
gate orderings are placeholders for the structural compilation test;
the source-side fault-tolerance proof doesn't depend on them).

The compiled circuit's gate count = 72 stabilizers × (|ord| + 3)
× R rounds. With singleton orderings, R=1, that's 72 × 4 × 1 = 288 gates. -/

open QStab.Verifier.BB72SEX
open QStab.Paper.BB72SEInstance
open QStab.Paper.BB72Instance

/-- A minimal CodeSpec for BB72: n=72, numStab=72, singleton orderings.
    NOT the actual BB72 protocol — placeholder for structural
    compilation smoke test. -/
def bb72_minimal_spec : CodeSpec where
  n := 72
  k := 12
  d := 6
  R := 1
  numStab := 72
  stabilizers := bb_stabilizers
  gateOrdering := fun _ => [⟨0, by omega⟩]
  hn := by omega
  hns := by omega
  hR := by omega

/-- The compiled QClifford bundle for BB72 SE X-side. -/
def bb72_SE_X_compiled : QCliffordFTBundle :=
  compileBundleSpec bb72_SE_X_bundle bb72_minimal_spec rfl

/-- **Phase D smoke test**: the compiled BB72 SE X-side bundle
    passes QClifford verification. -/
theorem bb72_SE_X_compiled_verified :
    verifyQClifford bb72_SE_X_compiled = true := rfl

/-- The compiled bundle has the expected qubit count (72 data + 1 ancilla). -/
theorem bb72_SE_X_compiled_nq :
    bb72_SE_X_compiled.nq = 73 := rfl

end QStab.Compiler.CompiledBundles
