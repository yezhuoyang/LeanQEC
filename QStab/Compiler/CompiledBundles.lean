import QStab.Verifier.QCliffordBundle
import QStab.Verifier.SurfaceD3X
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

end QStab.Compiler.CompiledBundles
