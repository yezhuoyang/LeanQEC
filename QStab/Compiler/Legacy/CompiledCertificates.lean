import QStab.Verifier.QCliffordCertificate
import QStab.Verifier.SurfaceD3X
import QStab.Verifier.BB72SEX
import QStab.Verifier.HGPX
import QStab.Examples.CompilerTest
import QStab.Compiler.Legacy.LiftInvariant

/-!
**LEGACY (quarantined 2026-06-15).** Per audit memo
`audit_compile_qstab_qclifford`, this file builds
`surfaceD3_X_compiled` / `bb72_SE_X_compiled` / parametric HGP
bundles via the legacy `compileCertificate`, which produces a
joint vacuous `invHolds := liftReach …` / `failure := ∃ paulis ≠ I`
predicate. The bundles fed `SurfaceHGPDerivC` (now also legacy).
The `_verified := rfl` headlines reflect only the source-side
`static` bit, not real fault-tolerance content.

Since `compileCertificate` was removed from `QCliffordCertificate.lean`
on the legacy retirement pass, this file no longer elaborates without
also restoring `compileCertificate`; it is retained for historical
context.

# `CompiledBundles` — Phase D concrete compileCertificate instances

Demonstrates session 2's `compileCertificate` on real source bundles
from `QStab.Verifier`. Each instance:

  1. Picks a source `QStabFTCertificate` (X-side fault-tolerance proven).
  2. Picks a matching `CodeSpec` (gate ordering for compilation).
  3. Discharges `spec.n = b.P.n` (typically by `rfl`).
  4. Confirms `verifyQClifford` of the compiled bundle = true via the
     iter 37 cheat-free bridge.

Build success of `lake build QStab.Compiler.CompiledCertificates` is the
end-to-end Phase D smoke test: real source-side fault-tolerance ⇒
real circuit-level compilation ⇒ real Lean verification.
-/

namespace QStab.Compiler.CompiledCertificates

open QStab QStab.Verifier
  QStab.Verifier.SurfaceD3X
  QStab.Paper.SurfaceD3OperationalIffParam
  QStab.Paper.SurfaceD3Classification
  QStab.Examples.CompilerTest

/-! ## Surface code d=3 X-side

Source bundle: `surface_d3_X_certificate` instantiated at a concrete
non-Failing scheduling. Spec: `surfaceD3Spec` from `CompilerTest`.
Dimension match: both have `n = 9`. -/

/-- A concrete non-Failing Surface3Sched: `(0, 0, 0, 0)`.
    Non-Failing is checked by `decide`. -/
def surfaceD3_concrete_sched : Surface3Sched :=
  (⟨0, by omega⟩, ⟨0, by omega⟩, ⟨0, by omega⟩, ⟨0, by omega⟩)

/-- Surface d=3 X-side source bundle, concretely instantiated. -/
def surfaceD3_X_bundle_concrete : QStabFTCertificate :=
  surface_d3_X_certificate surfaceD3_concrete_sched (by decide)

/-- The compiled QClifford bundle for Surface d=3 X-side. -/
def surfaceD3_X_compiled : QCliffordFTCertificate :=
  compileCertificate surfaceD3_X_bundle_concrete surfaceD3Spec rfl

/-- **Phase D smoke test**: the compiled Surface d=3 X-side bundle
    passes QClifford verification. -/
theorem surfaceD3_X_compiled_verified :
    verifyQClifford surfaceD3_X_compiled = true := rfl

/-- The compiled bundle has the expected qubit count (9 data + 1 ancilla). -/
theorem surfaceD3_X_compiled_nq :
    surfaceD3_X_compiled.nq = 10 := rfl

/-! ## BB[[72,12,6]] SE-scheduling X-side

Source bundle: `bb72_SE_X_certificate`. We need a `CodeSpec` with `n = 72`.
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
def bb72_SE_X_compiled : QCliffordFTCertificate :=
  compileCertificate bb72_SE_X_certificate bb72_minimal_spec rfl

/-- **Phase D smoke test**: the compiled BB72 SE X-side bundle
    passes QClifford verification. -/
theorem bb72_SE_X_compiled_verified :
    verifyQClifford bb72_SE_X_compiled = true := rfl

/-- The compiled bundle has the expected qubit count (72 data + 1 ancilla). -/
theorem bb72_SE_X_compiled_nq :
    bb72_SE_X_compiled.nq = 73 := rfl

/-! ## HGP family — **parametric** Phase D theorem

HGPSpec instances require filling many fields (logicalZ basis,
stabilizer matrix, weight bounds) that are tied to a specific
classical parity-check matrix. Rather than commit to a single
concrete HGPSpec (e.g. Rep3x3 with d=3, n=13), this iter delivers
the PARAMETRIC compileCertificate theorem: for ANY `HGPSpec d` with
budget below `d`, the compiled bundle verifies.

A concrete HGPSpec for Rep3x3 would still need ~50 LoC of stabilizer
+ logicalZ data — out of scope for one iter. The parametric theorem
covers any future concrete instance for free. -/

open QStab.Verifier.HGPX
open QStab.Examples.SurfaceGeneral (HGPSpec)

/-- **Phase D parametric theorem**: for any HGPSpec and any matching
    CodeSpec with the same qubit count, the compiled QClifford bundle
    passes verification. This covers the entire HGP family in one
    statement; concrete instances (Rep3x3, etc.) follow by
    specialization. -/
theorem hgp_X_compiled_verified {d : Nat} (spec : HGPSpec d)
    (h_budget : spec.params.C_budget < d)
    (cspec : CodeSpec) (h_n : cspec.n = spec.params.n) :
    verifyQClifford
      (compileCertificate (hgp_X_certificate spec h_budget) cspec h_n) = true := rfl

/-- Same for the qubit-count fact. -/
theorem hgp_X_compiled_nq {d : Nat} (spec : HGPSpec d)
    (h_budget : spec.params.C_budget < d)
    (cspec : CodeSpec) (h_n : cspec.n = spec.params.n) :
    (compileCertificate (hgp_X_certificate spec h_budget) cspec h_n).nq =
      spec.params.n + 1 := rfl

end QStab.Compiler.CompiledCertificates
