import QStab.QClifford.Compile.SurfaceNZFtDistance
import QStab.QClifford.Compile.SurfaceZLeg
import QStab.QClifford.Compile.SurfaceNZReachFold
import QStab.Examples.SurfaceHookErrors

/-!
# The surface `ftDistance` slot: full-coverage assembly (X-floor as hypothesis)

This file assembles the **full** surface circuit-level `ftDistance` obligation
from the landed pieces, mirroring `HGPNZFtDistance.lean` line-for-line:

* `surfaceNZ_logicalFailure_iff` (landed): the PCC `logicalFailure` is a
  source-side `(Centralizer ∧ ¬ InStab)` statement over `mkSurfaceQECParams`;
* `surface_coverage` (the maximal-isotropic contrapositive, landed keystone):
  any such residual anticommutes with `X̄ = mkSurfaceAttackerX` or with
  `Z̄ = mkSurfaceLogicalZ` — `Ȳ`-type residuals do both, so either floor fires;
* the `barZ` floor `surface_compiled_barZ_distance` (landed) discharges the
  `Z̄` disjunct in full.

The `X̄` disjunct is the compiled bar-X distance floor, the subject of
**Session 3** (the ρ-rotation duality transport — gated on and cleared by the
`notes/validate_rotated_hookset_pin.py` absorbability pin).  Until it lands, we
carry it as the explicit named hypothesis `SurfaceBarXFloor`: the plumbing is
fully verified now, and the hypothesis discharges the moment the X-floor exists.
-/

namespace QStab.QClifford.Compile

open QStab QStab.QClifford QStab.QClifford.PCC
open QStab.QClifford.PCC.SurfaceNZ
open QStab.Examples.SurfaceParametric
open QHL.AssertionLang
open QHL.Source.Examples.Surface
open QHL.Source.Examples.SurfaceUnionSpec
open QHL.Source.Examples.SurfaceParametricUpperBound

/-- **The compiled bar-X distance floor, as an explicit named hypothesis.**  A
clean-start run of the compiled surface circuit whose data residual is a bar-X
logical (anticommutes with `X̄ = mkSurfaceAttackerX`, commutes with every
stabilizer) fired at least `d` faults.  This is the exact `parity`-form counterpart
of the landed `barZ` floor; Session 3's ρ-duality transport discharges it. -/
def SurfaceBarXFloor (d : Nat) (hd : 0 < d) (hodd : d % 2 = 1) : Prop :=
  ∀ (sigma : QCState (d * d + programHelperCount (surfaceXZProgram d hd))),
    qceval (compileProgram (surfaceXZProgram d hd))
      (QCState.clean (d * d + programHelperCount (surfaceXZProgram d hd))) sigma →
    (∀ j : Fin (mkSurfaceQECParams d hd hodd).numStab,
      ErrorVec.parity ((mkSurfaceQECParams d hd hodd).stabilizers j)
        (dataErrorOfQCState (mkSurfaceQECParams d hd hodd)
          (programHelperCount (surfaceXZProgram d hd)) sigma) = false) →
    ErrorVec.parity (mkSurfaceAttackerX d)
      (dataErrorOfQCState (mkSurfaceQECParams d hd hodd)
        (programHelperCount (surfaceXZProgram d hd)) sigma) = true →
    d ≤ sigma.lambda

/-- **Surface circuit-level `ftDistance`, full coverage (X-floor hypothesised).**
Every clean-start run of `compileProgram (surfaceXZProgram d)` whose error state is
a PCC `logicalFailure` fired at least `d` faults — the full slot obligation, no
bar-Z restriction, modulo the compiled bar-X floor `hBarX`. -/
theorem surfaceNZ_ftDistance (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (hBarX : SurfaceBarXFloor d hd hodd)
    (sigma : QCState (d * d + programHelperCount (surfaceXZProgram d hd)))
    (hrun : qceval (compileProgram (surfaceXZProgram d hd))
      (QCState.clean (d * d + programHelperCount (surfaceXZProgram d hd))) sigma)
    (hfail : QStab.QClifford.PCC.logicalFailure (fullProgramCodeSpecD (surfaceXZProgram d hd)
        (fullProgramReadoutDisjoint_auto (surfaceXZProgram d hd)) d hd) sigma.es) :
    d ≤ sigma.lambda := by
  rw [surfaceNZ_logicalFailure_iff d hd hd3 hodd sigma] at hfail
  obtain ⟨hcent, hnot⟩ := hfail
  rcases surface_coverage d hd hd3 hodd _ hcent hnot with hx | hz
  · -- bar-X disjunct: discharged by the hypothesised compiled X-floor
    exact hBarX sigma hrun hcent hx
  · -- bar-Z disjunct: land the bar-Z class, fire the landed bar-Z floor
    refine surface_compiled_barZ_distance d hd hd3 hodd sigma hrun ⟨fun S hS => ?_, fun T hT => ?_⟩
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hS
      exact hcent i
    · rw [List.mem_singleton.mp hT]
      exact hz

/-! ## The VCGen `ftDistance` slot -/

/-- **The `ftDistance` VCGen slot** for the compiled surface program at distance
`d` — the verifier's ∀-logical obligation, met in full modulo the compiled
bar-X floor `hBarX`. -/
theorem surface_vcgen_ftDistanceD (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (hBarX : SurfaceBarXFloor d hd hodd)
    (hnq : 0 < d * d + programHelperCount (surfaceXZProgram d hd))
    (hnumStab : 0 < programNumStab (surfaceXZProgram d hd)) :
    (vcgen (fullProgramVCInputD (surfaceXZProgram d hd)
      (fullProgramReadoutDisjoint_auto (surfaceXZProgram d hd)) d hd hnq hnumStab)).denoteSlot
      .ftDistance := by
  intro sigma hrun _hflags
  rw [denoteQC_circuitDistanceAny]
  intro hfail
  have hfail' : QStab.QClifford.PCC.logicalFailure (fullProgramCodeSpecD (surfaceXZProgram d hd)
      (fullProgramReadoutDisjoint_auto (surfaceXZProgram d hd)) d hd) sigma.es := hfail
  have hrun' : qceval (compileProgram (surfaceXZProgram d hd))
      (QCState.clean (d * d + programHelperCount (surfaceXZProgram d hd))) sigma := hrun
  exact surfaceNZ_ftDistance d hd hd3 hodd hBarX sigma hrun' hfail'

/-- **Surface passes VCGen slot 4: `ftDistance`** — the canonical
`generatedFullProgramVCInputD` form, positivity side conditions discharged
internally, modulo the compiled bar-X floor `hBarX`. -/
theorem surfaceXZ_vcgen_ftDistanceD (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (hBarX : SurfaceBarXFloor d hd hodd) :
    (vcgen (generatedFullProgramVCInputD (surfaceXZProgram d hd) d hd
      (surfaceXZ_nq_pos d hd) (surfaceXZ_numStab_pos d hd))).denoteSlot .ftDistance :=
  surface_vcgen_ftDistanceD d hd hd3 hodd hBarX (surfaceXZ_nq_pos d hd) (surfaceXZ_numStab_pos d hd)

/-! ## Session-3 gate witness: the `d = 3` per-site residual (suffix-hook) table

The compiled X-floor is to be transported from the landed bar-Z floor along the
ρ-rotation duality (ρ = 90° lattice rotation + Hadamard).  The gate — cleared by
`notes/validate_rotated_hookset_pin.py` at d = 3, 5, 7 — is that ρ is a
stabilizer-set automorphism and every hook-set mismatch between the NZ order and
the ρ-rotated order is weight-1-mod-stabilizer (absorbable).  The
interpreter-checked `#eval` below is the Lean-side witness of the native NZ-order residual table: the
per-stabilizer suffix-hook weight profile, `[3,2,1]` for the four weight-4 bulk
checks and `[1]` for the four weight-2 boundary checks — matching the scout and
`ρ`-invariant in profile (the mismatches are purely which weight-2 pair, all
absorbable). -/
/-- info: [[3, 2, 1], [3, 2, 1], [3, 2, 1], [3, 2, 1], [1], [1], [1], [1]] -/
#guard_msgs in
#eval (List.finRange (numStabFormula 3)).map fun s =>
  let k := QStab.Examples.SurfaceParametric.classifyStab 3 s.val
  (QStab.Examples.SurfaceParametric.suffixIndices 3 k).map fun j =>
    (List.finRange 9).countP fun q =>
      decide (QStab.Examples.SurfaceParametric.suffixHook 3 k j q ≠ Pauli.I)

-- Regression guards (axiom pins) for the slot headliners.
/--
info: 'QStab.QClifford.Compile.surfaceNZ_ftDistance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms surfaceNZ_ftDistance

/--
info: 'QStab.QClifford.Compile.surfaceXZ_vcgen_ftDistanceD' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms surfaceXZ_vcgen_ftDistanceD

end QStab.QClifford.Compile
