import QStab.QClifford.Compile.SurfaceRhoXDistance
import QStab.QClifford.Compile.SurfaceNZFtDistanceFull
import QStab.QClifford.Compile.SurfaceNZVCGen
import QStab.QClifford.Compile.CodeSafeAssembly

/-!
# `surface_Safe` — the surface capstone

The ρ-duality X-floor (`surface_compiled_barX_distance`) discharges Session 2's
`SurfaceBarXFloor` hypothesis, making the surface `ftDistance` slot
unconditional.  With the three VCBridge slots (`programEq` / `wf` / `syn`) and
the discharged `reach` slot, all **five** VCGen obligations assemble into the
`DischargedVCs` record consumed by the verifier's own `vcgen_sound` —
`surface_compiled_Safe`, for every odd `d ≥ 3`, with `hd`/`hd3`/`hodd` the only
hypotheses.
-/

namespace QStab.QClifford.Compile

open QStab QStab.QClifford QStab.QClifford.PCC
open QStab.QClifford.PCC.SurfaceNZ
open QStab.Examples.SurfaceParametric
open QHL
open QHL.Source.Examples.SurfaceParametricUpperBound

/-- **The compiled bar-X floor holds** — Session 2's explicit hypothesis,
discharged by the ρ-duality transport. -/
theorem surfaceBarXFloor_holds (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d)
    (hodd : d % 2 = 1) : SurfaceBarXFloor d hd hodd :=
  fun sigma hrun hcent hx =>
    surface_compiled_barX_distance d hd hd3 hodd sigma hrun hcent hx

/-- **Surface passes VCGen slot 4 unconditionally**: the `ftDistance` slot with
the bar-X floor discharged. -/
theorem surfaceXZ_vcgen_ftDistanceD_final (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d)
    (hodd : d % 2 = 1) :
    (vcgen (generatedFullProgramVCInputD (surfaceXZProgram d hd) d hd
      (surfaceXZ_nq_pos d hd) (surfaceXZ_numStab_pos d hd))).denoteSlot .ftDistance :=
  surfaceXZ_vcgen_ftDistanceD d hd hd3 hodd (surfaceBarXFloor_holds d hd hd3 hodd)

/-- **`surface_Safe` — the headline artifact.**  All five VCGen slots for the
compiled surface program, discharged into the `DischargedVCs` record the
verifier's `vcgen_sound` consumes: `programEq`, `wf`, `syn`, `ftDistance`
(full coverage, bar-X floor by ρ-duality) and `reach` (the column-0 script) —
for every odd `d ≥ 3`. -/
def surface_Safe (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1) :
    DischargedVCs (generatedFullProgramVCInputD (surfaceXZProgram d hd) d hd
      (surfaceXZ_nq_pos d hd) (surfaceXZ_numStab_pos d hd)) :=
  assembleDischargedVCs (surfaceXZProgram d hd) d hd
    (surfaceXZ_nq_pos d hd) (surfaceXZ_numStab_pos d hd)
    (surfaceReachScript d hd)
    (surfaceXZ_vcgen_ftDistanceD_final d hd hd3 hodd)
    (surfaceXZ_vcgen_reachD d hd hd3 hodd)

/-- **The verifier's own soundness, applied**: the compiled surface program is
`Safe` against its generated spec, for every odd `d ≥ 3` — a one-line instance of
the generic `assembleCodeSafe`. -/
theorem surface_compiled_Safe (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d)
    (hodd : d % 2 = 1) :
    Safe (compileProgram (surfaceXZProgram d hd))
      ((generatedFullProgramVCInputD (surfaceXZProgram d hd) d hd
        (surfaceXZ_nq_pos d hd) (surfaceXZ_numStab_pos d hd)).toCodeSpec) :=
  assembleCodeSafe (surfaceXZProgram d hd) d hd
    (surfaceXZ_nq_pos d hd) (surfaceXZ_numStab_pos d hd)
    (surfaceReachScript d hd)
    (surfaceXZ_vcgen_ftDistanceD_final d hd hd3 hodd)
    (surfaceXZ_vcgen_reachD d hd hd3 hodd)

-- Regression guards (axiom pins) for the capstone headliners.
/--
info: 'QStab.QClifford.Compile.surfaceBarXFloor_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms surfaceBarXFloor_holds

/--
info: 'QStab.QClifford.Compile.surfaceXZ_vcgen_ftDistanceD_final' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms surfaceXZ_vcgen_ftDistanceD_final

/--
info: 'QStab.QClifford.Compile.surface_Safe' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms surface_Safe

/--
info: 'QStab.QClifford.Compile.surface_compiled_Safe' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms surface_compiled_Safe

end QStab.QClifford.Compile
