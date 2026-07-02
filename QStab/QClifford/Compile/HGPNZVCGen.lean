import QStab.QClifford.Compile.SurfaceNZVCGen
import QStab.QClifford.Compile.HGPNZProgram

/-!
# Parametric VCGen slots for the compiled HGP program

The three program-independent slots (`programEq` / `wf` / `syn`) instantiated
at `hgpXZProgram d`, for every `d ≥ 2` — the generic parametric slot theorems
applied to the generator-defined HGP program.  The remaining two slots
(`ftDistance` / `reach`) are the per-code work; the conditional compiled
distance lives in `HGPNZAssembly`.
-/

namespace QStab.QClifford.Compile

open QStab.QClifford.PCC

/-- **HGP passes VCGen slot 1/3 parametrically: `programEq`.** -/
theorem hgpXZ_vcgen_programEqD (d : Nat) (hd : 2 ≤ d)
    (hnq : 0 < (d * d + (d - 1) * (d - 1)) + programHelperCount (hgpXZProgram d))
    (hnumStab : 0 < programNumStab (hgpXZProgram d)) :
    (vcgen (generatedFullProgramVCInputD (hgpXZProgram d) d (by omega)
      hnq hnumStab)).denoteSlot .programEq :=
  generatedFullProgram_vcgen_programEqD (hgpXZProgram d) d (by omega) hnq hnumStab

/-- **HGP passes VCGen slot 2/3 parametrically: `wf`.** -/
theorem hgpXZ_vcgen_wfD (d : Nat) (hd : 2 ≤ d)
    (hnq : 0 < (d * d + (d - 1) * (d - 1)) + programHelperCount (hgpXZProgram d))
    (hnumStab : 0 < programNumStab (hgpXZProgram d)) :
    (vcgen (generatedFullProgramVCInputD (hgpXZProgram d) d (by omega)
      hnq hnumStab)).denoteSlot .wf :=
  generatedFullProgram_vcgen_wfD (hgpXZProgram d) d (by omega) hnq hnumStab

/-- **HGP passes VCGen slot 3/3 parametrically: `syn`.** -/
theorem hgpXZ_vcgen_synD (d : Nat) (hd : 2 ≤ d)
    (hnq : 0 < (d * d + (d - 1) * (d - 1)) + programHelperCount (hgpXZProgram d))
    (hnumStab : 0 < programNumStab (hgpXZProgram d)) :
    (vcgen (generatedFullProgramVCInputD (hgpXZProgram d) d (by omega)
      hnq hnumStab)).denoteSlot .syn :=
  generatedFullProgram_vcgen_synD (hgpXZProgram d) d (by omega) hnq hnumStab

#print axioms hgpXZ_vcgen_programEqD
#print axioms hgpXZ_vcgen_wfD
#print axioms hgpXZ_vcgen_synD

end QStab.QClifford.Compile
