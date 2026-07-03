import QStab.QClifford.Compile.SurfaceNZVCGen
import QStab.QClifford.Compile.HGPShorProgram

/-!
# Parametric VCGen slots for the compiled Shor-extraction HGP program

The three program-independent slots (`programEq` / `wf` / `syn`) instantiated at
`hgpShorProgram d`.  These are the **same** generic parametric slot theorems as
the NZ case (`generatedFullProgram_vcgen_{programEqD,wfD,synD}`), applied to a
different `XZProgram` — a pure instantiation, no spec structure changed.  In
particular `syn` goes through the existing list-valued `stabilizerReadout` /
`syndromeBit` machinery unchanged (the Shor gadget's multi-slot readout is
already a `List (Fin numFlags)` the generic `syndromeBit` XORs), confirming the
syndrome slot needs no widening for the cat-verifier scheme.
-/

namespace QStab.QClifford.Compile

open QStab.QClifford.PCC

/-- **Shor HGP passes VCGen slot 1/3: `programEq`** (instantiation). -/
theorem hgpShorXZ_vcgen_programEqD (d : Nat) (hd : 2 ≤ d)
    (hnq : 0 < (d * d + (d - 1) * (d - 1)) + programHelperCount (hgpShorProgram d))
    (hnumStab : 0 < programNumStab (hgpShorProgram d)) :
    (vcgen (generatedFullProgramVCInputD (hgpShorProgram d) d (by omega)
      hnq hnumStab)).denoteSlot .programEq :=
  generatedFullProgram_vcgen_programEqD (hgpShorProgram d) d (by omega) hnq hnumStab

/-- **Shor HGP passes VCGen slot 2/3: `wf`** (instantiation). -/
theorem hgpShorXZ_vcgen_wfD (d : Nat) (hd : 2 ≤ d)
    (hnq : 0 < (d * d + (d - 1) * (d - 1)) + programHelperCount (hgpShorProgram d))
    (hnumStab : 0 < programNumStab (hgpShorProgram d)) :
    (vcgen (generatedFullProgramVCInputD (hgpShorProgram d) d (by omega)
      hnq hnumStab)).denoteSlot .wf :=
  generatedFullProgram_vcgen_wfD (hgpShorProgram d) d (by omega) hnq hnumStab

/-- **Shor HGP passes VCGen slot 3/3: `syn`** (instantiation — the syndrome slot
goes through the unchanged list-valued readout machinery). -/
theorem hgpShorXZ_vcgen_synD (d : Nat) (hd : 2 ≤ d)
    (hnq : 0 < (d * d + (d - 1) * (d - 1)) + programHelperCount (hgpShorProgram d))
    (hnumStab : 0 < programNumStab (hgpShorProgram d)) :
    (vcgen (generatedFullProgramVCInputD (hgpShorProgram d) d (by omega)
      hnq hnumStab)).denoteSlot .syn :=
  generatedFullProgram_vcgen_synD (hgpShorProgram d) d (by omega) hnq hnumStab

/-- info: 'QStab.QClifford.Compile.hgpShorXZ_vcgen_synD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hgpShorXZ_vcgen_synD

end QStab.QClifford.Compile
