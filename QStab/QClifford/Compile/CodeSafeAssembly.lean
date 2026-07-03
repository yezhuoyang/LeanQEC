import QStab.QClifford.Compile.SurfaceNZVCGen

/-!
# Generic capstone assembly: five VCGen slots → `DischargedVCs` → `Safe`

`hgp_Safe` and `surface_Safe` are identical modulo the code: both bundle the same
three VCBridge slots (`programEq` / `wf` / `syn`, supplied by the generic
`generatedFullProgram_vcgen_*D` constructors) with the two per-code slots
(`ftDistance`, `reachOk`) and a `reachScript`, then feed the record to the
verifier's own `vcgen_sound`.

This file factors that assembly into `assembleDischargedVCs` (the record, with
the three bridge slots discharged generically) and `assembleCodeSafe` (the `Safe`
conclusion via `vcgen_sound`).  Any compiled program with its `ftDistance` and
`reach` slots discharged becomes a capstone by instantiation — no per-code
plumbing.
-/

namespace QStab.QClifford.Compile

open QStab QStab.QClifford QStab.QClifford.PCC

/-- **The generic discharged-VC record.**  The three VCBridge slots
(`programEq` / `wf` / `syn`) are the code-independent `generatedFullProgram_vcgen_*D`
constructors; the caller supplies only the `reachScript` and the two per-code
slot proofs (`ftDistance`, `reachOk`). -/
def assembleDischargedVCs {n : Nat} (program : XZProgram n) (dist : Nat) (hdist : 0 < dist)
    (hnq : 0 < n + programHelperCount program) (hnumStab : 0 < programNumStab program)
    (reachScript : List (Option Pauli))
    (ftDistance : (vcgen (generatedFullProgramVCInputD program dist hdist hnq hnumStab)).denoteSlot
      .ftDistance)
    (reachOk : (vcgen (generatedFullProgramVCInputD program dist hdist hnq hnumStab)).denoteSlot
      .reach reachScript) :
    DischargedVCs (generatedFullProgramVCInputD program dist hdist hnq hnumStab) where
  reachScript := reachScript
  programEq := generatedFullProgram_vcgen_programEqD program dist hdist hnq hnumStab
  wf := generatedFullProgram_vcgen_wfD program dist hdist hnq hnumStab
  syn := generatedFullProgram_vcgen_synD program dist hdist hnq hnumStab
  ftDistance := ftDistance
  reachOk := reachOk

/-- **The generic capstone.**  A compiled program whose `ftDistance` and `reach`
slots are discharged is `Safe` against its generated spec — the verifier's own
`vcgen_sound` applied to the assembled record. -/
theorem assembleCodeSafe {n : Nat} (program : XZProgram n) (dist : Nat) (hdist : 0 < dist)
    (hnq : 0 < n + programHelperCount program) (hnumStab : 0 < programNumStab program)
    (reachScript : List (Option Pauli))
    (ftDistance : (vcgen (generatedFullProgramVCInputD program dist hdist hnq hnumStab)).denoteSlot
      .ftDistance)
    (reachOk : (vcgen (generatedFullProgramVCInputD program dist hdist hnq hnumStab)).denoteSlot
      .reach reachScript) :
    Safe (compileProgram program)
      ((generatedFullProgramVCInputD program dist hdist hnq hnumStab).toCodeSpec) :=
  vcgen_sound (.mk (assembleDischargedVCs program dist hdist hnq hnumStab
    reachScript ftDistance reachOk))

end QStab.QClifford.Compile
