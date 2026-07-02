import QStab.QClifford.Compile.SurfaceNZVCGen
import QStab.QClifford.Compile.XZProgramOfPrograms
import QStab.QHL.CodeSteaneSchedule
import QStab.QHL.CodeSteane
import QStab.QHL.CodeHGP
import QStab.QHL.CodeHGPSchedule
import QStab.QClifford.Compile.HGPNZProgram

/-!
# Multi-code consumers: the generator's first real other codes

`xzProgramOfPrograms` is code-blind (see `XZProgramOfPrograms.lean` — imports only
`Calculus` + `CodeLang`).  Here the *same* generator produces a **real** `XZProgram` for
the Steane code from its schedule programs (`CodeSteaneSchedule.lean`), and the three
program-independent parametric VCGen slots (`programEqD` / `wfD` / `synD`) fire at that
instance — the "partially passes VCGen for a new code" milestone.

HGP now runs the same pipeline for real: `CodeHGPSchedule.lean`'s certified schedule
programs (order pinned against `HGP13PCC.hookErrors`: ascending qubit index =
sector-1-then-sector-2, `len = 4` iff the check's column/row index is interior) feed the
explicit-`nQ` front-end at `nQ = 13` — a non-square qubit count, unreachable before the
generalization — and the same three VCGen slots fire.
-/

namespace QStab.QClifford.Compile

open QHL.CodeLang
open QStab.QClifford.PCC

/-! ## Steane: real generated program + VCGen slots -/

/-- Steane's compiled `XZProgram` from the two schedule programs (embedded in `Fin 9`,
`d = 3`; qubits 7, 8 unused). -/
def steaneCompiledProgram : XZProgram (3 * 3) :=
  xzProgramOfPrograms QHL.CodeLang.Steane.code
    QHL.CodeSteaneSchedule.steaneOrderProg QHL.CodeSteaneSchedule.steaneLenProg 6 (3 * 3) 3

-- The real Steane program: 6 generators, ascending-in-Hamming-row order, X then Z.
#eval steaneCompiledProgram

/-- **Steane partially passes VCGen (1/3): `programEq`.**  The program-equality slot fires
for the generated Steane program (the generic slot theorem, instantiated). -/
theorem steane_vcgen_programEqD
    (hnq : 0 < 3 * 3 + programHelperCount steaneCompiledProgram)
    (hnumStab : 0 < programNumStab steaneCompiledProgram) :
    (vcgen (generatedFullProgramVCInputD steaneCompiledProgram 3 (by decide) hnq hnumStab)).denoteSlot
      .programEq :=
  generatedFullProgram_vcgen_programEqD steaneCompiledProgram 3 (by decide) hnq hnumStab

/-- **Steane partially passes VCGen (2/3): `wf`.** -/
theorem steane_vcgen_wfD
    (hnq : 0 < 3 * 3 + programHelperCount steaneCompiledProgram)
    (hnumStab : 0 < programNumStab steaneCompiledProgram) :
    (vcgen (generatedFullProgramVCInputD steaneCompiledProgram 3 (by decide) hnq hnumStab)).denoteSlot
      .wf :=
  generatedFullProgram_vcgen_wfD steaneCompiledProgram 3 (by decide) hnq hnumStab

/-- **Steane partially passes VCGen (3/3): `syn`.** -/
theorem steane_vcgen_synD
    (hnq : 0 < 3 * 3 + programHelperCount steaneCompiledProgram)
    (hnumStab : 0 < programNumStab steaneCompiledProgram) :
    (vcgen (generatedFullProgramVCInputD steaneCompiledProgram 3 (by decide) hnq hnumStab)).denoteSlot
      .syn :=
  generatedFullProgram_vcgen_synD steaneCompiledProgram 3 (by decide) hnq hnumStab

/-! ## HGP: real generated program + VCGen slots -/

/-- HGP `[[13,1,3]]`'s compiled `XZProgram` from the two certified schedule programs
(13 qubits — a non-square count, needing the explicit-`nQ` front-end; `d = 3`). -/
def hgpCompiledProgram : XZProgram 13 :=
  xzProgramOfPrograms QHL.CodeLang.HGP.code
    QHL.CodeHGPSchedule.hgpOrderProg QHL.CodeHGPSchedule.hgpLenProg 12 13 3

-- The real HGP program: 12 generators, 6 X then 6 Z, row-then-column supports.
#eval hgpCompiledProgram

/-- The demo instance is the `d = 3` member of the parametric family. -/
theorem hgpCompiledProgram_eq : hgpCompiledProgram = hgpXZProgram 3 := rfl

/-- **HGP partially passes VCGen (1/3): `programEq`.** -/
theorem hgp_vcgen_programEqD
    (hnq : 0 < 13 + programHelperCount hgpCompiledProgram)
    (hnumStab : 0 < programNumStab hgpCompiledProgram) :
    (vcgen (generatedFullProgramVCInputD hgpCompiledProgram 3 (by decide) hnq hnumStab)).denoteSlot
      .programEq :=
  generatedFullProgram_vcgen_programEqD hgpCompiledProgram 3 (by decide) hnq hnumStab

/-- **HGP partially passes VCGen (2/3): `wf`.** -/
theorem hgp_vcgen_wfD
    (hnq : 0 < 13 + programHelperCount hgpCompiledProgram)
    (hnumStab : 0 < programNumStab hgpCompiledProgram) :
    (vcgen (generatedFullProgramVCInputD hgpCompiledProgram 3 (by decide) hnq hnumStab)).denoteSlot
      .wf :=
  generatedFullProgram_vcgen_wfD hgpCompiledProgram 3 (by decide) hnq hnumStab

/-- **HGP partially passes VCGen (3/3): `syn`.** -/
theorem hgp_vcgen_synD
    (hnq : 0 < 13 + programHelperCount hgpCompiledProgram)
    (hnumStab : 0 < programNumStab hgpCompiledProgram) :
    (vcgen (generatedFullProgramVCInputD hgpCompiledProgram 3 (by decide) hnq hnumStab)).denoteSlot
      .syn :=
  generatedFullProgram_vcgen_synD hgpCompiledProgram 3 (by decide) hnq hnumStab

end QStab.QClifford.Compile
