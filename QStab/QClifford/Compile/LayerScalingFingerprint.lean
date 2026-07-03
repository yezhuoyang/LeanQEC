import QStab.QClifford.Compile.HGPNZSafe
import QStab.QClifford.Compile.SurfaceNZReachFold

/-!
# Layer-size scaling fingerprints

Kernel-pinned headline numbers for the layer-size study (full data and fits
in the untracked measurement harness): per code, the QStab measurement-leaf
count (`programNumStab`), the compiled QClifford instruction count, and the
fault-site count, at `d = 3` and `d = 11`.

Source-layer constancy is structural, not measured: the object programs
(`HGP.code`, `hgpOrderProg`/`hgpLenProg`, `Surface.code`) are closed terms in
which `d` does not occur, so their size is the same fixed constant for every
distance.  The QStab layer grows as the leaf count `Θ(d²)` with `O(1)`-size
per-leaf schedules; the QClifford layer is `Θ(d²)` with strictly larger
constants (≈ 6 instructions per scheduled coupling plus per-gadget
prep/measure overhead).  The reach-script length equals the fault-site count
equals the `errLoc` count, by construction.
-/

namespace QStab.QClifford.Compile

open QStab.QClifford QStab.QClifford.PCC
open QStab.QClifford.PCC.SurfaceNZ

private def scalingRow {n : Nat} (program : XZProgram n) : Nat × Nat × Nat :=
  (programNumStab program, (compileProgram program).length,
    errLocCount (compileProgram program))

/-- info: (12, 248, 144) -/
#guard_msgs in
#eval scalingRow (hgpXZProgram 3)

/-- info: (220, 5080, 2960) -/
#guard_msgs in
#eval scalingRow (hgpXZProgram 11)

/-- info: (8, 152, 88) -/
#guard_msgs in
#eval scalingRow (surfaceXZProgram 3 (by omega))

/-- info: (120, 2680, 1560) -/
#guard_msgs in
#eval scalingRow (surfaceXZProgram 11 (by omega))

-- Script/site/errLoc agreement at the largest measured distance.
/-- info: true -/
#guard_msgs in
#eval ((hgpReachScript 11 (by omega)).length == 2960)
  && (((errLocsWithContext (compileProgram (hgpXZProgram 11))).length) == 2960)

end QStab.QClifford.Compile
