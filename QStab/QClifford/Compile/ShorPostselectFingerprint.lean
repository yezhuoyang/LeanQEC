import QStab.QClifford.Compile.VCBridge

/-!
# Shor post-selection wiring: kernel-pinned fingerprint

Confirmation (not construction): the post-selection machinery already exists
in the TCB spec and is populated per scheme by `compiledPostselectFlag`.  For
Shor, the verifier `flagMeasZ` is detector slot `0` of each gadget
(`compiledPostselectFlag .Shor = fun f => decide (f.val = 0)`), while the cat
readouts (slots `1..w`) stay ordinary syndrome detectors; `fullProgramCodeSpec`
propagates this into `spec.postselectFlag` via `fullProgramPostselectFlag`
(any-gadget aggregation), so `allPostselectionFlagsZero ⊆ allFlagsZero`
conditions every `failure`/`Safe` obligation on surviving post-selection.

NZ/Standard has `compiledPostselectFlag = fun _ => false` — no discards.

The pins below are the machine-checked statement that post-selection is wired:
on a two-gadget Shor program the verifier flags (global slots `0`, `3`) are
post-select and the cat/syndrome slots are not; the NZ control has none.  The
negative direction — a fault firing the verifier flag is post-selected out,
not a failure — is exercised by `verify_all`'s `overflag-reach-witness`.
-/

namespace QStab.QClifford.Compile

open QStab.QClifford QStab.QClifford.PCC

/-- Two-gadget Shor program over two data qubits (`w = 2` per gadget). -/
def shorPostselectProbeSched : RuleSchedule 2 :=
  RuleSchedule.uniform .Z [⟨0, by omega⟩, ⟨1, by omega⟩]

def shorPostselectProbeProg : XZProgram 2 :=
  .seq (.meas .Shor shorPostselectProbeSched) (.meas .Shor shorPostselectProbeSched)

def nzPostselectProbeProg : XZProgram 2 :=
  .seq (.meas .NZ shorPostselectProbeSched) (.meas .NZ shorPostselectProbeSched)

/-- Shor: post-select flags true exactly at the two verifier slots (`0`, `3`). -/
/-- info: [(0, true), (1, false), (2, false), (3, true), (4, false), (5, false)] -/
#guard_msgs in
#eval (List.finRange (programDetectorCount shorPostselectProbeProg)).map
  (fun f => (f.val, fullProgramPostselectFlag shorPostselectProbeProg f))

/-- NZ control: no post-selection. -/
/-- info: [(0, false), (1, false)] -/
#guard_msgs in
#eval (List.finRange (programDetectorCount nzPostselectProbeProg)).map
  (fun f => (f.val, fullProgramPostselectFlag nzPostselectProbeProg f))

end QStab.QClifford.Compile
