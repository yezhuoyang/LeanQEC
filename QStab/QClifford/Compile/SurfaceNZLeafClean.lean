import QStab.QClifford.Compile.SurfaceHValid
import QStab.QClifford.Compile.NZBackAction
import QStab.QClifford.Compile.SiteSplitGen
import QStab.QClifford.Compile.NZReachCalculus

/-!
# The surface `LeafClean` witness (NZ scheme)

The NZ analog of `hgpShor_leafClean`: every measurement leaf of `surfaceXZProgram`
(an all-NZ program) compiles to a gadget block that **acts below** its helper
ceiling and **preserves data** — the `LeafClean` bundle the generic
`compileProgramAux_site_split_gen` (hence `compiled_hvalid_of_classifier`) consumes.

Both halves reuse existing machinery through the **syntactic** `compileGadgetBlock`:
`nzBlock_cab` from the `cab_*` primitives, and the preservation half directly from
the (unconditional) `compileStandardOrdered_preserves_data`.  No lower-level circuit
is redefined; the proof goes through `compileGadgetBlock Scheme.NZ`.
-/

namespace QStab.QClifford.Compile

open QStab QStab.QClifford QStab.Examples.SurfaceParametric QStab.QClifford.PCC.SurfaceNZ

/-- One `zParitySlot` acts below `L` when its data qubit and the ancilla do. -/
theorem zParitySlot_cab {nq L : Nat} (anc : Fin nq) (slot : ScheduledPauli nq)
    (hanc : anc.val < L) (hq : slot.qubit.val < L) :
    circuitActsBelow (eraseFaults (zParitySlot anc slot)) L := by
  unfold zParitySlot
  cases slot.kind with
  | X =>
      rw [eraseFaults_append, eraseFaults_append]
      exact cab_append (cab_append (cab_erase_hadamard slot.qubit hq)
        (cab_erase_cnot slot.qubit anc hq hanc)) (cab_erase_hadamard slot.qubit hq)
  | Z => exact cab_erase_cnot slot.qubit anc hq hanc

/-- **The NZ gadget block acts below its helper ceiling.**  Every gate touches the
ancilla (`= n+start`) or a data qubit (`< n`), all below `n + start + 1`. -/
theorem nzBlock_cab {n total : Nat} (sigma : RuleSchedule n) (start : Nat)
    (hfit : start + helperCount Scheme.NZ sigma ≤ total) :
    circuitActsBelow (eraseFaults (compileGadgetBlock Scheme.NZ sigma start hfit))
      (n + start + helperCount Scheme.NZ sigma) := by
  rw [compileGadgetBlock_NZ_eq_nzBlock]
  have hw : helperCount Scheme.NZ sigma = 1 := rfl
  set anc := blockHelperQ n total start 1 hfit ⟨0, Nat.one_pos⟩ with hanc_def
  have hanc : anc.val < n + start + helperCount Scheme.NZ sigma := by
    rw [hanc_def]; simp only [blockHelperQ]; omega
  have hslots : ∀ s ∈ (liftSchedule (k := total) sigma).slots,
      s.qubit.val < n + start + helperCount Scheme.NZ sigma := by
    intro s hs
    simp only [liftSchedule, List.mem_map] at hs
    obtain ⟨s', _, rfl⟩ := hs
    simp only [liftSlot, freshDataQ_val]
    have := s'.qubit.isLt
    omega
  show circuitActsBelow (eraseFaults (prep0 anc
      ++ zParitySlotsCircuit anc (liftSchedule (k := total) sigma).slots ++ flagMeasZ anc)) _
  rw [eraseFaults_append, eraseFaults_append]
  refine cab_append (cab_append (cab_erase_prep0 anc hanc) ?_) (cab_erase_flagMeasZ anc hanc)
  unfold zParitySlotsCircuit
  rw [eraseFaults_flatten]
  refine cab_flatten ?_
  intro c hc
  rw [List.mem_map] at hc
  obtain ⟨c0, hc0, rfl⟩ := hc
  rw [List.mem_map] at hc0
  obtain ⟨slot, hslot, rfl⟩ := hc0
  exact zParitySlot_cab anc slot hanc (hslots slot hslot)

/-- **The surface `LeafClean` witness.**  Every leaf of `surfaceXZProgram` acts
below its helper ceiling (`nzBlock_cab`) and preserves data
(`compileStandardOrdered_preserves_data`, unconditional). -/
theorem surface_leafClean (d : Nat) (hd : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1) :
    LeafClean (total := programHelperCount (surfaceXZProgram d hd)) (surfaceXZProgram d hd) := by
  intro sc sg hml st hf
  obtain ⟨i, rfl, rfl⟩ := surfaceXZProgram_measLeaf d hd sc sg hml
  refine ⟨nzBlock_cab (nzSchedule d hd i) st hf, ?_⟩
  intro es _ dd hdd
  rw [compileGadgetBlock_NZ_eq_nzBlock]
  set anc := blockHelperQ (d * d) (programHelperCount (surfaceXZProgram d hd)) st 1 hf
    ⟨0, Nat.one_pos⟩ with hanc_def
  have hda : dd ≠ anc := by
    intro h; rw [h, hanc_def] at hdd; simp only [blockHelperQ] at hdd; omega
  have hslots_ne : ∀ s ∈ (liftSchedule (k := programHelperCount (surfaceXZProgram d hd))
      (nzSchedule d hd i)).slots, s.qubit ≠ anc := by
    intro s hs
    simp only [liftSchedule, List.mem_map] at hs
    obtain ⟨s', _, rfl⟩ := hs
    intro h
    rw [hanc_def] at h
    have : (liftSlot (k := programHelperCount (surfaceXZProgram d hd)) s').qubit.val = anc.val :=
      congrArg Fin.val h
    simp only [liftSlot, freshDataQ_val, hanc_def, blockHelperQ] at this
    have := s'.qubit.isLt
    omega
  exact compileStandardOrdered_preserves_data
    (liftSchedule (k := programHelperCount (surfaceXZProgram d hd)) (nzSchedule d hd i))
    anc hslots_ne es dd hda

end QStab.QClifford.Compile
