import QStab.QClifford.Compile.HGPSchemeFramework
import QStab.QClifford.Compile.ShorClassify

/-!
# Flag-extraction HGP compiled bar-Z distance (framework instance)

The Flag scheme shares a single ancilla `anc` across all slots (like NZ), with a
`flag` qubit whose two `cnot flag anc` couplings bracket the schedule.  From the
data block's point of view the flag decorations are inert: the flag is a CNOT
*control* onto `anc` (so it never backflows onto data), and it is reset and
measured; the shared ancilla stays `Z`-free throughout, so the data couplings
preserve data.  Hence the flag block preserves data unconditionally — the
`LeafClean` witness — and every fault's data residual is weight `≤ 1` or an
anc-`Z` suffix hook (`dominatedByScheduleHook`), exactly as for NZ.

Everything goes through `compileGadgetBlock .Flag` — the syntactic scheme
compilation — reusing the NZ per-gate / chain lemmas.
-/

namespace QStab.QClifford.Compile

open QStab.QClifford
open QHL QHL.CodeHGPSchedule
open QHL.Source.Examples.HGP QHL.Source.Examples.HGPUnionSpec QStab.Examples.HGPParametric

/-! ## `anc`-Z-free is kept by a `zParitySlot` chain -/

/-- The whole `zParitySlots` chain keeps the ancilla `Z`-free. -/
theorem zParitySlots_keeps_ancZfree {nq : Nat} (anc : Fin nq) :
    ∀ (slots : List (ScheduledPauli nq)), (∀ s ∈ slots, s.qubit ≠ anc) →
      ∀ es : ErrorState nq, zPart (es.paulis anc) = Pauli.I →
        zPart ((propagateCircuit (eraseFaults ((slots.map (zParitySlot anc)).flatten)) es).paulis
          anc) = Pauli.I := by
  intro slots
  induction slots with
  | nil => intro _ es h; simpa [propagateCircuit] using h
  | cons s rest ih =>
      intro hq es hanc
      have hsq : s.qubit ≠ anc := hq s List.mem_cons_self
      have hrest : ∀ s' ∈ rest, s'.qubit ≠ anc := fun s' h => hq s' (List.mem_cons_of_mem _ h)
      have hcirc : eraseFaults (((s :: rest).map (zParitySlot anc)).flatten) =
          eraseFaults (zParitySlot anc s) ++
            eraseFaults ((rest.map (zParitySlot anc)).flatten) := by
        simp only [List.map_cons, List.flatten_cons, eraseFaults_append]
      rw [hcirc, QHL.Target.propagateCircuit_append]
      exact ih hrest _ (zParitySlot_keeps_ancZfree anc s hsq es hanc)

/-! ## Per-gate helpers on the flag couplings -/

/-- `cnot c t` (target `t`) keeps `t` `Z`-free when the control has no relevant
change: `zPart` of the target becomes `zPart` (via the incoming control's
`xPart`), so a `Z`-free target stays `Z`-free. -/
theorem cnot_target_keeps_Zfree {nq : Nat} (c t : Fin nq) (h : c ≠ t) (es : ErrorState nq)
    (ht : zPart (es.paulis t) = Pauli.I) :
    zPart ((propagateGate (Gate.cnot c t h) es).paulis t) = Pauli.I := by
  rw [propagateGate_cnot_target]
  exact zPart_pauliMul_xPart ht

/-! ## The block equation and its qubits -/

/-- The compiled Flag gadget block is `compileFlagOrdered` over the lifted
schedule and the block's two helpers `anc`, `flag`. -/
theorem compileGadgetBlock_Flag_eq {n total : Nat} (sigma : RuleSchedule n)
    (start : Nat) (hfit : start + helperCount Scheme.Flag sigma ≤ total) :
    compileGadgetBlock Scheme.Flag sigma start hfit
      = compileFlagOrdered (liftSchedule (k := total) sigma)
          (blockHelperQ n total start 2 hfit ⟨0, by decide⟩)
          (blockHelperQ n total start 2 hfit ⟨1, by decide⟩) := rfl

/-! ## Data preservation for the flag block -/

/-- A `zParitySlot` chain preserves every qubit `d ≠ anc` when the ancilla is
`Z`-free (packaging the NZ lemma for a flatten). -/
theorem zParitySlots_preserves_data' {nq : Nat} (anc : Fin nq)
    (slots : List (ScheduledPauli nq)) (hq : ∀ s ∈ slots, s.qubit ≠ anc)
    (es : ErrorState nq) (hanc : zPart (es.paulis anc) = Pauli.I) (d : Fin nq) (hd : d ≠ anc) :
    (propagateCircuit (eraseFaults ((slots.map (zParitySlot anc)).flatten)) es).paulis d
      = es.paulis d :=
  zParitySlots_preserves_data anc slots hq es hanc d hd

/-- **The flag block preserves every non-helper qubit** from a state with a
`Z`-free ancilla: the flag decorations are inert on data (flag is a CNOT control
and is reset/measured), the shared ancilla stays `Z`-free, and the data
couplings preserve data. -/
theorem compileFlagOrdered_preserves_data {nq : Nat} (sigma : RuleSchedule nq)
    (anc flag : Fin nq) (haf : flag ≠ anc)
    (hslots : ∀ s ∈ sigma.slots, s.qubit ≠ anc)
    (es : ErrorState nq) (hancZ : zPart (es.paulis anc) = Pauli.I)
    (d : Fin nq) (hda : d ≠ anc) (hdf : d ≠ flag) :
    (propagateCircuit (eraseFaults (compileFlagOrdered sigma anc flag)) es).paulis d
      = es.paulis d := by
  have htake : ∀ s ∈ sigma.slots.take (sigma.slots.length / 2), s.qubit ≠ anc :=
    fun s hs => hslots s (List.mem_of_mem_take hs)
  have hdrop : ∀ s ∈ sigma.slots.drop (sigma.slots.length / 2), s.qubit ≠ anc :=
    fun s hs => hslots s (List.mem_of_mem_drop hs)
  show (propagateCircuit (eraseFaults
    (prep0 anc ++ prepP flag ++
      ((sigma.slots.take (sigma.slots.length / 2)).map (zParitySlot anc)).flatten ++
      cnot flag anc ++
      ((sigma.slots.drop (sigma.slots.length / 2)).map (zParitySlot anc)).flatten ++
      cnot flag anc ++ flagMeasZ anc ++ hadamard flag ++ flagMeasZ flag)) es).paulis d = es.paulis d
  simp only [eraseFaults_append, QHL.Target.propagateCircuit_append]
  -- erase forms of the atomic builders
  have hcnot : eraseFaults (cnot flag anc) = [Gate.cnot flag anc haf] := by
    simp [cnot, haf, eraseFaults]
  -- s1 : prep0 anc
  set s1 := propagateCircuit (eraseFaults (prep0 anc)) es with hs1
  have hs1d : s1.paulis d = es.paulis d := by
    rw [hs1]; simp only [prep0, eraseFaults, propagateCircuit]
    exact propagateGate_prepZero_paulis_ne anc es d hda
  have hs1Z : zPart (s1.paulis anc) = Pauli.I := by
    rw [hs1]; simp only [prep0, eraseFaults, propagateCircuit, propagateGate_prepZero_self]; rfl
  -- s2 : prepP flag
  set s2 := propagateCircuit (eraseFaults (prepP flag)) s1 with hs2
  have hs2d : s2.paulis d = es.paulis d := by
    rw [hs2]; simp only [prepP, eraseFaults, propagateCircuit]
    rw [propagateGate_prepPlus_paulis_ne flag s1 d hdf, hs1d]
  have hs2Z : zPart (s2.paulis anc) = Pauli.I := by
    rw [hs2]; simp only [prepP, eraseFaults, propagateCircuit]
    rw [propagateGate_prepPlus_paulis_ne flag s1 anc (Ne.symm haf), hs1Z]
  -- s3 : take.zPS
  set s3 := propagateCircuit
    (eraseFaults ((sigma.slots.take (sigma.slots.length / 2)).map (zParitySlot anc)).flatten)
    s2 with hs3
  have hs3d : s3.paulis d = es.paulis d := by
    rw [hs3, zParitySlots_preserves_data' anc _ htake s2 hs2Z d hda, hs2d]
  have hs3Z : zPart (s3.paulis anc) = Pauli.I := by
    rw [hs3]; exact zParitySlots_keeps_ancZfree anc _ htake s2 hs2Z
  -- s4 : cnot flag anc
  set s4 := propagateCircuit (eraseFaults (cnot flag anc)) s3 with hs4
  have hs4d : s4.paulis d = es.paulis d := by
    rw [hs4, hcnot]; simp only [propagateCircuit]
    rw [propagateGate_cnot_paulis_ne flag anc haf s3 d hdf hda, hs3d]
  have hs4Z : zPart (s4.paulis anc) = Pauli.I := by
    rw [hs4, hcnot]; simp only [propagateCircuit]
    exact cnot_target_keeps_Zfree flag anc haf s3 hs3Z
  -- s5 : drop.zPS
  set s5 := propagateCircuit
    (eraseFaults ((sigma.slots.drop (sigma.slots.length / 2)).map (zParitySlot anc)).flatten)
    s4 with hs5
  have hs5d : s5.paulis d = es.paulis d := by
    rw [hs5, zParitySlots_preserves_data' anc _ hdrop s4 hs4Z d hda, hs4d]
  -- s6 : cnot flag anc
  set s6 := propagateCircuit (eraseFaults (cnot flag anc)) s5 with hs6
  have hs6d : s6.paulis d = es.paulis d := by
    rw [hs6, hcnot]; simp only [propagateCircuit]
    rw [propagateGate_cnot_paulis_ne flag anc haf s5 d hdf hda, hs5d]
  -- s7 : flagMeasZ anc
  set s7 := propagateCircuit (eraseFaults (flagMeasZ anc)) s6 with hs7
  have hs7d : s7.paulis d = es.paulis d := by
    rw [hs7]; simp only [flagMeasZ, eraseFaults, propagateCircuit, propagateGate_measZ_paulis]
    exact hs6d
  -- s8 : hadamard flag
  set s8 := propagateCircuit (eraseFaults (hadamard flag)) s7 with hs8
  have hs8d : s8.paulis d = es.paulis d := by
    rw [hs8]; simp only [hadamard, eraseFaults, propagateCircuit]
    rw [propagateGate_hadamard_paulis_ne flag s7 d hdf, hs7d]
  -- s9 : flagMeasZ flag
  simp only [flagMeasZ, eraseFaults, propagateCircuit, propagateGate_measZ_paulis]
  exact hs8d

/-! ## Block shape facts + the `LeafClean` fields -/

/-- Value of a block helper `⟨j⟩`. -/
theorem blockHelperQ_flag_val {n total start : Nat} {hfit : start + 2 ≤ total}
    (j : Fin 2) : (blockHelperQ n total start 2 hfit j).val = n + start + j.val := by
  simp only [blockHelperQ]

/-- The lifted slot qubits are data qubits (`< n`), hence `≠ anc`/`flag`. -/
theorem flag_lifted_slots_data {n total : Nat} (sigma : RuleSchedule n) :
    ∀ s ∈ (liftSchedule (k := total) sigma).slots, s.qubit.val < n := by
  intro s hs
  simp only [liftSchedule, List.mem_map] at hs
  obtain ⟨s0, _, hseq⟩ := hs
  rw [← hseq]; simp only [liftSlot, freshDataQ_val]; exact s0.qubit.isLt

/-- Acts-below (the `LeafClean` first field) for the Flag block. -/
theorem flagBlock_cab {n total : Nat} (sigma : RuleSchedule n) (start : Nat)
    (hfit : start + helperCount Scheme.Flag sigma ≤ total) :
    circuitActsBelow (eraseFaults (compileGadgetBlock Scheme.Flag sigma start hfit))
      (n + start + helperCount Scheme.Flag sigma) := by
  rw [compileGadgetBlock_Flag_eq]
  have hw : helperCount Scheme.Flag sigma = 2 := rfl
  set anc := blockHelperQ n total start 2 hfit ⟨0, by decide⟩ with hanc
  set flag := blockHelperQ n total start 2 hfit ⟨1, by decide⟩ with hflag
  have hancL : anc.val < n + start + helperCount Scheme.Flag sigma := by
    rw [hanc, blockHelperQ_flag_val, hw]; omega
  have hflagL : flag.val < n + start + helperCount Scheme.Flag sigma := by
    rw [hflag, blockHelperQ_flag_val, hw]; omega
  have hslotL : ∀ s ∈ (liftSchedule (k := total) sigma).slots,
      s.qubit.val < n + start + helperCount Scheme.Flag sigma :=
    fun s hs => by have := flag_lifted_slots_data (total := total) sigma s hs; omega
  set σ' := liftSchedule (k := total) sigma with hσ'
  show circuitActsBelow (eraseFaults (
    prep0 anc ++ prepP flag ++ ((σ'.slots.take (σ'.slots.length / 2)).map (zParitySlot anc)).flatten
      ++ cnot flag anc ++ ((σ'.slots.drop (σ'.slots.length / 2)).map (zParitySlot anc)).flatten
      ++ cnot flag anc ++ flagMeasZ anc ++ hadamard flag ++ flagMeasZ flag)) _
  simp only [eraseFaults_append]
  have hzps : ∀ (l : List (ScheduledPauli (n + total))),
      (∀ s ∈ l, s.qubit.val < n + start + helperCount Scheme.Flag sigma) →
      circuitActsBelow (eraseFaults ((l.map (zParitySlot anc)).flatten))
        (n + start + helperCount Scheme.Flag sigma) := by
    intro l hl
    exact cab_erase_flatten_map l (zParitySlot anc)
      (fun s hs => cab_erase_zParitySlot anc s hancL (hl s hs))
  refine cab_append (cab_append (cab_append (cab_append (cab_append (cab_append
    (cab_append (cab_append (cab_erase_prep0 anc hancL) (cab_erase_prepP flag hflagL))
      (hzps _ (fun s hs => hslotL s (List.mem_of_mem_take hs))))
      (cab_erase_cnot flag anc hflagL hancL))
      (hzps _ (fun s hs => hslotL s (List.mem_of_mem_drop hs))))
      (cab_erase_cnot flag anc hflagL hancL))
      (cab_erase_flagMeasZ anc hancL))
      (cab_erase_hadamard flag hflagL))
      (cab_erase_flagMeasZ flag hflagL)

/-- Preservation at floor `n + start` for the Flag block: with the two helpers
clean on entry (so `anc` is `Z`-free), the block preserves data. -/
theorem flagBlock_PDA {n total : Nat} (sigma : RuleSchedule n) (start : Nat)
    (hfit : start + helperCount Scheme.Flag sigma ≤ total) :
    PreservesDataAbove (eraseFaults (compileGadgetBlock Scheme.Flag sigma start hfit))
      (n + start) := by
  intro es hc d hd
  rw [compileGadgetBlock_Flag_eq]
  set anc := blockHelperQ n total start 2 hfit ⟨0, by decide⟩ with hanc
  set flag := blockHelperQ n total start 2 hfit ⟨1, by decide⟩ with hflag
  have hancZ : zPart (es.paulis anc) = Pauli.I := by
    have : es.paulis anc = Pauli.I := hc anc (by rw [hanc, blockHelperQ_flag_val]; omega)
    rw [this]; rfl
  have haf : flag ≠ anc := by
    rw [hanc, hflag]; refine Fin.ne_of_val_ne ?_; simp only [blockHelperQ_flag_val]; omega
  have hslots : ∀ s ∈ (liftSchedule (k := total) sigma).slots, s.qubit ≠ anc := by
    intro s hs
    refine Fin.ne_of_val_ne ?_
    have := flag_lifted_slots_data (total := total) sigma s hs
    rw [hanc, blockHelperQ_flag_val]; omega
  have hda : d ≠ anc := by
    refine Fin.ne_of_val_ne ?_; rw [hanc, blockHelperQ_flag_val]; omega
  have hdf : d ≠ flag := by
    refine Fin.ne_of_val_ne ?_; rw [hflag, blockHelperQ_flag_val]; omega
  exact compileFlagOrdered_preserves_data _ anc flag haf hslots es hancZ d hda hdf

/-! ## The Flag `LeafClean` witness -/

theorem hgpFlag_leafClean (d : Nat) (hd : 2 ≤ d) :
    LeafClean (total := hgpSchemeHelpers Scheme.Flag d) (hgpSchemeProgram Scheme.Flag d) := by
  intro sc sg hml st hf
  obtain ⟨i, rfl, rfl⟩ := hgpSchemeProgram_measLeaf Scheme.Flag d hd sc sg hml
  exact ⟨flagBlock_cab _ _ _, flagBlock_PDA _ _ _⟩

/-! ## Generalized anc-fault chain hook (helpers allowed in the chain)

The Flag block's ancilla chain contains the `flag` **helper** control (from
`cnot flag anc`), so `chain_residual_hook`'s data-only requirement is too
strong.  This drops it: the head control site is now split — a *data* control
gives a weight-`≤ 1` residual (excluded), a *helper* control gives a weight-`0`
residual (excluded) — and the anc site still yields the `Z` suffix hook (helper
entries in the suffix are invisible to the data residual). -/
theorem chain_residual_hook_gen {P : QECParams} {total : Nat} (a : Fin (P.n + total))
    (hancHelper : P.n ≤ a.val) (tail : FCircuit (P.n + total))
    (htail : ∀ (es : ErrorState (P.n + total)) (q'' : Fin P.n),
      (propagateCircuit (eraseFaults tail) es).paulis (freshDataQ P.n total q'') =
        es.paulis (freshDataQ P.n total q'')) :
    ∀ (qs : List (Fin (P.n + total))), a ∉ qs → qs.Nodup →
      ∀ (cursor : Nat) (site : PCC.ErrLocWithContext (P.n + total)) (p : Pauli) (hp : p ≠ Pauli.I),
        site ∈ prefixErrLocsWithContextAux cursor ((qs.map (fun q => cnot q a)).flatten) tail →
        ErrorVec.weight (targetFaultDataResidual P ⟨site, p, hp⟩) ≠ 0 →
        ErrorVec.weight (targetFaultDataResidual P ⟨site, p, hp⟩) ≠ 1 →
        ∃ k, targetFaultDataResidual P ⟨site, p, hp⟩ =
          fun q' => if freshDataQ P.n total q' ∈ qs.drop k then Pauli.Z else Pauli.I := by
  intro qs
  induction qs with
  | nil =>
      intro _ _ cursor site p hp hsite _ _
      simp [prefixErrLocsWithContextAux] at hsite
  | cons q qs' ih =>
      intro hanc hnd cursor site p hp hsite hw0 hw1
      have hqmem : q ∈ (q :: qs') := List.mem_cons_self
      have hqa : q ≠ a := fun h => hanc (h ▸ hqmem)
      have hanc' : a ∉ qs' := fun h => hanc (List.mem_cons_of_mem _ h)
      have hnd' : qs'.Nodup := (List.nodup_cons.mp hnd).2
      rw [show ((q :: qs').map (fun q => cnot q a)).flatten =
            cnot q a ++ (qs'.map (fun q => cnot q a)).flatten from by
            simp [List.map_cons, List.flatten_cons],
          prefixErrLocs_append] at hsite
      simp only [List.mem_append] at hsite
      have hsuffix :
          Gate.cnot q a hqa :: eraseFaults ((qs'.map (fun q => cnot q a)).flatten ++ tail) =
            eraseFaults (((q :: qs').map (fun q => cnot q a)).flatten) ++ eraseFaults tail := by
        rw [eraseFaults_append, eraseFaults_cnotChain_cons a q hqa, List.cons_append]
      rcases hsite with hhead | hrec
      · rw [prefixErrLocs_cnot a q hqa] at hhead
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hhead
        rcases hhead with rfl | rfl
        · -- head control site `q`: data ⇒ weight ≤ 1, helper ⇒ weight 0; both excluded
          exfalso
          have hres : targetFaultDataResidual P
              ⟨⟨q, Gate.cnot q a hqa :: eraseFaults ((qs'.map (fun q => cnot q a)).flatten ++ tail),
                cursor⟩, p, hp⟩ =
              fun q' => if freshDataQ P.n total q' = q then p else Pauli.I := by
            funext q'
            show (propagateCircuit
                (Gate.cnot q a hqa :: eraseFaults ((qs'.map (fun q => cnot q a)).flatten ++ tail))
                ((PCC.cleanAtDetector cursor).inject q p)).paulis (freshDataQ P.n total q') = _
            rw [hsuffix]
            exact residual_data_chainTail a (q :: qs') hanc hancHelper (eraseFaults tail) htail
              cursor q (List.mem_cons.mpr (Or.inl rfl)) p q'
          by_cases hqd : q.val < P.n
          · have hle : ErrorVec.weight
                (fun q' => if freshDataQ P.n total q' = q then p else Pauli.I) ≤ 1 := by
              apply weight_le_one_of_single _ ⟨q.val, hqd⟩
              intro q'' hne
              have hfne : freshDataQ P.n total q'' ≠ q := by
                intro h; apply hne; apply Fin.ext
                simpa [freshDataQ_val] using congrArg Fin.val h
              rw [if_neg hfne]
            rw [hres] at hw0 hw1
            omega
          · apply hw0
            rw [hres]
            apply weight_zero_of_allI
            intro q'
            refine if_neg (fun h => hqd ?_)
            have hval : q.val = q'.val := by rw [← h]; simp [freshDataQ_val]
            rw [hval]; exact q'.isLt
        · -- anc site: `zPart p` on the whole current suffix
          have hres : targetFaultDataResidual P
              ⟨⟨a, Gate.cnot q a hqa :: eraseFaults ((qs'.map (fun q => cnot q a)).flatten ++ tail),
                cursor⟩, p, hp⟩ =
              fun q' => if freshDataQ P.n total q' ∈ (q :: qs') then zPart p else Pauli.I := by
            funext q'
            show (propagateCircuit
                (Gate.cnot q a hqa :: eraseFaults ((qs'.map (fun q => cnot q a)).flatten ++ tail))
                ((PCC.cleanAtDetector cursor).inject a p)).paulis (freshDataQ P.n total q') = _
            rw [hsuffix]
            exact residual_anc_chainTail a (q :: qs') hanc hnd hancHelper (eraseFaults tail) htail
              cursor p q'
          by_cases hzp : zPart p = Pauli.I
          · exfalso; apply hw0; apply weight_zero_of_allI; intro q'; rw [hres]; simp [hzp]
          · have hzZ : zPart p = Pauli.Z := by cases p <;> simp_all [zPart]
            refine ⟨0, ?_⟩
            rw [hres]; funext q'; simp [hzZ, List.drop_zero]
      · obtain ⟨k, hk⟩ := ih hanc' hnd' _ site p hp hrec hw0 hw1
        exact ⟨k + 1, hk⟩

/-! ## Mixed-kind ancilla chain (for the X-side, with the bare `flag` couplings)

The X-check flag block interleaves H-sandwiched data couplings (`zParitySlot .X`)
with the bare `cnot flag anc = zParitySlot .Z`.  A single lemma over
`zParitySlot`s of *arbitrary* kind handles it: the ancilla is always the CNOT
target, so it **keeps** its Pauli through every coupling, depositing on each
control qubit the kind's transform of `zPart w`. -/

/-- The Pauli a `zParitySlot` of kind `k` deposits onto its (clean) data qubit
from an ancilla carrying `w`: `Z` backflows `zPart w`; `X`'s H-sandwich rotates
it to `hadamardAction (zPart w)`. -/
def kindTransform : XZPauli → Pauli → Pauli
  | .Z, w => zPart w
  | .X, w => hadamardAction (zPart w)

/-- **One mixed-kind coupling**: from an ancilla carrying `w` and a clean data
qubit, `zParitySlot anc s` puts `kindTransform s.kind w` on `s.qubit`, keeps `w`
on `anc`, and leaves every other qubit fixed. -/
theorem zParitySlot_anc_deposit {nq : Nat} (anc : Fin nq) (s : ScheduledPauli nq)
    (hqa : s.qubit ≠ anc) (es : ErrorState nq) (w : Pauli) (hanc : es.paulis anc = w)
    (hq : es.paulis s.qubit = Pauli.I) :
    (propagateCircuit (eraseFaults (zParitySlot anc s)) es).paulis s.qubit
        = kindTransform s.kind w
      ∧ (propagateCircuit (eraseFaults (zParitySlot anc s)) es).paulis anc = w
      ∧ ∀ i : Fin nq, i ≠ s.qubit → i ≠ anc →
          (propagateCircuit (eraseFaults (zParitySlot anc s)) es).paulis i = es.paulis i := by
  obtain ⟨sk, sq⟩ := s
  cases sk with
  | Z =>
      have hc : eraseFaults (zParitySlot anc ⟨.Z, sq⟩) = [Gate.cnot sq anc hqa] := by
        simp [zParitySlot, cnot, hqa, eraseFaults]
      rw [hc]; simp only [propagateCircuit]
      refine ⟨?_, ?_, ?_⟩
      · rw [propagateGate_cnot_control sq anc hqa, hanc, hq]; simp [kindTransform, pauliMul_I_right]
      · rw [propagateGate_cnot_target sq anc hqa, hq, hanc]; simp [xPart, pauliMul]
      · intro i hiq hia
        exact propagateGate_cnot_paulis_ne sq anc hqa es i hiq hia
  | X =>
      have hc : eraseFaults (zParitySlot anc ⟨.X, sq⟩) =
          [Gate.hadamard sq, Gate.cnot sq anc hqa, Gate.hadamard sq] := by
        simp [zParitySlot, hadamard, cnot, hqa, eraseFaults]
      rw [hc]; simp only [propagateCircuit]
      set e1 := propagateGate (Gate.hadamard sq) es with he1
      have he1q : e1.paulis sq = Pauli.I := by
        rw [he1, propagateGate_hadamard_self, hq]; rfl
      have he1a : e1.paulis anc = w := by
        rw [he1, propagateGate_hadamard_paulis_ne sq es anc (Ne.symm hqa), hanc]
      set e2 := propagateGate (Gate.cnot sq anc hqa) e1 with he2
      have he2q : e2.paulis sq = zPart w := by
        rw [he2, propagateGate_cnot_control sq anc hqa, he1a, he1q]; simp [pauliMul_I_right]
      have he2a : e2.paulis anc = w := by
        rw [he2, propagateGate_cnot_target sq anc hqa, he1q, he1a]; simp [xPart, pauliMul]
      refine ⟨?_, ?_, ?_⟩
      · rw [propagateGate_hadamard_self, he2q]; rfl
      · rw [propagateGate_hadamard_paulis_ne sq e2 anc (Ne.symm hqa), he2a]
      · intro i hiq hia
        rw [propagateGate_hadamard_paulis_ne sq e2 i hiq, he2,
          propagateGate_cnot_paulis_ne sq anc hqa e1 i hiq hia, he1,
          propagateGate_hadamard_paulis_ne sq es i hiq]

/-- **The mixed-kind ancilla chain**: from `w@anc` and clean data, propagating a
list of `zParitySlot`s deposits `kindTransform s.kind w` on each slot's qubit,
keeps `w` on `anc`, and fixes every off-chain qubit — the ancilla carrying `w`
throughout. -/
theorem propagate_zpsChain_anc {nq : Nat} (anc : Fin nq) (w : Pauli) :
    ∀ (slots : List (ScheduledPauli nq)), (∀ s ∈ slots, s.qubit ≠ anc) →
      (slots.map (·.qubit)).Nodup →
      ∀ (es : ErrorState nq), es.paulis anc = w → (∀ s ∈ slots, es.paulis s.qubit = Pauli.I) →
        (∀ s ∈ slots, (propagateCircuit (eraseFaults ((slots.map (zParitySlot anc)).flatten)) es).paulis
            s.qubit = kindTransform s.kind w)
        ∧ (propagateCircuit (eraseFaults ((slots.map (zParitySlot anc)).flatten)) es).paulis anc = w
        ∧ (∀ i : Fin nq, i ≠ anc → i ∉ slots.map (·.qubit) →
            (propagateCircuit (eraseFaults ((slots.map (zParitySlot anc)).flatten)) es).paulis i
              = es.paulis i) := by
  intro slots
  induction slots with
  | nil => intro _ _ es hanc _; exact ⟨fun s hs => absurd hs (List.not_mem_nil), by simpa [propagateCircuit] using hanc, fun i _ _ => by simp [propagateCircuit]⟩
  | cons s0 rest ih =>
      intro hqa hnd es hanc hclean
      have hs0q : s0.qubit ≠ anc := hqa s0 List.mem_cons_self
      have hcirc : eraseFaults (((s0 :: rest).map (zParitySlot anc)).flatten)
          = eraseFaults (zParitySlot anc s0) ++
            eraseFaults ((rest.map (zParitySlot anc)).flatten) := by
        simp only [List.map_cons, List.flatten_cons, eraseFaults_append]
      have hnd0 : (s0.qubit :: rest.map (·.qubit)).Nodup := hnd
      have hfresh : s0.qubit ∉ rest.map (·.qubit) := (List.nodup_cons.mp hnd0).1
      have hnd' : (rest.map (·.qubit)).Nodup := (List.nodup_cons.mp hnd0).2
      have hqa' : ∀ s ∈ rest, s.qubit ≠ anc := fun s hs => hqa s (List.mem_cons_of_mem _ hs)
      obtain ⟨hd0q, hd0a, hd0o⟩ := zParitySlot_anc_deposit anc s0 hs0q es w hanc
        (hclean s0 List.mem_cons_self)
      set e1 := propagateCircuit (eraseFaults (zParitySlot anc s0)) es with he1
      have he1clean : ∀ s ∈ rest, e1.paulis s.qubit = Pauli.I := by
        intro s hs
        have hne : s.qubit ≠ s0.qubit := fun h =>
          hfresh (h ▸ List.mem_map_of_mem (f := (·.qubit)) hs)
        rw [hd0o s.qubit hne (hqa' s hs)]
        exact hclean s (List.mem_cons_of_mem _ hs)
      obtain ⟨hrq, hra, hro⟩ := ih hqa' hnd' e1 hd0a he1clean
      rw [hcirc, QHL.Target.propagateCircuit_append]
      refine ⟨?_, ?_, ?_⟩
      · intro s hs
        rcases List.mem_cons.mp hs with rfl | hs'
        · rw [hro s.qubit hs0q hfresh]; exact hd0q
        · exact hrq s hs'
      · rw [hra]
      · intro i hia himem
        have hi0 : i ≠ s0.qubit := fun h => himem (h ▸ List.mem_cons_self)
        have hirest : i ∉ rest.map (·.qubit) := fun h => himem (List.mem_cons_of_mem _ h)
        rw [hro i hia hirest, hd0o i hi0 hia]

/--
info: 'QStab.QClifford.Compile.propagate_zpsChain_anc' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms propagate_zpsChain_anc

/--
info: 'QStab.QClifford.Compile.hgpFlag_leafClean' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hgpFlag_leafClean

end QStab.QClifford.Compile
