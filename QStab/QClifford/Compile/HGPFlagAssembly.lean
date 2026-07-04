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
    (es : ErrorState nq) (_hancZ : zPart (es.paulis anc) = Pauli.I)
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

/-! ## Gate locality of a `zParitySlot` and its errLocs -/

/-- The single errLoc of a compiled `hadamard`. -/
theorem prefixErrLocs_hadamard {nq : Nat} (q : Fin nq) (cursor : Nat) (tail : FCircuit nq) :
    prefixErrLocsWithContextAux cursor (hadamard q) tail =
      [⟨q, Gate.hadamard q :: eraseFaults tail, cursor⟩] := by
  simp [hadamard, prefixErrLocsWithContextAux, eraseFaults]

/-- `zParitySlot anc s = shorCouplingSlot s anc` (definitional, both kinds). -/
theorem zParitySlot_eq_shorCoupling {nq : Nat} (anc : Fin nq) (s : ScheduledPauli nq) :
    zParitySlot anc s = shorCouplingSlot s anc := by
  cases h : s.kind <;> simp [zParitySlot, shorCouplingSlot, h]

/-- Every erased gate of a `zParitySlot` acts only on `{s.qubit, anc}`. -/
theorem zParitySlot_gates_actOn {nq : Nat} (anc : Fin nq) (s : ScheduledPauli nq)
    (g : Gate nq) (hg : g ∈ eraseFaults (zParitySlot anc s)) :
    ∀ q : Fin nq, gateActsOn g q → q = s.qubit ∨ q = anc := by
  rw [zParitySlot_eq_shorCoupling] at hg
  intro q hq
  exact shorCouplingSlot_gates_actOn s anc g hg q hq

/-- errLoc markers of a `zParitySlot` lie in `{s.qubit, anc}`. -/
theorem zParitySlot_errLoc {nq : Nat} (anc : Fin nq) (s : ScheduledPauli nq) (q0 : Fin nq)
    (h : FInstr.errLoc q0 ∈ zParitySlot anc s) : q0 = s.qubit ∨ q0 = anc := by
  rw [zParitySlot_eq_shorCoupling] at h
  exact shorCouplingSlot_errLoc s anc q0 h

/-! ## The mixed-kind chain site classifier -/

/-- Pointwise: `kk.toPauli` on a subset of the chain's data qubits, identity
elsewhere — the chain-level shape of `dominatedByScheduleHook`. -/
def domHookChain {n : Nat} {total : Nat} (kk : XZPauli)
    (slots : List (ScheduledPauli (n + total))) (R : ErrorVec n) : Prop :=
  ∀ q' : Fin n, R q' = Pauli.I ∨
    (R q' = kk.toPauli ∧ freshDataQ n total q' ∈ slots.map (·.qubit))

/-- A `kindTransform kk p` is either `I` or the kind's Pauli `kk.toPauli`. -/
theorem kindTransform_mem (kk : XZPauli) (p : Pauli) :
    kindTransform kk p = Pauli.I ∨ kindTransform kk p = kk.toPauli := by
  cases kk <;> cases p <;> simp [kindTransform, zPart, hadamardAction, XZPauli.toPauli]

/-! ### The J-invariant: data-fault support via ancilla Z-freeness

A fault whose data residual is confined to one qubit `q0` and keeps the ancilla
`Z`-free is preserved by every gate of a `zParitySlot`/`cnot-to-anc` circuit
(all such cnots target `anc`, so a data control only ever deposits an `X`-part
on `anc`; `hadamard` on a clean qubit stays clean). -/

/-- One `zParitySlot` preserves the invariant "`anc` is `Z`-free and every data
qubit except `q0` is clean" — hence a fault at `q0` never spreads to other data. -/
theorem zParitySlot_keeps_offInvariant {nq : Nat} (anc : Fin nq) (s : ScheduledPauli nq)
    (hsa : s.qubit ≠ anc) (q0 : Fin nq) (es : ErrorState nq)
    (hancZ : zPart (es.paulis anc) = Pauli.I)
    (hoff : ∀ d : Fin nq, d ≠ anc → d ≠ q0 → es.paulis d = Pauli.I) :
    zPart ((propagateCircuit (eraseFaults (zParitySlot anc s)) es).paulis anc) = Pauli.I
      ∧ ∀ d : Fin nq, d ≠ anc → d ≠ q0 →
          (propagateCircuit (eraseFaults (zParitySlot anc s)) es).paulis d = Pauli.I := by
  refine ⟨zParitySlot_keeps_ancZfree anc s hsa es hancZ, ?_⟩
  intro d hda hdq
  rw [zParitySlot_preserves_data anc s hsa es hancZ d hda]
  exact hoff d hda hdq

/-- The whole `zParitySlot` chain preserves the "off-`q0` clean + `anc` Z-free"
invariant. -/
theorem zpsChain_keeps_offInvariant {nq : Nat} (anc : Fin nq) (q0 : Fin nq) :
    ∀ (slots : List (ScheduledPauli nq)), (∀ s ∈ slots, s.qubit ≠ anc) →
      ∀ es : ErrorState nq, zPart (es.paulis anc) = Pauli.I →
        (∀ d : Fin nq, d ≠ anc → d ≠ q0 → es.paulis d = Pauli.I) →
        ∀ d : Fin nq, d ≠ anc → d ≠ q0 →
          (propagateCircuit (eraseFaults ((slots.map (zParitySlot anc)).flatten)) es).paulis d
            = Pauli.I := by
  intro slots
  induction slots with
  | nil => intro _ es _ hoff d hda hdq; simpa [propagateCircuit] using hoff d hda hdq
  | cons s0 rest ih =>
      intro hsa es hancZ hoff d hda hdq
      have hs0 : s0.qubit ≠ anc := hsa s0 List.mem_cons_self
      have hcirc : eraseFaults (((s0 :: rest).map (zParitySlot anc)).flatten)
          = eraseFaults (zParitySlot anc s0) ++
            eraseFaults ((rest.map (zParitySlot anc)).flatten) := by
        simp only [List.map_cons, List.flatten_cons, eraseFaults_append]
      rw [hcirc, QHL.Target.propagateCircuit_append]
      obtain ⟨hZ1, hoff1⟩ := zParitySlot_keeps_offInvariant anc s0 hs0 q0 es hancZ hoff
      exact ih (fun s hs => hsa s (List.mem_cons_of_mem _ hs)) _ hZ1 hoff1 d hda hdq

/-! ### Per-gate `offInvariant` maintenance for the head-slot leading gates

The head slot's errloc suffix drops the pre-errloc gates, so the residual runs a
*partial* slot before the rest chain.  A `hadamard` (off `anc`) and a
`cnot _ anc` each maintain "`anc` `Z`-free and every data qubit but `q0` clean",
so the partial leading gates establish the `offInvariant` at `es_lead`. -/

/-- `hadamard q` (with `q ≠ anc`) maintains the off-`q0` invariant. -/
theorem hadamard_keeps_offInvariant {nq : Nat} (anc q0 : Fin nq) (q : Fin nq) (hqa : q ≠ anc)
    (es : ErrorState nq) (hZ : zPart (es.paulis anc) = Pauli.I)
    (hoff : ∀ d : Fin nq, d ≠ anc → d ≠ q0 → es.paulis d = Pauli.I) :
    zPart ((propagateGate (Gate.hadamard q) es).paulis anc) = Pauli.I
      ∧ ∀ d : Fin nq, d ≠ anc → d ≠ q0 →
          (propagateGate (Gate.hadamard q) es).paulis d = Pauli.I := by
  refine ⟨?_, ?_⟩
  · rw [propagateGate_hadamard_paulis_ne q es anc (Ne.symm hqa)]; exact hZ
  · intro d hda hdq
    by_cases hdq2 : d = q
    · subst hdq2; rw [propagateGate_hadamard_self, hoff d hda hdq]; rfl
    · rw [propagateGate_hadamard_paulis_ne q es d hdq2]; exact hoff d hda hdq

/-- `cnot c anc` (target `anc`) maintains the off-`q0` invariant. -/
theorem cnotToAnc_keeps_offInvariant {nq : Nat} (anc q0 : Fin nq) (c : Fin nq) (hca : c ≠ anc)
    (es : ErrorState nq) (hZ : zPart (es.paulis anc) = Pauli.I)
    (hoff : ∀ d : Fin nq, d ≠ anc → d ≠ q0 → es.paulis d = Pauli.I) :
    zPart ((propagateGate (Gate.cnot c anc hca) es).paulis anc) = Pauli.I
      ∧ ∀ d : Fin nq, d ≠ anc → d ≠ q0 →
          (propagateGate (Gate.cnot c anc hca) es).paulis d = Pauli.I := by
  refine ⟨cnot_target_keeps_Zfree c anc hca es hZ, ?_⟩
  intro d hda hdq
  by_cases hdc : d = c
  · subst hdc
    rw [propagateGate_cnot_control_preserved d anc hca es hZ]; exact hoff d hda hdq
  · rw [propagateGate_cnot_paulis_ne c anc hca es d hdc hda]; exact hoff d hda hdq

/-- A gate is a `hadamard` off `anc` or a `cnot` into `anc` — the only gate
shapes the coupling region (before the tail) contains. -/
def isHorCnotToAnc {nq : Nat} (anc : Fin nq) (g : Gate nq) : Prop :=
  (∃ q : Fin nq, q ≠ anc ∧ g = Gate.hadamard q) ∨
    (∃ (c : Fin nq) (h : c ≠ anc), g = Gate.cnot c anc h)

/-- A whole list of `isHorCnotToAnc` gates maintains the off-`q0` invariant. -/
theorem couplingList_keeps_offInvariant {nq : Nat} (anc q0 : Fin nq) :
    ∀ (c : Circuit nq), (∀ g ∈ c, isHorCnotToAnc anc g) →
      ∀ es : ErrorState nq, zPart (es.paulis anc) = Pauli.I →
        (∀ d : Fin nq, d ≠ anc → d ≠ q0 → es.paulis d = Pauli.I) →
        zPart ((propagateCircuit c es).paulis anc) = Pauli.I
          ∧ ∀ d : Fin nq, d ≠ anc → d ≠ q0 → (propagateCircuit c es).paulis d = Pauli.I := by
  intro c
  induction c with
  | nil => intro _ es hZ hoff; exact ⟨hZ, hoff⟩
  | cons g gs ih =>
      intro hc es hZ hoff
      have hstep : zPart ((propagateGate g es).paulis anc) = Pauli.I
          ∧ ∀ d : Fin nq, d ≠ anc → d ≠ q0 → (propagateGate g es).paulis d = Pauli.I := by
        rcases hc g List.mem_cons_self with ⟨q, hqa, rfl⟩ | ⟨cc, hcca, rfl⟩
        · exact hadamard_keeps_offInvariant anc q0 q hqa es hZ hoff
        · exact cnotToAnc_keeps_offInvariant anc q0 cc hcca es hZ hoff
      exact ih (fun g' h => hc g' (List.mem_cons_of_mem _ h)) (propagateGate g es) hstep.1 hstep.2

/-- **Data-fault support through leading gates + a `zParitySlot` chain + tail.**
A fault at `q0 ≠ anc` runs partial-slot leading gates (all `isHorCnotToAnc`),
then the rest chain, then a data-preserving tail; every data qubit but `q0`
stays clean. -/
theorem dataSite_support {P : QECParams} {total : Nat} (anc : Fin (P.n + total))
    (hancHelper : P.n ≤ anc.val) (L : Nat) (hancL : anc.val < L)
    (q0 : Fin (P.n + total)) (hq0a : q0 ≠ anc) (hq0L : q0.val < L)
    (leading : Circuit (P.n + total)) (hlead : ∀ g ∈ leading, isHorCnotToAnc anc g)
    (hleadBelow : circuitActsBelow leading L)
    (rest : List (ScheduledPauli (P.n + total))) (hrest : ∀ s ∈ rest, s.qubit ≠ anc)
    (hrestL : ∀ s ∈ rest, s.qubit.val < L)
    (tailG : Circuit (P.n + total)) (htailPDA : PreservesDataAbove tailG L)
    (cursor : Nat) (p : Pauli) (q' : Fin P.n) (hne : freshDataQ P.n total q' ≠ q0) :
    (propagateCircuit
        (leading ++ eraseFaults ((rest.map (zParitySlot anc)).flatten) ++ tailG)
        ((PCC.cleanAtDetector cursor).inject q0 p)).paulis (freshDataQ P.n total q') = Pauli.I := by
  set es0 := (PCC.cleanAtDetector cursor).inject q0 p with hes0
  have hZ0 : zPart (es0.paulis anc) = Pauli.I := by
    rw [hes0, injectClean_paulis, if_neg (Ne.symm hq0a)]; rfl
  have hoff0 : ∀ d : Fin (P.n + total), d ≠ anc → d ≠ q0 → es0.paulis d = Pauli.I := by
    intro d _ hdq; rw [hes0, injectClean_paulis, if_neg hdq]
  have hane : freshDataQ P.n total q' ≠ anc :=
    Fin.ne_of_val_ne (by have := q'.isLt; have := hancHelper; simp only [freshDataQ_val]; omega)
  have hchainBelow : circuitActsBelow (eraseFaults ((rest.map (zParitySlot anc)).flatten)) L :=
    cab_erase_flatten_map rest (zParitySlot anc)
      (fun s hs => cab_erase_zParitySlot anc s hancL (hrestL s hs))
  have hes0_clean : cleanAbove es0 L := by
    intro h hh
    rw [hes0, injectClean_paulis, if_neg (fun he => by rw [he] at hh; omega)]
  have hlc_clean : cleanAbove (propagateCircuit
      (leading ++ eraseFaults ((rest.map (zParitySlot anc)).flatten)) es0) L :=
    cleanAbove_preserved_of_actsBelow _ L (cab_append hleadBelow hchainBelow) es0 hes0_clean
  obtain ⟨hZ1, hoff1⟩ := couplingList_keeps_offInvariant anc q0 leading hlead es0 hZ0 hoff0
  rw [QHL.Target.propagateCircuit_append,
    htailPDA _ hlc_clean (freshDataQ P.n total q') (by simp only [freshDataQ_val]; exact q'.isLt),
    QHL.Target.propagateCircuit_append]
  exact zpsChain_keeps_offInvariant anc q0 rest hrest (propagateCircuit leading es0) hZ1 hoff1
    (freshDataQ P.n total q') hane hne

/-- **Ancilla-fault deposit from a partial leading state.**  Given `es_lead` with
`v` on `s0Q`, `p` on `anc`, and clean elsewhere, propagating the rest chain +
data-preserving tail deposits `kindTransform s.kind p` on each rest slot, keeps
`v` on `s0Q`, and clears every other data qubit. -/
theorem ancSite_from_lead {P : QECParams} {total : Nat} (anc : Fin (P.n + total))
    (hancHelper : P.n ≤ anc.val) (L : Nat) (hancL : anc.val < L)
    (rest : List (ScheduledPauli (P.n + total))) (hrest : ∀ s ∈ rest, s.qubit ≠ anc)
    (hndr : (rest.map (·.qubit)).Nodup) (hrestL : ∀ s ∈ rest, s.qubit.val < L)
    (s0Q : Fin (P.n + total)) (hs0Qrest : s0Q ∉ rest.map (·.qubit)) (hs0Qa : s0Q ≠ anc)
    (v p : Pauli) (tailG : Circuit (P.n + total)) (htailPDA : PreservesDataAbove tailG L)
    (es_lead : ErrorState (P.n + total)) (hlead_clean : cleanAbove es_lead L)
    (hlead_s0 : es_lead.paulis s0Q = v) (hlead_anc : es_lead.paulis anc = p)
    (hlead_off : ∀ i : Fin (P.n + total), i ≠ s0Q → i ≠ anc → es_lead.paulis i = Pauli.I) :
    (∀ q' : Fin P.n, freshDataQ P.n total q' = s0Q →
        (propagateCircuit (eraseFaults ((rest.map (zParitySlot anc)).flatten) ++ tailG)
          es_lead).paulis (freshDataQ P.n total q') = v)
      ∧ (∀ s ∈ rest, ∀ q' : Fin P.n, freshDataQ P.n total q' = s.qubit →
        (propagateCircuit (eraseFaults ((rest.map (zParitySlot anc)).flatten) ++ tailG)
          es_lead).paulis (freshDataQ P.n total q') = kindTransform s.kind p)
      ∧ (∀ q' : Fin P.n, freshDataQ P.n total q' ≠ s0Q → freshDataQ P.n total q' ∉ rest.map (·.qubit) →
        (propagateCircuit (eraseFaults ((rest.map (zParitySlot anc)).flatten) ++ tailG)
          es_lead).paulis (freshDataQ P.n total q') = Pauli.I) := by
  have hclean : ∀ s ∈ rest, es_lead.paulis s.qubit = Pauli.I := by
    intro s hs
    have hne1 : s.qubit ≠ s0Q := fun h => hs0Qrest (h ▸ List.mem_map_of_mem (f := (·.qubit)) hs)
    exact hlead_off s.qubit hne1 (hrest s hs)
  obtain ⟨hdep, hancW, hoff⟩ := propagate_zpsChain_anc anc p rest hrest hndr es_lead hlead_anc hclean
  have hchainBelow : circuitActsBelow (eraseFaults ((rest.map (zParitySlot anc)).flatten)) L :=
    cab_erase_flatten_map rest (zParitySlot anc)
      (fun s hs => cab_erase_zParitySlot anc s hancL (hrestL s hs))
  have hchain_clean : cleanAbove (propagateCircuit
      (eraseFaults ((rest.map (zParitySlot anc)).flatten)) es_lead) L :=
    cleanAbove_preserved_of_actsBelow _ L hchainBelow es_lead hlead_clean
  refine ⟨?_, ?_, ?_⟩
  · intro q' hq'
    rw [QHL.Target.propagateCircuit_append,
      htailPDA _ hchain_clean (freshDataQ P.n total q') (by simp only [freshDataQ_val]; exact q'.isLt),
      hq', hoff s0Q hs0Qa hs0Qrest, hlead_s0]
  · intro s hs q' hq'
    rw [QHL.Target.propagateCircuit_append,
      htailPDA _ hchain_clean (freshDataQ P.n total q') (by simp only [freshDataQ_val]; exact q'.isLt), hq']
    exact hdep s hs
  · intro q' hne hnm
    have hane : freshDataQ P.n total q' ≠ anc :=
      Fin.ne_of_val_ne (by have := q'.isLt; have := hancHelper; simp only [freshDataQ_val]; omega)
    rw [QHL.Target.propagateCircuit_append,
      htailPDA _ hchain_clean (freshDataQ P.n total q') (by simp only [freshDataQ_val]; exact q'.isLt),
      hoff (freshDataQ P.n total q') hane hnm, hlead_off (freshDataQ P.n total q') hne hane]

/-- Leading state after a `Z`-slot's anc errloc (`[cnot sq anc]` from `p @ anc`):
`kindTransform .Z p` on `sq`, `p` on `anc`, clean elsewhere. -/
theorem zLead_anc {nq : Nat} (anc sq : Fin nq) (hsa : sq ≠ anc) (cursor : Nat) (p : Pauli) :
    (propagateGate (Gate.cnot sq anc hsa) ((PCC.cleanAtDetector cursor).inject anc p)).paulis sq
        = kindTransform XZPauli.Z p
      ∧ (propagateGate (Gate.cnot sq anc hsa) ((PCC.cleanAtDetector cursor).inject anc p)).paulis anc
        = p
      ∧ ∀ i : Fin nq, i ≠ sq → i ≠ anc →
          (propagateGate (Gate.cnot sq anc hsa) ((PCC.cleanAtDetector cursor).inject anc p)).paulis i
            = Pauli.I := by
  refine ⟨?_, ?_, ?_⟩
  · rw [propagateGate_cnot_control sq anc hsa, injectClean_paulis, injectClean_paulis,
      if_pos rfl, if_neg hsa]
    simp [kindTransform, pauliMul_I_right]
  · rw [propagateGate_cnot_target sq anc hsa, injectClean_paulis, injectClean_paulis,
      if_neg hsa, if_pos rfl]
    simp [xPart, pauliMul]
  · intro i hisq hia
    rw [propagateGate_cnot_paulis_ne sq anc hsa _ i hisq hia, injectClean_paulis, if_neg hia]

/-- Leading state after an `X`-slot's anc errloc (`[cnot sq anc, hadamard sq]`
from `p @ anc`): `kindTransform .X p` on `sq`, `p` on `anc`, clean elsewhere. -/
theorem xLead_anc {nq : Nat} (anc sq : Fin nq) (hsa : sq ≠ anc) (cursor : Nat) (p : Pauli) :
    (propagateCircuit [Gate.cnot sq anc hsa, Gate.hadamard sq]
        ((PCC.cleanAtDetector cursor).inject anc p)).paulis sq = kindTransform XZPauli.X p
      ∧ (propagateCircuit [Gate.cnot sq anc hsa, Gate.hadamard sq]
        ((PCC.cleanAtDetector cursor).inject anc p)).paulis anc = p
      ∧ ∀ i : Fin nq, i ≠ sq → i ≠ anc →
          (propagateCircuit [Gate.cnot sq anc hsa, Gate.hadamard sq]
            ((PCC.cleanAtDetector cursor).inject anc p)).paulis i = Pauli.I := by
  obtain ⟨h1, h2, h3⟩ := zLead_anc anc sq hsa cursor p
  simp only [propagateCircuit] at *
  refine ⟨?_, ?_, ?_⟩
  · rw [propagateGate_hadamard_self, h1]; rfl
  · rw [propagateGate_hadamard_paulis_ne sq _ anc (Ne.symm hsa), h2]
  · intro i hisq hia
    rw [propagateGate_hadamard_paulis_ne sq _ i hisq, h3 i hisq hia]

/-- A `kindTransform kk p` value at a scheduled data qubit is a valid
`dominatedByScheduleHook`/`domHookChain` disjunct. -/
theorem domHook_kindTransform {n total : Nat} (kk : XZPauli)
    (slots : List (ScheduledPauli (n + total))) (R : ErrorVec n) (p : Pauli) (q' : Fin n)
    (hmem : freshDataQ n total q' ∈ slots.map (·.qubit))
    (hval : R q' = kindTransform kk p) :
    R q' = Pauli.I ∨ (R q' = kk.toPauli ∧ freshDataQ n total q' ∈ slots.map (·.qubit)) := by
  rcases kindTransform_mem kk p with h | h
  · exact Or.inl (hval.trans h)
  · exact Or.inr ⟨hval.trans h, hmem⟩

/-- **A data-fault site of the chain has weight `≤ 1`.**  With leading gates all
`isHorCnotToAnc`, the residual is supported on the injected qubit `s0Q` (or is
empty when `s0Q` is a helper). -/
theorem dataSite_weight_le_one {P : QECParams} {total : Nat} (anc : Fin (P.n + total))
    (hancHelper : P.n ≤ anc.val) (L : Nat) (hancL : anc.val < L)
    (s0Q : Fin (P.n + total)) (hs0Qa : s0Q ≠ anc) (hs0QL : s0Q.val < L)
    (leading : Circuit (P.n + total)) (hlead : ∀ g ∈ leading, isHorCnotToAnc anc g)
    (hleadBelow : circuitActsBelow leading L)
    (rest : List (ScheduledPauli (P.n + total))) (hrest : ∀ s ∈ rest, s.qubit ≠ anc)
    (hrestL : ∀ s ∈ rest, s.qubit.val < L)
    (tail : FCircuit (P.n + total)) (htailPDA : PreservesDataAbove (eraseFaults tail) L)
    (cursor : Nat) (p : Pauli) (hp : p ≠ Pauli.I) :
    ErrorVec.weight (targetFaultDataResidual P
        ⟨⟨s0Q, leading ++ eraseFaults ((rest.map (zParitySlot anc)).flatten ++ tail), cursor⟩,
          p, hp⟩) ≤ 1 := by
  have hkey : ∀ q'' : Fin P.n, freshDataQ P.n total q'' ≠ s0Q →
      targetFaultDataResidual P
        ⟨⟨s0Q, leading ++ eraseFaults ((rest.map (zParitySlot anc)).flatten ++ tail), cursor⟩,
          p, hp⟩ q'' = Pauli.I := by
    intro q'' hfne
    show (propagateCircuit (leading ++ eraseFaults ((rest.map (zParitySlot anc)).flatten ++ tail))
        ((PCC.cleanAtDetector cursor).inject s0Q p)).paulis (freshDataQ P.n total q'') = Pauli.I
    rw [eraseFaults_append, ← List.append_assoc]
    exact dataSite_support anc hancHelper L hancL s0Q hs0Qa hs0QL leading hlead hleadBelow
      rest hrest hrestL (eraseFaults tail) htailPDA cursor p q'' hfne
  by_cases hd : s0Q.val < P.n
  · apply weight_le_one_of_single _ ⟨s0Q.val, hd⟩
    intro q'' hne
    exact hkey q'' (fun h => hne (Fin.ext (by simpa [freshDataQ_val] using congrArg Fin.val h)))
  · have h0 : ErrorVec.weight (targetFaultDataResidual P
        ⟨⟨s0Q, leading ++ eraseFaults ((rest.map (zParitySlot anc)).flatten ++ tail), cursor⟩,
          p, hp⟩) = 0 := by
      apply weight_zero_of_allI
      intro q''
      exact hkey q'' (fun h => hd (by rw [← h]; simp only [freshDataQ_val]; exact q''.isLt))
    omega

/-! ## The mixed-kind chain site classifier -/

/-- **Every fault site of a mixed-kind `zParitySlot` chain** (data slots of kind
`kk`, plus possibly helper slots like the flag coupling) has a weight-`≤ 1` data
residual or a `domHookChain kk` one.  Data faults stay on one qubit; ancilla
faults deposit `kindTransform kk p` on the scheduled data qubits. -/
theorem zpsChain_site_classified {P : QECParams} {total : Nat} (anc : Fin (P.n + total))
    (hancHelper : P.n ≤ anc.val) (L : Nat) (hancL : anc.val < L) (kk : XZPauli)
    (tail : FCircuit (P.n + total)) (htailPDA : PreservesDataAbove (eraseFaults tail) L) :
    ∀ (slots : List (ScheduledPauli (P.n + total))),
      (∀ s ∈ slots, s.qubit ≠ anc) → (slots.map (·.qubit)).Nodup →
      (∀ s ∈ slots, s.qubit.val < L) →
      (∀ s ∈ slots, s.qubit.val < P.n → s.kind = kk) →
      ∀ (cursor : Nat) (site : PCC.ErrLocWithContext (P.n + total)) (p : Pauli) (hp : p ≠ Pauli.I),
        site ∈ prefixErrLocsWithContextAux cursor ((slots.map (zParitySlot anc)).flatten) tail →
        ErrorVec.weight (targetFaultDataResidual P ⟨site, p, hp⟩) ≤ 1 ∨
          domHookChain kk slots (targetFaultDataResidual P ⟨site, p, hp⟩) := by
  intro slots
  induction slots with
  | nil =>
      intro _ _ _ _ cursor site p hp hsite
      simp [prefixErrLocsWithContextAux] at hsite
  | cons s0 rest ih =>
      intro hqa hnd hslotsL hkindlt cursor site p hp hsite
      have hs0a : s0.qubit ≠ anc := hqa s0 List.mem_cons_self
      have hs0L : s0.qubit.val < L := hslotsL s0 List.mem_cons_self
      have hrestL : ∀ s ∈ rest, s.qubit.val < L := fun s hs => hslotsL s (List.mem_cons_of_mem _ hs)
      have hnd0 : (s0.qubit :: rest.map (·.qubit)).Nodup := by simpa using hnd
      have hfresh : s0.qubit ∉ rest.map (·.qubit) := (List.nodup_cons.mp hnd0).1
      have hndr : (rest.map (·.qubit)).Nodup := (List.nodup_cons.mp hnd0).2
      have hrestqa : ∀ s ∈ rest, s.qubit ≠ anc := fun s hs => hqa s (List.mem_cons_of_mem _ hs)
      have hleadBelow_cnot : circuitActsBelow [Gate.cnot s0.qubit anc hs0a] L := by
        intro g hg q hq
        simp only [List.mem_singleton] at hg; subst hg
        rcases hq with rfl | rfl
        · exact hs0L
        · exact hancL
      have hleadBelow_H : circuitActsBelow [Gate.hadamard s0.qubit] L := by
        intro g hg q hq
        simp only [List.mem_singleton] at hg; subst hg; cases hq; exact hs0L
      have hinj_clean : cleanAbove ((PCC.cleanAtDetector cursor).inject anc p) L := by
        intro h hh
        rw [injectClean_paulis, if_neg (fun he => by rw [he] at hh; omega)]
      have hcircsplit : ((s0 :: rest).map (zParitySlot anc)).flatten =
          zParitySlot anc s0 ++ (rest.map (zParitySlot anc)).flatten := by
        simp [List.map_cons, List.flatten_cons]
      rw [hcircsplit, prefixErrLocs_append, List.mem_append] at hsite
      rcases hsite with hhead | hrec
      · -- fault in the head slot
        cases hs0k : s0.kind with
        | Z =>
            have hzps : zParitySlot anc s0 = cnot s0.qubit anc := by
              simp only [zParitySlot, hs0k]
            rw [hzps, prefixErrLocs_cnot anc s0.qubit hs0a cursor
              ((rest.map (zParitySlot anc)).flatten ++ tail)] at hhead
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hhead
            rcases hhead with rfl | rfl
            · -- Z data-control site
              exact Or.inl (dataSite_weight_le_one anc hancHelper L hancL s0.qubit hs0a hs0L
                [Gate.cnot s0.qubit anc hs0a]
                (by intro g hg; simp only [List.mem_singleton] at hg; subst hg
                    exact Or.inr ⟨s0.qubit, hs0a, rfl⟩)
                hleadBelow_cnot rest hrestqa hrestL tail htailPDA cursor p hp)
            · -- Z anc site
              refine Or.inr ?_
              obtain ⟨hp_s0, hp_rest, hp_else⟩ := ancSite_from_lead anc hancHelper L hancL rest hrestqa
                hndr hrestL s0.qubit hfresh hs0a (kindTransform XZPauli.Z p) p (eraseFaults tail) htailPDA
                (propagateGate (Gate.cnot s0.qubit anc hs0a) ((PCC.cleanAtDetector cursor).inject anc p))
                (by
                  have hcl := cleanAbove_preserved_of_actsBelow ([Gate.cnot s0.qubit anc hs0a]) L
                    hleadBelow_cnot ((PCC.cleanAtDetector cursor).inject anc p) hinj_clean
                  simpa [propagateCircuit] using hcl)
                (zLead_anc anc s0.qubit hs0a cursor p).1 (zLead_anc anc s0.qubit hs0a cursor p).2.1
                (zLead_anc anc s0.qubit hs0a cursor p).2.2
              have hReq : ∀ q' : Fin P.n, targetFaultDataResidual P
                  ⟨⟨anc, Gate.cnot s0.qubit anc hs0a ::
                      eraseFaults ((rest.map (zParitySlot anc)).flatten ++ tail), cursor⟩, p, hp⟩ q'
                  = (propagateCircuit (eraseFaults ((rest.map (zParitySlot anc)).flatten)
                        ++ eraseFaults tail)
                      (propagateGate (Gate.cnot s0.qubit anc hs0a)
                        ((PCC.cleanAtDetector cursor).inject anc p))).paulis (freshDataQ P.n total q') := by
                intro q'
                show (propagateCircuit (Gate.cnot s0.qubit anc hs0a ::
                    eraseFaults ((rest.map (zParitySlot anc)).flatten ++ tail))
                    ((PCC.cleanAtDetector cursor).inject anc p)).paulis (freshDataQ P.n total q') = _
                rw [eraseFaults_append]; rfl
              intro q'
              rw [hReq q']
              by_cases hmem : freshDataQ P.n total q' ∈ (s0 :: rest).map (·.qubit)
              · have hval : (propagateCircuit (eraseFaults ((rest.map (zParitySlot anc)).flatten)
                      ++ eraseFaults tail)
                    (propagateGate (Gate.cnot s0.qubit anc hs0a)
                      ((PCC.cleanAtDetector cursor).inject anc p))).paulis (freshDataQ P.n total q')
                    = kindTransform kk p := by
                  rcases List.mem_map.mp hmem with ⟨s, hsmem, hsq⟩
                  have hslt : s.qubit.val < P.n := by rw [hsq]; simp only [freshDataQ_val]; exact q'.isLt
                  have hskk : s.kind = kk := hkindlt s hsmem hslt
                  rcases List.mem_cons.mp hsmem with heq | hsr
                  · have hkkZ : kk = XZPauli.Z := by rw [← hskk, heq, hs0k]
                    rw [hkkZ]; exact hp_s0 q' (heq ▸ hsq.symm)
                  · rw [← hskk]; exact hp_rest s hsr q' hsq.symm
                rcases kindTransform_mem kk p with h | h
                · exact Or.inl (hval.trans h)
                · exact Or.inr ⟨hval.trans h, hmem⟩
              · left
                have hmap : (s0 :: rest).map (·.qubit) = s0.qubit :: rest.map (·.qubit) := by simp
                rw [hmap, List.mem_cons] at hmem
                push_neg at hmem
                exact hp_else q' hmem.1 hmem.2
        | X =>
            have hzps : zParitySlot anc s0 =
                hadamard s0.qubit ++ cnot s0.qubit anc ++ hadamard s0.qubit := by
              simp only [zParitySlot, hs0k]
            rw [hzps, prefixErrLocs_hSandwich anc s0.qubit hs0a cursor
              ((rest.map (zParitySlot anc)).flatten ++ tail)] at hhead
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hhead
            rcases hhead with rfl | rfl | rfl | rfl
            · -- X site₁: leading [H, cnot, H]
              exact Or.inl (dataSite_weight_le_one anc hancHelper L hancL s0.qubit hs0a hs0L
                [Gate.hadamard s0.qubit, Gate.cnot s0.qubit anc hs0a, Gate.hadamard s0.qubit]
                (by intro g hg
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
                    rcases hg with rfl | rfl | rfl
                    · exact Or.inl ⟨s0.qubit, hs0a, rfl⟩
                    · exact Or.inr ⟨s0.qubit, hs0a, rfl⟩
                    · exact Or.inl ⟨s0.qubit, hs0a, rfl⟩)
                (cab_append (cab_append hleadBelow_H hleadBelow_cnot) hleadBelow_H)
                rest hrestqa hrestL tail htailPDA cursor p hp)
            · -- X site₂: leading [cnot, H]
              exact Or.inl (dataSite_weight_le_one anc hancHelper L hancL s0.qubit hs0a hs0L
                [Gate.cnot s0.qubit anc hs0a, Gate.hadamard s0.qubit]
                (by intro g hg
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
                    rcases hg with rfl | rfl
                    · exact Or.inr ⟨s0.qubit, hs0a, rfl⟩
                    · exact Or.inl ⟨s0.qubit, hs0a, rfl⟩)
                (cab_append hleadBelow_cnot hleadBelow_H)
                rest hrestqa hrestL tail htailPDA cursor p hp)
            · -- X site₃: anc site, leading [cnot, H]
              refine Or.inr ?_
              obtain ⟨hp_s0, hp_rest, hp_else⟩ := ancSite_from_lead anc hancHelper L hancL rest hrestqa
                hndr hrestL s0.qubit hfresh hs0a (kindTransform XZPauli.X p) p (eraseFaults tail) htailPDA
                (propagateCircuit [Gate.cnot s0.qubit anc hs0a, Gate.hadamard s0.qubit]
                  ((PCC.cleanAtDetector cursor).inject anc p))
                (cleanAbove_preserved_of_actsBelow
                  ([Gate.cnot s0.qubit anc hs0a, Gate.hadamard s0.qubit]) L
                  (cab_append hleadBelow_cnot hleadBelow_H)
                  ((PCC.cleanAtDetector cursor).inject anc p) hinj_clean)
                (xLead_anc anc s0.qubit hs0a cursor p).1 (xLead_anc anc s0.qubit hs0a cursor p).2.1
                (xLead_anc anc s0.qubit hs0a cursor p).2.2
              have hReq : ∀ q' : Fin P.n, targetFaultDataResidual P
                  ⟨⟨anc, Gate.cnot s0.qubit anc hs0a :: Gate.hadamard s0.qubit ::
                      eraseFaults ((rest.map (zParitySlot anc)).flatten ++ tail), cursor⟩, p, hp⟩ q'
                  = (propagateCircuit (eraseFaults ((rest.map (zParitySlot anc)).flatten)
                        ++ eraseFaults tail)
                      (propagateCircuit [Gate.cnot s0.qubit anc hs0a, Gate.hadamard s0.qubit]
                        ((PCC.cleanAtDetector cursor).inject anc p))).paulis (freshDataQ P.n total q') := by
                intro q'
                show (propagateCircuit (Gate.cnot s0.qubit anc hs0a :: Gate.hadamard s0.qubit ::
                    eraseFaults ((rest.map (zParitySlot anc)).flatten ++ tail))
                    ((PCC.cleanAtDetector cursor).inject anc p)).paulis (freshDataQ P.n total q') = _
                rw [eraseFaults_append]; rfl
              intro q'
              rw [hReq q']
              by_cases hmem : freshDataQ P.n total q' ∈ (s0 :: rest).map (·.qubit)
              · have hval : (propagateCircuit (eraseFaults ((rest.map (zParitySlot anc)).flatten)
                      ++ eraseFaults tail)
                    (propagateCircuit [Gate.cnot s0.qubit anc hs0a, Gate.hadamard s0.qubit]
                      ((PCC.cleanAtDetector cursor).inject anc p))).paulis (freshDataQ P.n total q')
                    = kindTransform kk p := by
                  rcases List.mem_map.mp hmem with ⟨s, hsmem, hsq⟩
                  have hslt : s.qubit.val < P.n := by rw [hsq]; simp only [freshDataQ_val]; exact q'.isLt
                  have hskk : s.kind = kk := hkindlt s hsmem hslt
                  rcases List.mem_cons.mp hsmem with heq | hsr
                  · have hkkX : kk = XZPauli.X := by rw [← hskk, heq, hs0k]
                    rw [hkkX]; exact hp_s0 q' (heq ▸ hsq.symm)
                  · rw [← hskk]; exact hp_rest s hsr q' hsq.symm
                rcases kindTransform_mem kk p with h | h
                · exact Or.inl (hval.trans h)
                · exact Or.inr ⟨hval.trans h, hmem⟩
              · left
                have hmap : (s0 :: rest).map (·.qubit) = s0.qubit :: rest.map (·.qubit) := by simp
                rw [hmap, List.mem_cons] at hmem
                push_neg at hmem
                exact hp_else q' hmem.1 hmem.2
            · -- X site₄: leading [H]
              exact Or.inl (dataSite_weight_le_one anc hancHelper L hancL s0.qubit hs0a hs0L
                [Gate.hadamard s0.qubit]
                (by intro g hg; simp only [List.mem_singleton] at hg; subst hg
                    exact Or.inl ⟨s0.qubit, hs0a, rfl⟩)
                hleadBelow_H rest hrestqa hrestL tail htailPDA cursor p hp)
      · -- fault in the rest of the chain
        rcases ih hrestqa hndr hrestL (fun s hs => hkindlt s (List.mem_cons_of_mem _ hs))
            _ site p hp hrec with hle | hdom
        · exact Or.inl hle
        · refine Or.inr (fun q' => ?_)
          rcases hdom q' with h | ⟨hv, hm⟩
          · exact Or.inl h
          · exact Or.inr ⟨hv, List.mem_cons_of_mem _ hm⟩

/-! ## PREP and TAIL regions of the flag block (weight-`0` sites) -/

/-- `prepPlus a` clears any injected fault: after it, all qubits are clean. -/
theorem injectClean_prepPlus_allI {nq : Nat} (a : Fin nq) (p : Pauli) (dstart : Nat) (i : Fin nq) :
    (propagateGate (Gate.prepPlus a) ((PCC.cleanAtDetector dstart).inject a p)).paulis i = Pauli.I := by
  by_cases h : i = a <;>
    simp [propagateGate, ErrorState.inject, PCC.cleanAtDetector, ErrorState.clean, h]

/-- The single `errLoc` site of a compiled `prepP a`. -/
theorem prefixErrLocs_prepP {nq : Nat} (a : Fin nq) (cursor : Nat) (tail : FCircuit nq) :
    prefixErrLocsWithContextAux cursor (prepP a) tail =
      [⟨a, Gate.prepPlus a :: eraseFaults tail, cursor⟩] := by
  simp [prepP, prefixErrLocsWithContextAux, eraseFaults]

/-- A `prepP`-site fault (on the flag qubit): residual on data is identity. -/
theorem residual_prepP_site {P : QECParams} {total : Nat} (a : Fin (P.n + total)) (p : Pauli)
    (rest : Circuit (P.n + total)) (dstart : Nat) (q' : Fin P.n) :
    (propagateCircuit (Gate.prepPlus a :: rest)
        ((PCC.cleanAtDetector dstart).inject a p)).paulis (freshDataQ P.n total q') = Pauli.I := by
  rw [propagateCircuit]
  exact propagateCircuit_preserves_allI rest _
    (fun i => injectClean_prepPlus_allI a p dstart i) (freshDataQ P.n total q')

/-- **A helper-region site has weight-`0` data residual.**  If a compiled circuit
`C` acts only on helper qubits (`[P.n, L)`) and its errlocs are helpers, any fault
gives an all-identity data residual (the data-preserving tail keeps it). -/
theorem helperRegion_site_wle1 {P : QECParams} {total : Nat} (C : FCircuit (P.n + total)) (L : Nat)
    (hbelow : circuitActsBelow (eraseFaults C) L) (habove : circuitActsAbove (eraseFaults C) P.n)
    (herr : ∀ q0 : Fin (P.n + total), FInstr.errLoc q0 ∈ C → P.n ≤ q0.val ∧ q0.val < L)
    (tail : FCircuit (P.n + total)) (htailPDA : PreservesDataAbove (eraseFaults tail) L)
    (cursor : Nat) (site : PCC.ErrLocWithContext (P.n + total)) (p : Pauli) (hp : p ≠ Pauli.I)
    (hsite : site ∈ prefixErrLocsWithContextAux cursor C tail) :
    ErrorVec.weight (targetFaultDataResidual P ⟨site, p, hp⟩) ≤ 1 := by
  obtain ⟨⟨hSqA, hSqB⟩, Xr, hsuf, hXrBelow, hXrAbove⟩ :=
    helperPrefix_site C L hbelow habove herr cursor tail site hsite
  have hall : ∀ q' : Fin P.n, targetFaultDataResidual P ⟨site, p, hp⟩ q' = Pauli.I := by
    intro q'
    have hane : freshDataQ P.n total q' ≠ site.q := by
      intro he
      have := hSqA; rw [← he, freshDataQ_val] at this; have := q'.isLt; omega
    show (propagateCircuit site.suffix
        ((PCC.cleanAtDetector site.detectorStart).inject site.q p)).paulis
        (freshDataQ P.n total q') = Pauli.I
    set es0 := (PCC.cleanAtDetector site.detectorStart).inject site.q p with hes0
    rw [hsuf, QHL.Target.propagateCircuit_append]
    set esA := propagateCircuit Xr es0 with hesA
    have hesA_data : esA.paulis (freshDataQ P.n total q') = Pauli.I := by
      rw [hesA, propagateCircuit_paulis_off Xr _
        (fun g hg hq => by
          have := hXrAbove g hg _ hq; simp only [freshDataQ_val] at this; have := q'.isLt; omega)
        es0, hes0, injectClean_paulis, if_neg hane]
    have hcleanA : cleanAbove esA L := by
      rw [hesA]
      refine cleanAbove_preserved_of_actsBelow Xr L hXrBelow es0 ?_
      intro h hh
      rw [hes0, injectClean_paulis, if_neg (fun he => by rw [he] at hh; omega)]
    rw [htailPDA esA hcleanA (freshDataQ P.n total q')
      (by simp only [freshDataQ_val]; exact q'.isLt), hesA_data]
  have h0 : ErrorVec.weight (targetFaultDataResidual P ⟨site, p, hp⟩) = 0 :=
    weight_zero_of_allI _ hall
  omega

/-- **Reshape** of the compiled flag block into `PREP ++ CHAIN ++ TAIL`, folding
the two flag-`cnot` couplings' first one into a `⟨.Z, flag⟩` slot of the chain. -/
theorem compileFlagOrdered_reshape {nq : Nat} (σ' : RuleSchedule nq) (anc flag : Fin nq) :
    compileFlagOrdered σ' anc flag
      = prep0 anc ++ prepP flag ++
          (((σ'.slots.take (σ'.slots.length / 2)) ++ [(⟨XZPauli.Z, flag⟩ : ScheduledPauli nq)] ++
            (σ'.slots.drop (σ'.slots.length / 2))).map (zParitySlot anc)).flatten ++
          (cnot flag anc ++ flagMeasZ anc ++ hadamard flag ++ flagMeasZ flag) := by
  unfold compileFlagOrdered
  simp only [List.map_append, List.map_cons, List.map_nil, List.flatten_append, List.flatten_cons,
    List.flatten_nil, List.append_nil, List.append_assoc]
  rfl

/--
info: 'QStab.QClifford.Compile.zpsChain_site_classified' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms zpsChain_site_classified

/-! ## The Flag gadget site classifier -/

open QHL.CodeHGPSchedule in
/-- **`flag_gadget_site_classified`** — the `SchemeClassifier`-shaped per-gadget
classifier for the Flag scheme.  Every fault site of the compiled Flag gadget
block has a weight-`≤ 1` data residual or a `dominatedByScheduleHook` one, going
through `compileGadgetBlock .Flag` (the syntactic compilation), the shared-ancilla
mixed chain (data slots `kk` + the flag `Z`-coupling), the two prep sites, and the
inert flag tail. -/
theorem flag_gadget_site_classified {P : QECParams} {total : Nat} (sigma : RuleSchedule P.n)
    (kk : XZPauli) (hkind : ∀ s ∈ sigma.slots, s.kind = kk)
    (hnd : (sigma.slots.map (·.qubit)).Nodup)
    (gstart : Nat) (ghfit : gstart + helperCount Scheme.Flag sigma ≤ total)
    (tail : FCircuit (P.n + total))
    (htailPDA : PreservesDataAbove (eraseFaults tail)
      (P.n + gstart + helperCount Scheme.Flag sigma))
    (cursor : Nat) (site : PCC.ErrLocWithContext (P.n + total)) (p : Pauli) (hp : p ≠ Pauli.I)
    (hsite : site ∈ prefixErrLocsWithContextAux cursor
      (compileGadgetBlock Scheme.Flag sigma gstart ghfit) tail) :
    ErrorVec.weight (targetFaultDataResidual P ⟨site, p, hp⟩) ≤ 1 ∨
      dominatedByScheduleHook sigma (targetFaultDataResidual P ⟨site, p, hp⟩) := by
  set L := P.n + gstart + helperCount Scheme.Flag sigma with hL
  have hhelp : helperCount Scheme.Flag sigma = 2 := rfl
  set σ' := liftSchedule (k := total) sigma with hσ'
  set anc := blockHelperQ P.n total gstart 2 ghfit ⟨0, by decide⟩ with hanc
  set flag := blockHelperQ P.n total gstart 2 ghfit ⟨1, by decide⟩ with hflag
  set half := σ'.slots.length / 2 with hhalf
  set fcs := (σ'.slots.take half) ++ [(⟨XZPauli.Z, flag⟩ : ScheduledPauli (P.n + total))] ++
    (σ'.slots.drop half) with hfcs
  set TAIL := cnot flag anc ++ flagMeasZ anc ++ hadamard flag ++ flagMeasZ flag with hTAIL
  -- helper values
  have hancV : anc.val = P.n + gstart := by rw [hanc, blockHelperQ_flag_val]; simp
  have hflagV : flag.val = P.n + gstart + 1 := by rw [hflag, blockHelperQ_flag_val]
  have hancL : anc.val < L := by rw [hancV, hL, hhelp]; omega
  have hflagL : flag.val < L := by rw [hflagV, hL, hhelp]; omega
  have hancA : P.n ≤ anc.val := by rw [hancV]; omega
  have hflagA : P.n ≤ flag.val := by rw [hflagV]; omega
  have hancHelper : P.n ≤ anc.val := hancA
  have haf : flag ≠ anc := Fin.ne_of_val_ne (by rw [hancV, hflagV]; omega)
  -- σ' slot facts
  have hσdata : ∀ s ∈ σ'.slots, s.qubit.val < P.n := flag_lifted_slots_data (total := total) sigma
  have hσkind : ∀ s ∈ σ'.slots, s.kind = kk := by
    intro s hs; rw [hσ'] at hs; simp only [liftSchedule, List.mem_map] at hs
    obtain ⟨s0, hs0, rfl⟩ := hs; simpa [liftSlot] using hkind s0 hs0
  have hσnd : (σ'.slots.map (·.qubit)).Nodup := by
    have heq : σ'.slots.map (·.qubit) = (sigma.slots.map (·.qubit)).map (freshDataQ P.n total) := by
      rw [hσ']; simp [liftSchedule, List.map_map, liftSlot, Function.comp]
    rw [heq]; exact hnd.map (fun _ _ => freshDataQ_inj)
  -- fcs facts (take ++ flag ++ drop of σ'.slots)
  have hσsplit : σ'.slots = σ'.slots.take half ++ σ'.slots.drop half := (List.take_append_drop _ _).symm
  have hfcs_qa : ∀ s ∈ fcs, s.qubit ≠ anc := by
    intro s hs; rw [hfcs] at hs
    simp only [List.mem_append, List.mem_singleton] at hs
    rcases hs with (h | h) | h
    · exact Fin.ne_of_val_ne (by have := hσdata s (by rw [hσsplit]; exact List.mem_append_left _ h); omega)
    · rw [h]; exact haf
    · exact Fin.ne_of_val_ne (by have := hσdata s (by rw [hσsplit]; exact List.mem_append_right _ h); omega)
  have hfcs_belowL : ∀ s ∈ fcs, s.qubit.val < L := by
    intro s hs; rw [hfcs] at hs
    simp only [List.mem_append, List.mem_singleton] at hs
    rcases hs with (h | h) | h
    · have := hσdata s (by rw [hσsplit]; exact List.mem_append_left _ h); omega
    · rw [h]; exact hflagL
    · have := hσdata s (by rw [hσsplit]; exact List.mem_append_right _ h); omega
  have hfcs_kind : ∀ s ∈ fcs, s.qubit.val < P.n → s.kind = kk := by
    intro s hs hlt; rw [hfcs] at hs
    simp only [List.mem_append, List.mem_singleton] at hs
    rcases hs with (h | h) | h
    · exact hσkind s (by rw [hσsplit]; exact List.mem_append_left _ h)
    · exfalso; subst h; have hcon : flag.val < P.n := hlt; omega
    · exact hσkind s (by rw [hσsplit]; exact List.mem_append_right _ h)
  have hfcs_nd : (fcs.map (·.qubit)).Nodup := by
    have hmapeq : fcs.map (·.qubit) =
        (σ'.slots.take half).map (·.qubit) ++ [flag] ++ (σ'.slots.drop half).map (·.qubit) := by
      rw [hfcs]; simp [List.map_append]
    have hσmap : σ'.slots.map (·.qubit) =
        (σ'.slots.take half).map (·.qubit) ++ (σ'.slots.drop half).map (·.qubit) := by
      rw [← List.map_append, ← hσsplit]
    have hperm : List.Perm (fcs.map (·.qubit)) (flag :: σ'.slots.map (·.qubit)) := by
      rw [hmapeq, hσmap]
      simpa [List.append_assoc] using List.perm_middle
        (l₁ := (σ'.slots.take half).map (·.qubit)) (a := flag)
        (l₂ := (σ'.slots.drop half).map (·.qubit))
    refine (hperm.nodup_iff).mpr ?_
    rw [List.nodup_cons]
    refine ⟨?_, hσnd⟩
    intro hmem
    rw [List.mem_map] at hmem
    obtain ⟨s, hs, hsq⟩ := hmem
    have := hσdata s hs; rw [hsq] at this; omega
  -- flag TAIL is a helper region (acts in [P.n, L))
  have hTAIL_cab : circuitActsBelow (eraseFaults TAIL) L := by
    rw [hTAIL]; simp only [eraseFaults_append]
    exact cab_append (cab_append (cab_append (cab_erase_cnot flag anc hflagL hancL)
      (cab_erase_flagMeasZ anc hancL)) (cab_erase_hadamard flag hflagL))
      (cab_erase_flagMeasZ flag hflagL)
  have hTAIL_caa : circuitActsAbove (eraseFaults TAIL) P.n := by
    rw [hTAIL]; simp only [eraseFaults_append]
    exact caa_append (caa_append (caa_append (caa_erase_cnot flag anc hflagA hancA)
      (caa_erase_flagMeasZ anc hancA)) (caa_erase_hadamard flag hflagA))
      (caa_erase_flagMeasZ flag hflagA)
  have hTAIL_err : ∀ q0 : Fin (P.n + total), FInstr.errLoc q0 ∈ TAIL →
      P.n ≤ q0.val ∧ q0.val < L := by
    intro q0 h; rw [hTAIL] at h
    simp only [List.mem_append] at h
    rcases h with ((hc | hm) | hh) | hf
    · rcases errLoc_mem_cnot hc with rfl | rfl
      · exact ⟨hflagA, hflagL⟩
      · exact ⟨hancA, hancL⟩
    · have hq : q0 = anc := errLoc_mem_pair hm; subst hq; exact ⟨hancA, hancL⟩
    · have hq : q0 = flag := errLoc_mem_pair hh; subst hq; exact ⟨hflagA, hflagL⟩
    · have hq : q0 = flag := errLoc_mem_pair hf; subst hq; exact ⟨hflagA, hflagL⟩
  -- TAIL ++ tail preserves data (conditional)
  have hflagTail_PDA : PreservesDataAbove (eraseFaults (TAIL ++ tail)) L := by
    intro es hclean d hd
    rw [eraseFaults_append, QHL.Target.propagateCircuit_append]
    have hTAIL_data : (propagateCircuit (eraseFaults TAIL) es).paulis d = es.paulis d :=
      propagateCircuit_paulis_off (eraseFaults TAIL) d
        (fun g hg hq => by have := hTAIL_caa g hg d hq; omega) es
    have hTAIL_clean : cleanAbove (propagateCircuit (eraseFaults TAIL) es) L :=
      cleanAbove_preserved_of_actsBelow (eraseFaults TAIL) L hTAIL_cab es hclean
    rw [htailPDA _ hTAIL_clean d hd, hTAIL_data]
  -- reshape the compiled block and split into PREP / CHAIN / TAIL
  rw [compileGadgetBlock_Flag_eq] at hsite
  have hblock : compileFlagOrdered σ' anc flag =
      prep0 anc ++ (prepP flag ++ ((fcs.map (zParitySlot anc)).flatten ++ TAIL)) := by
    rw [compileFlagOrdered_reshape, ← hhalf, hfcs, hTAIL]; simp only [List.append_assoc]
  rw [show compileFlagOrdered (liftSchedule (k := total) sigma)
      (blockHelperQ P.n total gstart 2 ghfit ⟨0, by decide⟩)
      (blockHelperQ P.n total gstart 2 ghfit ⟨1, by decide⟩)
      = compileFlagOrdered σ' anc flag from rfl, hblock,
    prefixErrLocs_append, List.mem_append] at hsite
  rcases hsite with hprep0 | hsite
  · -- prep0 anc site
    rw [prefixErrLocs_prep0] at hprep0
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hprep0
    subst hprep0
    exact Or.inl (le_trans (le_of_eq
      (weight_zero_of_allI _ (fun q' => residual_prep0_site anc p _ _ q'))) (Nat.zero_le 1))
  · rw [prefixErrLocs_append, List.mem_append] at hsite
    rcases hsite with hprepP | hsite
    · -- prepP flag site
      rw [prefixErrLocs_prepP] at hprepP
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hprepP
      subst hprepP
      exact Or.inl (le_trans (le_of_eq
        (weight_zero_of_allI _ (fun q' => residual_prepP_site flag p _ _ q'))) (Nat.zero_le 1))
    · rw [prefixErrLocs_append, List.mem_append] at hsite
      rcases hsite with hchain | hTAILsite
      · -- CHAIN site: mixed chain classifier
        rcases zpsChain_site_classified anc hancHelper L hancL kk (TAIL ++ tail) hflagTail_PDA
          fcs hfcs_qa hfcs_nd hfcs_belowL hfcs_kind _ site p hp hchain with hle | hdom
        · exact Or.inl hle
        · refine Or.inr ?_
          have hqmem : ∀ q : Fin P.n, freshDataQ P.n total q ∈ fcs.map (·.qubit) →
              q ∈ sigma.slots.map (·.qubit) := by
            intro q hq
            rw [hfcs] at hq
            simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
              List.mem_singleton] at hq
            have hqlt : (freshDataQ P.n total q).val < P.n := by simp [freshDataQ_val]
            have hnotflag : freshDataQ P.n total q ≠ flag := Fin.ne_of_val_ne (by omega)
            have hmem_σ : freshDataQ P.n total q ∈ σ'.slots.map (·.qubit) := by
              rw [show σ'.slots.map (·.qubit) = (σ'.slots.take half).map (·.qubit) ++
                    (σ'.slots.drop half).map (·.qubit) from by rw [← List.map_append, ← hσsplit]]
              rcases hq with (h | h) | h
              · exact List.mem_append_left _ h
              · exact absurd h hnotflag
              · exact List.mem_append_right _ h
            have heq2 : σ'.slots.map (·.qubit) =
                (sigma.slots.map (·.qubit)).map (freshDataQ P.n total) := by
              rw [hσ']; simp [liftSchedule, List.map_map, liftSlot, Function.comp]
            rw [heq2, List.mem_map] at hmem_σ
            obtain ⟨x, hx, hxq⟩ := hmem_σ
            rwa [freshDataQ_inj hxq] at hx
          intro q
          rcases hdom q with h | ⟨hval, hmem⟩
          · exact Or.inl h
          · have hqmem_q := hqmem q hmem
            have hne : sigma.slots ≠ [] := by
              intro he; rw [he] at hqmem_q; simp at hqmem_q
            have hkkeq : scheduleKind sigma = kk.toPauli := by
              obtain ⟨s0, srest, hs0⟩ := List.exists_cons_of_ne_nil hne
              have hs0mem : s0 ∈ sigma.slots := by rw [hs0]; exact List.mem_cons_self
              simp only [scheduleKind, hs0, List.head?_cons, hkind s0 hs0mem]
            exact Or.inr ⟨hval.trans hkkeq.symm, hqmem_q⟩
      · -- TAIL site
        exact Or.inl (helperRegion_site_wle1 TAIL L hTAIL_cab hTAIL_caa hTAIL_err
          tail htailPDA _ site p hp hTAILsite)

/-! ## Flag is an instance of the framework -/

/-- `flag_gadget_site_classified` is exactly a `SchemeClassifier .Flag`. -/
theorem flag_SchemeClassifier : SchemeClassifier Scheme.Flag :=
  fun sigma kk hkind hnd gstart ghfit tail htailPDA cursor site p hp hsite =>
    flag_gadget_site_classified sigma kk hkind hnd gstart ghfit tail htailPDA cursor site p hp hsite

/-- **The compiled HGP Flag-extraction bar-Z distance.**  Every clean-start run of
the Flag-compiled HGP circuit whose data residual is bar-Z fired `≥ d` faults, for
every `d ≥ 2`, through the verbatim bridge — closing the fourth (and final)
extraction scheme of the parametric HGP PCC pipeline. -/
theorem hgpFlag_compiled_barZ_distance (d : Nat) (hd : 2 ≤ d) :
    ∀ sigma : QCState ((hgpUParams d hd).n + hgpSchemeHelpers Scheme.Flag d),
      qceval (hgpSchemeCircuit Scheme.Flag d)
        (QCState.clean ((hgpUParams d hd).n + hgpSchemeHelpers Scheme.Flag d)) sigma →
      (hgpLogicalClass d (exactUnionHGPSpec d hd)).contains
        (dataErrorOfQCState (hgpUParams d hd) (hgpSchemeHelpers Scheme.Flag d) sigma) →
      d ≤ sigma.lambda :=
  hgpScheme_compiled_barZ_distance Scheme.Flag d hd
    (hgpScheme_hvalid Scheme.Flag d hd (hgpFlag_leafClean d hd) flag_SchemeClassifier)

/--
info: 'QStab.QClifford.Compile.flag_gadget_site_classified' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms flag_gadget_site_classified

/--
info: 'QStab.QClifford.Compile.hgpFlag_compiled_barZ_distance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hgpFlag_compiled_barZ_distance

/--
info: 'QStab.QClifford.Compile.hgpFlag_leafClean' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hgpFlag_leafClean

end QStab.QClifford.Compile
