import QStab.QClifford.Compile.HGPSchemeFramework
import QStab.QClifford.Compile.ShorClassify

/-!
# Knill-extraction HGP compiled bar-Z distance (framework instance)

The Knill scheme is transversal: each written slot gets its **own** freshly
prepared ancilla (`knillSlot = prep0 anc ++ zParitySlot anc slot ++ rawMeasZ
anc`), so a fault only ever reaches that slot's own data qubit — every residual
has weight `≤ 1`, with no correlated hook.  Its two framework inputs:

* `hgpKnill_leafClean` — the data-preservation witness (data qubits are CNOT
  *controls*, ancillas are reset, so the block preserves data unconditionally);
* `knill_SchemeClassifier` — the classifier, whose right (hook) branch is never
  needed: every site is weight `≤ 1`.

Everything goes through `compileGadgetBlock .Knill` — the syntactic scheme
compilation — reusing the Shor site-locality machinery (`prefixSite_local`,
`circuitActsAbove`) and the NZ per-gate lemmas.
-/

namespace QStab.QClifford.Compile

open QStab.QClifford
open QHL QHL.CodeHGPSchedule
open QHL.Source.Examples.HGP QHL.Source.Examples.HGPUnionSpec QStab.Examples.HGPParametric

/-! ## Data preservation -/

/-- One Knill slot preserves every non-ancilla qubit: `prep0` makes the ancilla
Z-free, the parity coupling preserves data (controls / H-sandwich), and the raw
measurement touches no Pauli. -/
theorem knillSlot_preserves_data {nq : Nat} (anc : Fin nq) (slot : ScheduledPauli nq)
    (hqa : slot.qubit ≠ anc) (es : ErrorState nq) (d : Fin nq) (hd : d ≠ anc) :
    (propagateCircuit (eraseFaults (knillSlot slot anc)) es).paulis d = es.paulis d := by
  have hc : knillSlot slot anc = prep0 anc ++ zParitySlot anc slot ++ rawMeasZ anc := rfl
  rw [hc, eraseFaults_append, eraseFaults_append,
    QHL.Target.propagateCircuit_append, QHL.Target.propagateCircuit_append]
  have hprep : eraseFaults (prep0 anc) = [Gate.prepZero anc] := by simp [prep0, eraseFaults]
  have hmeas : eraseFaults (rawMeasZ anc) = [Gate.measZ anc] := by simp [rawMeasZ, eraseFaults]
  set esA := propagateCircuit (eraseFaults (prep0 anc)) es with hesA
  have hesAd : esA.paulis d = es.paulis d := by
    rw [hesA, hprep]; simp only [propagateCircuit]
    exact propagateGate_prepZero_paulis_ne anc es d hd
  have hesAanc : zPart (esA.paulis anc) = Pauli.I := by
    rw [hesA, hprep]; simp only [propagateCircuit, propagateGate_prepZero_self]; rfl
  set esB := propagateCircuit (eraseFaults (zParitySlot anc slot)) esA with hesB
  have hesBd : esB.paulis d = es.paulis d := by
    rw [hesB, zParitySlot_preserves_data anc slot hqa esA hesAanc d hd, hesAd]
  rw [hmeas]; simp only [propagateCircuit, propagateGate_measZ_paulis]; exact hesBd

/-- The Knill block preserves every non-ancilla qubit, when the slot ancillas
are disjoint from that qubit. -/
theorem knillSlots_preserve_data {nq : Nat} :
    ∀ (pairs : List (ScheduledPauli nq × Fin nq)) (es : ErrorState nq) (d : Fin nq),
      (∀ pc ∈ pairs, pc.1.qubit ≠ pc.2) → (∀ pc ∈ pairs, d ≠ pc.2) →
      (propagateCircuit (eraseFaults
          ((pairs.map (fun sa => knillSlot sa.1 sa.2)).flatten)) es).paulis d = es.paulis d := by
  intro pairs
  induction pairs with
  | nil => intro es d _ _; simp [propagateCircuit]
  | cons p0 rest ih =>
      intro es d hqa hd
      have hcirc : eraseFaults (((p0 :: rest).map (fun sa => knillSlot sa.1 sa.2)).flatten)
          = eraseFaults (knillSlot p0.1 p0.2) ++
            eraseFaults ((rest.map (fun sa => knillSlot sa.1 sa.2)).flatten) := by
        simp only [List.map_cons, List.flatten_cons, eraseFaults_append]
      rw [hcirc, QHL.Target.propagateCircuit_append]
      have hqa0 : p0.1.qubit ≠ p0.2 := hqa p0 List.mem_cons_self
      have hd0 : d ≠ p0.2 := hd p0 List.mem_cons_self
      rw [ih _ d (fun pc hpc => hqa pc (List.mem_cons_of_mem _ hpc))
        (fun pc hpc => hd pc (List.mem_cons_of_mem _ hpc)),
        knillSlot_preserves_data p0.2 p0.1 hqa0 es d hd0]

/-! ## Block shape and the `LeafClean` fields -/

/-- The compiled Knill gadget block is `compileKnillOrdered` over the lifted
schedule and the block's transversal ancillas. -/
theorem compileGadgetBlock_Knill_eq {n total : Nat} (sigma : RuleSchedule n)
    (start : Nat) (hfit : start + helperCount Scheme.Knill sigma ≤ total) :
    compileGadgetBlock Scheme.Knill sigma start hfit
      = compileKnillOrdered (liftSchedule (k := total) sigma)
          (blockHelpers n total start sigma.slots.length hfit) := rfl

/-- Value window of a block ancilla. -/
theorem mem_blockHelpers_val {n total start w : Nat} {hfit : start + w ≤ total}
    {a : Fin (n + total)} (ha : a ∈ blockHelpers n total start w hfit) :
    n + start ≤ a.val ∧ a.val < n + start + w := by
  unfold blockHelpers at ha
  rw [List.mem_map] at ha
  obtain ⟨b, _, rfl⟩ := ha
  have := b.isLt; simp only [blockHelperQ]; omega

/-- Zip left/right projections match the lifted slots / ancillas. -/
theorem knill_zip_facts {n total : Nat} (sigma : RuleSchedule n) (start : Nat)
    (hfit : start + helperCount Scheme.Knill sigma ≤ total)
    (pc : ScheduledPauli (n + total) × Fin (n + total))
    (hpc : pc ∈ (liftSchedule (k := total) sigma).slots.zip
      (blockHelpers n total start sigma.slots.length hfit)) :
    pc.1.qubit.val < n ∧ (n + start ≤ pc.2.val ∧ pc.2.val < n + start + sigma.slots.length) := by
  refine ⟨?_, mem_blockHelpers_val (List.of_mem_zip hpc).2⟩
  have hs := (List.of_mem_zip hpc).1
  simp only [liftSchedule, List.mem_map] at hs
  obtain ⟨s0, _, hseq⟩ := hs
  rw [← hseq]; simp only [liftSlot, freshDataQ_val]; exact s0.qubit.isLt

/-- Acts-below (the `LeafClean` first field) for the Knill block. -/
theorem knillBlock_cab {n total : Nat} (sigma : RuleSchedule n) (start : Nat)
    (hfit : start + helperCount Scheme.Knill sigma ≤ total) :
    circuitActsBelow (eraseFaults (compileGadgetBlock Scheme.Knill sigma start hfit))
      (n + start + helperCount Scheme.Knill sigma) := by
  rw [compileGadgetBlock_Knill_eq]
  have hw : helperCount Scheme.Knill sigma = sigma.slots.length := rfl
  apply cab_erase_flatten_map
  intro sa hsa
  obtain ⟨hq, hc1, hc2⟩ := knill_zip_facts sigma start hfit sa hsa
  have hqL : sa.1.qubit.val < n + start + helperCount Scheme.Knill sigma := by rw [hw]; omega
  have hcL : sa.2.val < n + start + helperCount Scheme.Knill sigma := by rw [hw]; omega
  -- knillSlot = prep0 ++ zParitySlot ++ rawMeasZ
  have hc : knillSlot sa.1 sa.2 = prep0 sa.2 ++ zParitySlot sa.2 sa.1 ++ rawMeasZ sa.2 := rfl
  rw [hc, eraseFaults_append, eraseFaults_append]
  refine cab_append (cab_append (cab_erase_prep0 sa.2 hcL) ?_) (cab_erase_rawMeasZ sa.2 hcL)
  exact cab_erase_zParitySlot sa.2 sa.1 hcL hqL

/-- Preservation at floor `n + start` for the Knill block (in fact
unconditional — data qubits are controls). -/
theorem knillBlock_PDA {n total : Nat} (sigma : RuleSchedule n) (start : Nat)
    (hfit : start + helperCount Scheme.Knill sigma ≤ total) :
    PreservesDataAbove (eraseFaults (compileGadgetBlock Scheme.Knill sigma start hfit))
      (n + start) := by
  intro es _ d hd
  rw [compileGadgetBlock_Knill_eq]
  refine knillSlots_preserve_data _ es d ?_ ?_
  · intro pc hpc
    obtain ⟨hq, hc1, _⟩ := knill_zip_facts sigma start hfit pc hpc
    exact Fin.ne_of_val_ne (by omega)
  · intro pc hpc
    obtain ⟨_, hc1, _⟩ := knill_zip_facts sigma start hfit pc hpc
    exact Fin.ne_of_val_ne (by omega)

/-! ## The Knill `LeafClean` witness -/

/-- Every leaf of `hgpSchemeProgram .Knill` acts below its ceiling and preserves
data — the bundle `site_split_gen` consumes. -/
theorem hgpKnill_leafClean (d : Nat) (hd : 2 ≤ d) :
    LeafClean (total := hgpSchemeHelpers Scheme.Knill d) (hgpSchemeProgram Scheme.Knill d) := by
  intro sc sg hml st hf
  obtain ⟨i, rfl, rfl⟩ := hgpSchemeProgram_measLeaf Scheme.Knill d hd sc sg hml
  exact ⟨knillBlock_cab _ _ _, knillBlock_PDA _ _ _⟩

/-! ## Gate locality of one Knill slot -/

/-- `zParitySlot anc slot` is definitionally the Shor coupling slot `slot ↦ anc`
(both dispatch on `slot.kind` to the same gates) — lets the Knill gate-locality
reuse the Shor lemmas. -/
theorem zParitySlot_eq_shorCouplingSlot {nq : Nat} (anc : Fin nq) (slot : ScheduledPauli nq) :
    zParitySlot anc slot = shorCouplingSlot slot anc := by
  cases h : slot.kind <;> simp [zParitySlot, shorCouplingSlot, h]

/-- Every erased gate of one Knill slot acts only on `{slot.qubit, anc}`. -/
theorem knillSlot_gates_actOn {nq : Nat} (slot : ScheduledPauli nq) (anc : Fin nq)
    (g : Gate nq) (hg : g ∈ eraseFaults (knillSlot slot anc)) :
    ∀ q : Fin nq, gateActsOn g q → q = slot.qubit ∨ q = anc := by
  intro q hq
  have hc : knillSlot slot anc = prep0 anc ++ shorCouplingSlot slot anc ++ rawMeasZ anc := by
    show prep0 anc ++ zParitySlot anc slot ++ rawMeasZ anc = _
    rw [zParitySlot_eq_shorCouplingSlot]
  rw [hc, eraseFaults_append, eraseFaults_append, List.mem_append, List.mem_append] at hg
  rcases hg with (hg | hg) | hg
  · simp only [prep0, eraseFaults, List.mem_singleton] at hg
    subst hg; cases hq; exact Or.inr rfl
  · exact shorCouplingSlot_gates_actOn slot anc g hg q hq
  · simp only [rawMeasZ, eraseFaults, List.mem_singleton] at hg
    subst hg; cases hq; exact Or.inr rfl

/-- errLoc markers of one Knill slot lie in `{slot.qubit, anc}`. -/
theorem knillSlot_errLoc {nq : Nat} (slot : ScheduledPauli nq) (anc q0 : Fin nq)
    (h : FInstr.errLoc q0 ∈ knillSlot slot anc) : q0 = slot.qubit ∨ q0 = anc := by
  have hc : knillSlot slot anc = prep0 anc ++ shorCouplingSlot slot anc ++ rawMeasZ anc := by
    show prep0 anc ++ zParitySlot anc slot ++ rawMeasZ anc = _
    rw [zParitySlot_eq_shorCouplingSlot]
  rw [hc, List.mem_append, List.mem_append] at h
  rcases h with (hp | hz) | hm
  · exact Or.inr (errLoc_mem_pair hp)
  · exact shorCouplingSlot_errLoc slot anc q0 hz
  · exact Or.inr (errLoc_mem_pair hm)

/-! ## The Knill classifier: every site is weight ≤ 1 -/

/-- **Every fault site of the Knill block has weight-`≤ 1` residual.**  The fault
touches a single transversal slot; that slot localizes to its data qubit and
ancilla, and every later slot preserves the data block (data qubits are CNOT
controls), so the residual is supported on the one slot's data qubit. -/
theorem knill_site_wle1 {P : QECParams} {total : Nat}
    (tail : FCircuit (P.n + total)) (L : Nat) (hnL : P.n ≤ L)
    (htailPDA : PreservesDataAbove (eraseFaults tail) L) :
    ∀ (pairs : List (ScheduledPauli (P.n + total) × Fin (P.n + total)))
      (hqA : ∀ pc ∈ pairs, pc.1.qubit.val < P.n)
      (hcA : ∀ pc ∈ pairs, P.n ≤ pc.2.val) (hcB : ∀ pc ∈ pairs, pc.2.val < L)
      (cursor : Nat) (site : PCC.ErrLocWithContext (P.n + total)) (p : Pauli) (hp : p ≠ Pauli.I),
      site ∈ prefixErrLocsWithContextAux cursor
        ((pairs.map (fun sa => knillSlot sa.1 sa.2)).flatten) tail →
        ErrorVec.weight (targetFaultDataResidual P ⟨site, p, hp⟩) ≤ 1 := by
  intro pairs
  induction pairs with
  | nil => intro _ _ _ cursor site p hp hsite; simp [prefixErrLocsWithContextAux] at hsite
  | cons p0 rest ih =>
      intro hqA hcA hcB cursor site p hp hsite
      have hcirc : ((p0 :: rest).map (fun sa => knillSlot sa.1 sa.2)).flatten
          = knillSlot p0.1 p0.2 ++ (rest.map (fun sa => knillSlot sa.1 sa.2)).flatten := by
        simp only [List.map_cons, List.flatten_cons]
      rw [hcirc, prefixErrLocs_append, List.mem_append] at hsite
      have hqA' : ∀ pc ∈ rest, pc.1.qubit.val < P.n := fun pc h => hqA pc (List.mem_cons_of_mem _ h)
      have hcA' : ∀ pc ∈ rest, P.n ≤ pc.2.val := fun pc h => hcA pc (List.mem_cons_of_mem _ h)
      have hcB' : ∀ pc ∈ rest, pc.2.val < L := fun pc h => hcB pc (List.mem_cons_of_mem _ h)
      rcases hsite with hleft | hright
      · set S : Fin (P.n + total) → Prop := fun q => q = p0.1.qubit ∨ q = p0.2 with hS
        obtain ⟨hSq, Ys, hsuf, hYs⟩ :=
          prefixSite_local (knillSlot p0.1 p0.2) S
            (fun g hg q hq => knillSlot_gates_actOn p0.1 p0.2 g hg q hq)
            (fun q0 h => knillSlot_errLoc p0.1 p0.2 q0 h) cursor _ site hleft
        have hq0lt : p0.1.qubit.val < P.n := hqA p0 List.mem_cons_self
        have hp02L : p0.2.val < L := hcB p0 List.mem_cons_self
        have hSlt : ∀ q, S q → q.val < L := by
          intro q hq; rcases hq with rfl | rfl
          · exact lt_of_lt_of_le hq0lt hnL
          · exact hp02L
        have hSqL : site.q.val < L := hSlt site.q hSq
        refine weight_le_one_of_single _ ⟨p0.1.qubit.val, hq0lt⟩ ?_
        intro q' hq'
        have hqne : freshDataQ P.n total q' ≠ p0.1.qubit := by
          intro he; apply hq'; apply Fin.ext
          simpa [freshDataQ_val] using congrArg Fin.val he
        have hqnc : freshDataQ P.n total q' ≠ p0.2 := by
          refine Fin.ne_of_val_ne ?_
          have h2 := hcA p0 List.mem_cons_self; have := q'.isLt
          simp only [freshDataQ_val]; omega
        have hqnS : ¬ S (freshDataQ P.n total q') := fun h => h.elim hqne hqnc
        show (propagateCircuit site.suffix
            ((PCC.cleanAtDetector site.detectorStart).inject site.q p)).paulis
            (freshDataQ P.n total q') = Pauli.I
        set es0 := (PCC.cleanAtDetector site.detectorStart).inject site.q p with hes0
        rw [hsuf, eraseFaults_append, QHL.Target.propagateCircuit_append]
        set esA := propagateCircuit Ys es0 with hesA
        have hes0_off : ∀ dd : Fin (P.n + total), ¬ S dd → es0.paulis dd = Pauli.I := by
          intro dd hdd
          have hcond : ¬ (dd = site.q) := fun he => hdd (by rw [he]; exact hSq)
          rw [hes0, injectClean_paulis, if_neg hcond]
        have hYsBelow : circuitActsBelow Ys L := fun g hg q hq => hSlt q (hYs g hg q hq)
        have hesA_off : ∀ dd : Fin (P.n + total), ¬ S dd → esA.paulis dd = Pauli.I := by
          intro dd hdd
          rw [hesA, propagateCircuit_paulis_off Ys dd (fun g hg hq => hdd (hYs g hg dd hq)) es0]
          exact hes0_off dd hdd
        have hcleanA : cleanAbove esA L := by
          rw [hesA]
          refine cleanAbove_preserved_of_actsBelow Ys L hYsBelow es0 ?_
          intro h hh
          refine hes0_off h ?_
          rintro (rfl | rfl) <;> omega
        -- later slots preserve the data qubit
        rw [QHL.Target.propagateCircuit_append]
        set esB := propagateCircuit
          (eraseFaults ((rest.map (fun sa => knillSlot sa.1 sa.2)).flatten)) esA with hesB
        have hesB_data : esB.paulis (freshDataQ P.n total q') = Pauli.I := by
          rw [hesB, knillSlots_preserve_data rest esA (freshDataQ P.n total q') ?_ ?_]
          · exact hesA_off _ hqnS
          · intro pc hpc
            exact Fin.ne_of_val_ne (by have := hqA' pc hpc; have := hcA' pc hpc; omega)
          · intro pc hpc
            exact Fin.ne_of_val_ne (by have := q'.isLt; have := hcA' pc hpc
                                       simp only [freshDataQ_val]; omega)
        have hcleanB : cleanAbove esB L := by
          rw [hesB]
          refine cleanAbove_preserved_of_actsBelow _ L ?_ esA hcleanA
          apply cab_erase_flatten_map
          intro pc hpc
          have hc : knillSlot pc.1 pc.2 = prep0 pc.2 ++ zParitySlot pc.2 pc.1 ++ rawMeasZ pc.2 := rfl
          rw [hc, eraseFaults_append, eraseFaults_append]
          refine cab_append (cab_append (cab_erase_prep0 pc.2 (hcB' pc hpc)) ?_)
            (cab_erase_rawMeasZ pc.2 (hcB' pc hpc))
          exact cab_erase_zParitySlot pc.2 pc.1 (hcB' pc hpc)
            (lt_of_lt_of_le (hqA' pc hpc) hnL)
        rw [htailPDA esB hcleanB (freshDataQ P.n total q') q'.isLt]
        exact hesB_data
      · exact ih hqA' hcA' hcB' _ site p hp hright

/-- `knill_site_wle1` packaged as a `SchemeClassifier .Knill` (the hook branch is
never taken — every Knill fault is weight `≤ 1`). -/
theorem knill_SchemeClassifier : SchemeClassifier Scheme.Knill := by
  intro P total sigma kk _ _ gstart ghfit tail htailPDA cursor site p hp hsite
  left
  rw [compileGadgetBlock_Knill_eq] at hsite
  refine knill_site_wle1 tail (P.n + gstart + helperCount Scheme.Knill sigma) (by omega)
    htailPDA ((liftSchedule (k := total) sigma).slots.zip
      (blockHelpers P.n total gstart sigma.slots.length ghfit)) ?_ ?_ ?_ cursor site p hp hsite
  · intro pc hpc; exact (knill_zip_facts sigma gstart ghfit pc hpc).1
  · intro pc hpc; have := (knill_zip_facts sigma gstart ghfit pc hpc).2.1; omega
  · intro pc hpc
    have := (knill_zip_facts sigma gstart ghfit pc hpc).2.2
    have hw : helperCount Scheme.Knill sigma = sigma.slots.length := rfl
    rw [hw]; omega

/-! ## The Knill instance -/

/-- **The Knill-extraction HGP compiled bar-Z distance** — through the framework
and the verbatim bridge. -/
theorem hgpKnill_compiled_barZ_distance (d : Nat) (hd : 2 ≤ d) :
    ∀ sigma : QCState ((hgpUParams d hd).n + hgpSchemeHelpers Scheme.Knill d),
      qceval (hgpSchemeCircuit Scheme.Knill d)
        (QCState.clean ((hgpUParams d hd).n + hgpSchemeHelpers Scheme.Knill d)) sigma →
      (hgpLogicalClass d (exactUnionHGPSpec d hd)).contains
        (dataErrorOfQCState (hgpUParams d hd) (hgpSchemeHelpers Scheme.Knill d) sigma) →
      d ≤ sigma.lambda :=
  hgpScheme_compiled_barZ_distance Scheme.Knill d hd
    (hgpScheme_hvalid Scheme.Knill d hd (hgpKnill_leafClean d hd) knill_SchemeClassifier)

/-! ## Regression guards -/

/--
info: 'QStab.QClifford.Compile.hgpKnill_leafClean' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hgpKnill_leafClean

/--
info: 'QStab.QClifford.Compile.hgpKnill_compiled_barZ_distance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hgpKnill_compiled_barZ_distance

end QStab.QClifford.Compile
