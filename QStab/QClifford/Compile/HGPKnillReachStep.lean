import QStab.QClifford.Compile.HGPKnillReach
import QStab.QClifford.Compile.HGPReachCommon

/-!
# HGP-Knill reach: the per-gadget step

One compiled Knill gadget of the HGP program (`compileGadgetBlock Scheme.Knill
(hgpSchedule d hd k) …`), run under its row-0 injection script
(`knillPairsScript … (hgpInjs d k.val)`), from a state whose **data block**
carries the row-prefix `hgpRowPref d k.val`:

1. advances the row prefix by one column (`hgpRowPref d (k.val+1)`) on the data
   block — via the chain's `injectE` data update, `injectE_congr`, and
   `hgp_injectE_advances_amb`;
2. fires `1` fault iff the gadget is an injector (`k.val < d`) — via `injCount`
   and `hgpInjs_count`;
3. advances the detector cursor by the block's detector count
   (`= (hgpSchedule d hd k).slots.length`, i.e. `compiledDetectorCount .Knill`);
4. preserves every earlier detector;
5. leaves the gadget's own detector-XOR (`detectorXorFromAcc` over its detector
   window — exactly the shifted readout, since `compiledReadoutFlags .Knill`
   is `finRange` of consecutive flags) **false** — via the chain's
   `scheduleParityList` value and `hgp_heven_amb`.

**Invariant is data-only.**  Unlike the NZ step (`hgp_reach_step`, whose single
ancilla returns to `I` because its parity is even, and which needs *all*
detectors quiet), each Knill ancilla couples to exactly one data qubit, so after
the gadget it carries that qubit's coupled Pauli — an `X`-component on the
`X̄` residual, **not** `I`.  Hence the fold invariant constrains only the data
block (`q.val < n`); the helpers/ancillas are unconstrained (each gadget
`prep0`-resets its own fresh ancillas, so their input values are irrelevant).
Only the per-gadget detector-XOR — not any global all-detectors-false — cancels.

Everything routes through `runFScript_knillPairs_chain` and the shared,
scheme-independent lemmas in `HGPReachCommon`; no NZ lemma is copied.  The
ambient helper count `total` is abstract (the fold instantiates it at
`programHelperCount (hgpSchemeProgram Scheme.Knill d)`); `compileGadgetBlock_Knill_eq`
bridges the compiled block to `compileKnillOrdered`/`knillPairsCircuit`.
-/

namespace QStab.QClifford.Compile

open QStab QStab.QClifford QStab.QClifford.PCC
open QStab.Examples.HGPParametric
open QHL QHL.CodeHGPSchedule
open QHL.Source.Examples.HGPUnionSpec

/-- Every block ancilla is a helper qubit (`n ≤ ·`). -/
private theorem blockHelpers_ge {n total start width : Nat} (hfit : start + width ≤ total)
    (a : Fin (n + total)) (ha : a ∈ blockHelpers n total start width hfit) :
    n ≤ a.val := by
  rw [blockHelpers] at ha
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
  simp only [blockHelperQ]
  omega

/-- Lifted schedule slot qubits are data-block indices (`< n`). -/
private theorem lifted_slot_data {n total : Nat} (sigma : RuleSchedule n)
    (s : ScheduledPauli (n + total))
    (hs : s ∈ (liftSchedule (k := total) sigma).slots) : s.qubit.val < n := by
  have h : (liftSchedule (k := total) sigma).slots = sigma.slots.map liftSlot := rfl
  rw [h] at hs
  obtain ⟨s0, _, rfl⟩ := List.mem_map.mp hs
  show (freshDataQ n total s0.qubit).val < n
  rw [freshDataQ_val]
  exact s0.qubit.isLt

/-- **The per-gadget Knill reach step** (data-only invariant). -/
theorem hgpKnill_reach_step (d : Nat) (hd : 2 ≤ d) (k : Fin (2 * ((d - 1) * d)))
    (total start detectorStart : Nat)
    (hfit : start + helperCount Scheme.Knill (hgpSchedule d hd k) ≤ total)
    (es : ErrorState (d * d + (d - 1) * (d - 1) + total))
    (hes_data : ∀ q : Fin (d * d + (d - 1) * (d - 1) + total),
      q.val < d * d + (d - 1) * (d - 1) →
      es.paulis q = (dataInputState (k := total) (hgpRowPref d k.val)).paulis q)
    (hcursor : es.detectorCursor = detectorStart) :
    let pairs := (liftSchedule (k := total) (hgpSchedule d hd k)).slots.zip
        (blockHelpers (d * d + (d - 1) * (d - 1)) total start
          (hgpSchedule d hd k).slots.length hfit)
    let run := runFScript (compileGadgetBlock Scheme.Knill (hgpSchedule d hd k) start hfit)
        (knillPairsScript pairs (hgpInjs d k.val)) es
    (∀ q : Fin (d * d + (d - 1) * (d - 1) + total),
      q.val < d * d + (d - 1) * (d - 1) →
      run.1.paulis q
        = (dataInputState (k := total) (hgpRowPref d (k.val + 1))).paulis q) ∧
    run.2 = (if k.val < d then 1 else 0) ∧
    run.1.detectorCursor = detectorStart + (hgpSchedule d hd k).slots.length ∧
    (∀ j, j < detectorStart → run.1.detectors j = es.detectors j) ∧
    detectorXorFromAcc detectorStart (hgpSchedule d hd k).slots.length run.1 false = false := by
  intro pairs run
  -- lengths
  have hslots_len : (liftSchedule (k := total) (hgpSchedule d hd k)).slots.length
      = (hgpSchedule d hd k).slots.length := by
    show ((hgpSchedule d hd k).slots.map liftSlot).length = _
    rw [List.length_map]
  have hanc_len : (blockHelpers (d * d + (d - 1) * (d - 1)) total start
      (hgpSchedule d hd k).slots.length hfit).length = (hgpSchedule d hd k).slots.length := by
    rw [blockHelpers, List.length_map, List.length_finRange]
  have hfst : pairs.map Prod.fst = (liftSchedule (k := total) (hgpSchedule d hd k)).slots :=
    List.map_fst_zip (le_of_eq (by rw [hslots_len, hanc_len]))
  have hpairs_len : pairs.length = (hgpSchedule d hd k).slots.length := by
    show ((liftSchedule (k := total) (hgpSchedule d hd k)).slots.zip _).length = _
    rw [List.length_zip, hslots_len, hanc_len, Nat.min_self]
  -- ancillas are helpers; slots are data
  have hanc_ge : ∀ a ∈ blockHelpers (d * d + (d - 1) * (d - 1)) total start
      (hgpSchedule d hd k).slots.length hfit, d * d + (d - 1) * (d - 1) ≤ a.val :=
    fun a ha => blockHelpers_ge hfit a ha
  have hslot_data' : ∀ s ∈ (liftSchedule (k := total) (hgpSchedule d hd k)).slots,
      s.qubit.val < d * d + (d - 1) * (d - 1) :=
    fun s hs => lifted_slot_data (hgpSchedule d hd k) s hs
  -- chain hypotheses
  have hnodup : (pairs.map (fun p => p.1.qubit)).Nodup := by
    have hmap : pairs.map (fun p => p.1.qubit)
        = (liftSchedule (k := total) (hgpSchedule d hd k)).slots.map (·.qubit) := by
      rw [show (fun p : ScheduledPauli _ × Fin _ => p.1.qubit)
            = (fun s : ScheduledPauli _ => s.qubit) ∘ Prod.fst from rfl,
        ← List.map_map, hfst]
    rw [hmap]
    exact lifted_nodup (hgpSchedule d hd k) (hgpSchedule_support_nodup d hd k)
  have hdata : ∀ pair ∈ pairs, es.paulis pair.1.qubit
      = (dataInputState (k := total) (hgpRowPref d k.val)).paulis pair.1.qubit :=
    fun pair hpair => hes_data pair.1.qubit
      (hslot_data' pair.1 (List.of_mem_zip hpair).1)
  have hself : ∀ pair ∈ pairs, pair.1.qubit ≠ pair.2 := by
    intro pair hpair
    obtain ⟨h1, h2⟩ := List.of_mem_zip hpair
    exact lifted_slot_ne_anc (hgpSchedule d hd k) pair.2 (hanc_ge pair.2 h2) pair.1 h1
  have hslotanc : ∀ sp ∈ pairs, ∀ ap ∈ pairs, sp.1.qubit ≠ ap.2 := by
    intro sp hsp ap hap
    obtain ⟨hs1, _⟩ := List.of_mem_zip hsp
    obtain ⟨_, ha2⟩ := List.of_mem_zip hap
    exact lifted_slot_ne_anc (hgpSchedule d hd k) ap.2 (hanc_ge ap.2 ha2) sp.1 hs1
  -- the compiled block is the scripted `knillPairsCircuit`
  have hcirc : compileGadgetBlock Scheme.Knill (hgpSchedule d hd k) start hfit
      = knillPairsCircuit pairs := by
    rw [compileGadgetBlock_Knill_eq]; rfl
  -- apply the chain
  obtain ⟨hpar, hcur, hprev, hdat, hcnt⟩ :=
    runFScript_knillPairs_chain pairs (hgpInjs d k.val)
      (dataInputState (k := total) (hgpRowPref d k.val)).paulis false es detectorStart
      hcursor hnodup hdata hself hslotanc
  have hrun_eq : run = runFScript (knillPairsCircuit pairs)
      (knillPairsScript pairs (hgpInjs d k.val)) es := by
    show runFScript (compileGadgetBlock Scheme.Knill (hgpSchedule d hd k) start hfit)
      (knillPairsScript pairs (hgpInjs d k.val)) es = _
    rw [hcirc]
  rw [hrun_eq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- data advance on the data block
    intro q hqn
    have hqpairs : ∀ pair ∈ pairs, q ≠ pair.2 := fun pair hpair heq => by
      have := hanc_ge pair.2 (List.of_mem_zip hpair).2
      rw [heq] at hqn; omega
    rw [hdat q hqpairs, hfst, ← hgp_injectE_advances_amb d hd k total]
    apply injectE_congr
    · exact fun s hs => hes_data s.qubit (hslot_data' s hs)
    · exact hes_data q hqn
  · -- fault count
    rw [hcnt, hfst,
      injCount_eq_count _ (hgpInjs d k.val) (hgpInjs_length_amb d hd k total), hgpInjs_count]
  · -- cursor
    rw [hcur, hpairs_len]
  · -- earlier detectors
    exact hprev
  · -- gadget detector-XOR is quiet
    rw [← hpairs_len, hpar, hfst]
    exact hgp_heven_amb d hd k total

/-! ## Regression guard (axiom pin) -/

/--
info: 'QStab.QClifford.Compile.hgpKnill_reach_step' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hgpKnill_reach_step

end QStab.QClifford.Compile
