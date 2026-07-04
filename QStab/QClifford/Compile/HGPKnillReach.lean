import QStab.QClifford.Compile.NZReachCalculus
import QStab.QClifford.Compile.HGPKnillAssembly

/-!
# Knill reach foundation: the scripted per-slot detector-tracking chain

The compiled Knill gadget is `compileKnillOrdered = (pairs.map knillSlot).flatten`
with one fresh ancilla PER slot (`knillSlot slot anc = prep0 anc ++ zParitySlot anc
slot ++ rawMeasZ anc`).  Unlike NZ's single shared ancilla, each slot's `rawMeasZ`
is its own detector; the reach acceptance `undetected` is the **XOR** of a gadget's
per-slot detectors (`syndromeBit`), which cancels for a residual that commutes with
the stabilizer — so the NZ "all raw detectors false" route (`runFScript_nzBlock`'s
`heven`) does **not** apply (Knill Z-check slots genuinely fire on X residuals).

This file builds the scripted (fault-injected) analogue of the no-fault
`knillPairsCircuit_chain`: running `knillPairsCircuit` under its injection script,
the per-slot detector XOR equals `scheduleParityList` of the *injected* data
(`injectE`), the data gains `X` at the injected slots, the cursor advances by the
pair count, earlier detectors are preserved, and the fault count is `injCount`.
This is the atom the HGP-Knill per-gadget reach step will fold over; `undetected`
then follows by the same parity fact behind `hgp_heven` (XOR = stabilizer parity =
0).  It does **not** yet close `hgpKnill_vcgen_reachD` or `hgpKnill_Safe`.

Reuses the no-fault per-slot atom `knillSlot_step` (`Calculus.lean`) and the script
machinery (`runFScript`, `slotScript`, `injectE`, `runFScript_append`) from
`NZReachCalculus.lean`; no compiler semantics are re-implemented.
-/

namespace QStab.QClifford.Compile

open QStab QStab.QClifford QStab.QClifford.PCC

/-! ## The per-slot and per-pairs injection scripts -/

/-- The injection script for one `knillSlot = prep0 ++ zParitySlot ++ rawMeasZ`:
`none` at the prep, the slot's `slotScript`, `none` at the measurement. -/
def knillSlotScript {nq : Nat} (slot : ScheduledPauli nq) (inj : Bool) : List (Option Pauli) :=
  [none] ++ (slotScript slot inj ++ [none])

/-- The per-pairs injection script: per-slot scripts concatenated in pair order. -/
def knillPairsScript {nq : Nat} :
    List (ScheduledPauli nq × Fin nq) → List Bool → List (Option Pauli)
  | [], _ => []
  | pair :: rest, injs =>
      knillSlotScript pair.1 (injs.headD false) ++ knillPairsScript rest injs.tail

/-- errLoc count of one `knillSlot` = its script length (2 for a `Z` slot's coupling
+ prep + meas = 4; `X` slot = 6). -/
theorem errLocCount_knillSlot {nq : Nat} (slot : ScheduledPauli nq) (anc : Fin nq)
    (inj : Bool) (hne : slot.qubit ≠ anc) :
    errLocCount (knillSlot slot anc) = (knillSlotScript slot inj).length := by
  rw [knillSlot, errLocCount_append, errLocCount_append,
    errLocCount_zParitySlot anc slot hne, knillSlotScript]
  simp only [prep0, rawMeasZ, errLocCount, List.length_append, List.length_cons,
    List.length_nil]
  have hl := slotScript_length_inj slot inj
  omega

/-! ## The scripted per-slot atom -/

/-- `prepZero` on the ancilla commutes with an `X`-injection on a different qubit. -/
private theorem prepZero_inject_comm {nq : Nat} (anc q : Fin nq) (hq : q ≠ anc)
    (p : Pauli) (es : ErrorState nq) :
    propagateGate (Gate.prepZero anc) (es.inject q p)
      = (propagateGate (Gate.prepZero anc) es).inject q p := by
  cases es with
  | mk paulis measFlips detectors detectorCursor =>
    simp only [propagateGate, ErrorState.inject]
    congr 1
    funext i
    by_cases hi : i = anc
    · subst hi
      rw [if_pos rfl, if_neg (Ne.symm hq), if_pos rfl]
    · rw [if_neg hi]
      by_cases hiq : i = q
      · subst hiq; rw [if_pos rfl, if_pos rfl, if_neg hi]
      · rw [if_neg hiq, if_neg hiq, if_neg hi]

/-- **The scripted `knillSlot` run.**  Running one Knill slot under its injection
script is the no-fault propagation of the slot from the (optionally) `X`-injected
input, with fault count = the injection bit. -/
theorem runFScript_knillSlot {nq : Nat} (slot : ScheduledPauli nq) (anc : Fin nq)
    (inj : Bool) (es : ErrorState nq) (hne : slot.qubit ≠ anc) :
    runFScript (knillSlot slot anc) (knillSlotScript slot inj) es
      = (propagateCircuit (eraseFaults (knillSlot slot anc))
          (if inj then es.inject slot.qubit Pauli.X else es), if inj then 1 else 0) := by
  have hrawRun : ∀ X : ErrorState nq,
      runFScript (rawMeasZ anc) [none] X = (propagateGate (Gate.measZ anc) X, 0) :=
    fun X => by simp [rawMeasZ, runFScript]
  have hzpsLen : errLocCount (zParitySlot anc slot) = (slotScript slot inj).length := by
    rw [errLocCount_zParitySlot anc slot hne]; exact (slotScript_length_inj slot inj).symm
  have hd1 : List.drop (errLocCount (prep0 anc)) ([none] ++ (slotScript slot inj ++ [none]))
      = slotScript slot inj ++ [none] := by simp [prep0, errLocCount]
  have hd2 : List.drop (errLocCount (zParitySlot anc slot)) (slotScript slot inj ++ [none])
      = [none] := by rw [hzpsLen]; simp
  rw [knillSlot,
    show prep0 anc ++ zParitySlot anc slot ++ rawMeasZ anc
      = prep0 anc ++ (zParitySlot anc slot ++ rawMeasZ anc) from by rw [List.append_assoc],
    knillSlotScript,
    runFScript_append (prep0 anc),
    runFScript_take_errLoc (prep0 anc) [none] (slotScript slot inj ++ [none]) es
      (by simp [prep0, errLocCount]),
    runFScript_prep0, hd1,
    runFScript_append (zParitySlot anc slot),
    runFScript_take_errLoc (zParitySlot anc slot) (slotScript slot inj) [none]
      (propagateGate (Gate.prepZero anc) es) (by rw [hzpsLen]),
    runFScript_zParitySlot anc slot inj (propagateGate (Gate.prepZero anc) es) hne, hd2,
    hrawRun]
  refine Prod.ext ?_ (by cases inj <;> simp)
  cases inj
  · simp [prep0, rawMeasZ, eraseFaults, propagateCircuit,
      QHL.Target.propagateCircuit_append, eraseFaults_append]
  · simp only [if_true, eraseFaults_append, QHL.Target.propagateCircuit_append,
      prep0, rawMeasZ, eraseFaults, propagateCircuit]
    rw [prepZero_inject_comm anc slot.qubit hne Pauli.X es]

/-! ## `injectE` congruence -/

/-- `injectE` reads its input `E` only at the schedule's data qubits and at the queried
qubit, so two inputs that agree there give the same result.  Needed to thread the
scripted per-pair recursion (where the head slot's ancilla is off-support). -/
theorem injectE_congr {nq : Nat} (q : Fin nq) :
    ∀ (slots : List (ScheduledPauli nq)) (injs : List Bool) (F G : Fin nq → Pauli),
      (∀ s ∈ slots, F s.qubit = G s.qubit) → F q = G q →
      injectE slots injs F q = injectE slots injs G q := by
  intro slots
  induction slots with
  | nil => intro injs F G _ hq; exact hq
  | cons slot rest ih =>
      intro injs F G hslots hq
      rw [injectE, injectE]
      apply ih injs.tail
      · intro s hs
        simp only [hslots s (List.mem_cons_of_mem _ hs)]
      · simp only [hq]

/-! ## The scripted per-pairs chain -/

/-- **The scripted `knillPairsCircuit` chain** — the fault-injected analogue of the
no-fault `knillPairsCircuit_chain`.  Running the Knill gadget under its per-pair
injection script: the per-slot detector XOR over the block equals `scheduleParityList`
of the *injected* schedule (`injectE E`), the cursor advances by the pair count,
earlier detectors are preserved, the data becomes `injectE` of the input, and the fault
count is `injCount`.  Slot qubits are `Nodup` (as in each HGP gadget). -/
theorem runFScript_knillPairs_chain {nq : Nat} :
    ∀ (pairs : List (ScheduledPauli nq × Fin nq)) (injs : List Bool) (E : Fin nq → Pauli)
      (init : Bool) (es : ErrorState nq) (start : Nat),
      es.detectorCursor = start →
      (pairs.map (·.1.qubit)).Nodup →
      (∀ pair, pair ∈ pairs → es.paulis pair.1.qubit = E pair.1.qubit) →
      (∀ pair, pair ∈ pairs → pair.1.qubit ≠ pair.2) →
      (∀ slotPair, slotPair ∈ pairs → ∀ ancPair, ancPair ∈ pairs →
        slotPair.1.qubit ≠ ancPair.2) →
      let run := runFScript (knillPairsCircuit pairs) (knillPairsScript pairs injs) es
      detectorXorFromAcc start pairs.length run.1 init =
          scheduleParityList (pairs.map Prod.fst) (injectE (pairs.map Prod.fst) injs E) init ∧
        run.1.detectorCursor = start + pairs.length ∧
        (∀ j, j < start → run.1.detectors j = es.detectors j) ∧
        (∀ q, (∀ pair, pair ∈ pairs → q ≠ pair.2) →
          run.1.paulis q = injectE (pairs.map Prod.fst) injs (fun q' => es.paulis q') q) ∧
        run.2 = injCount (pairs.map Prod.fst) injs := by
  intro pairs
  induction pairs with
  | nil =>
      intro injs E init es start hcursor _ _ _ _
      refine ⟨rfl, ?_, ?_, ?_, rfl⟩
      · simpa [knillPairsCircuit, knillPairsScript, runFScript] using hcursor
      · intro j _; rfl
      · intro q _; rfl
  | cons pair rest ih =>
      intro injs E init es start hcursor hnodup hdata hself hslot_ne_anc
      have hpairMem : pair ∈ pair :: rest := by simp
      have hpairSelf : pair.1.qubit ≠ pair.2 := hself pair hpairMem
      set inj0 := injs.headD false with hinj0
      set esInj := (if inj0 then es.inject pair.1.qubit Pauli.X else es) with hesInj
      set es1 := propagateCircuit (eraseFaults (knillSlot pair.1 pair.2)) esInj with hes1
      set E'0 : Fin nq → Pauli :=
        (fun q => if inj0 = true ∧ q = pair.1.qubit then pauliMul Pauli.X (E q) else E q)
        with hE'0
      -- Nodup split
      rw [List.map_cons] at hnodup
      obtain ⟨hheadNotInRest, hnodupTail⟩ := List.nodup_cons.mp hnodup
      -- esInj facts
      have hInjCursor : esInj.detectorCursor = start := by
        rw [hesInj]; cases inj0 <;> simp [ErrorState.inject, hcursor]
      have hEsInjPaulis : ∀ q', esInj.paulis q' =
          (if inj0 = true ∧ q' = pair.1.qubit then pauliMul Pauli.X (es.paulis q') else es.paulis q') := by
        intro q'; rw [hesInj]; cases inj0 <;> simp [ErrorState.inject]
      have hInjSlot : esInj.paulis pair.1.qubit = E'0 pair.1.qubit := by
        rw [hEsInjPaulis, hE'0]; simp [hdata pair hpairMem]
      -- the head slot run (via the atom)
      have hlen : errLocCount (knillSlot pair.1 pair.2) = (knillSlotScript pair.1 inj0).length :=
        errLocCount_knillSlot pair.1 pair.2 inj0 hpairSelf
      have hhead : runFScript (knillSlot pair.1 pair.2) (knillPairsScript (pair :: rest) injs) es
          = (es1, if inj0 then 1 else 0) := by
        rw [knillPairsScript, ← hinj0,
          runFScript_take_errLoc (knillSlot pair.1 pair.2) (knillSlotScript pair.1 inj0)
            (knillPairsScript rest injs.tail) es (by rw [hlen]),
          runFScript_knillSlot pair.1 pair.2 inj0 es hpairSelf]
      have hdrop : (knillPairsScript (pair :: rest) injs).drop
          (errLocCount (knillSlot pair.1 pair.2)) = knillPairsScript rest injs.tail := by
        rw [knillPairsScript, ← hinj0, hlen, List.drop_left]
      set runRest := runFScript (knillPairsCircuit rest) (knillPairsScript rest injs.tail) es1
        with hrunRest
      have hrun : runFScript (knillPairsCircuit (pair :: rest)) (knillPairsScript (pair :: rest) injs) es
          = (runRest.1, (if inj0 then 1 else 0) + runRest.2) := by
        rw [show knillPairsCircuit (pair :: rest)
              = knillSlot pair.1 pair.2 ++ knillPairsCircuit rest from by simp [knillPairsCircuit],
          runFScript_append, hhead, hdrop]
      -- the head slot's effect (no-fault step from the injected input)
      have hstep := knillSlot_step pair.1 pair.2 esInj hpairSelf
      have hbit : es1.detectors start = anticommute pair.1.kind.toPauli (E'0 pair.1.qubit) := by
        have hb := hstep.1
        rw [hInjCursor] at hb
        rw [hInjSlot] at hb
        exact hb
      -- ih hypotheses for rest
      have htailCursor : es1.detectorCursor = start + 1 := by
        have := hstep.2.1; rw [hInjCursor] at this; exact this
      have htailData : ∀ tailPair, tailPair ∈ rest →
          es1.paulis tailPair.1.qubit = E'0 tailPair.1.qubit := by
        intro tailPair htailMem
        have hneq : tailPair.1.qubit ≠ pair.2 :=
          hslot_ne_anc tailPair (by simp [htailMem]) pair hpairMem
        have hqne : tailPair.1.qubit ≠ pair.1.qubit := fun h =>
          hheadNotInRest (h ▸ List.mem_map_of_mem (f := fun x => x.1.qubit) htailMem)
        have hE'0val : E'0 tailPair.1.qubit = E tailPair.1.qubit := by
          rw [hE'0]; exact if_neg (by simp [hqne])
        have hesInjVal : esInj.paulis tailPair.1.qubit = es.paulis tailPair.1.qubit := by
          rw [hEsInjPaulis]; exact if_neg (by simp [hqne])
        rw [hstep.2.2.1 tailPair.1.qubit hneq, hesInjVal, hdata tailPair (by simp [htailMem]),
          hE'0val]
      have htailSelf : ∀ tailPair, tailPair ∈ rest → tailPair.1.qubit ≠ tailPair.2 :=
        fun tailPair htailMem => hself tailPair (by simp [htailMem])
      have htailSlotAnc : ∀ slotPair, slotPair ∈ rest → ∀ ancPair, ancPair ∈ rest →
          slotPair.1.qubit ≠ ancPair.2 :=
        fun slotPair hs ancPair ha => hslot_ne_anc slotPair (by simp [hs]) ancPair (by simp [ha])
      have htail := ih injs.tail E'0 (xor init (anticommute pair.1.kind.toPauli (E'0 pair.1.qubit)))
        es1 (start + 1) htailCursor hnodupTail htailData htailSelf htailSlotAnc
      -- injectE cons unfolds (rest' = E'0 for parity, esInj.paulis for data)
      have hheadNotInRest' : pair.1.qubit ∉ (rest.map Prod.fst).map (·.qubit) := by
        rw [List.map_map]; exact hheadNotInRest
      have hInjE_parity : injectE ((pair :: rest).map Prod.fst) injs E
          = injectE (rest.map Prod.fst) injs.tail E'0 := by
        rw [List.map_cons, injectE, ← hinj0, hE'0]
      have hInjE_data : injectE ((pair :: rest).map Prod.fst) injs (fun q' => es.paulis q')
          = injectE (rest.map Prod.fst) injs.tail (fun q' => esInj.paulis q') := by
        rw [List.map_cons, injectE, ← hinj0]
        congr 1; funext q'; rw [hEsInjPaulis]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · -- parity
        rw [hrun]
        show detectorXorFromAcc start (rest.length + 1) runRest.1 init = _
        have hFpair : injectE (rest.map Prod.fst) injs.tail E'0 pair.1.qubit = E'0 pair.1.qubit :=
          injectE_preserves pair.1.qubit (rest.map Prod.fst) injs.tail E'0 hheadNotInRest'
        rw [detectorXorFromAcc, htail.2.2.1 start (by omega), hbit, htail.1, hInjE_parity,
          List.map_cons]
        simp [scheduleParityList, hFpair]
      · -- cursor
        rw [hrun]
        show runRest.1.detectorCursor = start + (rest.length + 1)
        rw [htail.2.1]; omega
      · -- previous detectors preserved
        intro j hj
        rw [hrun]
        show runRest.1.detectors j = es.detectors j
        rw [htail.2.2.1 j (by omega)]
        have := hstep.2.2.2 j (by rw [hInjCursor]; omega)
        rw [this, hesInj]; cases inj0 <;> simp [ErrorState.inject]
      · -- data
        intro q hq
        rw [hrun]
        show runRest.1.paulis q = _
        have hqne : q ≠ pair.2 := hq pair hpairMem
        rw [htail.2.2.2.1 q (fun p hp => hq p (by simp [hp])), hInjE_data]
        apply injectE_congr
        · intro s hs
          obtain ⟨tailPair, htailMem, rfl⟩ := List.mem_map.mp hs
          exact hstep.2.2.1 tailPair.1.qubit
            (hslot_ne_anc tailPair (by simp [htailMem]) pair hpairMem)
        · exact hstep.2.2.1 q hqne
      · -- count
        rw [hrun]
        show (if inj0 then 1 else 0) + runRest.2 = injCount ((pair :: rest).map Prod.fst) injs
        rw [List.map_cons, injCount, ← hinj0, htail.2.2.2.2]

/-! ## Regression guards (axiom pins) -/

/--
info: 'QStab.QClifford.Compile.runFScript_knillSlot' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms runFScript_knillSlot

/--
info: 'QStab.QClifford.Compile.errLocCount_knillSlot' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms errLocCount_knillSlot

/--
info: 'QStab.QClifford.Compile.runFScript_knillPairs_chain' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms runFScript_knillPairs_chain

end QStab.QClifford.Compile
