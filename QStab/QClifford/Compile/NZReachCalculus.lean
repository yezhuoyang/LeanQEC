import QStab.QClifford.Compile.NZBackAction
import QStab.QClifford.PCC.Basic

/-!
# NZ reach calculus — the surface-free reusable core (HGP-G3 shared)

This module builds the parametric **reach witness** machinery for any NZ-scheme gadget
block, with nothing surface-specific.  A downstream code (surface, HGP, …) instantiates the
generic `runFScript_nzBlock` master lemma by a per-leaf equality on its own schedule family.

The `runFScript`/`runFScript_sound` primitives live in the verifier-protected `PCC/Basic.lean`
— consumed here, never edited.

## Contents
* `errLocCount` + `runFScript_append` (unconditional composition law) + `errLocCount_append`;
* generic parity facts (`vectorParity_congr_on_support`, `scheduleParityList_X_uniform`);
* the `ReachState` invariant (data an X-support `xs`, helpers all `I`, all detectors `false`)
  — the induction invariant threaded through a surface/HGP reach proof;
* the per-block injection-script builder (`slotScript`/`slotsScript`/`blockScript`) and the
  master lemma `runFScript_nzBlock` — stated for an arbitrary injection list, so the three
  canonical injection patterns are its specialisations (no separate corollaries needed).
-/

namespace QStab.QClifford.Compile

open QStab QStab.QClifford QStab.QClifford.PCC

/-- **The reach invariant.**  The running state of a reach witness: its data qubits carry the
X-support `xs` (X-only), every helper (ancilla) is clean `I`, and every detector reads
`false`.  This is the induction invariant threaded through the compiled program (each block
cleans its own ancilla via `runFScript_nzBlock`'s ancilla-clean clause, keeping `helpers`). -/
structure ReachState {n total : Nat} (xs : Fin n → Bool) (es : ErrorState (n + total)) :
    Prop where
  data : ∀ q : Fin n, es.paulis (freshDataQ n total q) = xOfBool (xs q)
  helpers : ∀ q : Fin (n + total), n ≤ q.val → es.paulis q = Pauli.I
  det : ∀ s, es.detectors s = false

/-- **(c) Ambient packaging.**  A state whose data restricts to `E` and whose helpers are all
`I` has `paulis = (dataInputState E).paulis` — the exact syntactic shape
`scheduleParityList_liftSchedule` pattern-matches, consumed at every gadget. -/
theorem paulis_eq_dataInputState {n total : Nat} (es : ErrorState (n + total)) (E : Fin n → Pauli)
    (hdata : ∀ q' : Fin n, es.paulis (freshDataQ n total q') = E q')
    (hhelp : ∀ q : Fin (n + total), n ≤ q.val → es.paulis q = Pauli.I) :
    es.paulis = (dataInputState (k := total) E).paulis := by
  funext q
  simp only [dataInputState]
  by_cases hq : q.val < n
  · rw [dif_pos hq, ← hdata ⟨q.val, hq⟩]
    exact congrArg es.paulis (Fin.ext rfl)
  · rw [dif_neg hq]
    exact hhelp q (by omega)

/-! ## `runFScript` composition machinery (surface-free) -/

/-- Number of `errLoc` sites in a fault circuit = number of script entries it consumes. -/
def errLocCount {nq : Nat} : FCircuit nq → Nat
  | [] => 0
  | .gate _ :: rest => errLocCount rest
  | .errLoc _ :: rest => errLocCount rest + 1

/-- **`runFScript` composition law** (unconditional).  Running `fc1 ++ fc2` runs `fc1` on the
script prefix, then `fc2` on `script.drop (errLocCount fc1)`; counts add. -/
theorem runFScript_append {nq : Nat} :
    ∀ (fc1 fc2 : FCircuit nq) (script : List (Option Pauli)) (es : ErrorState nq),
      runFScript (fc1 ++ fc2) script es =
        ((runFScript fc2 (script.drop (errLocCount fc1)) (runFScript fc1 script es).1).1,
         (runFScript fc1 script es).2 +
           (runFScript fc2 (script.drop (errLocCount fc1)) (runFScript fc1 script es).1).2) := by
  intro fc1
  induction fc1 with
  | nil =>
      intro fc2 script es
      simp [runFScript, errLocCount]
  | cons ev rest ih =>
      intro fc2 script es
      cases ev with
      | gate g =>
          show runFScript (rest ++ fc2) script (propagateGate g es) = _
          rw [ih fc2 script (propagateGate g es)]
          simp [runFScript, errLocCount]
      | errLoc q =>
          cases script with
          | nil =>
              show runFScript (rest ++ fc2) [] es = _
              rw [ih fc2 [] es]
              simp [runFScript, errLocCount, List.drop_nil]
          | cons o script' =>
              cases o with
              | none =>
                  show runFScript (rest ++ fc2) script' es = _
                  rw [ih fc2 script' es]
                  simp [runFScript, errLocCount]
              | some p =>
                  by_cases hp : p = Pauli.I
                  · subst hp
                    show runFScript (rest ++ fc2) script' es = _
                    rw [ih fc2 script' es]
                    simp [runFScript, errLocCount]
                  · rw [List.cons_append]
                    simp only [runFScript, if_neg hp]
                    rw [ih fc2 script' (es.inject q p)]
                    simp only [errLocCount, List.drop_succ_cons]
                    congr 1
                    omega

/-- errLoc counts add over circuit concatenation. -/
@[simp] theorem errLocCount_append {nq : Nat} (fc1 fc2 : FCircuit nq) :
    errLocCount (fc1 ++ fc2) = errLocCount fc1 + errLocCount fc2 := by
  induction fc1 with
  | nil => simp [errLocCount]
  | cons ev rest ih =>
      cases ev with
      | gate g => simpa [errLocCount] using ih
      | errLoc q => simp only [List.cons_append, errLocCount, ih]; omega

/-! ## Per-slot injection reduction (the injection-tolerant chain atom) -/

/-- The per-slot injection script: `some X` at the entry (data-coupling) site if `inj`, then
`none`s filling the slot's errLoc count (2 for a `Z` `CNOT`, 4 for an `X` `H`-sandwich). -/
def slotScript {nq : Nat} (slot : ScheduledPauli nq) (inj : Bool) : List (Option Pauli) :=
  match slot.kind with
  | .Z => [if inj then some Pauli.X else none, none]
  | .X => [if inj then some Pauli.X else none, none, none, none]

/-- **Per-slot reduction.**  Running one `zParitySlot` under its injection script equals the
no-fault propagation of the slot applied to the entry-site injection, with count = the
injection bit.  This is the atom that turns the fault run into the reusable no-fault chain
(`zParitySlot_step` / `zParitySlotsCircuit_chain`). -/
theorem runFScript_zParitySlot {nq : Nat} (anc : Fin nq) (slot : ScheduledPauli nq)
    (inj : Bool) (es : ErrorState nq) (hne : slot.qubit ≠ anc) :
    runFScript (zParitySlot anc slot) (slotScript slot inj) es =
      (propagateCircuit (eraseFaults (zParitySlot anc slot))
        (if inj then es.inject slot.qubit Pauli.X else es), if inj then 1 else 0) := by
  cases slot with
  | mk kind qubit =>
    cases kind <;> cases inj <;>
      simp [slotScript, zParitySlot, hadamard, cnot, hne, eraseFaults,
        runFScript, propagateCircuit, propagateGate]

/-- errLoc count of one `zParitySlot` (off the ancilla): 2 for `Z`, 4 for `X`. -/
theorem errLocCount_zParitySlot {nq : Nat} (anc : Fin nq) (slot : ScheduledPauli nq)
    (hne : slot.qubit ≠ anc) :
    errLocCount (zParitySlot anc slot) = (slotScript slot true).length := by
  cases slot with
  | mk kind qubit =>
    cases kind <;> simp [slotScript, zParitySlot, hadamard, cnot, hne, errLocCount]

/-- `slotScript`'s length is independent of the injection bit. -/
theorem slotScript_length_inj {nq : Nat} (slot : ScheduledPauli nq) (inj : Bool) :
    (slotScript slot inj).length = (slotScript slot true).length := by
  cases slot with
  | mk kind qubit => cases kind <;> rfl

/-- `runFScript` reads only the first `errLocCount fc` script entries: a longer script agrees
with its prefix.  (Foundation for peeling a gadget block off the front of the full script.) -/
theorem runFScript_take_errLoc {nq : Nat} :
    ∀ (fc : FCircuit nq) (s1 s2 : List (Option Pauli)) (es : ErrorState nq),
      errLocCount fc ≤ s1.length →
      runFScript fc (s1 ++ s2) es = runFScript fc s1 es := by
  intro fc
  induction fc with
  | nil => intro s1 s2 es _; rfl
  | cons ev rest ih =>
      intro s1 s2 es h
      cases ev with
      | gate g => exact ih s1 s2 (propagateGate g es) (by simpa [errLocCount] using h)
      | errLoc q =>
          cases s1 with
          | nil => simp only [errLocCount, List.length_nil] at h; omega
          | cons o s1' =>
              have hrest : errLocCount rest ≤ s1'.length := by
                simp only [errLocCount, List.length_cons] at h; omega
              cases o with
              | none => simpa [runFScript] using ih s1' s2 es hrest
              | some p =>
                  by_cases hp : p = Pauli.I
                  · subst hp; simpa [runFScript] using ih s1' s2 es hrest
                  · simp only [List.cons_append, runFScript, if_neg hp]
                    rw [ih s1' s2 (es.inject q p) hrest]

/-- The full slots-script: per-slot injection scripts concatenated in schedule order. -/
def slotsScript {nq : Nat} : List (ScheduledPauli nq) → List Bool → List (Option Pauli)
  | [], _ => []
  | slot :: rest, injs => slotScript slot (injs.headD false) ++ slotsScript rest injs.tail

/-- The data error after applying the entry-site injections along the schedule.  Injecting
`X` at slot `j`'s data qubit (when its injection bit is set) multiplies its Pauli by `X`. -/
def injectE {nq : Nat} :
    List (ScheduledPauli nq) → List Bool → (Fin nq → Pauli) → (Fin nq → Pauli)
  | [], _, E => E
  | slot :: rest, injs, E =>
      injectE rest injs.tail
        (fun q => if injs.headD false = true ∧ q = slot.qubit
                    then pauliMul Pauli.X (E q) else E q)

/-- Number of injected slots. -/
def injCount {nq : Nat} : List (ScheduledPauli nq) → List Bool → Nat
  | [], _ => 0
  | _ :: rest, injs => (if injs.headD false then 1 else 0) + injCount rest injs.tail

/-- `injectE` leaves a qubit outside the schedule support untouched. -/
theorem injectE_preserves {nq : Nat} (q : Fin nq) :
    ∀ (slots : List (ScheduledPauli nq)) (injs : List Bool) (E : Fin nq → Pauli),
      q ∉ slots.map (·.qubit) → injectE slots injs E q = E q := by
  intro slots
  induction slots with
  | nil => intro injs E _; rfl
  | cons slot rest ih =>
      intro injs E hq
      simp only [List.map_cons, List.mem_cons, not_or] at hq
      rw [injectE, ih injs.tail _ hq.2]
      simp only [if_neg (show ¬ (injs.headD false = true ∧ q = slot.qubit)
        from fun h => hq.1 h.2)]

/-- `zParitySlotsCircuit` peels one slot off the front. -/
theorem zParitySlotsCircuit_cons {nq : Nat} (anc : Fin nq) (slot : ScheduledPauli nq)
    (rest : List (ScheduledPauli nq)) :
    zParitySlotsCircuit anc (slot :: rest) =
      zParitySlot anc slot ++ zParitySlotsCircuit anc rest := by
  simp [zParitySlotsCircuit]

/-! ## The injection-tolerant chain walk -/

/-- **Injection-tolerant `zParitySlots` chain.**  Running the slots-block of an NZ gadget under
its injection script behaves as the no-fault chain applied to the *injected* data error
`injectE`: the ancilla accumulates the schedule parity of the injected error, the data gains
`X` exactly at the injected slots, the detectors and cursor are untouched (no `measZ` in the
slots), and the fault count is the number of injections. -/
theorem runFScript_zParitySlots_chain {nq : Nat} (anc : Fin nq) :
    ∀ (slots : List (ScheduledPauli nq)) (injs : List Bool)
      (E : Fin nq → Pauli) (b : Bool) (es : ErrorState nq),
      (∀ slot ∈ slots, slot.qubit ≠ anc) →
      (slots.map (·.qubit)).Nodup →
      (∀ q, q ≠ anc → es.paulis q = E q) →
      es.paulis anc = xOfBool b →
      (runFScript (zParitySlotsCircuit anc slots) (slotsScript slots injs) es).1.paulis anc
          = xOfBool (scheduleParityList slots (injectE slots injs E) b) ∧
      (∀ q, q ≠ anc →
        (runFScript (zParitySlotsCircuit anc slots) (slotsScript slots injs) es).1.paulis q
          = injectE slots injs E q) ∧
      (runFScript (zParitySlotsCircuit anc slots) (slotsScript slots injs) es).1.detectors
          = es.detectors ∧
      (runFScript (zParitySlotsCircuit anc slots) (slotsScript slots injs) es).1.detectorCursor
          = es.detectorCursor ∧
      (runFScript (zParitySlotsCircuit anc slots) (slotsScript slots injs) es).2
          = injCount slots injs := by
  intro slots
  induction slots with
  | nil =>
      intro injs E b es _ _ hdata hanc
      exact ⟨by simpa [zParitySlotsCircuit, slotsScript, injectE, scheduleParityList,
                  runFScript] using hanc,
        fun q hq => by simpa [zParitySlotsCircuit, slotsScript, injectE, runFScript]
                    using hdata q hq, rfl, rfl, rfl⟩
  | cons slot0 rest ih =>
      intro injs E b es hne hnodup hdata hanc
      have hne0 : slot0.qubit ≠ anc := hne slot0 (by simp)
      have hnodup' : (rest.map (·.qubit)).Nodup := by
        simp only [List.map_cons, List.nodup_cons] at hnodup; exact hnodup.2
      have hslot0_notin : slot0.qubit ∉ rest.map (·.qubit) := by
        simp only [List.map_cons, List.nodup_cons] at hnodup; exact hnodup.1
      set inj0 := injs.headD false with hinj0
      set esInj := (if inj0 then es.inject slot0.qubit Pauli.X else es) with hesInj
      set E'0 := (fun q => if inj0 = true ∧ q = slot0.qubit
                    then pauliMul Pauli.X (E q) else E q) with hE'0
      have hancInj : esInj.paulis anc = xOfBool b := by
        rw [hesInj]; cases inj0 <;> simp [ErrorState.inject, hne0.symm, hanc]
      have hdataInj : ∀ q, q ≠ anc → esInj.paulis q = E'0 q := by
        intro q hq
        by_cases hi0 : inj0 = true
        · rw [hesInj, if_pos hi0, hE'0]
          simp only [hi0, true_and, ErrorState.inject]
          by_cases hqs : q = slot0.qubit
          · rw [if_pos hqs, if_pos hqs, hdata q hq]
          · rw [if_neg hqs, if_neg hqs]; exact hdata q hq
        · rw [hesInj, if_neg hi0, hE'0]
          simp only [if_neg (show ¬(inj0 = true ∧ q = slot0.qubit) from fun h => hi0 h.1)]
          exact hdata q hq
      -- peel slot0 into a clean equation
      have hlen : errLocCount (zParitySlot anc slot0) = (slotScript slot0 inj0).length := by
        rw [errLocCount_zParitySlot anc slot0 hne0]; exact (slotScript_length_inj slot0 inj0).symm
      have hdrop : List.drop (errLocCount (zParitySlot anc slot0))
          (slotScript slot0 inj0 ++ slotsScript rest injs.tail) = slotsScript rest injs.tail := by
        rw [hlen]; simp
      have hpeel : runFScript (zParitySlotsCircuit anc (slot0 :: rest))
            (slotsScript (slot0 :: rest) injs) es
          = ((runFScript (zParitySlotsCircuit anc rest) (slotsScript rest injs.tail)
                (propagateCircuit (eraseFaults (zParitySlot anc slot0)) esInj)).1,
             (if inj0 then 1 else 0) +
               (runFScript (zParitySlotsCircuit anc rest) (slotsScript rest injs.tail)
                (propagateCircuit (eraseFaults (zParitySlot anc slot0)) esInj)).2) := by
        rw [zParitySlotsCircuit_cons, slotsScript, ← hinj0, runFScript_append,
          runFScript_take_errLoc (zParitySlot anc slot0) (slotScript slot0 inj0)
            (slotsScript rest injs.tail) es (le_of_eq hlen),
          runFScript_zParitySlot anc slot0 inj0 es hne0, hdrop, ← hesInj]
      -- no-fault per-slot step + recurse
      have hstep := zParitySlot_step anc slot0 E'0 b esInj hne0 hdataInj hancInj
      have hread := zParitySlot_preserves_readout anc slot0 esInj
      have hih := ih injs.tail E'0
        (xor b (anticommute slot0.kind.toPauli (E'0 slot0.qubit)))
        (propagateCircuit (eraseFaults (zParitySlot anc slot0)) esInj)
        (fun s hs => hne s (by simp [hs])) hnodup' hstep.2 hstep.1
      obtain ⟨hihAnc, hihData, hihDet, hihCur, hihCnt⟩ := hih
      have hEeq : injectE (slot0 :: rest) injs E = injectE rest injs.tail E'0 := rfl
      rw [hpeel]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · show (runFScript (zParitySlotsCircuit anc rest) (slotsScript rest injs.tail)
              (propagateCircuit (eraseFaults (zParitySlot anc slot0)) esInj)).1.paulis anc = _
        rw [hihAnc, hEeq]; congr 1
        conv_rhs => rw [scheduleParityList, List.foldl_cons, ← scheduleParityList]
        rw [injectE_preserves slot0.qubit rest injs.tail E'0 hslot0_notin]
      · intro q hq
        show (runFScript (zParitySlotsCircuit anc rest) (slotsScript rest injs.tail)
              (propagateCircuit (eraseFaults (zParitySlot anc slot0)) esInj)).1.paulis q = _
        rw [hihData q hq, hEeq]
      · show (runFScript (zParitySlotsCircuit anc rest) (slotsScript rest injs.tail)
              (propagateCircuit (eraseFaults (zParitySlot anc slot0)) esInj)).1.detectors = _
        rw [hihDet, hread.1, hesInj]; cases inj0 <;> simp [ErrorState.inject]
      · show (runFScript (zParitySlotsCircuit anc rest) (slotsScript rest injs.tail)
              (propagateCircuit (eraseFaults (zParitySlot anc slot0)) esInj)).1.detectorCursor = _
        rw [hihCur, hread.2, hesInj]; cases inj0 <;> simp [ErrorState.inject]
      · show (if inj0 then 1 else 0) + _ = _
        rw [hihCnt, injCount, ← hinj0]

/-! ## The gadget block: prep, couple, measure -/

/-- The NZ gadget block for a schedule: prepare the ancilla, couple every slot, measure. -/
def nzBlock {nq : Nat} (anc : Fin nq) (slots : List (ScheduledPauli nq)) : FCircuit nq :=
  prep0 anc ++ zParitySlotsCircuit anc slots ++ flagMeasZ anc

/-- The block injection script: no injection at prep/measure, injections along the slots. -/
def blockScript {nq : Nat} (slots : List (ScheduledPauli nq)) (injs : List Bool) :
    List (Option Pauli) :=
  [none] ++ (slotsScript slots injs ++ [none])

/-- errLoc count of the slots-block equals the slots-script length (off the ancilla). -/
theorem errLocCount_zParitySlotsCircuit {nq : Nat} (anc : Fin nq) :
    ∀ (slots : List (ScheduledPauli nq)) (injs : List Bool),
      (∀ slot ∈ slots, slot.qubit ≠ anc) →
      errLocCount (zParitySlotsCircuit anc slots) = (slotsScript slots injs).length := by
  intro slots
  induction slots with
  | nil => intro injs _; rfl
  | cons slot0 rest ih =>
      intro injs hne
      rw [zParitySlotsCircuit_cons, errLocCount_append,
        errLocCount_zParitySlot anc slot0 (hne slot0 (by simp)),
        ih injs.tail (fun s hs => hne s (by simp [hs])),
        slotsScript, List.length_append, slotScript_length_inj slot0 (injs.headD false)]

/-- `runFScript` over `prep0`/`flagMeasZ` under a `none` entry is the plain gate propagation. -/
theorem runFScript_prep0 {nq : Nat} (anc : Fin nq) (es : ErrorState nq) :
    runFScript (prep0 anc) [none] es = (propagateGate (Gate.prepZero anc) es, 0) := by
  simp [prep0, runFScript]

theorem runFScript_flagMeasZ {nq : Nat} (anc : Fin nq) (es : ErrorState nq) :
    runFScript (flagMeasZ anc) [none] es = (propagateGate (Gate.measZ anc) es, 0) := by
  simp [flagMeasZ, runFScript]

/-- **The master lemma `runFScript_nzBlock`.**  Running one NZ gadget block under its injection
script, starting from a state whose detectors are all `false` and whose data agrees with `E`
off the ancilla: the data gains `X` exactly at the injected slots (`injectE`), *every* detector
stays `false` (under the parity-even hypothesis — the domino condition), and the fault count is
the number of injections. -/
theorem runFScript_nzBlock {nq : Nat} (anc : Fin nq) (slots : List (ScheduledPauli nq))
    (injs : List Bool) (E : Fin nq → Pauli) (es : ErrorState nq)
    (hne : ∀ slot ∈ slots, slot.qubit ≠ anc)
    (hnodup : (slots.map (·.qubit)).Nodup)
    (hdata : ∀ q, q ≠ anc → es.paulis q = E q)
    (hdet : ∀ s, es.detectors s = false)
    (heven : scheduleParityList slots (injectE slots injs E) false = false) :
    (∀ q, q ≠ anc →
        (runFScript (nzBlock anc slots) (blockScript slots injs) es).1.paulis q
          = injectE slots injs E q) ∧
    (runFScript (nzBlock anc slots) (blockScript slots injs) es).1.paulis anc = Pauli.I ∧
    (∀ s, (runFScript (nzBlock anc slots) (blockScript slots injs) es).1.detectors s = false) ∧
    (runFScript (nzBlock anc slots) (blockScript slots injs) es).2 = injCount slots injs := by
  -- peel prep0, then slots, then flagMeasZ
  have hlenSlots : errLocCount (zParitySlotsCircuit anc slots) = (slotsScript slots injs).length :=
    errLocCount_zParitySlotsCircuit anc slots injs hne
  -- prep0 state (reuse the no-fault atom)
  have hprep := prep0_state_for_chain anc es
  set esPrep := propagateGate (Gate.prepZero anc) es with hesPrep
  have hesPrep_eq : esPrep = propagateCircuit (eraseFaults (prep0 anc)) es := by
    simp [hesPrep, prep0, eraseFaults, propagateCircuit]
  have hprepAnc : esPrep.paulis anc = xOfBool false := by rw [hesPrep_eq]; exact hprep.1
  have hprepData : ∀ q, q ≠ anc → esPrep.paulis q = E q := by
    intro q hq; rw [hesPrep_eq, hprep.2.1 q hq]; exact hdata q hq
  have hprepDet : esPrep.detectors = es.detectors := by rw [hesPrep_eq]; exact hprep.2.2.1
  -- chain over slots
  have hchain := runFScript_zParitySlots_chain anc slots injs E false esPrep hne hnodup
    hprepData hprepAnc
  obtain ⟨hcAnc, hcData, hcDet, hcCur, hcCnt⟩ := hchain
  set esSlots := runFScript (zParitySlotsCircuit anc slots) (slotsScript slots injs) esPrep
    with hesSlots
  -- the block reduces to: prep, chain, then a single measZ on the ancilla
  have hblock : runFScript (nzBlock anc slots) (blockScript slots injs) es
      = (propagateGate (Gate.measZ anc) esSlots.1, esSlots.2) := by
    have hd1 : List.drop (errLocCount (prep0 anc))
        ([none] ++ (slotsScript slots injs ++ [none])) = slotsScript slots injs ++ [none] := by
      simp [prep0, errLocCount]
    have hd2 : List.drop (errLocCount (zParitySlotsCircuit anc slots))
        (slotsScript slots injs ++ [none]) = [none] := by rw [hlenSlots]; simp
    rw [nzBlock, blockScript,
      show prep0 anc ++ zParitySlotsCircuit anc slots ++ flagMeasZ anc
        = prep0 anc ++ (zParitySlotsCircuit anc slots ++ flagMeasZ anc) from by
          rw [List.append_assoc],
      runFScript_append (prep0 anc),
      runFScript_take_errLoc (prep0 anc) [none] (slotsScript slots injs ++ [none]) es
        (by simp [prep0, errLocCount]),
      runFScript_prep0, ← hesPrep, hd1,
      runFScript_append (zParitySlotsCircuit anc slots),
      runFScript_take_errLoc (zParitySlotsCircuit anc slots) (slotsScript slots injs) [none]
        esPrep (by rw [hlenSlots]),
      ← hesSlots, hd2, runFScript_flagMeasZ]
    simp
  rw [hblock]
  -- read off the three conclusions
  have hdetSlots : esSlots.1.detectors = es.detectors := by rw [hcDet, hprepDet]
  have hcurSlots : esSlots.1.detectorCursor = es.detectorCursor := by
    rw [hcCur, hesPrep_eq]; exact hprep.2.2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q hq
    show (propagateGate (Gate.measZ anc) esSlots.1).paulis q = _
    simp only [propagateGate]
    exact hcData q hq
  · show (propagateGate (Gate.measZ anc) esSlots.1).paulis anc = Pauli.I
    simp only [propagateGate]
    rw [hcAnc, heven]; rfl
  · intro s
    show (propagateGate (Gate.measZ anc) esSlots.1).detectors s = false
    simp only [propagateGate]
    by_cases hs : s = esSlots.1.detectorCursor
    · rw [if_pos hs, hcAnc]
      show hasXComp (xOfBool (scheduleParityList slots (injectE slots injs E) false)) = false
      rw [heven]; rfl
    · rw [if_neg hs, hdetSlots]; exact hdet s
  · show esSlots.2 = injCount slots injs
    exact hcCnt

/-- `injectE` with an all-`false` injection list leaves the data unchanged (non-injector
gadgets). -/
theorem injectE_all_false {nq : Nat} :
    ∀ (slots : List (ScheduledPauli nq)) (injs : List Bool) (E : Fin nq → Pauli),
      (∀ b ∈ injs, b = false) → injectE slots injs E = E := by
  intro slots
  induction slots with
  | nil => intro injs E _; rfl
  | cons slot rest ih =>
      intro injs E hf
      have hhead : injs.headD false = false := by
        cases injs with
        | nil => rfl
        | cons b bs => exact hf b (by simp)
      rw [injectE, hhead,
        show (fun q => if (false : Bool) = true ∧ q = slot.qubit
                then pauliMul Pauli.X (E q) else E q) = E from by funext q; simp]
      exact ih injs.tail E (fun b hb => hf b (List.tail_subset injs hb))

/-! ## Generic parity facts (surface-free; reused by surface + HGP) -/

/-- **`vectorParity` depends only on the support of `S`.**  If `E`, `E'` agree wherever `S`
is non-identity, their parities against `S` are equal (`anticommute I _ = false`). -/
theorem vectorParity_congr_on_support {n : Nat} (S E E' : Fin n → Pauli)
    (h : ∀ q, S q ≠ Pauli.I → E q = E' q) : vectorParity S E = vectorParity S E' := by
  unfold vectorParity
  have hstep : (fun acc (q : Fin n) => xor acc (anticommute (S q) (E q)))
             = (fun acc q => xor acc (anticommute (S q) (E' q))) := by
    funext acc q
    by_cases hq : S q = Pauli.I
    · rw [hq]; cases E q <;> cases E' q <;> rfl
    · rw [h q hq]
  rw [hstep]

/-- **X-triviality.**  An `X`-kind-uniform schedule's parity against any *pure-X* error
(`X` or `I` pointwise) is the initial value — every `anticommute X (X/I)` term vanishes.  This
discharges every `X`-check gadget in one stroke, independent of the stage. -/
theorem scheduleParityList_X_uniform {nq : Nat} (E : Fin nq → Pauli)
    (hX : ∀ q, E q = Pauli.X ∨ E q = Pauli.I) :
    ∀ (slots : List (ScheduledPauli nq)) (init : Bool),
      (∀ slot ∈ slots, slot.kind = XZPauli.X) →
      scheduleParityList slots E init = init := by
  intro slots
  induction slots with
  | nil => intro init _; rfl
  | cons slot rest ih =>
      intro init hk
      have hslot : anticommute slot.kind.toPauli (E slot.qubit) = false := by
        rw [hk slot (by simp)]
        rcases hX slot.qubit with h | h <;> rw [h] <;> rfl
      rw [scheduleParityList, List.foldl_cons, ← scheduleParityList, hslot, Bool.xor_false]
      exact ih init (fun s hs => hk s (by simp [hs]))

/-- The block's errLoc count equals its injection script's length (count alignment). -/
theorem errLocCount_nzBlock {nq : Nat} (anc : Fin nq) (slots : List (ScheduledPauli nq))
    (injs : List Bool) (hne : ∀ slot ∈ slots, slot.qubit ≠ anc) :
    errLocCount (nzBlock anc slots) = (blockScript slots injs).length := by
  rw [nzBlock, errLocCount_append, errLocCount_append,
    errLocCount_zParitySlotsCircuit anc slots injs hne, blockScript]
  simp only [prep0, flagMeasZ, errLocCount, List.length_append, List.length_cons,
    List.length_nil]
  omega

/-! ## Bridge to the compiler front-end -/

/-- **The compiled NZ gadget block is an `nzBlock`.**  `compileGadgetBlock .NZ` unfolds to
`prep0 ++ (slots.map zParitySlot).flatten ++ flagMeasZ` on the fresh ancilla — literally the
generic block.  (Surface/HGP instantiate the master lemma through this.) -/
theorem compileGadgetBlock_NZ_eq_nzBlock {n total : Nat} (sigma : RuleSchedule n)
    (start : Nat) (hfit : start + helperCount Scheme.NZ sigma ≤ total) :
    compileGadgetBlock Scheme.NZ sigma start hfit
      = nzBlock (blockHelperQ n total start 1 hfit ⟨0, Nat.one_pos⟩)
          (liftSchedule (k := total) sigma).slots :=
  rfl

end QStab.QClifford.Compile
