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

end QStab.QClifford.Compile
