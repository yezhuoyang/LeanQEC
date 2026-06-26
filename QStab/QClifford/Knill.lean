import QStab.QClifford.Gate
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

set_option maxRecDepth 8192

/-! # Knill scheme: transversal CNOT syndrome extraction

The Knill syndrome extraction uses a transversal CNOT: each data qubit i
is coupled to a dedicated ancilla qubit i via a single CNOT, then all
ancillae are measured. Because each ancilla couples to exactly ONE data
qubit, no hook error can create a weight-2 data error.

Layout: data[0..n-1] | anc[n..2n-1]  (total 2n qubits)

Circuit for each qubit i:
  prepZero(anc_i),  CNOT(data_i, anc_i),  measZ(anc_i)
-/

namespace QStab.QClifford.Knill

open QStab.QClifford

-- ============================================================
-- Qubit layout
-- ============================================================

private def dataQ (n : Nat) (i : Fin n) : Fin (n + n) :=
  ⟨i.val, by have := i.isLt; omega⟩

private def ancQ (n : Nat) (i : Fin n) : Fin (n + n) :=
  ⟨n + i.val, by have := i.isLt; omega⟩

private theorem data_ne_anc (n : Nat) (i : Fin n) : dataQ n i ≠ ancQ n i := by
  unfold dataQ ancQ
  intro h
  have : i.val = n + i.val := congrArg Fin.val h
  omega

-- ============================================================
-- General circuit
-- ============================================================

/-- Single-qubit syndrome gadget. -/
def qubitGadget (n : Nat) (i : Fin n) : List (Gate (n + n)) :=
  [ Gate.prepZero (ancQ n i),
    Gate.cnot (dataQ n i) (ancQ n i) (data_ne_anc n i),
    Gate.measZ (ancQ n i) ]

/-- Full Knill transversal circuit: gadget for each qubit 0..n-1. -/
def knillCircuit (n : Nat) : Circuit (n + n) :=
  List.flatten ((List.finRange n).map (qubitGadget n))

-- ============================================================
-- Error analysis helpers
-- ============================================================

/-- Data error weight. -/
def dataWt (n : Nat) (es : ErrorState (n + n)) : Nat :=
  (Finset.univ.filter fun i : Fin n => es.paulis (dataQ n i) ≠ .I).card

/-- Syndrome bit i. -/
def syndrome (n : Nat) (es : ErrorState (n + n)) (i : Fin n) : Bool :=
  es.measFlips (ancQ n i)

-- ============================================================
-- Soundness theorem (existential)
-- ============================================================

/-- **SOUNDNESS**: Every fault produces a well-defined data weight. -/
theorem soundness (n : Nat) (fault : Fault (n + n)) :
    ∃ wt : Nat, wt = dataWt n (computeFaultEffect (knillCircuit n) fault) :=
  ⟨_, rfl⟩

-- ============================================================
-- Key structural lemmas
-- ============================================================

/-- Every gate preserves the all-identity Pauli invariant.

This is the component of the old "clean propagates to clean" fact that remains
true after `measZ` started writing a time-resolved detector record.  Measurement
may advance `detectorCursor`, but it does not introduce a Pauli. -/
private theorem propagateGate_allPaulis_I {nq : Nat} (g : Gate nq)
    (es : ErrorState nq) (hall : ∀ q, es.paulis q = .I) :
    ∀ q, (propagateGate g es).paulis q = .I := by
  intro q
  cases g <;> simp [propagateGate, hall, xPart, zPart, pauliMul, hadamardAction]

/-- Any circuit preserves the all-identity Pauli invariant. -/
private theorem propagateCircuit_allPaulis_I {nq : Nat} (circuit : Circuit nq)
    (es : ErrorState nq) (hall : ∀ q, es.paulis q = .I) :
    ∀ q, (propagateCircuit circuit es).paulis q = .I := by
  induction circuit generalizing es with
  | nil =>
      intro q
      simpa [propagateCircuit] using hall q
  | cons g gs ih =>
      exact ih (propagateGate g es) (propagateGate_allPaulis_I g es hall)

/-- Proof irrelevance for computeFaultEffect. -/
private theorem ce_irrel {nq : Nat} (circuit : Circuit nq) (pos : Nat) (q : Fin nq)
    (p : Pauli) (hp1 hp2 : p ≠ .I) :
    computeFaultEffect circuit ⟨pos, q, p, hp1⟩ =
    computeFaultEffect circuit ⟨pos, q, p, hp2⟩ := rfl

-- ============================================================
-- Auxiliary lemmas for general weight bound
-- ============================================================

/-- dataQ values are distinct. -/
private theorem dataQ_injective (n : Nat) (i j : Fin n) (h : dataQ n i = dataQ n j) : i = j := by
  unfold dataQ at h; simp [Fin.ext_iff] at h; exact Fin.ext h

/-- dataQ n j ≠ ancQ n i for any i, j. -/
private theorem dataQ_ne_ancQ (n : Nat) (j i : Fin n) : dataQ n j ≠ ancQ n i := by
  unfold dataQ ancQ; intro h; have := congrArg Fin.val h; simp at this; omega

/-- ancQ n i ≠ dataQ n j for any i, j. -/
private theorem ancQ_ne_dataQ (n : Nat) (i j : Fin n) : ancQ n i ≠ dataQ n j :=
  Ne.symm (dataQ_ne_ancQ n j i)

/-- ancQ values are distinct. -/
private theorem ancQ_injective (n : Nat) (i j : Fin n) (h : ancQ n i = ancQ n j) : i = j := by
  unfold ancQ at h; simp [Fin.ext_iff] at h; exact Fin.ext (by omega)

/-- ancQ n i ≠ ancQ n j when i ≠ j. -/
private theorem ancQ_ne_ancQ (n : Nat) (i j : Fin n) (h : i ≠ j) : ancQ n i ≠ ancQ n j := by
  intro heq; exact h (ancQ_injective n i j heq)

-- ============================================================
-- Slot-based invariant
-- ============================================================

/-- A "slot" groups the data-ancilla pair for index i.
    slotWt counts how many slots have ANY non-I error (data or ancilla). -/
private def slotWt (n : Nat) (es : ErrorState (n + n)) : Nat :=
  (Finset.univ.filter fun i : Fin n =>
    es.paulis (dataQ n i) ≠ .I ∨ es.paulis (ancQ n i) ≠ .I).card

/-- slotWt ≥ dataWt: every non-I data qubit contributes to its slot. -/
private theorem dataWt_le_slotWt (n : Nat) (es : ErrorState (n + n)) :
    dataWt n es ≤ slotWt n es := by
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact Or.inl hi

/-- Abstract helper: if predicate P differs from Q at most at index i,
    and ¬Q i → ¬P i, then |filter P| ≤ 1 whenever |filter Q| ≤ 1. -/
private theorem filter_card_le_one_of_local_change {n : Nat}
    (P Q : Fin n → Prop) [DecidablePred P] [DecidablePred Q]
    (i : Fin n)
    (h_agree : ∀ k : Fin n, k ≠ i → (P k ↔ Q k))
    (h_clean : ¬Q i → ¬P i)
    (hQ : (Finset.univ.filter Q).card ≤ 1) :
    (Finset.univ.filter P).card ≤ 1 := by
  by_cases hi_Q : Q i
  · -- i ∈ filter Q. Since card ≤ 1, every other k has ¬Q k, hence ¬P k.
    apply Finset.card_le_one.mpr
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    by_contra hab
    have : a ≠ i ∨ b ≠ i := by
      by_contra h; push_neg at h; exact hab (h.1 ▸ h.2 ▸ rfl)
    rcases this with hai | hbi
    · have : Q a := (h_agree a hai).mp ha
      have ha_in := Finset.mem_filter.mpr ⟨Finset.mem_univ _, this⟩
      have hi_in := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi_Q⟩
      exact hai (Finset.card_le_one.mp hQ a ha_in i hi_in)
    · have : Q b := (h_agree b hbi).mp hb
      have hb_in := Finset.mem_filter.mpr ⟨Finset.mem_univ _, this⟩
      have hi_in := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi_Q⟩
      exact hbi (Finset.card_le_one.mp hQ b hb_in i hi_in)
  · -- ¬Q i, hence ¬P i. So filter P ⊆ filter Q.
    have hi_P := h_clean hi_Q
    have : Finset.univ.filter P ⊆ Finset.univ.filter Q := by
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      by_cases hki : k = i
      · exact absurd (hki ▸ hk) hi_P
      · exact (h_agree k hki).mp hk
    exact Nat.le_trans (Finset.card_le_card this) hQ

-- ============================================================
-- Gate-level preservation of slotWt
-- ============================================================

/-- CNOT(dataQ n i, ancQ n i) does not change data qubit j when j ≠ i. -/
private theorem propagateGate_cnot_data_other (n : Nat) (i : Fin n) (j : Fin n) (hji : j ≠ i)
    (es : ErrorState (n + n)) :
    (propagateGate (Gate.cnot (dataQ n i) (ancQ n i) (data_ne_anc n i)) es).paulis (dataQ n j) =
    es.paulis (dataQ n j) := by
  simp only [propagateGate]
  have htj : dataQ n j ≠ ancQ n i := dataQ_ne_ancQ n j i
  have hcj : dataQ n j ≠ dataQ n i := fun h => hji (dataQ_injective n j i h)
  simp [htj, hcj]

/-- CNOT(dataQ n i, ancQ n i) does not change ancQ n j when j ≠ i. -/
private theorem propagateGate_cnot_anc_other (n : Nat) (i : Fin n) (j : Fin n) (hji : j ≠ i)
    (es : ErrorState (n + n)) :
    (propagateGate (Gate.cnot (dataQ n i) (ancQ n i) (data_ne_anc n i)) es).paulis (ancQ n j) =
    es.paulis (ancQ n j) := by
  simp only [propagateGate]
  have htj : ancQ n j ≠ ancQ n i := ancQ_ne_ancQ n j i hji
  have hcj : ancQ n j ≠ dataQ n i := ancQ_ne_dataQ n j i
  simp [htj, hcj]

/-- prepZero on ancQ n i preserves slotWt ≤ 1. -/
private theorem propagateGate_prepZero_slotWt (n : Nat) (i : Fin n)
    (es : ErrorState (n + n)) (hes : slotWt n es ≤ 1) :
    slotWt n (propagateGate (Gate.prepZero (ancQ n i)) es) ≤ 1 := by
  apply filter_card_le_one_of_local_change
    (fun k => (propagateGate (Gate.prepZero (ancQ n i)) es).paulis (dataQ n k) ≠ .I ∨
              (propagateGate (Gate.prepZero (ancQ n i)) es).paulis (ancQ n k) ≠ .I)
    (fun k => es.paulis (dataQ n k) ≠ .I ∨ es.paulis (ancQ n k) ≠ .I)
    i
  · intro k hki
    simp only [propagateGate]
    have hd : dataQ n k ≠ ancQ n i := dataQ_ne_ancQ n k i
    have ha : ancQ n k ≠ ancQ n i := ancQ_ne_ancQ n k i hki
    simp [hd, ha]
  · intro hi; push_neg at hi ⊢
    obtain ⟨hdi, hai⟩ := hi
    simp only [propagateGate]
    have hd : dataQ n i ≠ ancQ n i := dataQ_ne_ancQ n i i
    exact ⟨by simp [hd]; exact hdi, by simp⟩
  · exact hes

/-- measZ preserves slotWt (paulis are unchanged by measZ). -/
private theorem propagateGate_measZ_slotWt (n : Nat) (i : Fin n)
    (es : ErrorState (n + n)) (hes : slotWt n es ≤ 1) :
    slotWt n (propagateGate (Gate.measZ (ancQ n i)) es) ≤ 1 :=
  hes  -- definitionally equal

/-- CNOT(dataQ n i, ancQ n i) preserves slotWt ≤ 1. -/
private theorem propagateGate_cnot_slotWt (n : Nat) (i : Fin n)
    (es : ErrorState (n + n)) (hes : slotWt n es ≤ 1) :
    slotWt n (propagateGate (Gate.cnot (dataQ n i) (ancQ n i) (data_ne_anc n i)) es) ≤ 1 := by
  set es' := propagateGate (Gate.cnot (dataQ n i) (ancQ n i) (data_ne_anc n i)) es
  apply filter_card_le_one_of_local_change
    (fun k => es'.paulis (dataQ n k) ≠ .I ∨ es'.paulis (ancQ n k) ≠ .I)
    (fun k => es.paulis (dataQ n k) ≠ .I ∨ es.paulis (ancQ n k) ≠ .I)
    i
  · -- agree outside slot i
    intro k hki
    rw [show es'.paulis (dataQ n k) = es.paulis (dataQ n k) from
          propagateGate_cnot_data_other n i k hki es,
        show es'.paulis (ancQ n k) = es.paulis (ancQ n k) from
          propagateGate_cnot_anc_other n i k hki es]
  · -- clean slot i stays clean after CNOT
    intro hi; push_neg at hi ⊢
    obtain ⟨hdi, hai⟩ := hi
    constructor
    · show es'.paulis (dataQ n i) = .I
      show (propagateGate _ es).paulis (dataQ n i) = .I
      simp only [propagateGate]
      have hne : dataQ n i ≠ ancQ n i := data_ne_anc n i
      simp [hne, hai, hdi, zPart, pauliMul]
    · show es'.paulis (ancQ n i) = .I
      show (propagateGate _ es).paulis (ancQ n i) = .I
      simp only [propagateGate]
      simp [hdi, hai, xPart, pauliMul]
  · exact hes

-- ============================================================
-- Circuit-level lemmas
-- ============================================================

/-- Injecting a single Pauli on qubit `q` into any all-I Pauli state gives
slot weight at most one.  Detector logs and cursors are irrelevant here. -/
private theorem slotWt_inject_allPaulis_I (n : Nat) (q : Fin (n + n)) (p : Pauli)
    (es : ErrorState (n + n)) (hall : ∀ j, es.paulis j = .I) :
    slotWt n (es.inject q p) ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ErrorState.inject] at ha hb
  simp [hall, pauliMul_I_right] at ha hb
  -- Each of a, b must have q in their slot (dataQ or ancQ equal to q).
  have ha_slot : dataQ n a = q ∨ ancQ n a = q := by
    rcases ha with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hb_slot : dataQ n b = q ∨ ancQ n b = q := by
    rcases hb with h | h
    · exact Or.inl h.1
    · exact Or.inr h.1
  -- q determines the slot index uniquely (dataQ and ancQ ranges are disjoint)
  ext
  have qval_a : q.val = a.val ∨ q.val = n + a.val := by
    rcases ha_slot with h | h <;> [left; right] <;> exact (congrArg Fin.val h).symm
  have qval_b : q.val = b.val ∨ q.val = n + b.val := by
    rcases hb_slot with h | h <;> [left; right] <;> exact (congrArg Fin.val h).symm
  have := a.isLt; have := b.isLt
  rcases qval_a with ha | ha <;> rcases qval_b with hb | hb <;> omega

/-- Every gate in knillCircuit n is a prepZero, CNOT, or measZ on the appropriate slot. -/
private theorem knill_gate_mem (n : Nat) (g : Gate (n + n))
    (hg : List.Mem g (knillCircuit n)) :
    ∃ i : Fin n, g = Gate.prepZero (ancQ n i) ∨
                 g = Gate.cnot (dataQ n i) (ancQ n i) (data_ne_anc n i) ∨
                 g = Gate.measZ (ancQ n i) := by
  unfold knillCircuit at hg
  have hg' : g ∈ (List.map (qubitGadget n) (List.finRange n)).flatten := hg
  rw [List.mem_flatten] at hg'
  obtain ⟨gadget, hgadget_mem, hg_in⟩ := hg'
  rw [List.mem_map] at hgadget_mem
  obtain ⟨i, _, rfl⟩ := hgadget_mem
  simp only [qubitGadget, List.mem_cons, List.mem_nil_iff, or_false] at hg_in
  exact ⟨i, hg_in⟩

/-- Propagating through a list of Knill gates preserves slotWt ≤ 1. -/
private theorem propagateCircuit_knillGates_slotWt (n : Nat) (gates : List (Gate (n + n)))
    (hgates : ∀ g, g ∈ gates → ∃ i : Fin n,
      g = Gate.prepZero (ancQ n i) ∨
      g = Gate.cnot (dataQ n i) (ancQ n i) (data_ne_anc n i) ∨
      g = Gate.measZ (ancQ n i))
    (es : ErrorState (n + n)) (hes : slotWt n es ≤ 1) :
    slotWt n (propagateCircuit gates es) ≤ 1 := by
  induction gates generalizing es with
  | nil => simpa [propagateCircuit]
  | cons g rest ih =>
    simp only [propagateCircuit]
    apply ih (fun g' hg' => hgates g' (List.mem_cons.mpr (Or.inr hg')))
    obtain ⟨i, hgi⟩ := hgates g (List.mem_cons.mpr (Or.inl rfl))
    rcases hgi with rfl | rfl | rfl
    · exact propagateGate_prepZero_slotWt n i es hes
    · exact propagateGate_cnot_slotWt n i es hes
    · exact propagateGate_measZ_slotWt n i es hes

-- ============================================================
-- Weight bound: general statement
-- ============================================================

/-- **WEIGHT BOUND (general)**: Every single fault has data weight ≤ 1.

    Proof: slotWt is preserved through the circuit, and dataWt ≤ slotWt. -/
theorem weightBound (n : Nat) (fault : Fault (n + n)) :
    dataWt n (computeFaultEffect (knillCircuit n) fault) ≤ 1 := by
  simp only [computeFaultEffect, splitAt]
  apply Nat.le_trans (dataWt_le_slotWt n _)
  apply propagateCircuit_knillGates_slotWt n _ (fun g hg =>
    knill_gate_mem n g (List.mem_of_mem_drop hg))
  apply slotWt_inject_allPaulis_I
  intro q
  exact propagateCircuit_allPaulis_I _ _ (fun q => by simp [ErrorState.clean]) q

-- ============================================================
-- Concrete circuits checked by kernel `decide`
-- ============================================================

-- n=1: [prepZero(1), CNOT(0,1), measZ(1)]
def knill1 : Circuit 2 :=
  [ Gate.prepZero ⟨1, by omega⟩,
    Gate.cnot ⟨0, by omega⟩ ⟨1, by omega⟩ (by decide),
    Gate.measZ ⟨1, by omega⟩ ]

-- n=2
def knill2 : Circuit 4 :=
  [ Gate.prepZero ⟨2, by omega⟩,
    Gate.cnot ⟨0, by omega⟩ ⟨2, by omega⟩ (by decide),
    Gate.measZ ⟨2, by omega⟩,
    Gate.prepZero ⟨3, by omega⟩,
    Gate.cnot ⟨1, by omega⟩ ⟨3, by omega⟩ (by decide),
    Gate.measZ ⟨3, by omega⟩ ]

-- n=3
def knill3 : Circuit 6 :=
  [ Gate.prepZero ⟨3, by omega⟩,
    Gate.cnot ⟨0, by omega⟩ ⟨3, by omega⟩ (by decide),
    Gate.measZ ⟨3, by omega⟩,
    Gate.prepZero ⟨4, by omega⟩,
    Gate.cnot ⟨1, by omega⟩ ⟨4, by omega⟩ (by decide),
    Gate.measZ ⟨4, by omega⟩,
    Gate.prepZero ⟨5, by omega⟩,
    Gate.cnot ⟨2, by omega⟩ ⟨5, by omega⟩ (by decide),
    Gate.measZ ⟨5, by omega⟩ ]

-- n=4
def knill4 : Circuit 8 :=
  [ Gate.prepZero ⟨4, by omega⟩,
    Gate.cnot ⟨0, by omega⟩ ⟨4, by omega⟩ (by decide),
    Gate.measZ ⟨4, by omega⟩,
    Gate.prepZero ⟨5, by omega⟩,
    Gate.cnot ⟨1, by omega⟩ ⟨5, by omega⟩ (by decide),
    Gate.measZ ⟨5, by omega⟩,
    Gate.prepZero ⟨6, by omega⟩,
    Gate.cnot ⟨2, by omega⟩ ⟨6, by omega⟩ (by decide),
    Gate.measZ ⟨6, by omega⟩,
    Gate.prepZero ⟨7, by omega⟩,
    Gate.cnot ⟨3, by omega⟩ ⟨7, by omega⟩ (by decide),
    Gate.measZ ⟨7, by omega⟩ ]

-- Data weight helpers for concrete sizes
private def dataWt1 (es : ErrorState 2) : Nat :=
  (Finset.univ.filter fun i : Fin 1 => es.paulis ⟨i.val, by omega⟩ ≠ .I).card

private def dataWt2 (es : ErrorState 4) : Nat :=
  (Finset.univ.filter fun i : Fin 2 => es.paulis ⟨i.val, by omega⟩ ≠ .I).card

private def dataWt3 (es : ErrorState 6) : Nat :=
  (Finset.univ.filter fun i : Fin 3 => es.paulis ⟨i.val, by omega⟩ ≠ .I).card

private def dataWt4' (es : ErrorState 8) : Nat :=
  (Finset.univ.filter fun i : Fin 4 => es.paulis ⟨i.val, by omega⟩ ≠ .I).card

private def hpX : Pauli.X ≠ .I := by decide
private def hpY : Pauli.Y ≠ .I := by decide
private def hpZ : Pauli.Z ≠ .I := by decide

-- ============================================================
-- WEIGHT BOUND for n=1 (all 3 positions x 2 qubits x 3 Paulis)
-- ============================================================

/-- Every single fault in the n=1 Knill circuit has data weight ≤ 1. -/
theorem weightBound1 (fault : Fault 2) :
    dataWt1 (computeFaultEffect knill1 fault) ≤ 1 := by
  simpa [dataWt1, dataWt, knill1, knillCircuit, qubitGadget, dataQ, ancQ] using
    weightBound 1 fault

-- ============================================================
-- WEIGHT BOUND for n=2
-- ============================================================

/-- Every single fault in the n=2 Knill circuit has data weight ≤ 1. -/
theorem weightBound2 (fault : Fault 4) :
    dataWt2 (computeFaultEffect knill2 fault) ≤ 1 := by
  simpa [dataWt2, dataWt, knill2, knillCircuit, qubitGadget, dataQ, ancQ] using
    weightBound 2 fault

-- ============================================================
-- WEIGHT BOUND for n=3
-- ============================================================

/-- Every single fault in the n=3 Knill circuit has data weight ≤ 1. -/
theorem weightBound3 (fault : Fault 6) :
    dataWt3 (computeFaultEffect knill3 fault) ≤ 1 := by
  simpa [dataWt3, dataWt, knill3, knillCircuit, qubitGadget, dataQ, ancQ] using
    weightBound 3 fault

-- ============================================================
-- WEIGHT BOUND for n=4
-- ============================================================

/-- Every single fault in the n=4 Knill circuit has data weight ≤ 1. -/
theorem weightBound4 (fault : Fault 8) :
    dataWt4' (computeFaultEffect knill4 fault) ≤ 1 := by
  simpa [dataWt4', dataWt, knill4, knillCircuit, qubitGadget, dataQ, ancQ] using
    weightBound 4 fault

-- ============================================================
-- Kernel `decide` verification: n=1
-- ============================================================

example : dataWt1 (computeFaultEffect knill1 ⟨0, ⟨1, by omega⟩, .X, by decide⟩) = 0 := by
  decide
example : dataWt1 (computeFaultEffect knill1 ⟨1, ⟨0, by omega⟩, .X, by decide⟩) = 1 := by
  decide
example : dataWt1 (computeFaultEffect knill1 ⟨1, ⟨0, by omega⟩, .Z, by decide⟩) = 1 := by
  decide
example : dataWt1 (computeFaultEffect knill1 ⟨1, ⟨0, by omega⟩, .Y, by decide⟩) = 1 := by
  decide
example : dataWt1 (computeFaultEffect knill1 ⟨1, ⟨1, by omega⟩, .X, by decide⟩) = 0 := by
  decide
example : dataWt1 (computeFaultEffect knill1 ⟨1, ⟨1, by omega⟩, .Z, by decide⟩) = 1 := by
  decide
example : dataWt1 (computeFaultEffect knill1 ⟨2, ⟨1, by omega⟩, .X, by decide⟩) = 0 := by
  decide
example : dataWt1 (computeFaultEffect knill1 ⟨2, ⟨1, by omega⟩, .Z, by decide⟩) = 0 := by
  decide

-- ============================================================
-- Kernel `decide` verification: n=2
-- ============================================================

example : dataWt2 (computeFaultEffect knill2 ⟨1, ⟨0, by omega⟩, .X, by decide⟩) = 1 := by
  decide
example : dataWt2 (computeFaultEffect knill2 ⟨1, ⟨0, by omega⟩, .Z, by decide⟩) = 1 := by
  decide
example : dataWt2 (computeFaultEffect knill2 ⟨1, ⟨2, by omega⟩, .X, by decide⟩) = 0 := by
  decide
example : dataWt2 (computeFaultEffect knill2 ⟨1, ⟨2, by omega⟩, .Z, by decide⟩) = 1 := by
  decide
example : dataWt2 (computeFaultEffect knill2 ⟨4, ⟨1, by omega⟩, .X, by decide⟩) = 1 := by
  decide
example : dataWt2 (computeFaultEffect knill2 ⟨4, ⟨1, by omega⟩, .Y, by decide⟩) = 1 := by
  decide
example : dataWt2 (computeFaultEffect knill2 ⟨5, ⟨3, by omega⟩, .X, by decide⟩) = 0 := by
  decide

-- ============================================================
-- Kernel `decide` verification: n=4
-- ============================================================

example : dataWt4' (computeFaultEffect knill4 ⟨1, ⟨0, by omega⟩, .X, by decide⟩) = 1 := by
  decide
example : dataWt4' (computeFaultEffect knill4 ⟨4, ⟨1, by omega⟩, .Y, by decide⟩) = 1 := by
  decide
example : dataWt4' (computeFaultEffect knill4 ⟨7, ⟨2, by omega⟩, .Z, by decide⟩) = 1 := by
  decide
example : dataWt4' (computeFaultEffect knill4 ⟨10, ⟨3, by omega⟩, .X, by decide⟩) = 1 := by
  decide
example : dataWt4' (computeFaultEffect knill4 ⟨1, ⟨4, by omega⟩, .X, by decide⟩) = 0 := by
  decide
example : dataWt4' (computeFaultEffect knill4 ⟨5, ⟨5, by omega⟩, .Z, by decide⟩) = 0 := by
  decide
example : dataWt4' (computeFaultEffect knill4 ⟨0, ⟨4, by omega⟩, .X, by decide⟩) = 0 := by
  decide
example : dataWt4' (computeFaultEffect knill4 ⟨3, ⟨5, by omega⟩, .Y, by decide⟩) = 0 := by
  decide

end QStab.QClifford.Knill
