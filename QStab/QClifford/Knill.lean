import QStab.QClifford.Gate
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

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

/-- propagateGate applied to a clean state gives a clean state. -/
private theorem propagateGate_clean {nq : Nat} (g : Gate nq) :
    propagateGate g (ErrorState.clean nq) = ErrorState.clean nq := by
  cases g with
  | cnot c t hne => simp [propagateGate, ErrorState.clean, xPart, zPart]
  | hadamard q => simp [propagateGate, ErrorState.clean, hadamardAction]
  | prepZero q => simp [propagateGate, ErrorState.clean]
  | prepPlus q => simp [propagateGate, ErrorState.clean]
  | measZ q => simp [propagateGate, ErrorState.clean, hasXComp]

/-- Any circuit applied to a clean state gives a clean state. -/
private theorem propagateCircuit_clean {nq : Nat} (circuit : Circuit nq) :
    propagateCircuit circuit (ErrorState.clean nq) = ErrorState.clean nq := by
  induction circuit with
  | nil => simp [propagateCircuit]
  | cons g gs ih => simp [propagateCircuit, propagateGate_clean, ih]

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

/-- computeFaultEffect simplifies: the prefix propagation on clean state gives clean. -/
private theorem computeFaultEffect_eq (circuit : Circuit nq) (fault : Fault nq) :
    computeFaultEffect circuit fault =
    propagateCircuit (circuit.drop fault.position)
      ((ErrorState.clean nq).inject fault.qubit fault.pauli) := by
  simp [computeFaultEffect, splitAt, propagateCircuit_clean]

/-- Injecting a single Pauli on qubit q into a clean state gives slotWt ≤ 1. -/
private theorem slotWt_inject_clean (n : Nat) (q : Fin (n + n)) (p : Pauli) :
    slotWt n ((ErrorState.clean (n + n)).inject q p) ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
             ErrorState.inject, ErrorState.clean, pauliMul_I_right] at ha hb
  -- Each of a, b must have q in their slot (dataQ or ancQ equal to q)
  have get_slot : ∀ (k : Fin n),
      ((if dataQ n k = q then p else .I) ≠ .I ∨ (if ancQ n k = q then p else .I) ≠ .I) →
      dataQ n k = q ∨ ancQ n k = q := by
    intro k hk; rcases hk with hd | ha
    · left; by_contra h; simp [h] at hd
    · right; by_contra h; simp [h] at ha
  have ha_slot := get_slot a ha
  have hb_slot := get_slot b hb
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
  rw [computeFaultEffect_eq]
  apply Nat.le_trans (dataWt_le_slotWt n _)
  apply propagateCircuit_knillGates_slotWt n _ (fun g hg =>
    knill_gate_mem n g (List.mem_of_mem_drop hg))
  exact slotWt_inject_clean n fault.qubit fault.pauli

-- ============================================================
-- Concrete circuits (no sorry, for native_decide)
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
  rcases fault with ⟨pos, q, p, hp⟩
  -- For large pos, circuit suffix is empty, at most 1 data qubit affected
  by_cases hpos : pos < knill1.length
  · simp [knill1] at hpos
    cases p with
    | I => exact absurd rfl hp
    | X =>
      rw [ce_irrel knill1 pos q .X hp hpX]
      interval_cases pos <;> fin_cases q <;> native_decide
    | Y =>
      rw [ce_irrel knill1 pos q .Y hp hpY]
      interval_cases pos <;> fin_cases q <;> native_decide
    | Z =>
      rw [ce_irrel knill1 pos q .Z hp hpZ]
      interval_cases pos <;> fin_cases q <;> native_decide
  · -- pos >= circuit length: suffix is empty, at most 1 qubit affected
    push_neg at hpos
    simp only [computeFaultEffect, splitAt, List.take_of_length_le hpos,
               List.drop_eq_nil_iff.mpr hpos, propagateCircuit_clean, propagateCircuit]
    simp only [dataWt1, ErrorState.inject]
    apply Finset.card_le_one.mpr
    intro ⟨i, hi⟩ hmemi ⟨j, hj⟩ hmemj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmemi hmemj
    simp only [ErrorState.clean] at hmemi hmemj
    split_ifs at hmemi hmemj with hiq hjq
    · ext; have := congrArg Fin.val hiq; have := congrArg Fin.val hjq; omega
    · simp at hmemj
    · simp at hmemi
    · simp at hmemi

-- ============================================================
-- WEIGHT BOUND for n=2
-- ============================================================

/-- Every single fault in the n=2 Knill circuit has data weight ≤ 1. -/
theorem weightBound2 (fault : Fault 4) :
    dataWt2 (computeFaultEffect knill2 fault) ≤ 1 := by
  rcases fault with ⟨pos, q, p, hp⟩
  by_cases hpos : pos < knill2.length
  · simp [knill2] at hpos
    cases p with
    | I => exact absurd rfl hp
    | X =>
      rw [ce_irrel knill2 pos q .X hp hpX]
      interval_cases pos <;> fin_cases q <;> native_decide
    | Y =>
      rw [ce_irrel knill2 pos q .Y hp hpY]
      interval_cases pos <;> fin_cases q <;> native_decide
    | Z =>
      rw [ce_irrel knill2 pos q .Z hp hpZ]
      interval_cases pos <;> fin_cases q <;> native_decide
  · push_neg at hpos
    simp only [computeFaultEffect, splitAt, List.take_of_length_le hpos,
               List.drop_eq_nil_iff.mpr hpos, propagateCircuit_clean, propagateCircuit]
    simp only [dataWt2, ErrorState.inject]
    apply Finset.card_le_one.mpr
    intro ⟨i, hi⟩ hmemi ⟨j, hj⟩ hmemj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmemi hmemj
    simp only [ErrorState.clean] at hmemi hmemj
    split_ifs at hmemi hmemj with hiq hjq
    · ext; have := congrArg Fin.val hiq; have := congrArg Fin.val hjq; omega
    · simp at hmemj
    · simp at hmemi
    · simp at hmemi

-- ============================================================
-- WEIGHT BOUND for n=3
-- ============================================================

/-- Every single fault in the n=3 Knill circuit has data weight ≤ 1. -/
theorem weightBound3 (fault : Fault 6) :
    dataWt3 (computeFaultEffect knill3 fault) ≤ 1 := by
  rcases fault with ⟨pos, q, p, hp⟩
  by_cases hpos : pos < knill3.length
  · simp [knill3] at hpos
    cases p with
    | I => exact absurd rfl hp
    | X =>
      rw [ce_irrel knill3 pos q .X hp hpX]
      interval_cases pos <;> fin_cases q <;> native_decide
    | Y =>
      rw [ce_irrel knill3 pos q .Y hp hpY]
      interval_cases pos <;> fin_cases q <;> native_decide
    | Z =>
      rw [ce_irrel knill3 pos q .Z hp hpZ]
      interval_cases pos <;> fin_cases q <;> native_decide
  · push_neg at hpos
    simp only [computeFaultEffect, splitAt, List.take_of_length_le hpos,
               List.drop_eq_nil_iff.mpr hpos, propagateCircuit_clean, propagateCircuit]
    simp only [dataWt3, ErrorState.inject]
    apply Finset.card_le_one.mpr
    intro ⟨i, hi⟩ hmemi ⟨j, hj⟩ hmemj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmemi hmemj
    simp only [ErrorState.clean] at hmemi hmemj
    split_ifs at hmemi hmemj with hiq hjq
    · ext; have := congrArg Fin.val hiq; have := congrArg Fin.val hjq; omega
    · simp at hmemj
    · simp at hmemi
    · simp at hmemi

-- ============================================================
-- WEIGHT BOUND for n=4
-- ============================================================

/-- Every single fault in the n=4 Knill circuit has data weight ≤ 1. -/
theorem weightBound4 (fault : Fault 8) :
    dataWt4' (computeFaultEffect knill4 fault) ≤ 1 := by
  rcases fault with ⟨pos, q, p, hp⟩
  by_cases hpos : pos < knill4.length
  · simp [knill4] at hpos
    cases p with
    | I => exact absurd rfl hp
    | X =>
      rw [ce_irrel knill4 pos q .X hp hpX]
      interval_cases pos <;> fin_cases q <;> native_decide
    | Y =>
      rw [ce_irrel knill4 pos q .Y hp hpY]
      interval_cases pos <;> fin_cases q <;> native_decide
    | Z =>
      rw [ce_irrel knill4 pos q .Z hp hpZ]
      interval_cases pos <;> fin_cases q <;> native_decide
  · push_neg at hpos
    simp only [computeFaultEffect, splitAt, List.take_of_length_le hpos,
               List.drop_eq_nil_iff.mpr hpos, propagateCircuit_clean, propagateCircuit]
    simp only [dataWt4', ErrorState.inject]
    apply Finset.card_le_one.mpr
    intro ⟨i, hi⟩ hmemi ⟨j, hj⟩ hmemj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmemi hmemj
    simp only [ErrorState.clean] at hmemi hmemj
    split_ifs at hmemi hmemj with hiq hjq
    · ext; have := congrArg Fin.val hiq; have := congrArg Fin.val hjq; omega
    · simp at hmemj
    · simp at hmemi
    · simp at hmemi

-- ============================================================
-- native_decide verification: n=1
-- ============================================================

example : dataWt1 (computeFaultEffect knill1 ⟨0, ⟨1, by omega⟩, .X, by decide⟩) = 0 := by
  native_decide
example : dataWt1 (computeFaultEffect knill1 ⟨1, ⟨0, by omega⟩, .X, by decide⟩) = 1 := by
  native_decide
example : dataWt1 (computeFaultEffect knill1 ⟨1, ⟨0, by omega⟩, .Z, by decide⟩) = 1 := by
  native_decide
example : dataWt1 (computeFaultEffect knill1 ⟨1, ⟨0, by omega⟩, .Y, by decide⟩) = 1 := by
  native_decide
example : dataWt1 (computeFaultEffect knill1 ⟨1, ⟨1, by omega⟩, .X, by decide⟩) = 0 := by
  native_decide
example : dataWt1 (computeFaultEffect knill1 ⟨1, ⟨1, by omega⟩, .Z, by decide⟩) = 1 := by
  native_decide
example : dataWt1 (computeFaultEffect knill1 ⟨2, ⟨1, by omega⟩, .X, by decide⟩) = 0 := by
  native_decide
example : dataWt1 (computeFaultEffect knill1 ⟨2, ⟨1, by omega⟩, .Z, by decide⟩) = 0 := by
  native_decide

-- ============================================================
-- native_decide verification: n=2
-- ============================================================

example : dataWt2 (computeFaultEffect knill2 ⟨1, ⟨0, by omega⟩, .X, by decide⟩) = 1 := by
  native_decide
example : dataWt2 (computeFaultEffect knill2 ⟨1, ⟨0, by omega⟩, .Z, by decide⟩) = 1 := by
  native_decide
example : dataWt2 (computeFaultEffect knill2 ⟨1, ⟨2, by omega⟩, .X, by decide⟩) = 0 := by
  native_decide
example : dataWt2 (computeFaultEffect knill2 ⟨1, ⟨2, by omega⟩, .Z, by decide⟩) = 1 := by
  native_decide
example : dataWt2 (computeFaultEffect knill2 ⟨4, ⟨1, by omega⟩, .X, by decide⟩) = 1 := by
  native_decide
example : dataWt2 (computeFaultEffect knill2 ⟨4, ⟨1, by omega⟩, .Y, by decide⟩) = 1 := by
  native_decide
example : dataWt2 (computeFaultEffect knill2 ⟨5, ⟨3, by omega⟩, .X, by decide⟩) = 0 := by
  native_decide

-- ============================================================
-- native_decide verification: n=4
-- ============================================================

example : dataWt4' (computeFaultEffect knill4 ⟨1, ⟨0, by omega⟩, .X, by decide⟩) = 1 := by
  native_decide
example : dataWt4' (computeFaultEffect knill4 ⟨4, ⟨1, by omega⟩, .Y, by decide⟩) = 1 := by
  native_decide
example : dataWt4' (computeFaultEffect knill4 ⟨7, ⟨2, by omega⟩, .Z, by decide⟩) = 1 := by
  native_decide
example : dataWt4' (computeFaultEffect knill4 ⟨10, ⟨3, by omega⟩, .X, by decide⟩) = 1 := by
  native_decide
example : dataWt4' (computeFaultEffect knill4 ⟨1, ⟨4, by omega⟩, .X, by decide⟩) = 0 := by
  native_decide
example : dataWt4' (computeFaultEffect knill4 ⟨5, ⟨5, by omega⟩, .Z, by decide⟩) = 0 := by
  native_decide
example : dataWt4' (computeFaultEffect knill4 ⟨0, ⟨4, by omega⟩, .X, by decide⟩) = 0 := by
  native_decide
example : dataWt4' (computeFaultEffect knill4 ⟨3, ⟨5, by omega⟩, .Y, by decide⟩) = 0 := by
  native_decide

end QStab.QClifford.Knill
