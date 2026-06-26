import QStab.QClifford.Standard
import QStab.QClifford.Gate
import QStab.Paper.SoundnessPrime

/-! # Shared multi-ancilla geometric lemmas

Week-1 deliverable from the scheme-integration roadmap (workflow
`wxb4qbyrv`). All three multi-ancilla schemes (Chao--Reichardt flag,
multi-ancilla Knill block, Shor cat-state) reuse the lemmas in this
file.

The standard CNOT scheme works on `Circuit (n + 1)` with a single
ancilla at qubit index `n`. This file lifts the standard-scheme
geometric lemmas (`SchemeCorrect/SchemeCorrectStandard.lean`) to a
multi-ancilla layout `Circuit (n + k)` where:

* qubit indices `0 .. n - 1` are data qubits,
* qubit indices `n .. n + k - 1` are ancilla qubits (organised in
  scheme-specific ways: one ancilla + one flag for Flag schemes; a
  cat-block of `w` qubits + one verifier for Shor; one ancilla per
  data qubit for the multi-ancilla Knill block).

Five families of lemmas:

* **(A)** `multiAncReset_*`        — prepZero / prepPlus on a specific
  ancilla preserves the data Paulis and establishes
  `ancHasNoX_at` / `ancHasNoZ_at` for that ancilla.
* **(B)** `cnot_anc_to_data_*`     — CNOT from a specific ancilla to a
  specific data qubit preserves data Paulis under `ancHasNoX_at`.
* **(C)** `cnot_anc_to_anc_*`      — CNOT between two ancilla qubits
  preserves `ancHasNoX_at` of both endpoints when both started with
  ancHasNoX_at.
* **(D)** `multiAnc_meas_*`        — measZ / hadamard / measX on any
  ancilla preserves data Paulis.
* **(E)** `cnotByPauli`            — Pauli-type-driven CNOT orientation
  dispatch for the Knill collapsed scheme.

The lemmas are stated in terms of `Circuit (n + k)` directly, not via
`SchemeBundle'`, so they can be consumed both inside per-scheme files
(Flag.lean, Knill.lean, Shor.lean) and inside compiler-level adapters.

Zero `sorry`, axiom-clean.
-/

namespace QStab.Compiler.SharedLemmas

open QStab QStab.QClifford QStab.QClifford.Standard

/-! ## Qubit constructors and disequality (multi-ancilla layout)

`mkDataQ' n k i` is the data qubit at position `i` in a layout with `n`
data + `k` ancilla qubits. `mkAncQ' n k a` is the ancilla at offset `a`
inside the ancilla block (so its global index is `n + a.val`). -/

/-- Data qubit at index `i` in a multi-ancilla layout. -/
def mkDataQ' (n k : Nat) (i : Fin n) : Fin (n + k) :=
  ⟨i.val, by have := i.isLt; omega⟩

/-- Ancilla qubit at offset `a` (global index `n + a`) in a multi-ancilla
    layout. -/
def mkAncQ' (n k : Nat) (a : Fin k) : Fin (n + k) :=
  ⟨n + a.val, by have := a.isLt; omega⟩

theorem anc_ne_data' (n k : Nat) (a : Fin k) (i : Fin n) :
    mkAncQ' n k a ≠ mkDataQ' n k i := by
  intro h
  have : n + a.val = i.val := congrArg Fin.val h
  have := i.isLt
  omega

theorem data_ne_anc' (n k : Nat) (i : Fin n) (a : Fin k) :
    mkDataQ' n k i ≠ mkAncQ' n k a :=
  fun h => anc_ne_data' n k a i h.symm

theorem anc_ne_anc' (n k : Nat) (a b : Fin k) (hab : a ≠ b) :
    mkAncQ' n k a ≠ mkAncQ' n k b := by
  intro h
  have : n + a.val = n + b.val := congrArg Fin.val h
  exact hab (Fin.ext (by omega))

theorem data_ne_data' (n k : Nat) (i j : Fin n) (hij : i ≠ j) :
    mkDataQ' n k i ≠ mkDataQ' n k j := by
  intro h
  apply hij
  apply Fin.ext
  exact Fin.mk.inj h

/-! ## Per-ancilla X / Z purity predicates -/

/-- Ancilla `a` carries no X component in `es`. -/
def ancHasNoX_at (n k : Nat) (a : Fin k) (es : ErrorState (n + k)) : Prop :=
  xPart (es.paulis (mkAncQ' n k a)) = .I

/-- Ancilla `a` carries no Z component in `es`. -/
def ancHasNoZ_at (n k : Nat) (a : Fin k) (es : ErrorState (n + k)) : Prop :=
  zPart (es.paulis (mkAncQ' n k a)) = .I

/-- Every ancilla in the block carries no X component. -/
def allAncHasNoX (n k : Nat) (es : ErrorState (n + k)) : Prop :=
  ∀ a : Fin k, ancHasNoX_at n k a es

/-- Every ancilla in the block carries no Z component. -/
def allAncHasNoZ (n k : Nat) (es : ErrorState (n + k)) : Prop :=
  ∀ a : Fin k, ancHasNoZ_at n k a es

/-- Data Paulis of `es` match an externally fixed vector `E`. -/
def dataMatches' (n k : Nat) (E : ErrorVec n) (es : ErrorState (n + k)) : Prop :=
  ∀ i : Fin n, es.paulis (mkDataQ' n k i) = E i

/-! ## (A) Multi-ancilla reset: prepPlus / prepZero -/

/-- `prepPlus` on ancilla `a` preserves `dataMatches'` (data qubits
    untouched). -/
theorem prepPlus_ancQ'_dataMatches' (n k : Nat) (a : Fin k) (E : ErrorVec n)
    (es : ErrorState (n + k)) (h : dataMatches' n k E es) :
    dataMatches' n k E (propagateGate (Gate.prepPlus (mkAncQ' n k a)) es) := by
  intro i
  simp only [propagateGate]
  rw [if_neg (data_ne_anc' n k i a)]
  exact h i

/-- `prepZero` on ancilla `a` preserves `dataMatches'`. -/
theorem prepZero_ancQ'_dataMatches' (n k : Nat) (a : Fin k) (E : ErrorVec n)
    (es : ErrorState (n + k)) (h : dataMatches' n k E es) :
    dataMatches' n k E (propagateGate (Gate.prepZero (mkAncQ' n k a)) es) := by
  intro i
  simp only [propagateGate]
  rw [if_neg (data_ne_anc' n k i a)]
  exact h i

/-- `prepPlus` on ancilla `a` establishes `ancHasNoX_at a` regardless
    of the prior state. -/
theorem prepPlus_ancQ'_establishes_ancHasNoX_at (n k : Nat) (a : Fin k)
    (es : ErrorState (n + k)) :
    ancHasNoX_at n k a (propagateGate (Gate.prepPlus (mkAncQ' n k a)) es) := by
  show xPart _ = .I
  simp [propagateGate, xPart]

/-- `prepZero` on ancilla `a` establishes `ancHasNoZ_at a`. -/
theorem prepZero_ancQ'_establishes_ancHasNoZ_at (n k : Nat) (a : Fin k)
    (es : ErrorState (n + k)) :
    ancHasNoZ_at n k a (propagateGate (Gate.prepZero (mkAncQ' n k a)) es) := by
  show zPart _ = .I
  simp [propagateGate, zPart]

/-- `prepPlus` on ancilla `a` preserves `ancHasNoX_at b` for any other
    ancilla `b ≠ a` (and trivially establishes it for `a`). -/
theorem prepPlus_ancQ'_preserves_ancHasNoX_at (n k : Nat) (a b : Fin k)
    (es : ErrorState (n + k)) (h : ancHasNoX_at n k b es) :
    ancHasNoX_at n k b (propagateGate (Gate.prepPlus (mkAncQ' n k a)) es) := by
  by_cases hab : a = b
  · subst hab
    exact prepPlus_ancQ'_establishes_ancHasNoX_at n k a es
  · show xPart _ = .I
    simp only [propagateGate]
    rw [if_neg (anc_ne_anc' n k b a (Ne.symm hab))]
    exact h

/-- `prepZero` on ancilla `a` preserves `ancHasNoZ_at b` for any
    ancilla `b`. -/
theorem prepZero_ancQ'_preserves_ancHasNoZ_at (n k : Nat) (a b : Fin k)
    (es : ErrorState (n + k)) (h : ancHasNoZ_at n k b es) :
    ancHasNoZ_at n k b (propagateGate (Gate.prepZero (mkAncQ' n k a)) es) := by
  by_cases hab : a = b
  · subst hab
    exact prepZero_ancQ'_establishes_ancHasNoZ_at n k a es
  · show zPart _ = .I
    simp only [propagateGate]
    rw [if_neg (anc_ne_anc' n k b a (Ne.symm hab))]
    exact h

/-- `prepZero` on ancilla `a` preserves `ancHasNoX_at b` for any other
    ancilla `b ≠ a`. (Reset doesn't introduce X-component on the
    untouched ancilla.) -/
theorem prepZero_ancQ'_preserves_ancHasNoX_at_other (n k : Nat) (a b : Fin k)
    (hab : a ≠ b) (es : ErrorState (n + k)) (h : ancHasNoX_at n k b es) :
    ancHasNoX_at n k b (propagateGate (Gate.prepZero (mkAncQ' n k a)) es) := by
  show xPart _ = .I
  simp only [propagateGate]
  rw [if_neg (anc_ne_anc' n k b a (Ne.symm hab))]
  exact h

/-- `prepPlus` on ancilla `a` preserves `ancHasNoZ_at b` for any other
    ancilla `b ≠ a`. -/
theorem prepPlus_ancQ'_preserves_ancHasNoZ_at_other (n k : Nat) (a b : Fin k)
    (hab : a ≠ b) (es : ErrorState (n + k)) (h : ancHasNoZ_at n k b es) :
    ancHasNoZ_at n k b (propagateGate (Gate.prepPlus (mkAncQ' n k a)) es) := by
  show zPart _ = .I
  simp only [propagateGate]
  rw [if_neg (anc_ne_anc' n k b a (Ne.symm hab))]
  exact h

/-! ## (B) CNOT from ancilla to data qubit -/

/-- `CNOT(anc a, data i)` preserves `dataMatches'` under
    `ancHasNoX_at a`. The X-component of the control (ancilla) is I,
    so the target qubit (data) is unchanged. -/
theorem cnot_anc_to_data_dataMatches' (n k : Nat) (a : Fin k) (q : Fin n)
    (E : ErrorVec n) (es : ErrorState (n + k))
    (hdm : dataMatches' n k E es) (hax : ancHasNoX_at n k a es) :
    dataMatches' n k E (propagateGate
      (Gate.cnot (mkAncQ' n k a) (mkDataQ' n k q) (anc_ne_data' n k a q)) es) := by
  intro i
  simp only [propagateGate]
  by_cases hiq : i = q
  · subst hiq
    rw [if_pos rfl]
    have hax' : xPart (es.paulis (mkAncQ' n k a)) = .I := hax
    rw [hax']
    show pauliMul Pauli.I _ = E i
    rw [pauliMul_I_left]
    exact hdm i
  · have h1 : mkDataQ' n k i ≠ mkDataQ' n k q := data_ne_data' n k i q hiq
    have h2 : mkDataQ' n k i ≠ mkAncQ' n k a := data_ne_anc' n k i a
    rw [if_neg h1, if_neg h2]
    exact hdm i

/-- `CNOT(anc a, data i)` preserves `ancHasNoX_at a` (ancilla X-part
    unchanged by a CNOT in which the ancilla is the control). -/
theorem cnot_anc_to_data_ancHasNoX_at (n k : Nat) (a : Fin k) (q : Fin n)
    (es : ErrorState (n + k)) (hax : ancHasNoX_at n k a es) :
    ancHasNoX_at n k a (propagateGate
      (Gate.cnot (mkAncQ' n k a) (mkDataQ' n k q) (anc_ne_data' n k a q)) es) := by
  show xPart _ = .I
  simp only [propagateGate, if_neg (anc_ne_data' n k a q), if_true]
  have hax' : xPart (es.paulis (mkAncQ' n k a)) = .I := hax
  -- xPart (pauliMul (zPart _) p) = xPart p because zPart is in {I, Z},
  -- both of which have trivial xPart contribution.
  generalize hp : es.paulis (mkAncQ' n k a) = p
  generalize hz : zPart (es.paulis (mkDataQ' n k q)) = z
  have hz_cases : z = .I ∨ z = .Z := by
    rw [← hz]
    cases hpd : es.paulis (mkDataQ' n k q) <;> simp [zPart]
  rw [hp] at hax'
  rcases hz_cases with rfl | rfl
  · rw [pauliMul_I_left]; exact hax'
  · cases p <;> simp_all [pauliMul, xPart]

/-- `CNOT(data i, anc a)` preserves `dataMatches'` under
    `ancHasNoZ_at a`. The Z-component of the target (ancilla) is I,
    so the control qubit (data) is unchanged. -/
theorem cnot_data_to_anc_dataMatches' (n k : Nat) (q : Fin n) (a : Fin k)
    (E : ErrorVec n) (es : ErrorState (n + k))
    (hdm : dataMatches' n k E es) (haz : ancHasNoZ_at n k a es) :
    dataMatches' n k E (propagateGate
      (Gate.cnot (mkDataQ' n k q) (mkAncQ' n k a) (data_ne_anc' n k q a)) es) := by
  intro i
  simp only [propagateGate]
  by_cases hiq : i = q
  · subst hiq
    have h_ne : mkDataQ' n k i ≠ mkAncQ' n k a := data_ne_anc' n k i a
    rw [if_neg h_ne, if_pos rfl]
    have haz' : zPart (es.paulis (mkAncQ' n k a)) = .I := haz
    rw [haz']
    show pauliMul Pauli.I _ = E i
    rw [pauliMul_I_left]
    exact hdm i
  · have h1 : mkDataQ' n k i ≠ mkDataQ' n k q := data_ne_data' n k i q hiq
    have h2 : mkDataQ' n k i ≠ mkAncQ' n k a := data_ne_anc' n k i a
    rw [if_neg h2, if_neg h1]
    exact hdm i

/-! ## (C) CNOT between two ancillae -/

/-- `CNOT(anc a, anc b)` (a ≠ b) preserves data Paulis (neither qubit
    is data). -/
theorem cnot_anc_to_anc_dataMatches' (n k : Nat) (a b : Fin k) (hab : a ≠ b)
    (E : ErrorVec n) (es : ErrorState (n + k))
    (h : dataMatches' n k E es) :
    dataMatches' n k E (propagateGate
      (Gate.cnot (mkAncQ' n k a) (mkAncQ' n k b) (anc_ne_anc' n k a b hab)) es) := by
  intro i
  simp only [propagateGate]
  have h1 : mkDataQ' n k i ≠ mkAncQ' n k b := data_ne_anc' n k i b
  have h2 : mkDataQ' n k i ≠ mkAncQ' n k a := data_ne_anc' n k i a
  rw [if_neg h1, if_neg h2]
  exact h i

/-- `CNOT(anc a, anc b)` (a ≠ b) preserves `ancHasNoX_at a` (control
    ancilla X-part unchanged when target ancilla's Z-part is I). -/
theorem cnot_anc_to_anc_ancHasNoX_at_ctrl (n k : Nat) (a b : Fin k)
    (hab : a ≠ b) (es : ErrorState (n + k))
    (hax_a : ancHasNoX_at n k a es) (haz_b : ancHasNoZ_at n k b es) :
    ancHasNoX_at n k a (propagateGate
      (Gate.cnot (mkAncQ' n k a) (mkAncQ' n k b) (anc_ne_anc' n k a b hab)) es) := by
  show xPart _ = .I
  simp only [propagateGate, if_neg (anc_ne_anc' n k a b hab), if_true]
  have hax' : xPart (es.paulis (mkAncQ' n k a)) = .I := hax_a
  have haz' : zPart (es.paulis (mkAncQ' n k b)) = .I := haz_b
  rw [haz', pauliMul_I_left]
  exact hax'

/-- `CNOT(anc a, anc b)` (a ≠ b) preserves `ancHasNoX_at b` (target
    ancilla X-part picks up control's X, which is I). -/
theorem cnot_anc_to_anc_ancHasNoX_at_target (n k : Nat) (a b : Fin k)
    (hab : a ≠ b) (es : ErrorState (n + k))
    (hax_a : ancHasNoX_at n k a es) (hax_b : ancHasNoX_at n k b es) :
    ancHasNoX_at n k b (propagateGate
      (Gate.cnot (mkAncQ' n k a) (mkAncQ' n k b) (anc_ne_anc' n k a b hab)) es) := by
  show xPart _ = .I
  simp only [propagateGate, if_true]
  have hax' : xPart (es.paulis (mkAncQ' n k a)) = .I := hax_a
  have hax_b' : xPart (es.paulis (mkAncQ' n k b)) = .I := hax_b
  rw [hax', pauliMul_I_left]
  exact hax_b'

/-! ## (D) Measurement / Hadamard on ancilla preserve data -/

/-- `measZ` on ancilla `a` preserves `dataMatches'` (no data qubit
    touched). -/
theorem measZ_ancQ'_dataMatches' (n k : Nat) (a : Fin k) (E : ErrorVec n)
    (es : ErrorState (n + k)) (h : dataMatches' n k E es) :
    dataMatches' n k E (propagateGate (Gate.measZ (mkAncQ' n k a)) es) := by
  intro i
  simp only [propagateGate]
  exact h i

/-- `hadamard` on ancilla `a` preserves `dataMatches'`. -/
theorem hadamard_ancQ'_dataMatches' (n k : Nat) (a : Fin k) (E : ErrorVec n)
    (es : ErrorState (n + k)) (h : dataMatches' n k E es) :
    dataMatches' n k E (propagateGate (Gate.hadamard (mkAncQ' n k a)) es) := by
  intro i
  simp only [propagateGate]
  rw [if_neg (data_ne_anc' n k i a)]
  exact h i

/-! ## (E) Pauli-type-driven CNOT orientation dispatch (for Knill) -/

/-- For an X-type stabilizer Pauli, return CNOT(anc, data); for a
    Z-type Pauli, return CNOT(data, anc); for I or Y, return a
    sentinel `measZ(anc)` (which acts as identity on data, since data
    is unchanged by measurement). The Y case must be ruled out by a
    CSS-typing hypothesis at the call site. -/
def cnotByPauli (n k : Nat) (a : Fin k) (q : Fin n) (p : Pauli) :
    Gate (n + k) :=
  match p with
  | .X => Gate.cnot (mkAncQ' n k a) (mkDataQ' n k q) (anc_ne_data' n k a q)
  | .Z => Gate.cnot (mkDataQ' n k q) (mkAncQ' n k a) (data_ne_anc' n k q a)
  | .I | .Y => Gate.measZ (mkAncQ' n k a)  -- identity on data; CSS hypothesis rules out

/-- `cnotByPauli` preserves data when the source Pauli is X, given
    `ancHasNoX_at a`. -/
theorem cnotByPauli_X_dataMatches' (n k : Nat) (a : Fin k) (q : Fin n)
    (E : ErrorVec n) (es : ErrorState (n + k))
    (hdm : dataMatches' n k E es) (hax : ancHasNoX_at n k a es) :
    dataMatches' n k E (propagateGate (cnotByPauli n k a q .X) es) := by
  unfold cnotByPauli
  exact cnot_anc_to_data_dataMatches' n k a q E es hdm hax

/-- `cnotByPauli` preserves data when the source Pauli is Z, given
    `ancHasNoZ_at a`. -/
theorem cnotByPauli_Z_dataMatches' (n k : Nat) (a : Fin k) (q : Fin n)
    (E : ErrorVec n) (es : ErrorState (n + k))
    (hdm : dataMatches' n k E es) (haz : ancHasNoZ_at n k a es) :
    dataMatches' n k E (propagateGate (cnotByPauli n k a q .Z) es) := by
  unfold cnotByPauli
  exact cnot_data_to_anc_dataMatches' n k q a E es hdm haz

/-- `cnotByPauli` is the identity-on-data measZ for I (CSS hypothesis
    rules out reaching this case in valid stabilizers). -/
theorem cnotByPauli_I_dataMatches' (n k : Nat) (a : Fin k) (q : Fin n)
    (E : ErrorVec n) (es : ErrorState (n + k)) (h : dataMatches' n k E es) :
    dataMatches' n k E (propagateGate (cnotByPauli n k a q .I) es) := by
  unfold cnotByPauli
  exact measZ_ancQ'_dataMatches' n k a E es h

/-! ## Multi-ancilla CNOT chain (anc to data list, generic ancilla) -/

/-- Induction: a chain of `CNOT(anc a, data q_i)` for `q_i ∈ qs`
    preserves `ancHasNoX_at a` and `dataMatches'`. -/
theorem cnotChain_anc_to_data_preserves (n k : Nat) (a : Fin k)
    (E : ErrorVec n) (qs : List (Fin n)) (es : ErrorState (n + k))
    (hdm : dataMatches' n k E es) (hax : ancHasNoX_at n k a es) :
    ancHasNoX_at n k a (propagateCircuit
      (qs.map fun q => Gate.cnot (mkAncQ' n k a) (mkDataQ' n k q)
        (anc_ne_data' n k a q)) es)
    ∧ dataMatches' n k E (propagateCircuit
      (qs.map fun q => Gate.cnot (mkAncQ' n k a) (mkDataQ' n k q)
        (anc_ne_data' n k a q)) es) := by
  induction qs generalizing es with
  | nil => exact ⟨hax, hdm⟩
  | cons q rest ih =>
    simp only [List.map, propagateCircuit]
    have hax' := cnot_anc_to_data_ancHasNoX_at n k a q es hax
    have hdm' := cnot_anc_to_data_dataMatches' n k a q E es hdm hax
    exact ih _ hdm' hax'

/-! ## Initial state lifters (compatibility with `SoundnessPrime`) -/

/-- The initial state `initialFromData' n k E` has all ancillae I
    (and so `ancHasNoX_at` holds for every ancilla). -/
theorem initialFromData'_ancHasNoX (n k : Nat) (a : Fin k) (E : ErrorVec n) :
    ancHasNoX_at n k a
      (QStab.Paper.SoundnessPrime.initialFromData' n k E) := by
  show xPart _ = .I
  have h_not_lt : ¬ (mkAncQ' n k a).val < n := by
    show ¬ n + a.val < n; omega
  unfold QStab.Paper.SoundnessPrime.initialFromData'
  simp [dif_neg h_not_lt, xPart]

/-- The initial state has all ancillae carrying no Z either. -/
theorem initialFromData'_ancHasNoZ (n k : Nat) (a : Fin k) (E : ErrorVec n) :
    ancHasNoZ_at n k a
      (QStab.Paper.SoundnessPrime.initialFromData' n k E) := by
  show zPart _ = .I
  have h_not_lt : ¬ (mkAncQ' n k a).val < n := by
    show ¬ n + a.val < n; omega
  unfold QStab.Paper.SoundnessPrime.initialFromData'
  simp [dif_neg h_not_lt, zPart]

/-- The initial state satisfies `dataMatches' E` (data qubits carry E). -/
theorem initialFromData'_dataMatches' (n k : Nat) (E : ErrorVec n) :
    dataMatches' n k E (QStab.Paper.SoundnessPrime.initialFromData' n k E) := by
  intro i
  simp only [QStab.Paper.SoundnessPrime.initialFromData', mkDataQ']
  have h_lt : i.val < n := i.isLt
  simp [h_lt]

end QStab.Compiler.SharedLemmas
