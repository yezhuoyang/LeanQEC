import QStab.QClifford.Standard
import QStab.Paper.Soundness

/-! # `SchemeCorrect` for the standard CNOT scheme

Phase B (session 2, iter 9-10). Discharges the `SchemeCorrect`
hypothesis that `qstab_sound` requires.

`SchemeCorrect Γ T_s r := parityFaithful Γ T_s ∧ noBackAction Γ ∧
boundedHook Γ r` where:
- **C2 (noBackAction)**: `dataPauli (runClean Γ E) i = E i`.
  *This file (iter 10): full assembly for xCircuit.*
- **C1 (parityFaithful)**: `measFlipped (runClean Γ E) = parity T_s E`.
  *Iter 11 task.*
- **C3 (boundedHook)**: already proven by `Standard.weight_bounded`.
-/

namespace QStab.Compiler.SchemeCorrectStandard

open QStab QStab.QClifford QStab.QClifford.Standard QStab.Paper.Soundness

/-! ## `dataMatches`: each data qubit equals an externally fixed input -/

/-- `dataMatches E es`: each data qubit of `es` (indices `0..n-1`)
    carries Pauli `E i`. -/
def dataMatches {n : Nat} (E : ErrorVec n) (es : ErrorState (n + 1)) : Prop :=
  ∀ i : Fin n, es.paulis (mkDataQubit n i) = E i

/-- The clean state with `E` injected satisfies `dataMatches E`. -/
theorem dataMatches_init {n : Nat} (E : ErrorVec n) :
    dataMatches E (initialFromData E) := by
  intro i
  simp only [initialFromData, mkDataQubit]
  have h_lt : i.val < n := i.isLt
  simp [h_lt]

/-- `prepPlus` on the ancilla preserves `dataMatches`. -/
theorem dataMatches_prepPlus_anc {n : Nat} (E : ErrorVec n)
    (es : ErrorState (n+1)) (h : dataMatches E es) :
    dataMatches E (propagateGate (Gate.prepPlus (ancQubit n)) es) := by
  intro i
  simp only [propagateGate]
  rw [if_neg (Ne.symm (anc_ne_data n i))]
  exact h i

/-- `Hadamard` on the ancilla preserves `dataMatches`. -/
theorem dataMatches_hadamard_anc {n : Nat} (E : ErrorVec n)
    (es : ErrorState (n+1)) (h : dataMatches E es) :
    dataMatches E (propagateGate (Gate.hadamard (ancQubit n)) es) := by
  intro i
  simp only [propagateGate]
  rw [if_neg (Ne.symm (anc_ne_data n i))]
  exact h i

/-- `measZ` on the ancilla preserves `dataMatches`. -/
theorem dataMatches_measZ_anc {n : Nat} (E : ErrorVec n)
    (es : ErrorState (n+1)) (h : dataMatches E es) :
    dataMatches E (propagateGate (Gate.measZ (ancQubit n)) es) := by
  intro i
  simp only [propagateGate]
  exact h i

/-- `CNOT(anc, q)` preserves `dataMatches` if the ancilla has no
    X-component. The proof: at target `q`, the contribution from
    control is `xPart anc = I`, so the target is unchanged
    (`pauliMul I E = E`); other data qubits are untouched. -/
theorem dataMatches_cnot_anc_to_data {n : Nat} (E : ErrorVec n)
    (q : Fin n) (es : ErrorState (n+1))
    (h : dataMatches E es) (hax : ancHasNoX n es) :
    dataMatches E (propagateGate
      (Gate.cnot (ancQubit n) (mkDataQubit n q) (anc_ne_data n q)) es) := by
  intro i
  simp only [propagateGate]
  by_cases hiq : i = q
  · -- i = q: target qubit. X-from-control is I, so pauliMul I (es.paulis t) = es.paulis t.
    subst hiq
    rw [if_pos rfl]
    have hax' : xPart (es.paulis (ancQubit n)) = .I := hax
    rw [hax']
    show pauliMul Pauli.I _ = E i
    rw [pauliMul_I_left]
    exact h i
  · -- i ≠ q: not the target. Also i is a data index, not the ancilla.
    have h1 : mkDataQubit n i ≠ mkDataQubit n q := by
      simp [mkDataQubit, Fin.ext_iff]
      intro h'; exact hiq (Fin.ext h')
    have h2 : mkDataQubit n i ≠ ancQubit n := data_ne_anc n i
    rw [if_neg h1, if_neg h2]
    exact h i

/-! ## Assembly: induct over the CNOT support list -/

/-- Induction: the CNOT-chain (anc → each data qubit in `qs`) preserves
    both `ancHasNoX` and `dataMatches E`. -/
theorem ancHasNoX_dataMatches_cnotChain {n : Nat} (E : ErrorVec n)
    (qs : List (Fin n)) (es : ErrorState (n+1))
    (hax : ancHasNoX n es) (hdm : dataMatches E es) :
    ancHasNoX n (propagateCircuit
      (qs.map fun q => Gate.cnot (ancQubit n) (mkDataQubit n q) (anc_ne_data n q)) es)
    ∧ dataMatches E (propagateCircuit
      (qs.map fun q => Gate.cnot (ancQubit n) (mkDataQubit n q) (anc_ne_data n q)) es) := by
  induction qs generalizing es with
  | nil => exact ⟨hax, hdm⟩
  | cons q rest ih =>
    simp only [List.map, propagateCircuit]
    obtain ⟨hax', _⟩ := cnot_anc_ancNoX n q es hax
    have hdm' : dataMatches E (propagateGate _ es) :=
      dataMatches_cnot_anc_to_data E q es hdm hax
    exact ih _ hax' hdm'

/-- `prepPlus` on the ancilla yields `ancHasNoX` regardless of input. -/
theorem ancHasNoX_prepPlus_anc {n : Nat} (es : ErrorState (n+1)) :
    ancHasNoX n (propagateGate (Gate.prepPlus (ancQubit n)) es) := by
  show xPart _ = .I
  simp [propagateGate, xPart]

/-- The initial state with E injected has `ancHasNoX` (ancilla = I). -/
theorem ancHasNoX_initialFromData {n : Nat} (E : ErrorVec n) :
    ancHasNoX n (initialFromData E) := by
  show xPart _ = .I
  simp [initialFromData, ancQubit, xPart]

/-- The bedrock dataMatches lemma: full xCircuit preserves data
    qubits. -/
theorem xCircuit_dataMatches_preserved {n : Nat} (support : List (Fin n))
    (E : ErrorVec n) :
    dataMatches E (propagateCircuit (xCircuit n support) (initialFromData E)) := by
  unfold xCircuit
  rw [propagateCircuit_append, propagateCircuit_append]
  -- After prepPlus block: ancHasNoX + dataMatches preserved (dataMatches via prepPlus, ancHasNoX strengthens)
  set es0 := initialFromData E
  -- propagateCircuit [prepPlus] es0 = propagateGate prepPlus es0
  have hpc1 : propagateCircuit [Gate.prepPlus (ancQubit n)] es0 =
              propagateGate (Gate.prepPlus (ancQubit n)) es0 := by
    simp [propagateCircuit]
  rw [hpc1]
  set es1 := propagateGate (Gate.prepPlus (ancQubit n)) es0
  have h_ax1 : ancHasNoX n es1 := ancHasNoX_prepPlus_anc es0
  have h_dm1 : dataMatches E es1 :=
    dataMatches_prepPlus_anc E es0 (dataMatches_init E)
  -- After CNOT chain: dataMatches preserved (ancHasNoX also preserved but not needed downstream)
  obtain ⟨_, h_dm2⟩ := ancHasNoX_dataMatches_cnotChain E support es1 h_ax1 h_dm1
  set es2 := propagateCircuit (support.map _) es1
  -- After [hadamard, measZ]: dataMatches preserved (neither gate touches data).
  simp only [propagateCircuit]
  have h_dm3 := dataMatches_hadamard_anc E es2 h_dm2
  exact dataMatches_measZ_anc E _ h_dm3

/-- **C2 noBackAction for `xCircuit`**: the standard X-side gadget
    leaves data qubits unchanged on a fault-free run. -/
theorem xCircuit_noBackAction {n : Nat} (support : List (Fin n)) :
    noBackAction (xCircuit n support) := by
  intro E i
  show dataErr n (propagateCircuit (xCircuit n support) (initialFromData E)) i = E i
  simp only [dataErr]
  exact xCircuit_dataMatches_preserved support E i

/-! ## Towards C1 (parityFaithful) — ancilla Pauli accumulation

For C1, we need to track what Pauli the ancilla carries after the
CNOT chain. Initial ancilla = I (after prepPlus). Each CNOT(anc, q)
accumulates `pauliMul (zPart (E q)) (anc.paulis)` onto the ancilla,
because the Z-component of the target qubit propagates back to the
control. After the chain, anc.paulis is a product of `zPart` values
over support qubits.

After Hadamard: paulis swap X↔Z; after measZ: hasXComp flips
measFlips. So the measurement-flip parity equals the parity of
Z-components of `E` over `support`. -/

/-- After `CNOT(anc, q)`: if the ancilla had no X-component, the new
    ancilla Pauli is `pauliMul (zPart (es.paulis q-data)) (es.paulis anc)`.
    Data qubits are unchanged (when ancNoX holds — see
    `dataMatches_cnot_anc_to_data`). -/
theorem cnot_anc_to_data_anc_paulis {n : Nat} (q : Fin n)
    (es : ErrorState (n+1)) (_hax : ancHasNoX n es) :
    (propagateGate (Gate.cnot (ancQubit n) (mkDataQubit n q) (anc_ne_data n q)) es).paulis
      (ancQubit n)
    = pauliMul (zPart (es.paulis (mkDataQubit n q))) (es.paulis (ancQubit n)) := by
  simp only [propagateGate]
  have h_ne : ancQubit n ≠ mkDataQubit n q := anc_ne_data n q
  rw [if_neg h_ne]
  simp

end QStab.Compiler.SchemeCorrectStandard
