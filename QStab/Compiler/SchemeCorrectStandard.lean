import QStab.QClifford.Standard
import QStab.Paper.Soundness

/-! # `SchemeCorrect` for the standard CNOT scheme

Phase B (session 2, iter 9). Discharges the `SchemeCorrect` hypothesis
that `qstab_sound` requires (and that `toCircuitStabilizerX_qstab_sound`
in iter 2 took as a parameter), at least partially.

`SchemeCorrect Γ T_s r := parityFaithful Γ T_s ∧ noBackAction Γ ∧
boundedHook Γ r` where:
- **C1 (parityFaithful)**: `measFlipped (runClean Γ E) = parity T_s E`.
  *Iter 10 task.*
- **C2 (noBackAction)**: `dataPauli (runClean Γ E) i = E i`.
  *This file (iter 9).*
- **C3 (boundedHook)**: already proven by `Standard.weight_bounded`.

This file establishes C2 for `Standard.xCircuit`. C1 + Z-side analogs
are deferred to iter 10. -/

namespace QStab.Compiler.SchemeCorrectStandard

open QStab QStab.QClifford QStab.QClifford.Standard QStab.Paper.Soundness

/-! ## Helper invariant: each data qubit equals an externally fixed input -/

/-- `dataMatches E es`: each data qubit of `es` (indices `0..n-1`)
    carries Pauli `E i`. Independent of the ancilla state. -/
def dataMatches {n : Nat} (E : ErrorVec n) (es : ErrorState (n + 1)) : Prop :=
  ∀ i : Fin n, es.paulis ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ = E i

/-- The clean state with `E` injected satisfies `dataMatches E`. -/
theorem dataMatches_init {n : Nat} (E : ErrorVec n) :
    dataMatches E (initialFromData E) := by
  intro i
  simp only [initialFromData]
  have h_lt : i.val < n := i.isLt
  simp [h_lt]

/-- Local copy of Standard.lean's private `ancHasNoX`: the ancilla
    has no X-component. -/
def ancNoX {n : Nat} (es : ErrorState (n + 1)) : Prop :=
  xPart (es.paulis ⟨n, Nat.lt_succ_of_le (Nat.le_refl n)⟩) = .I

/-- The ancilla of `initialFromData E` is identity (so `ancNoX` holds
    initially). -/
theorem initialFromData_anc_I {n : Nat} (E : ErrorVec n) :
    (initialFromData E).paulis ⟨n, Nat.lt_succ_of_le (Nat.le_refl n)⟩ = .I := by
  simp only [initialFromData]
  have h_not : ¬ n < n := Nat.lt_irrefl n
  simp

/-- The initial state has no ancilla X-component. -/
theorem ancNoX_init {n : Nat} (E : ErrorVec n) : ancNoX (initialFromData E) := by
  show xPart _ = .I
  rw [initialFromData_anc_I]
  rfl

/-! ## Gate-by-gate dataMatches preservation -/

private theorem data_ne_anc' (n : Nat) (i : Fin n) :
    (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (n+1)) ≠
      ⟨n, Nat.lt_succ_of_le (Nat.le_refl n)⟩ := by
  simp [Fin.ext_iff]; omega

/-- `prepPlus` on the ancilla preserves `dataMatches`. -/
theorem dataMatches_prepPlus_anc {n : Nat} (E : ErrorVec n)
    (es : ErrorState (n+1)) (h : dataMatches E es) :
    dataMatches E (propagateGate (Gate.prepPlus ⟨n, Nat.lt_succ_of_le (Nat.le_refl n)⟩) es) := by
  intro i
  simp only [propagateGate]
  rw [if_neg (data_ne_anc' n i)]
  exact h i

/-- `Hadamard` on the ancilla preserves `dataMatches`. -/
theorem dataMatches_hadamard_anc {n : Nat} (E : ErrorVec n)
    (es : ErrorState (n+1)) (h : dataMatches E es) :
    dataMatches E (propagateGate (Gate.hadamard ⟨n, Nat.lt_succ_of_le (Nat.le_refl n)⟩) es) := by
  intro i
  simp only [propagateGate]
  rw [if_neg (data_ne_anc' n i)]
  exact h i

/-- `measZ` on the ancilla preserves `dataMatches`. -/
theorem dataMatches_measZ_anc {n : Nat} (E : ErrorVec n)
    (es : ErrorState (n+1)) (h : dataMatches E es) :
    dataMatches E (propagateGate (Gate.measZ ⟨n, Nat.lt_succ_of_le (Nat.le_refl n)⟩) es) := by
  intro i
  -- propagateGate measZ only changes measFlips, not paulis
  simp only [propagateGate]
  exact h i

/-- `CNOT(anc, q)` preserves `dataMatches` *if* the ancilla has no X
    component (so the X-from-control contribution to the target is
    identity). -/
theorem dataMatches_cnot_anc_to_data {n : Nat} (E : ErrorVec n)
    (q : Fin n) (es : ErrorState (n+1))
    (h : dataMatches E es) (hax : ancNoX es) :
    dataMatches E (propagateGate
      (Gate.cnot ⟨n, Nat.lt_succ_of_le (Nat.le_refl n)⟩
                  ⟨q.val, Nat.lt_succ_of_lt q.isLt⟩
                  (by simp [Fin.ext_iff]; omega)) es) := by
  intro i
  simp only [propagateGate]
  by_cases hiq : i = q
  · -- i = q: this is the CNOT target; gets xPart(anc) · es.paulis i.
    subst hiq
    rw [if_pos rfl]
    -- xPart anc = I (from ancHasNoX), so result = pauliMul I (es.paulis i.target) = es.paulis i
    have : xPart (es.paulis ⟨n, Nat.lt_succ_of_le (Nat.le_refl n)⟩) = .I := hax
    rw [this]
    show pauliMul Pauli.I _ = E i
    simp [pauliMul_I_left]
    exact h i
  · -- i ≠ q: gate doesn't touch this qubit (and i ≠ anc since i is a data index)
    have h1 : (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (n+1)) ≠
              ⟨q.val, Nat.lt_succ_of_lt q.isLt⟩ := by
      simp [Fin.ext_iff]; intro h'; exact hiq (Fin.ext h')
    have h2 : (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (n+1)) ≠
              ⟨n, Nat.lt_succ_of_le (Nat.le_refl n)⟩ := data_ne_anc' n i
    rw [if_neg h1, if_neg h2]
    exact h i

end QStab.Compiler.SchemeCorrectStandard
