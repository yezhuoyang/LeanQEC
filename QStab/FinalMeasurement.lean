import QStab.DecoderFT
import QStab.Examples.SurfaceGeometry

/-! # Final data measurement and logical observable

Models Stim's `memory_z` experiment ending:
1. After R noisy syndrome rounds, measure ALL data qubits in Z basis (with noise)
2. The OBSERVABLE = parity of Z-measurements on the logical operator's support
3. A LOGICAL ERROR occurs when the decoder's predicted observable differs
   from the actual measured observable.

In QStab terms:
- The final measurement of data qubit q gives: hasZComponent(E_tilde[q]) XOR noise[q]
  (Z-basis measurement sees the Z-component of the Pauli error, plus measurement noise)
- The observable is the parity of these measurements on the logical X-bar support
- The decoder sees G (syndrome history) + final measurements, predicts the observable

This matches Stim's model:
  X_ERROR(p) data_qubits   ← noise before final M (Type-0 errors)
  M data_qubits             ← Z-basis measurement
  OBSERVABLE_INCLUDE(0) rec[support of X-bar]
-/

namespace QStab.FinalMeasurement

open QECParams Pauli

/-! ### Final measurement state

Extends the done state with final data measurements. -/

/-- The result of measuring data qubit q in the Z basis.
    The data qubit starts in |0⟩ (code space). In the Heisenberg picture,
    the measurement outcome is FLIPPED iff the accumulated error E[q] has
    an X-component: X and Y anticommute with Z (flip the outcome), while
    I and Z commute with Z (don't flip).

    So: Z-basis measurement of qubit q = hasXComponent(E[q]).
    NOT hasZComponent — a Z error on a |0⟩ qubit does not flip the Z-measurement. -/
def dataMeasurement {n : Nat} (E : ErrorVec n) (q : Fin n) : Bool :=
  hasXComponent (E q)

/-- The final data measurement record: Z-basis measurement of each data qubit.
    M_data[q] = hasXComponent(E_final[q]) where E_final is the error flow
    AFTER all faults (syndrome rounds + final-measurement noise).

    In the QStab execution, final-measurement noise is modeled as Type-0
    errors that fire after the last syndrome round but before the halt
    transition. These consume error budget just like syndrome-round faults. -/
def finalMeasRecord {n : Nat} (E : ErrorVec n) : Fin n → Bool :=
  fun q => dataMeasurement E q

/-- The logical observable for the memory_z experiment.
    Observable = parity of Z-measurements on the support of logical X-bar.

    logicalX is a Pauli vector representing X-bar. The support of X-bar
    is where logicalX[q] ∈ {X, Y}. The observable is the XOR of
    M_data[q] = hasXComponent(E[q]) for q in supp(X-bar).

    Matches Stim: OBSERVABLE_INCLUDE(0) rec[support of X-bar].

    The observable flips (= true) iff E has an odd number of X-component
    errors on the X-bar support qubits — i.e., E anticommutes with Z-bar
    restricted to the X-bar support. This is the physical definition of
    "a logical X error occurred". -/
def observable {n : Nat} (E : ErrorVec n) (logicalX : ErrorVec n) : Bool :=
  (Finset.univ.filter fun q : Fin n =>
    hasXComponent (logicalX q) && dataMeasurement E q).card % 2 == 1

/-! ### Logical error definition -/

/-- A **logical error** occurs when the decoder's predicted observable
    value differs from the actual measured observable value.

    The decoder sees:
    - G : syndrome measurement record from R rounds
    - M_data : final data measurement record (noisy)
    It outputs a predicted observable value (Bool).

    Actual observable: `observable E_actual logicalX`
    Predicted observable: the decoder computes this from G and M_data.

    For a minimum-weight decoder: it finds the most likely E_hat consistent
    with (G, M_data), then computes `observable E_hat logicalX`.
    Logical error iff `observable E_hat logicalX ≠ observable E_actual logicalX`. -/
def isLogicalError (predicted_obs actual_obs : Bool) : Prop :=
  predicted_obs ≠ actual_obs

/-! ### Circuit-level decoder with final measurement -/

/-- A decoder for the memory experiment: takes the full measurement record
    (syndrome G + final data M) and outputs a predicted observable value. -/
def MemoryDecoder (P : QECParams) :=
  (Fin P.numStab → Fin P.R → Bool) →  -- G (syndrome record)
  (Fin P.n → Bool) →                   -- M_data (final data measurements)
  Bool                                  -- predicted observable

/-- The decoder succeeds if its predicted observable matches the actual. -/
def memDecoderSucceeds (P : QECParams)
    (D : MemoryDecoder P) (s : State P) (logicalX : ErrorVec P.n) : Prop :=
  D s.G (finalMeasRecord s.E_tilde) = observable s.E_tilde logicalX

/-- The memory experiment is t-fault-tolerant under decoder D if
    D's observable prediction is correct for all ≤t-fault executions. -/
def memoryFT (P : QECParams) (D : MemoryDecoder P)
    (logicalX : ErrorVec P.n) (t : Nat) : Prop :=
  ∀ (s : State P), Run P (.done s) → P.C_budget - s.C ≤ t →
    memDecoderSucceeds P D s logicalX

/-! ### Circuit-level distance (memory experiment version)

Two executions are confusable if they produce the same G and M_data
but different observable values. This is the correct R-dependent definition. -/

/-- Two executions are **memory-confusable** if:
    1. Same syndrome record G
    2. Same final data measurements M_data
    3. Different observable value -/
def memConfusable (P : QECParams) (logicalX : ErrorVec P.n)
    (s1 s2 : State P) : Prop :=
  (∀ j y, s1.G j y = s2.G j y) ∧
  (∀ q, finalMeasRecord s1.E_tilde q = finalMeasRecord s2.E_tilde q) ∧
  observable s1.E_tilde logicalX ≠ observable s2.E_tilde logicalX

/-- No decoder succeeds on both memory-confusable executions.
    Same G and M_data → same decoder output → wrong on one of them. -/
theorem memDecoder_fails_on_confusable (P : QECParams)
    (D : MemoryDecoder P) (logicalX : ErrorVec P.n)
    (s1 s2 : State P)
    (hconf : memConfusable P logicalX s1 s2) :
    ¬ memDecoderSucceeds P D s1 logicalX ∨
    ¬ memDecoderSucceeds P D s2 logicalX := by
  obtain ⟨hG, hM, hObs⟩ := hconf
  unfold memDecoderSucceeds
  -- D sees same (G, M_data) for both, so D outputs the same value
  have hG_eq : s1.G = s2.G := funext (fun j => funext (fun y => hG j y))
  have hM_eq : finalMeasRecord s1.E_tilde = finalMeasRecord s2.E_tilde :=
    funext (fun q => hM q)
  -- D's output is the same Bool for both (same input). But observables differ.
  -- So D matches at most one.
  set d_out := D s2.G (finalMeasRecord s2.E_tilde) with hd_def
  have hd1 : D s1.G (finalMeasRecord s1.E_tilde) = d_out := by
    rw [hG_eq, hM_eq]
  by_cases h : d_out = observable s1.E_tilde logicalX
  · right; intro h2; rw [h] at h2; exact hObs h2
  · left; intro h1; rw [hd1] at h1; exact h h1

/-- Memory-confusable pair with ≤t faults each implies not t-FT. -/
theorem memConfusable_implies_not_FT (P : QECParams)
    (D : MemoryDecoder P) (logicalX : ErrorVec P.n) (t : Nat)
    (s1 s2 : State P)
    (hrun1 : Run P (.done s1))
    (hrun2 : Run P (.done s2))
    (hf1 : P.C_budget - s1.C ≤ t)
    (hf2 : P.C_budget - s2.C ≤ t)
    (hconf : memConfusable P logicalX s1 s2) :
    ¬ memoryFT P D logicalX t := by
  intro hFT
  have h := memDecoder_fails_on_confusable P D logicalX s1 s2 hconf
  cases h with
  | inl hf => exact hf (hFT s1 hrun1 hf1)
  | inr hf => exact hf (hFT s2 hrun2 hf2)

end QStab.FinalMeasurement
