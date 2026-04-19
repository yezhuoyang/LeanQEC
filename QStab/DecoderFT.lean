import QStab.Invariant
import QStab.MultiStep
import QStab.Examples.SurfaceGeometry

/-! # Decoder-based fault tolerance from code distance

Formalizes the connection between Definition 3.6 (circuit-level distance)
and Definition 3.9 (decoder-based t-fault-tolerance).

Key result: Lemma 3.8 (DistImpliesFT) — if d^circ ≥ d, then the circuit
is ⌊(d-1)/2⌋-fault-tolerant under any decoder that picks a minimum-weight
explanation of the detector data.
-/

namespace QStab.DecoderFT

open QECParams

/-! ### Definition 3.7: Circuit-level decoder -/

/-- A circuit-level decoder maps the done state (which contains the
    measurement record G) to a Pauli correction on data qubits. -/
def Decoder (P : QECParams) := State P → ErrorVec P.n

/-- The decoder succeeds if the correction times the actual error flow
    is in the stabilizer group (equivalently: the residual is trivial). -/
def decoderSucceeds (P : QECParams) (D : Decoder P) (s : State P) : Prop :=
  InStab P (ErrorVec.mul (D s) s.E_tilde)

/-- The decoder fails (logical error) if the residual is not in S. -/
def decoderFails (P : QECParams) (D : Decoder P) (s : State P) : Prop :=
  ¬ InStab P (ErrorVec.mul (D s) s.E_tilde)

/-! ### Definition 3.9: Decoder-based t-fault-tolerance -/

/-- A circuit is t-fault-tolerant under decoder D if D succeeds on every
    execution reaching σ_done with at most t faults. -/
def isFaultTolerant (P : QECParams) (D : Decoder P) (t : Nat) : Prop :=
  ∀ (s : State P), Run P (.done s) → P.C_budget - s.C ≤ t →
    decoderSucceeds P D s

/-! ### The trivial decoder (identity correction) -/

/-- The trivial decoder applies no correction: D(s) = identity. -/
def trivialDecoder (P : QECParams) : Decoder P :=
  fun _ => ErrorVec.identity P.n

/-- The trivial decoder succeeds iff E_tilde ∈ S. -/
theorem trivialDecoder_succeeds_iff (P : QECParams) (s : State P) :
    decoderSucceeds P (trivialDecoder P) s ↔ InStab P s.E_tilde := by
  unfold decoderSucceeds trivialDecoder
  constructor
  · intro h
    -- mul identity E = E (need this lemma)
    rwa [ErrorVec.mul_identity_left] at h
  · intro h
    rwa [ErrorVec.mul_identity_left]

/-! ### Code distance definition -/

/-- **Undetected logical error**: the condition defining circuit-level code distance.
    An execution produces an undetected logical error if:
    1. G = 0: all measurement records are zero (undetectable by syndrome history)
    2. Syn(E) = 0: E commutes with all stabilizers (zero syndrome)
    3. E ∉ S: the error is not a stabilizer (nontrivial logical class)

    Equivalently: E ∈ N(S)\S with G = 0.

    The combined-configuration argument (Lemma `decoder_FT_from_distance`)
    shows this is equivalent to decoder-based fault-tolerance: if the minimum
    fault count for an undetected logical error is d, then any decoder that
    picks a minimum-weight consistent explanation is ⌊(d-1)/2⌋-fault-tolerant.

    Paper: Definition 4.8 (Circuit-level distance). -/
def isUndetectedLogicalError (P : QECParams) (s : State P) : Prop :=
  (∀ (j : Fin P.numStab) (y : Fin P.R), s.G j y = false) ∧
  (∀ (i : Fin P.numStab),
    ErrorVec.parity (P.stabilizers i) s.E_tilde = false) ∧
  ¬ InStab P s.E_tilde

/-- d^circ ≥ d means: every execution reaching σ_done with an undetected
    logical error used at least d faults. -/
def circuitDistanceGe (P : QECParams) (d_val : Nat) : Prop :=
  ∀ (s : State P), Run P (.done s) → isUndetectedLogicalError P s →
    d_val ≤ P.C_budget - s.C

/-! ### Lemma 3.8: Code distance implies trivial-decoder FT (G = 0 case)

This is the easy direction: when G = 0, the trivial decoder (identity
correction) succeeds because d^circ ≥ d forces E_tilde ∈ S. -/

/-- If d^circ ≥ d, then any execution with < d faults, G = 0,
    and zero syndrome has E_tilde ∈ S.
    This is the contrapositive of the d^circ definition. -/
theorem undetected_faults_ge_d (P : QECParams) (d_val : Nat) (s : State P)
    (hd : circuitDistanceGe P d_val)
    (hrun : Run P (.done s))
    (hG : ∀ (j : Fin P.numStab) (y : Fin P.R), s.G j y = false)
    (hSyn : ∀ (i : Fin P.numStab),
      ErrorVec.parity (P.stabilizers i) s.E_tilde = false)
    (hfaults : P.C_budget - s.C < d_val) :
    InStab P s.E_tilde := by
  by_contra h_not_stab
  have h_ule := hd s hrun ⟨hG, hSyn, h_not_stab⟩
  omega

/-- Corollary: the trivial decoder is ⌊(d-1)/2⌋-fault-tolerant when
    restricted to executions with G = 0 and zero syndrome. -/
theorem trivialDecoder_FT_on_G_zero (P : QECParams) (d_val : Nat) (s : State P)
    (hd : circuitDistanceGe P d_val)
    (hrun : Run P (.done s))
    (hG : ∀ (j : Fin P.numStab) (y : Fin P.R), s.G j y = false)
    (hSyn : ∀ (i : Fin P.numStab),
      ErrorVec.parity (P.stabilizers i) s.E_tilde = false)
    (hd_pos : 0 < d_val)
    (hfaults : P.C_budget - s.C ≤ (d_val - 1) / 2) :
    decoderSucceeds P (trivialDecoder P) s := by
  rw [trivialDecoder_succeeds_iff]
  apply undetected_faults_ge_d P d_val s hd hrun hG hSyn
  have : (d_val - 1) / 2 < d_val := Nat.div_lt_of_lt_mul (by omega)
  omega

/-! ### Lemma 3.8: Full combined-configuration argument

The full argument handles G ≠ 0: if the decoder picks a hypothesis F*
consistent with G with |F*| ≤ |F|, the combined configuration F + F*
has G ⊕ G = 0 and total faults |F| + |F*| ≤ 2t < d.

This requires reasoning about TWO executions of the same circuit.
In the QStab framework, we model this by assuming the "combined
execution" exists as a hypothesis. -/

/-- The combined-configuration argument as a theorem.
    Hypothesis: if the decoder's correction E_hat, combined with the
    actual error E_tilde, produces E_hat · E_tilde ∉ S, and the combined
    execution (which has G = 0 and error E_hat · E_tilde) exists as a
    valid run with at most |F| + |F*| faults, then d^circ ≤ |F| + |F*|.

    This gives: if d^circ ≥ d and |F| + |F*| < d, then E_hat · E_tilde ∈ S. -/
theorem combined_config_implies_stab
    (P : QECParams) (d_val : Nat)
    (hd : circuitDistanceGe P d_val)
    (E_residual : ErrorVec P.n)
    (s_combined : State P)
    (hrun_combined : Run P (.done s_combined))
    (hG_combined : ∀ (j : Fin P.numStab) (y : Fin P.R), s_combined.G j y = false)
    (hSyn_combined : ∀ (i : Fin P.numStab),
      ErrorVec.parity (P.stabilizers i) s_combined.E_tilde = false)
    (hE_combined : s_combined.E_tilde = E_residual)
    (hfaults_combined : P.C_budget - s_combined.C < d_val) :
    InStab P E_residual := by
  have h := undetected_faults_ge_d P d_val s_combined hd hrun_combined
    hG_combined hSyn_combined hfaults_combined
  rw [hE_combined] at h
  exact h

/-- The full decoder FT theorem (abstract form).
    The combined execution must produce G=0, zero syndrome, and the
    residual error E_hat · E_tilde. The zero-syndrome condition on the
    combined execution is what connects d^circ to decoder FT. -/
theorem decoder_FT_from_distance
    (P : QECParams) (d_val : Nat) (D : Decoder P)
    (hd : circuitDistanceGe P d_val)
    (hd_pos : 0 < d_val)
    (h_combined : ∀ (s : State P), Run P (.done s) →
      ¬ InStab P (ErrorVec.mul (D s) s.E_tilde) →
      ∃ (s_c : State P), Run P (.done s_c) ∧
        (∀ j y, s_c.G j y = false) ∧
        (∀ i, ErrorVec.parity (P.stabilizers i) s_c.E_tilde = false) ∧
        s_c.E_tilde = ErrorVec.mul (D s) s.E_tilde ∧
        P.C_budget - s_c.C ≤ 2 * (P.C_budget - s.C)) :
    isFaultTolerant P D ((d_val - 1) / 2) := by
  intro s hrun hfaults
  unfold decoderSucceeds
  by_contra h_fail
  obtain ⟨s_c, hrun_c, hG_c, hSyn_c, hE_c, hfaults_c⟩ := h_combined s hrun h_fail
  have : 2 * ((d_val - 1) / 2) < d_val := by omega
  have h_stab := undetected_faults_ge_d P d_val s_c hd hrun_c hG_c hSyn_c (by omega)
  rw [hE_c] at h_stab
  exact h_fail h_stab

end QStab.DecoderFT
