import QStab.Invariant
import QStab.MultiStep
import QStab.Examples.SurfaceGeometry

/-! # Decoder-based fault tolerance

The PRIMARY definition of circuit-level fault tolerance is decoder-based:
a circuit is t-fault-tolerant if there exists a decoder that correctly
recovers the logical state from any ≤t-fault execution.

This is R-dependent: with more syndrome rounds, the decoder has more
information to distinguish data errors from measurement errors.

Key result: if two executions produce the same measurement record G
but different logical classes, no decoder can succeed on both
(Lemma `decoder_fails_on_confusable`).
-/

namespace QStab.DecoderFT

open QECParams

/-! ### Decoder and fault-tolerance definitions -/

/-- A circuit-level decoder maps the done state (which contains the
    measurement record G) to a Pauli correction on data qubits. -/
def Decoder (P : QECParams) := State P → ErrorVec P.n

/-- The decoder succeeds if the correction times the actual error flow
    is in the stabilizer group (the logical state is preserved). -/
def decoderSucceeds (P : QECParams) (D : Decoder P) (s : State P) : Prop :=
  InStab P (ErrorVec.mul (D s) s.E_tilde)

/-- The decoder fails if the residual is not in S. -/
def decoderFails (P : QECParams) (D : Decoder P) (s : State P) : Prop :=
  ¬ InStab P (ErrorVec.mul (D s) s.E_tilde)

/-- **Primary definition: decoder-based t-fault-tolerance.**
    A circuit is t-fault-tolerant under decoder D if D succeeds on every
    execution reaching σ_done with at most t faults.
    This is the ground truth for circuit-level fault tolerance. -/
def isFaultTolerant (P : QECParams) (D : Decoder P) (t : Nat) : Prop :=
  ∀ (s : State P), Run P (.done s) → P.C_budget - s.C ≤ t →
    decoderSucceeds P D s

/-! ### Confusable executions -/

/-- Two executions are **confusable** if they produce the same measurement
    record G but their combined error is not in S. A decoder seeing G
    cannot distinguish them and must fail on at least one. -/
def confusable (P : QECParams) (s1 s2 : State P) : Prop :=
  (∀ j y, s1.G j y = s2.G j y) ∧
  ¬ InStab P (ErrorVec.mul s1.E_tilde s2.E_tilde)

/-- **No decoder succeeds on both confusable executions.**
    If s1 and s2 are confusable (same G, combined error ∉ S), and the
    decoder depends only on G, then the decoder fails on at least one.
    Proof: (D·E1)·(D·E2) = E1·E2 by Pauli self-inverse. -/
theorem decoder_fails_on_confusable (P : QECParams) (D : Decoder P)
    (s1 s2 : State P)
    (hconf : confusable P s1 s2)
    (hD_det : ∀ (a b : State P), (∀ j y, a.G j y = b.G j y) → D a = D b) :
    decoderFails P D s1 ∨ decoderFails P D s2 := by
  obtain ⟨hG_eq, h_not_stab⟩ := hconf
  have hD_eq : D s1 = D s2 := hD_det s1 s2 hG_eq
  by_contra h_both_ok
  push_neg at h_both_ok
  unfold decoderFails at h_both_ok
  push_neg at h_both_ok
  obtain ⟨h1, h2⟩ := h_both_ok
  have h12 := InStab.mul h1 (hD_eq ▸ h2)
  have key : ErrorVec.mul (ErrorVec.mul (D s1) s1.E_tilde)
               (ErrorVec.mul (D s1) s2.E_tilde)
             = ErrorVec.mul s1.E_tilde s2.E_tilde := by
    funext i
    show Pauli.mul (Pauli.mul (D s1 i) (s1.E_tilde i))
                   (Pauli.mul (D s1 i) (s2.E_tilde i))
         = Pauli.mul (s1.E_tilde i) (s2.E_tilde i)
    cases (D s1 i) <;> cases (s1.E_tilde i) <;> cases (s2.E_tilde i) <;> rfl
  rw [key] at h12
  exact h_not_stab h12

/-- **Confusable pair implies not fault-tolerant.**
    If two executions with ≤ t faults each are confusable, then no
    G-deterministic decoder is t-fault-tolerant. -/
theorem confusable_implies_not_FT (P : QECParams) (D : Decoder P) (t : Nat)
    (s1 s2 : State P)
    (hrun1 : Run P (.done s1))
    (hrun2 : Run P (.done s2))
    (hf1 : P.C_budget - s1.C ≤ t)
    (hf2 : P.C_budget - s2.C ≤ t)
    (hconf : confusable P s1 s2)
    (hD_det : ∀ (a b : State P), (∀ j y, a.G j y = b.G j y) → D a = D b) :
    ¬ isFaultTolerant P D t := by
  intro hFT
  have h := decoder_fails_on_confusable P D s1 s2 hconf hD_det
  cases h with
  | inl hf => exact hf (hFT s1 hrun1 hf1)
  | inr hf => exact hf (hFT s2 hrun2 hf2)

/-! ### Trivial decoder -/

/-- The trivial decoder applies no correction. -/
def trivialDecoder (P : QECParams) : Decoder P :=
  fun _ => ErrorVec.identity P.n

/-- The trivial decoder succeeds iff E_tilde ∈ S. -/
theorem trivialDecoder_succeeds_iff (P : QECParams) (s : State P) :
    decoderSucceeds P (trivialDecoder P) s ↔ InStab P s.E_tilde := by
  unfold decoderSucceeds trivialDecoder
  constructor
  · intro h; rwa [ErrorVec.mul_identity_left] at h
  · intro h; rwa [ErrorVec.mul_identity_left]

/-! ### Connection to invariant-based proofs

The perpendicular spread invariant + topological lower bound gives a
SUFFICIENT condition for decoder FT. The connection goes through the
following theorem: if at every reachable state with G=0 and Syn(E)=0,
the error must be in S (because ω_perp < d forces this), then the
trivial decoder succeeds on all G=0 executions.

The R-dependence enters through the clean-round argument: with enough
rounds, G=0 IMPLIES Syn(E)=0 at some intermediate state (the clean
round), which propagates to the final state. Without enough rounds,
G=0 does NOT imply Syn(E)=0, so the bound doesn't apply. -/

/-- If at a reachable state, G=0 and Syn(E)=0 together with < d faults
    implies E ∈ S, then the trivial decoder succeeds on that state
    (assuming G=0 and Syn=0). -/
theorem trivialDecoder_succeeds_from_spread
    (P : QECParams) (d_val : Nat) (s : State P)
    (hrun : Run P (.done s))
    (hG : ∀ j y, s.G j y = false)
    (hSyn : ∀ i, ErrorVec.parity (P.stabilizers i) s.E_tilde = false)
    (hfaults : P.C_budget - s.C < d_val)
    -- The invariant-based bound: G=0 + Syn=0 + < d faults → E ∈ S
    (hinv : ∀ (s' : State P), Run P (.done s') →
      (∀ j y, s'.G j y = false) →
      (∀ i, ErrorVec.parity (P.stabilizers i) s'.E_tilde = false) →
      P.C_budget - s'.C < d_val →
      InStab P s'.E_tilde) :
    decoderSucceeds P (trivialDecoder P) s := by
  rw [trivialDecoder_succeeds_iff]
  exact hinv s hrun hG hSyn hfaults

end QStab.DecoderFT
