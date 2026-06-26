import QStab.QClifford.FaultHoare

/-! # Concrete F-Hoare derivation examples

This file demonstrates that the canonical QClifford F-Hoare logic
(`FaultHoare.lean`) is **constructively usable**: derivations are
built by direct application of the `F_*` rules, witnessing fault-
tolerance facts syntactically.

The examples below are deliberately tiny (1 qubit, 1-2 instructions)
so the derivation tree is inspectable in a few dozen lines. For real
fault-tolerance proofs (e.g., surface d=3), see the `BarrierDist`
meta-rule in `FTHoare.lean`, which composes these atomic rules into
a one-step certificate via `barrier_tolerates`.

This file exists to address the audit concern that `FDeriv` was
defined but never instantiated: with the `F_ErrLoc` example below,
the calculus has at least one non-trivial concrete witness.
-/

namespace QStab.QClifford.Examples

open QStab.QClifford

/-! ## Example 1: single error location, λ ≤ 1 after one fault

The simplest non-trivial F-Hoare derivation: a 1-qubit circuit
consisting of a single `err(0)` site. Starting from the clean state
(λ = 0), one fault can occur (Step-Inject) or not (Step-Idle).
Either way, λ ≤ 1 in the final state.

This exercises:
- `F_ErrLoc`: the demonic rule for an error location, which must
  discharge both the idle case (λ stays 0) and the inject case
  (λ becomes 1).
- `F_Conseq`: to weaken the precondition from the WP to the actual
  starting condition (`σ = QCState.clean 1`).
-/

/-- Postcondition: after the circuit, λ ≤ 1. -/
def Q_one_err : AssertionF 1 := fun σ => σ.lambda ≤ 1

/-- Precondition: start from the clean state. -/
def P_clean : AssertionF 1 := fun σ => σ = QCState.clean 1

/-- The circuit: a single error location on qubit 0. -/
def circ_one_err : FCircuit 1 := [.errLoc 0]

/-- Weakest precondition for `Q_one_err` after one error location.
    By `F_ErrLoc`: the precondition is `Q σ ∧ ∀ p ≠ I, Q ⟨inject, λ+1⟩`,
    which here unfolds to `σ.lambda ≤ 1 ∧ ∀ p ≠ I, σ.lambda + 1 ≤ 1`. -/
def wp_one_err : AssertionF 1 := fun σ =>
  Q_one_err σ ∧ ∀ p, p ≠ Pauli.I → Q_one_err ⟨σ.es.inject 0 p, σ.lambda + 1⟩

/-- `P_clean` implies `wp_one_err`: from `σ = clean 1` we get `σ.lambda = 0`,
    so `0 ≤ 1` (idle conjunct) and `0 + 1 ≤ 1` (inject conjunct) both hold. -/
theorem clean_implies_wp (σ : QCState 1) (h : P_clean σ) : wp_one_err σ := by
  subst h
  refine ⟨?_, ?_⟩
  · show (QCState.clean 1).lambda ≤ 1
    simp [QCState.clean]
  · intro p _hp
    show (1 : Nat) ≤ 1
    rfl

/-- WP-form derivation: apply `F_ErrLoc` directly. The precondition
    `wp_one_err` is by construction the WP of `Q_one_err` w.r.t. `err(0)`. -/
def deriv_wp : FDeriv wp_one_err circ_one_err Q_one_err :=
  FDeriv.F_ErrLoc 0 Q_one_err

/-- Full derivation with weakened precondition: apply `F_Conseq` to
    weaken from `wp_one_err` to `P_clean` (forward implication is
    `clean_implies_wp`; the postcondition implication is identity). -/
def deriv_full : FDeriv P_clean circ_one_err Q_one_err :=
  FDeriv.F_Conseq deriv_wp clean_implies_wp (fun _ h => h)

/-- **Soundness** via `fhoare_sound`: the syntactic derivation
    `deriv_full` witnesses the semantic Hoare triple.
    Every `qceval` execution from `P_clean` ends in `Q_one_err`. -/
theorem example_sound : FHoare P_clean circ_one_err Q_one_err :=
  fhoare_sound deriv_full

/-- Direct corollary: running `circ_one_err` from the clean state
    indeed leaves the final λ at most 1. -/
theorem example_direct (σ' : QCState 1)
    (h_run : qceval circ_one_err (QCState.clean 1) σ') :
    σ'.lambda ≤ 1 := by
  exact example_sound (QCState.clean 1) σ' h_run rfl

/-! ## Example 2: gate + error location

Combining `F_Gate` and `F_ErrLoc` via `F_App`: a hadamard followed by
an error location. Same λ-bound (`λ ≤ 1`) because gates preserve λ. -/

/-- Circuit: H(0); err(0). -/
def circ_h_err : FCircuit 1 := [.gate (Gate.hadamard 0), .errLoc 0]

/-- Weakest precondition for the tail `[err(0)]`. -/
def wp_tail : AssertionF 1 := wp_one_err

/-- Weakest precondition for the prefix `[gate H(0)]` w.r.t. `wp_tail`.
    By `F_Gate`: `wp_gate(Q)(σ) = Q ⟨propagateGate g σ.es, σ.lambda⟩`. -/
def wp_gate : AssertionF 1 := fun σ =>
  wp_tail ⟨propagateGate (Gate.hadamard 0) σ.es, σ.lambda⟩

/-- Derivation of `[gate H(0)]`: direct `F_Gate` application. -/
def deriv_gate : FDeriv wp_gate [.gate (Gate.hadamard 0)] wp_tail :=
  FDeriv.F_Gate (Gate.hadamard 0) wp_tail

/-- Derivation of `[err(0)]`: same as `deriv_wp`. -/
def deriv_err : FDeriv wp_tail [.errLoc 0] Q_one_err := deriv_wp

/-- Compose via `F_App` to derive the full circuit `H; err`. -/
def deriv_h_err : FDeriv wp_gate circ_h_err Q_one_err :=
  FDeriv.F_App deriv_gate deriv_err

/-- `P_clean` implies `wp_gate`: from clean, propagating through H
    gives a state whose λ stays 0; the demonic conjunct then needs
    0 ≤ 1 and 0+1 ≤ 1, both trivial. -/
theorem clean_implies_wp_gate (σ : QCState 1) (h : P_clean σ) : wp_gate σ := by
  subst h
  refine ⟨?_, ?_⟩
  · show (QCState.clean 1).lambda ≤ 1
    simp [QCState.clean]
  · intro p _hp
    show (1 : Nat) ≤ 1
    rfl

/-- Full derivation for `H; err`: weaken `wp_gate` to `P_clean`. -/
def deriv_h_err_full : FDeriv P_clean circ_h_err Q_one_err :=
  FDeriv.F_Conseq deriv_h_err clean_implies_wp_gate (fun _ h => h)

/-- Soundness of the two-instruction example. -/
theorem example2_sound : FHoare P_clean circ_h_err Q_one_err :=
  fhoare_sound deriv_h_err_full

end QStab.QClifford.Examples
