import LeanQEC.Pauli

/-! # Pauli operator utilities for the QStab semantic framework

Defines `ErrorVec` (n-qubit Pauli error vectors without global phase),
along with weight, parity, and pointwise update operations.
-/

/-- An n-qubit Pauli error vector (without global phase).
    Represents the error flow Ẽ in the paper. -/
abbrev ErrorVec (n : Nat) := Fin n → Pauli

namespace ErrorVec

/-- The identity (all-I) error vector. -/
def identity (n : Nat) : ErrorVec n := fun _ => Pauli.I

/-- Whether two single-qubit Paulis anticommute.
    Two non-identity, non-equal Paulis anticommute. -/
def Pauli.anticommutes : Pauli → Pauli → Bool
  | .I, _  => false
  | _,  .I => false
  | .X, .X => false
  | .Y, .Y => false
  | .Z, .Z => false
  | _,  _  => true

/-- The weight (number of non-identity positions) of an error vector. -/
def weight {n : Nat} (e : ErrorVec n) : Nat :=
  (Finset.univ.filter fun i => e i ≠ Pauli.I).card

/-- Pointwise multiplication of error vectors. -/
def mul {n : Nat} (e₁ e₂ : ErrorVec n) : ErrorVec n :=
  fun i => Pauli.mul (e₁ i) (e₂ i)

/-- Compute the parity of an error vector with respect to a stabilizer.
    Parity(T_s, Ẽ) = true iff an odd number of positions anticommute. -/
def parity {n : Nat} (stabilizer : ErrorVec n) (err : ErrorVec n) : Bool :=
  (Finset.univ.filter fun i =>
    Pauli.anticommutes (stabilizer i) (err i)).card % 2 == 1

/-- Update a single qubit position in an error vector by left-multiplying. -/
def update {n : Nat} (e : ErrorVec n) (i : Fin n) (p : Pauli) : ErrorVec n :=
  Function.update e i (Pauli.mul p (e i))

/-- Anticommuting with the identity is always false. -/
theorem Pauli.anticommutes_identity_right (p : Pauli) :
    Pauli.anticommutes p .I = false := by
  cases p <;> rfl

/-- Parity of any stabilizer with the identity error vector is false.
    Since every position is Pauli.I, no anticommutation occurs. -/
theorem parity_identity {n : Nat} (stabilizer : ErrorVec n) :
    parity stabilizer (identity n) = false := by
  unfold parity identity
  suffices h : (Finset.univ.filter fun i => Pauli.anticommutes (stabilizer i) Pauli.I).card = 0 by
    rw [h]; rfl
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro i _
  simp [Pauli.anticommutes_identity_right]

end ErrorVec
