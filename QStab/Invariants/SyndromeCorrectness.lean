import QStab.Invariants.ConstantErrorFlow
import QStab.Invariants.RegisterInit

/-! # Syndrome correctness invariant (Theorem 3 & 4)

When C = 0, the inferred syndrome matches the actual error parity
for all stabilizers measured before the current position:
  p(σ) = (C = 0) ∧ ∀ s < x, I[T_s] = Parity(T_s, Ẽ)

Also the parameterized version (Theorem 4):
  p(σ) = (C < t) ∨ { (C = t) ∧ ∀ s < x, I[T_s] = Parity(T_s, E⃗) }
-/

namespace QStab.Invariants

/-- Syndrome correctness invariant (Theorem 3):
    When C = 0, all stabilizers measured so far in the current round
    have I[T_s] matching the actual parity. -/
def syndromeCorrectnessInvariant (P : QECParams) : Invariant P where
  holds := fun s =>
    s.C = 0 →
    ∀ (j : Fin P.numStab), j < s.coord.x →
      s.I_syn j = ErrorVec.parity (P.stabilizers j) s.E_tilde
  holds_init := sorry
  preservation := sorry

/-- Second syndrome correctness invariant (Theorem 4):
    Parameterized by budget level t and constant error vector. -/
def syndromeCorrectnessParam (P : QECParams) (t : Nat) (E_const : ErrorVec P.n)
    : Invariant P where
  holds := fun s =>
    s.C < t ∨
    (s.C = t ∧ ∀ (j : Fin P.numStab), j < s.coord.x →
      s.I_syn j = ErrorVec.parity (P.stabilizers j) E_const)
  holds_init := sorry
  preservation := sorry

end QStab.Invariants
