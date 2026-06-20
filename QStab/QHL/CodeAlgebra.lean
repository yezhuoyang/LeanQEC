import QStab.QHL.CodeRules

/-! # Algebraic derived rules for code-level assertions

No assertion-language primitive is added here.  The small builders below expand
to existing `CodeLang` syntax, and the theorems prove semantic preservation
facts that later Hoare rules can call as assertion-logic side conditions.
-/

namespace QHL.CodeLang

namespace PartialStabilizer

/-- Semantic helper for "same old stabilizer, except slot `q` is `p`".
    This is not assertion syntax. -/
def setAt (slot : Nat) (p : Pauli) (A : PartialStabilizer) : PartialStabilizer :=
  fun q => if q = slot then some p else A q

end PartialStabilizer

namespace Formula

/-- Derived AST builder for setting one stabilizer entry.

This is not a new primitive: it expands to `stabLam`, `ite`, `eqNat`,
`stabAt`, and weakening. -/
def withEntry {arity : Nat} (A : Term arity .stab)
    (slot : Term arity .nat) (p : Term arity .pauli) : Term arity .stab :=
  .stabLam <|
    .ite (.eqNat qVar slot.weaken)
      p.weaken
      (.stabAt A.weaken qVar)

end Formula

/-! ## Pauli and parity algebra -/

private theorem pauli_anticommutes_symm (p q : Pauli) :
    ErrorVec.Pauli.anticommutes p q = ErrorVec.Pauli.anticommutes q p := by
  cases p <;> cases q <;> rfl

private theorem pauli_anticommutes_self (p : Pauli) :
    ErrorVec.Pauli.anticommutes p p = false := by
  cases p <;> rfl

private theorem xor_false_right (b : Bool) : xor b false = b := by
  cases b <;> rfl

theorem parityUpTo_symm {n : Nat} {A B : PartialStabilizer} :
    parityUpTo n A B = parityUpTo n B A := by
  induction n with
  | zero =>
      rfl
  | succ m ih =>
      unfold parityUpTo
      rw [ih]
      cases hB : B m <;> cases hA : A m <;>
        simp [pauli_anticommutes_symm]

theorem commutesUpTo_symm_eval {codeBody : Term 2 .stab} {fuel n : Nat}
    {A B : Term 0 .stab} :
    Formula.eval codeBody fuel
        (.commutesUpTo (.natLit n) A B) Env.empty = some true ->
      Formula.eval codeBody fuel
        (.commutesUpTo (.natLit n) B A) Env.empty = some true := by
  intro h
  simp [Formula.eval, Term.eval] at h ⊢
  cases hA : Term.eval codeBody fuel A Env.empty with
  | none =>
      simp [hA] at h
  | some SA =>
      cases hB : Term.eval codeBody fuel B Env.empty with
      | none =>
          simp [hA, hB] at h
      | some SB =>
          simp [hA, hB] at h ⊢
          rw [parityUpTo_symm]
          exact h

theorem parityUpTo_setAt_prefix {m slot : Nat} {p : Pauli}
    {A B : PartialStabilizer} :
    m <= slot ->
      parityUpTo m
          (PartialStabilizer.setAt slot p A)
          (PartialStabilizer.setAt slot p B) =
        parityUpTo m A B := by
  intro hle
  induction m with
  | zero =>
      rfl
  | succ m ih =>
      unfold parityUpTo
      have hm_ne : m ≠ slot := by omega
      rw [ih (by omega)]
      simp [PartialStabilizer.setAt, hm_ne]

theorem parityUpTo_setAt_same_succ {n : Nat} {p : Pauli}
    {A B : PartialStabilizer} :
    parityUpTo n A B = some false ->
      parityUpTo (n + 1)
          (PartialStabilizer.setAt n p A)
          (PartialStabilizer.setAt n p B) = some false := by
  intro h
  unfold parityUpTo
  rw [parityUpTo_setAt_prefix (m := n) (slot := n) (p := p) (A := A) (B := B) (by omega)]
  simp [h, PartialStabilizer.setAt, pauli_anticommutes_self]

/-- Semantic bridge rule for the common pattern:
    if assertion logic proves `A` and `B` commute over the old prefix, and
    program semantics updates both denotations by setting the same fresh slot
    to the same Pauli, then the updated denotations commute over the extended
    prefix. -/
theorem commutesUpTo_semanticSetAt_same_succ {codeBody : Term 2 .stab}
    {fuel n : Nat} {p : Pauli} {A B : Term 0 .stab} {SA SB : PartialStabilizer}
    (hA : Term.eval codeBody fuel A Env.empty = some SA)
    (hB : Term.eval codeBody fuel B Env.empty = some SB) :
    Formula.eval codeBody fuel
        (.commutesUpTo (.natLit n) A B) Env.empty = some true ->
      parityUpTo (n + 1)
          (PartialStabilizer.setAt n p SA)
          (PartialStabilizer.setAt n p SB) = some false := by
  intro h
  simp [Formula.eval, Term.eval] at h
  simp [hA, hB] at h
  have hpar : parityUpTo n SA SB = some false := by
    cases hp : parityUpTo n SA SB with
    | none =>
        simp [hp] at h
    | some parity =>
        cases parity
        · rfl
        · simp [hp] at h
  exact parityUpTo_setAt_same_succ hpar

#print axioms parityUpTo_symm
#print axioms commutesUpTo_symm_eval
#print axioms commutesUpTo_semanticSetAt_same_succ

end QHL.CodeLang
