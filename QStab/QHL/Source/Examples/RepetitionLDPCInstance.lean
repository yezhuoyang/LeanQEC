import QStab.QHL.Source.ProofKernel

/-! # Classical 3-bit repetition code as a concrete LDPC instance

This module exhibits a small, fully concrete `QECParams` (the classical 3-bit
repetition code) together with a witnessed
`ProofKernel.ProgramObligationRule _ _ .ldpcSparse`.

The point of this file is to show that the LDPC-sparse program obligation kind
is non-vacuous: a real code satisfies it, and the kernel's
`ldpcSparse_bound` consistency lemma evaluates on the concrete witness.

We pick the repetition code rather than the surface code because the resulting
weight bound proof is `decide`-able row-by-row.  Every generator is the
two-position `X X` parity check, so the per-row weight is exactly `2`.
-/

namespace QHL.Source.Examples.RepetitionLDPCInstance

open QHL.Source

/-! ## The 3-bit classical repetition code -/

/-- Stabilizers `X X I` and `I X X`.  The classical repetition code only has
    `X`-type parity checks; we treat them as Pauli stabilizers so they fit the
    standard `QECParams` interface. -/
def repetitionStabilizers : Fin 2 → ErrorVec 3
  | ⟨0, _⟩ => fun q => if q.val = 0 ∨ q.val = 1 then Pauli.X else Pauli.I
  | ⟨1, _⟩ => fun q => if q.val = 1 ∨ q.val = 2 then Pauli.X else Pauli.I

/-- Concrete `QECParams` for the 3-bit repetition code.  We supply the
    smallest legal values for the structural fields; only `n`, `numStab`,
    `stabilizers` are load-bearing for the LDPC obligation below. -/
def repetitionParams : QECParams where
  n := 3
  k := 1
  d := 3
  R := 1
  numStab := 2
  stabilizers := repetitionStabilizers
  backActionSet := fun _ => ∅
  r := 0
  backAction_weight_bound := fun _ _ h => h.elim
  C_budget := 1
  hn := by decide
  hns := by decide
  hR := by decide

/-! ## Sparse-weight witness -/

/-- Every repetition-code generator has Hamming weight exactly `2`. -/
theorem repetition_stabilizer_weight_le_two
    (i : Fin repetitionParams.numStab) :
    ErrorVec.weight (repetitionParams.stabilizers i) ≤ 2 := by
  fin_cases i <;> decide

/-- The LDPC sparsity witness with bound `w = 2`. -/
def repetitionLdpcWitness :
    ProofKernel.LdpcSparseWitness repetitionParams where
  bound := 2
  proof := repetition_stabilizer_weight_le_two

/-- The `ldpcSparse` program-obligation rule for the repetition code. -/
def repetitionLdpcObligation (d : Nat) :
    ProofKernel.ProgramObligationRule repetitionParams d .ldpcSparse :=
  .ldpcSparse repetitionLdpcWitness

/-! ## Sanity checks: the obligation reduces -/

/-- The bound carried by the obligation reduces to the witness bound. -/
theorem repetitionLdpcObligation_bound (d : Nat) :
    ProofKernel.ProgramObligationRule.ldpcSparseBound
        (repetitionLdpcObligation d) = 2 := rfl

/-- The kernel's generic consistency lemma applied to the repetition-code
    obligation: every named generator has weight at most `2`. -/
theorem repetitionLdpc_consistent (d : Nat)
    (i : Fin repetitionParams.numStab) :
    ErrorVec.weight (repetitionParams.stabilizers i) ≤
      ProofKernel.ProgramObligationRule.ldpcSparseBound
        (repetitionLdpcObligation d) :=
  ProofKernel.ProgramObligationRule.ldpcSparse_bound
    (repetitionLdpcObligation d) i

/-- Concrete pointwise checks: the weight of each repetition-code stabilizer
    is literally `2`. -/
example : ErrorVec.weight (repetitionStabilizers ⟨0, by decide⟩) = 2 := by decide
example : ErrorVec.weight (repetitionStabilizers ⟨1, by decide⟩) = 2 := by decide

end QHL.Source.Examples.RepetitionLDPCInstance
