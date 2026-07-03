import QStab.Paper.LogicalCosets

/-!
# Generic code distance from the logical-coset decomposition

The **combinatorial** code distance (minimum weight of a nontrivial logical operator —
`min` over `N(S) \ S`), stated and proved in the assertion-level vocabulary
(`ErrorVec.parity` / `QStab.InStab` / `ErrorVec.weight`), independent of any specific code.

Every code — surface, HGP, five-qubit, Steane, repetition — obtains its distance lower
bound by instantiating the *single* theorem `codeDistanceAtLeast_of_cosetBounds`: supply a
`LogicalOps` system (whose `maximal_isotropic` field drives `normalizer_decomposition`) plus a
minimum-weight bound on each of the three nontrivial cosets `X̄·S`, `Z̄·S`, `X̄Z̄·S`.  Nothing
in this file mentions a particular code; the whole point of the QStab abstraction is that this
distance argument is derived once and reused.
-/

namespace QStab.Paper.CodeDistance

open QStab QStab.Paper.LogicalCosets

/-- **Code distance ≥ d.**  Every nontrivial logical — a normalizer element (commutes with
every stabilizer generator) that is not itself a stabilizer — has weight at least `d`. -/
def CodeDistanceAtLeast (P : QECParams) (d : Nat) : Prop :=
  ∀ E : ErrorVec P.n,
    (∀ s : Fin P.numStab, ErrorVec.parity (P.stabilizers s) E = false) →
    ¬ QStab.InStab P E →
    d ≤ ErrorVec.weight E

/-- **The generic code-distance lower bound.**  From a `LogicalOps` system plus a
minimum-weight bound on each nontrivial coset, the code distance is `≥ d`.  The proof is a
four-way case split on `normalizer_decomposition`: the identity coset is excluded by
`¬ InStab`, and each logical coset is bounded by its hypothesis. -/
theorem codeDistanceAtLeast_of_cosetBounds {P : QECParams} (L : LogicalOps P) (d : Nat)
    (hX : ∀ E, QStab.InStab P (ErrorVec.mul L.Xbar E) → d ≤ ErrorVec.weight E)
    (hZ : ∀ E, QStab.InStab P (ErrorVec.mul L.Zbar E) → d ≤ ErrorVec.weight E)
    (hXZ : ∀ E, QStab.InStab P (ErrorVec.mul L.Xbar (ErrorVec.mul L.Zbar E)) →
      d ≤ ErrorVec.weight E) :
    CodeDistanceAtLeast P d := by
  intro E hcent hnot
  rcases normalizer_decomposition L E hcent with h | h | h | h
  · exact absurd h hnot
  · exact hX E h
  · exact hZ E h
  · exact hXZ E h

/-- **`F` commutes with the whole stabilizer group** once it commutes with every generator —
the assertion-level normalizer closure, by structural induction on `InStab` (no enumeration
over `ErrorVec`).  Instantiated with `F := Z̄` (resp. `X̄`), this certifies that a `Z̄`-
(resp. `X̄`-)anticommuting witness is *not* itself a stabilizer. -/
theorem parity_commutes_of_InStab {P : QECParams} (F : ErrorVec P.n)
    (hgen : ∀ i : Fin P.numStab, ErrorVec.parity F (P.stabilizers i) = false)
    {E : ErrorVec P.n} (h : QStab.InStab P E) :
    ErrorVec.parity F E = false := by
  induction h with
  | identity =>
      unfold ErrorVec.parity ErrorVec.identity
      have hz : (Finset.univ.filter
          fun i : Fin P.n => ErrorVec.Pauli.anticommutes (F i) Pauli.I).card = 0 := by
        apply Finset.card_eq_zero.mpr
        apply Finset.filter_eq_empty_iff.mpr
        intro i _
        cases F i <;> decide
      rw [hz]; rfl
  | gen i => exact hgen i
  | mul _ _ ih₁ ih₂ => rw [parity_mul_right, ih₁, ih₂]; rfl

/-- A weight-`d` logical **witness**: an operator commuting with every stabilizer, not a
stabilizer itself, of weight exactly `d`.  Its existence certifies distance `≤ d`. -/
structure LogicalWitness (P : QECParams) (d : Nat) where
  op : ErrorVec P.n
  centralizes : ∀ s : Fin P.numStab, ErrorVec.parity (P.stabilizers s) op = false
  not_stab : ¬ QStab.InStab P op
  weight_eq : ErrorVec.weight op = d

/-- **Code distance exactly d**: the lower bound holds and a weight-`d` logical exists (so no
logical is lighter, and one achieves the bound). -/
def CodeDistanceExactly (P : QECParams) (d : Nat) : Prop :=
  CodeDistanceAtLeast P d ∧ Nonempty (LogicalWitness P d)

/-- The witness is a genuine lower-bound-achieving logical: distance ≥ d, and this operator
sits in `N(S) \ S` at weight exactly `d`. -/
theorem codeDistanceExactly_intro {P : QECParams} {d : Nat}
    (hlb : CodeDistanceAtLeast P d) (w : LogicalWitness P d) :
    CodeDistanceExactly P d :=
  ⟨hlb, ⟨w⟩⟩

end QStab.Paper.CodeDistance
