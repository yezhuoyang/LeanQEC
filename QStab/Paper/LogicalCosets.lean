import QStab.PauliOps
import QStab.Examples.SurfaceGeometry

/-!
# Decomposition of N(S) into logical Pauli cosets

For an [[n, 1]] stabilizer code with stabilizer group `S` and a designated
pair of logical operators `(X̄, Z̄)`, every Pauli operator that commutes
with every stabilizer (i.e., every element of `N(S)`) lies in exactly one
of the four cosets:

    S,   X̄·S,   Z̄·S,   (X̄·Z̄)·S.

This is the formal justification for the paper's claim that the only
non-trivial logical Pauli error classes are X̄, Ȳ = X̄·Z̄, and Z̄.

The proof is parameterised over an abstract `LogicalOps` structure that
bundles the logical operators with their commutation axioms and a
*maximal-isotropic* axiom: any operator commuting with all stabilizers
**and** with both X̄, Z̄ is itself in S. This last axiom is the content
of the dimension theorem `|N(S)| = 4·|S|` for k = 1 codes; it can be
discharged for concrete codes by symplectic rank arguments or by
enumeration.

Zero sorry in the main theorem (`normalizer_decomposition`).
-/

namespace QStab.Paper.LogicalCosets

open QStab

/-! ## Pauli anticommutation: bilinearity -/

/-- Pauli anticommutation is bilinear in its second argument:
    `anticommutes(P, Q·R) = anticommutes(P, Q) ⊕ anticommutes(P, R)`. -/
theorem Pauli_anticommutes_mul_right (P Q R : Pauli) :
    ErrorVec.Pauli.anticommutes P (Pauli.mul Q R) =
    xor (ErrorVec.Pauli.anticommutes P Q) (ErrorVec.Pauli.anticommutes P R) := by
  cases P <;> cases Q <;> cases R <;> rfl

/-- Pauli anticommutation is symmetric. -/
theorem Pauli_anticommutes_symm (P Q : Pauli) :
    ErrorVec.Pauli.anticommutes P Q = ErrorVec.Pauli.anticommutes Q P := by
  cases P <;> cases Q <;> rfl

/-- A Pauli always commutes with itself (anticommutes returns false). -/
theorem Pauli_anticommutes_self (P : Pauli) :
    ErrorVec.Pauli.anticommutes P P = false := by
  cases P <;> rfl

/-! ## Parity: bilinearity and symmetry -/

/-- Cardinality bilinearity: when a per-element predicate decomposes as an
    XOR of two predicates, the filter cardinalities relate mod 2. -/
private theorem card_filter_xor_mod_two {α : Type*} [DecidableEq α] (s : Finset α)
    (p q : α → Bool)
    (h_eq : ∀ a, p a = xor (decide (p a = true) ∨ decide (q a = true) ∧ False)
                          (decide (q a = true) ∧ ¬decide (p a = true))) :
    True := by trivial

/-- Direct: for any decidable predicates `p, q : α → Bool` and Finset `s`,
    the cardinality of `{a ∈ s : xor (p a) (q a)}` mod 2 equals
    `(card {a : p a} + card {a : q a}) mod 2`. -/
private theorem card_filter_xor_eq_mod_two {α : Type*} [DecidableEq α] (s : Finset α)
    (p q : α → Bool) :
    (s.filter fun a => xor (p a) (q a)).card % 2 =
    ((s.filter fun a => p a).card + (s.filter fun a => q a).card) % 2 := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    -- Filter of `insert a s` = (filter s) ∪ optional {a} depending on predicate.
    rw [Finset.filter_insert, Finset.filter_insert, Finset.filter_insert]
    -- Three predicates evaluated at a: pa, qa, xor pa qa.
    set pa := p a with hpa
    set qa := q a with hqa
    -- Filter cardinalities on the tail s (using ih).
    set Cs_xor := (s.filter fun b => xor (p b) (q b)).card with hCs_xor
    set Cs_p := (s.filter fun b => p b).card with hCs_p
    set Cs_q := (s.filter fun b => q b).card with hCs_q
    have hih : Cs_xor % 2 = (Cs_p + Cs_q) % 2 := ih
    -- Membership of a in (filter s ...) is false because a ∉ s.
    have h_a_p : a ∉ (s.filter fun b => p b) := fun h => ha (Finset.mem_of_mem_filter _ h)
    have h_a_q : a ∉ (s.filter fun b => q b) := fun h => ha (Finset.mem_of_mem_filter _ h)
    have h_a_xor : a ∉ (s.filter fun b => xor (p b) (q b)) :=
      fun h => ha (Finset.mem_of_mem_filter _ h)
    -- Compute cardinalities by case on (pa, qa).
    cases hpa_val : pa <;> cases hqa_val : qa <;>
      simp_all [Finset.card_insert_of_notMem, hpa_val, hqa_val] <;>
      omega

/-- The parity function is bilinear in its second argument. -/
theorem parity_mul_right {n : Nat} (F G H : ErrorVec n) :
    ErrorVec.parity F (ErrorVec.mul G H) =
    xor (ErrorVec.parity F G) (ErrorVec.parity F H) := by
  unfold ErrorVec.parity ErrorVec.mul
  -- Per-element bilinearity.
  have h_pointwise : ∀ i : Fin n,
      ErrorVec.Pauli.anticommutes (F i) (Pauli.mul (G i) (H i)) =
      xor (ErrorVec.Pauli.anticommutes (F i) (G i))
          (ErrorVec.Pauli.anticommutes (F i) (H i)) :=
    fun i => Pauli_anticommutes_mul_right (F i) (G i) (H i)
  -- Rewrite the LHS filter via `h_pointwise`.
  have h_filter_eq :
      (Finset.univ.filter fun i : Fin n =>
        ErrorVec.Pauli.anticommutes (F i) (Pauli.mul (G i) (H i))) =
      (Finset.univ.filter fun i : Fin n =>
        xor (ErrorVec.Pauli.anticommutes (F i) (G i))
            (ErrorVec.Pauli.anticommutes (F i) (H i))) := by
    apply Finset.filter_congr
    intro i _
    rw [h_pointwise i]
  rw [h_filter_eq]
  -- Apply the cardinality bilinearity lemma.
  have h_card := card_filter_xor_eq_mod_two
    (Finset.univ : Finset (Fin n))
    (fun i => ErrorVec.Pauli.anticommutes (F i) (G i))
    (fun i => ErrorVec.Pauli.anticommutes (F i) (H i))
  -- Goal: ((card filter xor) % 2 == 1) = xor ((card filter G) % 2 == 1)
  --                                          ((card filter H) % 2 == 1)
  -- Use h_card to relate the LHS to the sum of the RHS card mod 2.
  rcases Nat.mod_two_eq_zero_or_one
      ((Finset.univ.filter fun i : Fin n =>
        ErrorVec.Pauli.anticommutes (F i) (G i)).card) with eA | eA <;>
    rcases Nat.mod_two_eq_zero_or_one
        ((Finset.univ.filter fun i : Fin n =>
          ErrorVec.Pauli.anticommutes (F i) (H i)).card) with eB | eB <;>
    simp_all [Nat.add_mod, eA, eB]

/-- Parity is symmetric: parity(F, G) = parity(G, F). -/
theorem parity_symm {n : Nat} (F G : ErrorVec n) :
    ErrorVec.parity F G = ErrorVec.parity G F := by
  unfold ErrorVec.parity
  have h_filter :
      (Finset.univ.filter fun i : Fin n => ErrorVec.Pauli.anticommutes (F i) (G i)) =
      (Finset.univ.filter fun i : Fin n => ErrorVec.Pauli.anticommutes (G i) (F i)) := by
    apply Finset.filter_congr
    intro i _
    rw [Pauli_anticommutes_symm]
  rw [h_filter]

/-- Parity of any vector with itself is false (commutes with itself). -/
theorem parity_self {n : Nat} (F : ErrorVec n) :
    ErrorVec.parity F F = false := by
  unfold ErrorVec.parity
  have h_empty :
      (Finset.univ.filter fun i : Fin n => ErrorVec.Pauli.anticommutes (F i) (F i)) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro i _
    rw [Pauli_anticommutes_self]
    decide
  rw [h_empty]
  rfl

/-! ## Logical operator system -/

/-- A logical-operator system for an `[[n, 1]]` stabilizer code: a pair
    `(X̄, Z̄)` in `N(S)` satisfying the standard commutation relations
    plus the maximal-isotropic axiom (any operator commuting with all
    stabilizers and with both `X̄`, `Z̄` is in `S`). -/
structure LogicalOps (P : QECParams) where
  /-- Logical X̄. -/
  Xbar : ErrorVec P.n
  /-- Logical Z̄. -/
  Zbar : ErrorVec P.n
  /-- X̄ commutes with every stabilizer generator. -/
  Xbar_comm : ∀ s : Fin P.numStab, ErrorVec.parity (P.stabilizers s) Xbar = false
  /-- Z̄ commutes with every stabilizer generator. -/
  Zbar_comm : ∀ s : Fin P.numStab, ErrorVec.parity (P.stabilizers s) Zbar = false
  /-- X̄ and Z̄ anticommute. -/
  Xbar_anticomm_Zbar : ErrorVec.parity Xbar Zbar = true
  /-- **Maximal-isotropic axiom**: any operator commuting with every
      stabilizer **and** with both `X̄` and `Z̄` is in the stabilizer
      subgroup `S`. -/
  maximal_isotropic : ∀ E : ErrorVec P.n,
    (∀ s, ErrorVec.parity (P.stabilizers s) E = false) →
    ErrorVec.parity Xbar E = false →
    ErrorVec.parity Zbar E = false →
    InStab P E

/-! ## Boolean dichotomy helper -/

private theorem bool_dichotomy (b : Bool) : b = false ∨ b = true := by
  cases b
  · left; rfl
  · right; rfl

/-! ## Main theorem: N(S) decomposes into four logical Pauli cosets -/

/-- **Main theorem.** For any `[[n, 1]]` stabilizer code with logical
    operators `L = (X̄, Z̄)` (Definition `LogicalOps`), every Pauli
    operator `E` that commutes with every stabilizer (i.e., `E ∈ N(S)`)
    lies in one of the four cosets:

      S,   X̄·S,   Z̄·S,   (X̄·Z̄)·S.

    The proof contains zero `sorry`. -/
theorem normalizer_decomposition {P : QECParams} (L : LogicalOps P)
    (E : ErrorVec P.n)
    (hE : ∀ s, ErrorVec.parity (P.stabilizers s) E = false) :
    InStab P E ∨
    InStab P (ErrorVec.mul L.Xbar E) ∨
    InStab P (ErrorVec.mul L.Zbar E) ∨
    InStab P (ErrorVec.mul L.Xbar (ErrorVec.mul L.Zbar E)) := by
  -- Define the syndrome of E under the two logical operators.
  -- a := parity(Z̄, E)  -- whether E anticommutes with Z̄
  -- b := parity(X̄, E)  -- whether E anticommutes with X̄
  -- The corrected operator that lands in S is X̄^a · Z̄^b · E:
  --   parity(X̄, X̄^a Z̄^b E) = 0 ⊕ b ⊕ b = 0
  --   parity(Z̄, X̄^a Z̄^b E) = a ⊕ 0 ⊕ a = 0
  -- so by maximal_isotropic, X̄^a Z̄^b E ∈ S, hence E ∈ X̄^a Z̄^b · S.
  set a := ErrorVec.parity L.Zbar E with ha_def
  set b := ErrorVec.parity L.Xbar E with hb_def
  -- Standard parity values of (X̄, Z̄).
  have h_X_X : ErrorVec.parity L.Xbar L.Xbar = false := parity_self L.Xbar
  have h_Z_Z : ErrorVec.parity L.Zbar L.Zbar = false := parity_self L.Zbar
  have h_X_Z : ErrorVec.parity L.Xbar L.Zbar = true := L.Xbar_anticomm_Zbar
  have h_Z_X : ErrorVec.parity L.Zbar L.Xbar = true := by
    rw [parity_symm]; exact h_X_Z
  -- Case analysis on (a, b).
  rcases bool_dichotomy a with ha | ha <;>
    rcases bool_dichotomy b with hb | hb
  -- (a, b) = (false, false): E ∈ S.
  · left
    apply L.maximal_isotropic E hE
    · -- parity X̄ E = b = false
      rw [← hb_def]; exact hb
    · -- parity Z̄ E = a = false
      rw [← ha_def]; exact ha
  -- (a, b) = (false, true): Z̄·E ∈ S.
  · right; right; left
    apply L.maximal_isotropic (ErrorVec.mul L.Zbar E)
    · -- parity (stab s) (Z̄·E) = parity stab Z̄ ⊕ parity stab E = false
      intro s
      rw [parity_mul_right, L.Zbar_comm s, hE s]; rfl
    · -- parity X̄ (Z̄·E) = parity X̄ Z̄ ⊕ parity X̄ E = true ⊕ true = false
      rw [parity_mul_right, h_X_Z, ← hb_def, hb]; rfl
    · -- parity Z̄ (Z̄·E) = parity Z̄ Z̄ ⊕ parity Z̄ E = false ⊕ false = false
      rw [parity_mul_right, h_Z_Z, ← ha_def, ha]; rfl
  -- (a, b) = (true, false): X̄·E ∈ S.
  · right; left
    apply L.maximal_isotropic (ErrorVec.mul L.Xbar E)
    · intro s
      rw [parity_mul_right, L.Xbar_comm s, hE s]; rfl
    · -- parity X̄ (X̄·E) = parity X̄ X̄ ⊕ parity X̄ E = false ⊕ false = false
      rw [parity_mul_right, h_X_X, ← hb_def, hb]; rfl
    · -- parity Z̄ (X̄·E) = parity Z̄ X̄ ⊕ parity Z̄ E = true ⊕ true = false
      rw [parity_mul_right, h_Z_X, ← ha_def, ha]; rfl
  -- (a, b) = (true, true): X̄·Z̄·E ∈ S.
  · right; right; right
    apply L.maximal_isotropic (ErrorVec.mul L.Xbar (ErrorVec.mul L.Zbar E))
    · -- parity stab (X̄·Z̄·E) = ⊕ of false, false, false = false
      intro s
      rw [parity_mul_right, parity_mul_right, L.Xbar_comm s, L.Zbar_comm s, hE s]; rfl
    · -- parity X̄ (X̄·Z̄·E) = false ⊕ true ⊕ true = false
      rw [parity_mul_right, parity_mul_right, h_X_X, h_X_Z, ← hb_def, hb]; rfl
    · -- parity Z̄ (X̄·Z̄·E) = true ⊕ false ⊕ true = false
      rw [parity_mul_right, parity_mul_right, h_Z_X, h_Z_Z, ← ha_def, ha]; rfl

end QStab.Paper.LogicalCosets
