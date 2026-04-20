import QStab.Examples.SurfaceCode
import Mathlib.Tactic.FinCases
import Mathlib.Data.Finset.SymmDiff

open scoped symmDiff

/-! # Phase 2: Grid geometry, projections, and stabilizer subgroup

Formalizes constructs from invariant.tex §3.3:

* `Pauli.hasXComponent`, `Pauli.hasZComponent`  —  characterize X/Y and Z/Y Paulis.
* `QStab.InStab P`                              —  the stabilizer subgroup of P.
* `QStab.ErrorVec.stabEquiv P E₁ E₂`            —  E₁ ≡ E₂ (mod stabilizers).
* `QStab.Examples.toIdx d i j`                  —  qubit Fin-index from (row, col).
* `QStab.Examples.projRowsX`, `projColsZ`       —  row/column projections (ProjRows_X,
                                                    ProjCols_Z in invariant.tex:1538).
-/

/-! ## Pauli component predicates -/

namespace Pauli

/-- True iff `p ∈ {X, Y}`. These are the Paulis that anticommute with `Z`. -/
def hasXComponent : Pauli → Bool
  | .X | .Y => true
  | .I | .Z => false

/-- True iff `p ∈ {Z, Y}`. These are the Paulis that anticommute with `X`. -/
def hasZComponent : Pauli → Bool
  | .Z | .Y => true
  | .I | .X => false

@[simp] theorem hasXComponent_I : hasXComponent .I = false := rfl
@[simp] theorem hasZComponent_I : hasZComponent .I = false := rfl

/-! ### Anticommutation lemmas (foundation for Phase 5 step 2) -/

/-- Anticommutation is symmetric. -/
theorem anticommutes_symm (p q : Pauli) :
    ErrorVec.Pauli.anticommutes p q = ErrorVec.Pauli.anticommutes q p := by
  cases p <;> cases q <;> rfl

/-- Z anticommutes with p iff p has an X-component. -/
@[simp] theorem anticommutes_Z_eq_hasXComponent (p : Pauli) :
    ErrorVec.Pauli.anticommutes .Z p = hasXComponent p := by
  cases p <;> rfl

/-- X anticommutes with p iff p has a Z-component. -/
@[simp] theorem anticommutes_X_eq_hasZComponent (p : Pauli) :
    ErrorVec.Pauli.anticommutes .X p = hasZComponent p := by
  cases p <;> rfl

/-- Bilinearity of Pauli anticommutation on the right:
    `anticomm(p, q·r) = anticomm(p, q) ⊕ anticomm(p, r)`.
    This is the pointwise version of the parity-bilinearity lemma, and is the
    algebraic core of the Phase 5 Step 2 anticommutation-transfer argument. -/
theorem anticommutes_mul_right (p q r : Pauli) :
    ErrorVec.Pauli.anticommutes p (Pauli.mul q r) =
    xor (ErrorVec.Pauli.anticommutes p q) (ErrorVec.Pauli.anticommutes p r) := by
  cases p <;> cases q <;> cases r <;> rfl

/-- Bilinearity of Pauli anticommutation on the left. -/
theorem anticommutes_mul_left (p q r : Pauli) :
    ErrorVec.Pauli.anticommutes (Pauli.mul p q) r =
    xor (ErrorVec.Pauli.anticommutes p r) (ErrorVec.Pauli.anticommutes q r) := by
  cases p <;> cases q <;> cases r <;> rfl

/-- Identity anticommutes with nothing on the left (direct from the definition). -/
@[simp] theorem anticommutes_I_left (p : Pauli) :
    ErrorVec.Pauli.anticommutes .I p = false := rfl

end Pauli

/-! ## Stabilizer subgroup (general, code-agnostic) -/

namespace QStab

/-- `InStab P E` holds iff `E` is a product of stabilizer generators of `P`
    under pointwise multiplication. Closed under identity, generators, and products. -/
inductive InStab (P : QECParams) : ErrorVec P.n → Prop
  | identity : InStab P (ErrorVec.identity P.n)
  | gen (i : Fin P.numStab) : InStab P (P.stabilizers i)
  | mul {E₁ E₂ : ErrorVec P.n} :
      InStab P E₁ → InStab P E₂ → InStab P (ErrorVec.mul E₁ E₂)

/-- Stabilizer equivalence: `E₁ ≡ E₂` iff `E₂ = S · E₁` for some S in the
    stabilizer subgroup. Used for the perpendicular spread quotient in §3.3. -/
def ErrorVec.stabEquiv (P : QECParams) (E₁ E₂ : ErrorVec P.n) : Prop :=
  ∃ S : ErrorVec P.n, InStab P S ∧ E₂ = ErrorVec.mul S E₁

end QStab

/-! ## d×d grid geometry -/

namespace QStab.Examples

/-- Qubit Fin-index from (row, col) on a d×d grid (0-based).
    Paper's 1-based `q_{d(i-1)+j}` corresponds to `toIdx d ⟨i-1, _⟩ ⟨j-1, _⟩`. -/
def toIdx (d : Nat) (i j : Fin d) : Fin (d * d) :=
  ⟨d * i.val + j.val, by
    have hi : i.val + 1 ≤ d := i.isLt
    have hj : j.val < d := j.isLt
    calc d * i.val + j.val
        < d * i.val + d := by omega
      _ = d * (i.val + 1) := (Nat.mul_succ d i.val).symm
      _ ≤ d * d := Nat.mul_le_mul_left d hi⟩

/-! ## Row and column projections (invariant.tex:1538) -/

/-- `projRowsX E` — number of rows in which `E` has an X- or Y-component. -/
def projRowsX {d : Nat} (E : ErrorVec (d * d)) : Nat :=
  (Finset.univ.filter fun i : Fin d =>
    ∃ j : Fin d, Pauli.hasXComponent (E (toIdx d i j)) = true).card

/-- `projColsZ E` — number of columns in which `E` has a Z- or Y-component. -/
def projColsZ {d : Nat} (E : ErrorVec (d * d)) : Nat :=
  (Finset.univ.filter fun j : Fin d =>
    ∃ i : Fin d, Pauli.hasZComponent (E (toIdx d i j)) = true).card

/-! ## Basic lemmas -/

/-- Identity has no X-component in any row. -/
theorem projRowsX_identity (d : Nat) :
    projRowsX (d := d) (ErrorVec.identity (d * d)) = 0 := by
  unfold projRowsX
  apply Finset.card_eq_zero.mpr
  rw [Finset.filter_eq_empty_iff]
  intro i _
  push_neg
  intro j
  simp [ErrorVec.identity]

/-- Identity has no Z-component in any column. -/
theorem projColsZ_identity (d : Nat) :
    projColsZ (d := d) (ErrorVec.identity (d * d)) = 0 := by
  unfold projColsZ
  apply Finset.card_eq_zero.mpr
  rw [Finset.filter_eq_empty_iff]
  intro j _
  push_neg
  intro i
  simp [ErrorVec.identity]

/-- `projRowsX` is bounded by `d`. -/
theorem projRowsX_le (d : Nat) (E : ErrorVec (d * d)) :
    projRowsX E ≤ d := by
  unfold projRowsX
  calc (Finset.univ.filter _).card
      ≤ (Finset.univ : Finset (Fin d)).card := Finset.card_filter_le _ _
    _ = d := by simp

/-- `projColsZ` is bounded by `d`. -/
theorem projColsZ_le (d : Nat) (E : ErrorVec (d * d)) :
    projColsZ E ≤ d := by
  unfold projColsZ
  calc (Finset.univ.filter _).card
      ≤ (Finset.univ : Finset (Fin d)).card := Finset.card_filter_le _ _
    _ = d := by simp

/-! ## Sanity checks (pass if all `#eval!` lines match the expected value) -/

-- Expected: 3  (X̄ = X₁X₄X₇ on left column has X in rows 0, 1, 2)
#eval! projRowsX (d := 3) SurfaceD3.logicalX

-- Expected: 0  (Z̄ = Z₁Z₂Z₃ has no X-component)
#eval! projRowsX (d := 3) SurfaceD3.logicalZ

-- Expected: 3  (Z̄ has Z in columns 0, 1, 2)
#eval! projColsZ (d := 3) SurfaceD3.logicalZ

-- Expected: 0  (X̄ has no Z-component)
#eval! projColsZ (d := 3) SurfaceD3.logicalX

-- Expected: 0  (identity has no non-trivial Pauli)
#eval! projRowsX (d := 3) (ErrorVec.identity 9)

-- Expected: 4  (X̄ on left column of 4×4)
#eval! projRowsX (d := 4) SurfaceD4.logicalX

-- Expected: 4  (Z̄ on top row of 4×4, Z in cols 0,1,2,3)
#eval! projColsZ (d := 4) SurfaceD4.logicalZ

end QStab.Examples

/-! ## ErrorVec multiplication identities (general) -/

/-- Left-identity: `mul (identity n) E = E`. -/
theorem ErrorVec.mul_identity_left {n : Nat} (E : ErrorVec n) :
    ErrorVec.mul (ErrorVec.identity n) E = E := by
  funext i; rfl

/-- Right-identity: `mul E (identity n) = E`. -/
theorem ErrorVec.mul_identity_right {n : Nat} (E : ErrorVec n) :
    ErrorVec.mul E (ErrorVec.identity n) = E := by
  funext i
  show Pauli.mul (E i) .I = E i
  cases (E i) <;> rfl

/-- Pauli multiplication is commutative (up to phase, which we ignore). -/
theorem ErrorVec.mul_comm {n : Nat} (a b : ErrorVec n) :
    ErrorVec.mul a b = ErrorVec.mul b a := by
  funext i; show Pauli.mul (a i) (b i) = Pauli.mul (b i) (a i)
  cases (a i) <;> cases (b i) <;> rfl

/-- Pauli multiplication is associative. -/
theorem ErrorVec.mul_assoc {n : Nat} (a b c : ErrorVec n) :
    ErrorVec.mul (ErrorVec.mul a b) c = ErrorVec.mul a (ErrorVec.mul b c) := by
  funext i; show Pauli.mul (Pauli.mul (a i) (b i)) (c i) =
                 Pauli.mul (a i) (Pauli.mul (b i) (c i))
  cases (a i) <;> cases (b i) <;> cases (c i) <;> rfl

/-- Every Pauli vector is its own inverse: `mul E E = identity`. -/
theorem ErrorVec.mul_self_cancel {n : Nat} (E : ErrorVec n) :
    ErrorVec.mul E E = ErrorVec.identity n := by
  funext i; show Pauli.mul (E i) (E i) = Pauli.I
  cases (E i) <;> rfl

/-- Helper: `|U ∆ V| + 2 |U ∩ V| = |U| + |V|`. Derived locally since Mathlib's
    `Finset.card_symmDiff` isn't directly available here. -/
private theorem Finset.card_symmDiff_add_inter {α : Type*} [DecidableEq α]
    (s t : Finset α) :
    (s ∆ t).card + 2 * (s ∩ t).card = s.card + t.card := by
  have hunion : s ∪ t = (s ∆ t) ∪ (s ∩ t) := by
    ext i
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_symmDiff]
    tauto
  have hdisj : Disjoint (s ∆ t) (s ∩ t) := by
    rw [Finset.disjoint_left]
    intro i hsd hint
    simp only [Finset.mem_inter, Finset.mem_symmDiff] at hsd hint
    rcases hsd with ⟨_, h⟩ | ⟨_, h⟩
    · exact h hint.2
    · exact h hint.1
  have h1 : (s ∪ t).card = (s ∆ t).card + (s ∩ t).card := by
    rw [hunion]; exact Finset.card_union_of_disjoint hdisj
  have h2 : (s ∪ t).card + (s ∩ t).card = s.card + t.card :=
    Finset.card_union_add_card_inter s t
  omega

/-- Identity has no anticommutations with anything, so parity with identity
    on the left is `false`. Counterpart to `parity_identity` (identity on right). -/
theorem ErrorVec.parity_identity_left {n : Nat} (E : ErrorVec n) :
    ErrorVec.parity (ErrorVec.identity n) E = false := by
  unfold ErrorVec.parity ErrorVec.identity
  suffices h : (Finset.univ.filter fun i : Fin n =>
      ErrorVec.Pauli.anticommutes Pauli.I (E i) = true).card = 0 by
    rw [h]; rfl
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro i _
  simp [Pauli.anticommutes_I_left]

/-- Parity is F₂-bilinear in the right argument:
    `parity S (A · B) = parity S A ⊕ parity S B`.

    This is the key algebraic identity used in Phase 5 Step 2 (anticommutation
    transfer). Proof: the filtered index set for `A · B` equals the symmetric
    difference of the filtered sets for `A` and `B` (via pointwise bilinearity),
    and `|U ∆ V| ≡ |U| + |V| (mod 2)`. -/
theorem ErrorVec.parity_mul_right {n : Nat} (S A B : ErrorVec n) :
    ErrorVec.parity S (ErrorVec.mul A B) =
    xor (ErrorVec.parity S A) (ErrorVec.parity S B) := by
  have hgen : ∀ (U V : Finset (Fin n)),
      ((U ∆ V).card % 2 == 1) = xor (U.card % 2 == 1) (V.card % 2 == 1) := by
    intro U V
    have hc := Finset.card_symmDiff_add_inter U V
    have hmod : (U ∆ V).card % 2 = (U.card + V.card) % 2 := by omega
    rw [hmod]
    rcases Nat.mod_two_eq_zero_or_one U.card with hu | hu <;>
      rcases Nat.mod_two_eq_zero_or_one V.card with hv | hv <;>
      simp [Nat.add_mod, hu, hv]
  have hW : (Finset.univ.filter fun i : Fin n =>
              ErrorVec.Pauli.anticommutes (S i) ((ErrorVec.mul A B) i) = true)
          = (Finset.univ.filter fun i : Fin n =>
              ErrorVec.Pauli.anticommutes (S i) (A i) = true) ∆
            (Finset.univ.filter fun i : Fin n =>
              ErrorVec.Pauli.anticommutes (S i) (B i) = true) := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_symmDiff]
    show (ErrorVec.Pauli.anticommutes (S i) (Pauli.mul (A i) (B i)) = true) ↔ _
    rw [Pauli.anticommutes_mul_right]
    cases h1 : ErrorVec.Pauli.anticommutes (S i) (A i) <;>
      cases h2 : ErrorVec.Pauli.anticommutes (S i) (B i) <;>
      simp
  unfold ErrorVec.parity
  rw [hW]
  exact hgen _ _

/-- Parity is F₂-bilinear in the left argument (via `anticommutes_mul_left`). -/
theorem ErrorVec.parity_mul_left {n : Nat} (A B X : ErrorVec n) :
    ErrorVec.parity (ErrorVec.mul A B) X =
    xor (ErrorVec.parity A X) (ErrorVec.parity B X) := by
  have hgen : ∀ (U V : Finset (Fin n)),
      ((U ∆ V).card % 2 == 1) = xor (U.card % 2 == 1) (V.card % 2 == 1) := by
    intro U V
    have hc := Finset.card_symmDiff_add_inter U V
    have hmod : (U ∆ V).card % 2 = (U.card + V.card) % 2 := by omega
    rw [hmod]
    rcases Nat.mod_two_eq_zero_or_one U.card with hu | hu <;>
      rcases Nat.mod_two_eq_zero_or_one V.card with hv | hv <;>
      simp [Nat.add_mod, hu, hv]
  have hW : (Finset.univ.filter fun i : Fin n =>
              ErrorVec.Pauli.anticommutes ((ErrorVec.mul A B) i) (X i) = true)
          = (Finset.univ.filter fun i : Fin n =>
              ErrorVec.Pauli.anticommutes (A i) (X i) = true) ∆
            (Finset.univ.filter fun i : Fin n =>
              ErrorVec.Pauli.anticommutes (B i) (X i) = true) := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_symmDiff]
    show (ErrorVec.Pauli.anticommutes (Pauli.mul (A i) (B i)) (X i) = true) ↔ _
    rw [Pauli.anticommutes_mul_left]
    cases h1 : ErrorVec.Pauli.anticommutes (A i) (X i) <;>
      cases h2 : ErrorVec.Pauli.anticommutes (B i) (X i) <;>
      simp
  unfold ErrorVec.parity
  rw [hW]
  exact hgen _ _

/-- **Phase 5 Step 2 (anticommutation transfer, half 1).**

    If `E` lies in the normalizer of the stabilizer group (every generator
    commutes with `E`, i.e. zero syndrome), then every element of the stabilizer
    subgroup commutes with `E`.

    Proof: induction on the `InStab` tree using parity F₂-bilinearity
    (`parity_mul_left`) for the multiplication case and `parity_identity_left`
    for the identity case. -/
theorem QStab.InStab.parity_of_normalizer {P : QECParams} {E : ErrorVec P.n}
    (hSyn : ∀ i : Fin P.numStab, ErrorVec.parity (P.stabilizers i) E = false)
    {S : ErrorVec P.n} (hS : QStab.InStab P S) :
    ErrorVec.parity S E = false := by
  induction hS with
  | identity => exact ErrorVec.parity_identity_left E
  | gen i => exact hSyn i
  | mul _ _ ih1 ih2 =>
    rw [ErrorVec.parity_mul_left, ih1, ih2]
    rfl

/-! ## Row-cut stabilizer equivalences for d=3 (Phase 5 step 1)

The topological lower bound (invariant.tex §3.4, Lemma TopoLowerBound) requires
every row-cut operator Ẑ_i to be stabilizer-equivalent to Z̄. For d=3:

  Ẑ_1 = Z̄                            (trivial)
  Ẑ_2 = (ŝ₁ · ŝ₆) · Ẑ_1              (bulk Z + right boundary)
  Ẑ_3 = (ŝ₄ · ŝ₇) · Ẑ_2              (bulk Z + left boundary)

By transitivity all Ẑ_i ≡ Z̄ (mod S). -/

namespace QStab.Examples.SurfaceD3

/-- Ẑ_1 = Z̄ (definitionally equal after reducing `ofList`). -/
theorem rowCut_one_eq_logicalZ : rowCut 1 = logicalZ := by
  funext i; fin_cases i <;> rfl

/-- Telescoping identity: Ẑ_2 = (ŝ₁ · ŝ₆) · Ẑ_1. -/
theorem rowCut_two_eq : rowCut 2 = ErrorVec.mul (ErrorVec.mul s1 s6) (rowCut 1) := by
  funext i; fin_cases i <;> rfl

/-- Telescoping identity: Ẑ_3 = (ŝ₄ · ŝ₇) · Ẑ_2. -/
theorem rowCut_three_eq : rowCut 3 = ErrorVec.mul (ErrorVec.mul s4 s7) (rowCut 2) := by
  funext i; fin_cases i <;> rfl

/-- Ẑ_1 ≡ Z̄ (mod S), witnessed by the identity stabilizer. -/
theorem rowCut_one_stabEquiv_logicalZ :
    QStab.ErrorVec.stabEquiv code logicalZ (rowCut 1) := by
  refine ⟨ErrorVec.identity 9, QStab.InStab.identity, ?_⟩
  funext i; fin_cases i <;> rfl

/-- Ẑ_2 ≡ Z̄ (mod S), witnessed by ŝ₁ · ŝ₆. -/
theorem rowCut_two_stabEquiv_logicalZ :
    QStab.ErrorVec.stabEquiv code logicalZ (rowCut 2) := by
  refine ⟨ErrorVec.mul s1 s6,
          QStab.InStab.mul
            (QStab.InStab.gen (⟨0, by decide⟩ : Fin code.numStab))
            (QStab.InStab.gen (⟨5, by decide⟩ : Fin code.numStab)), ?_⟩
  rw [← rowCut_one_eq_logicalZ]
  exact rowCut_two_eq

/-- Ẑ_3 ≡ Z̄ (mod S), witnessed by (ŝ₄ · ŝ₇) · (ŝ₁ · ŝ₆). -/
theorem rowCut_three_stabEquiv_logicalZ :
    QStab.ErrorVec.stabEquiv code logicalZ (rowCut 3) := by
  refine ⟨ErrorVec.mul (ErrorVec.mul s4 s7) (ErrorVec.mul s1 s6),
          QStab.InStab.mul
            (QStab.InStab.mul
              (QStab.InStab.gen (⟨3, by decide⟩ : Fin code.numStab))
              (QStab.InStab.gen (⟨6, by decide⟩ : Fin code.numStab)))
            (QStab.InStab.mul
              (QStab.InStab.gen (⟨0, by decide⟩ : Fin code.numStab))
              (QStab.InStab.gen (⟨5, by decide⟩ : Fin code.numStab))), ?_⟩
  rw [← rowCut_one_eq_logicalZ, rowCut_three_eq, rowCut_two_eq]
  funext i; fin_cases i <;> rfl

end QStab.Examples.SurfaceD3

/-! ## Row-cut stabilizer equivalences for d=4

For d=4 (using the paper-correct identities, not [invariant.tex:1437]'s bug):
  Ẑ_1 = Z̄
  Ẑ_2 = (ŝ₁·ŝ₂) · Ẑ_1                    (bulk Z only)
  Ẑ_3 = (ŝ₃·ŝ₁₀·ŝ₁₁) · Ẑ_2              (bulk Z + 2 side boundary Z)
  Ẑ_4 = (ŝ₄·ŝ₅) · Ẑ_3                    (bulk Z only)
-/

namespace QStab.Examples.SurfaceD4

theorem rowCut_one_eq_logicalZ : rowCut 1 = logicalZ := by
  funext i; fin_cases i <;> rfl

theorem rowCut_two_eq :
    rowCut 2 = ErrorVec.mul (ErrorVec.mul s1 s2) (rowCut 1) := by
  funext i; fin_cases i <;> rfl

theorem rowCut_three_eq :
    rowCut 3 = ErrorVec.mul (ErrorVec.mul s3 (ErrorVec.mul s10 s11)) (rowCut 2) := by
  funext i; fin_cases i <;> rfl

theorem rowCut_four_eq :
    rowCut 4 = ErrorVec.mul (ErrorVec.mul s4 s5) (rowCut 3) := by
  funext i; fin_cases i <;> rfl

/-- Ẑ_1 ≡ Z̄ (mod S), witness = identity. -/
theorem rowCut_one_stabEquiv_logicalZ :
    QStab.ErrorVec.stabEquiv code logicalZ (rowCut 1) := by
  refine ⟨ErrorVec.identity 16, QStab.InStab.identity, ?_⟩
  funext i; fin_cases i <;> rfl

/-- Ẑ_2 ≡ Z̄ (mod S), witness = ŝ₁·ŝ₂. -/
theorem rowCut_two_stabEquiv_logicalZ :
    QStab.ErrorVec.stabEquiv code logicalZ (rowCut 2) := by
  refine ⟨ErrorVec.mul s1 s2,
          QStab.InStab.mul
            (QStab.InStab.gen (⟨0, by decide⟩ : Fin code.numStab))
            (QStab.InStab.gen (⟨1, by decide⟩ : Fin code.numStab)), ?_⟩
  rw [← rowCut_one_eq_logicalZ]
  exact rowCut_two_eq

/-- Ẑ_3 ≡ Z̄ (mod S), witness = (ŝ₃·ŝ₁₀·ŝ₁₁)·(ŝ₁·ŝ₂). -/
theorem rowCut_three_stabEquiv_logicalZ :
    QStab.ErrorVec.stabEquiv code logicalZ (rowCut 3) := by
  refine ⟨ErrorVec.mul (ErrorVec.mul s3 (ErrorVec.mul s10 s11))
                       (ErrorVec.mul s1 s2),
          QStab.InStab.mul
            (QStab.InStab.mul
              (QStab.InStab.gen (⟨2, by decide⟩ : Fin code.numStab))
              (QStab.InStab.mul
                (QStab.InStab.gen (⟨9, by decide⟩ : Fin code.numStab))
                (QStab.InStab.gen (⟨10, by decide⟩ : Fin code.numStab))))
            (QStab.InStab.mul
              (QStab.InStab.gen (⟨0, by decide⟩ : Fin code.numStab))
              (QStab.InStab.gen (⟨1, by decide⟩ : Fin code.numStab))), ?_⟩
  rw [← rowCut_one_eq_logicalZ, rowCut_three_eq, rowCut_two_eq]
  funext i; fin_cases i <;> rfl

/-- Ẑ_4 ≡ Z̄ (mod S), witness = (ŝ₄·ŝ₅)·(ŝ₃·ŝ₁₀·ŝ₁₁)·(ŝ₁·ŝ₂). -/
theorem rowCut_four_stabEquiv_logicalZ :
    QStab.ErrorVec.stabEquiv code logicalZ (rowCut 4) := by
  refine ⟨ErrorVec.mul (ErrorVec.mul s4 s5)
            (ErrorVec.mul (ErrorVec.mul s3 (ErrorVec.mul s10 s11))
              (ErrorVec.mul s1 s2)),
          QStab.InStab.mul
            (QStab.InStab.mul
              (QStab.InStab.gen (⟨3, by decide⟩ : Fin code.numStab))
              (QStab.InStab.gen (⟨4, by decide⟩ : Fin code.numStab)))
            (QStab.InStab.mul
              (QStab.InStab.mul
                (QStab.InStab.gen (⟨2, by decide⟩ : Fin code.numStab))
                (QStab.InStab.mul
                  (QStab.InStab.gen (⟨9, by decide⟩ : Fin code.numStab))
                  (QStab.InStab.gen (⟨10, by decide⟩ : Fin code.numStab))))
              (QStab.InStab.mul
                (QStab.InStab.gen (⟨0, by decide⟩ : Fin code.numStab))
                (QStab.InStab.gen (⟨1, by decide⟩ : Fin code.numStab)))), ?_⟩
  rw [← rowCut_one_eq_logicalZ, rowCut_four_eq, rowCut_three_eq, rowCut_two_eq]
  funext i; fin_cases i <;> rfl

end QStab.Examples.SurfaceD4
