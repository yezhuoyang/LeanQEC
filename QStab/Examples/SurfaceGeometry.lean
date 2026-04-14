import QStab.Examples.SurfaceCode

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
