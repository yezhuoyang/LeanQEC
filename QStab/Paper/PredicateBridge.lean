import QStab.Paper.Predicates
import QStab.Paper.AlignedBarrier
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image

/-!
# Bridge lemmas from abstract semantic predicates to Finset.card machinery

This file connects the propositional predicates of `QStab.Paper.Predicates`
to the existing `Finset.card`-of-filter machinery in
`QStab.Paper.AlignedBarrier` and `QStab.Examples.SurfaceGeometry`
(`groupsX`, `projRowsX`, `projColsZ`). Each bridge lemma converts between
the high-level Prop form (used in paper §3 / §6.5) and the Finset image
form (used inside the perpendicular-spread invariant proofs).

Bridges proved here:

* `RowRestrictedX_iff_filter_image_subset` — `RowRestrictedX E i` is
  equivalent to "the image of the X-support under `(·.val / d)` is a
  subset of `{i.val}`".
* `ColRestrictedZ_iff_filter_image_subset` — column/Z mirror.
* `HookAlignedX_implies_filter_image_card_le_one` — an aligned hook has
  X-support image of size at most one (the "card ≤ 1" form used in
  `hook_spread_bound`).
* `HookAlignedZ_implies_filter_image_card_le_one` — column/Z mirror.
* `TouchesEveryRowX_iff_projRowsX_eq_d` — touching every row is the
  same as `projRowsX E = d`.
* `TouchesEveryColZ_iff_projColsZ_eq_d` — column/Z mirror.
* `SameSyndrome_iff_normalizer` — same-syndrome iff the product
  `E · F` is in the normalizer (every stabilizer-parity is `false`).
* `FaultBudget_iff_le_sub` — alternate budget form
  `s.C ≤ P.C_budget - t` (under `t ≤ P.C_budget`).

Strict discipline: no `sorry`, no `native_decide`, no `Classical.choose`,
no `Exists.choose`, no `by_contra`. Kernel reasoning only.
-/

namespace QStab.Paper.PredicateBridge

open QStab QStab.Examples QStab.Paper.Predicates QStab.Paper.AlignedBarrier

/-! ## Helper: every qubit `q : Fin (d*d)` has `q.val / d < d` -/

/-- For a qubit `q : Fin (d*d)`, the row index `q.val / d` is < d. -/
theorem qubit_row_lt (d : Nat) (q : Fin (d * d)) : q.val / d < d :=
  Nat.div_lt_of_lt_mul q.isLt

/-- For a qubit `q : Fin (d*d)` with `0 < d`, the row index packaged as `Fin d`. -/
def qubitRow (d : Nat) (q : Fin (d * d)) : Fin d :=
  ⟨q.val / d, qubit_row_lt d q⟩

/-- For a qubit `q : Fin (d*d)` with `0 < d`, the column index packaged as `Fin d`. -/
def qubitCol (d : Nat) (q : Fin (d * d)) (hd : 0 < d) : Fin d :=
  ⟨q.val % d, Nat.mod_lt _ hd⟩

/-- `toIdx d (qubitRow d q) (qubitCol d q hd) = q`. The grid coordinates
    reconstruct the original qubit index. -/
theorem toIdx_qubitRow_qubitCol (d : Nat) (q : Fin (d * d)) (hd : 0 < d) :
    toIdx d (qubitRow d q) (qubitCol d q hd) = q := by
  apply Fin.ext
  show d * (q.val / d) + q.val % d = q.val
  exact Nat.div_add_mod q.val d

/-! ## Row/column restriction bridges -/

/-- `RowRestrictedX E i` is equivalent to "every qubit with non-zero
    X-component has row index `i.val`". -/
theorem RowRestrictedX_iff_pointwise {d : Nat} (E : ErrorVec (d * d))
    (i : Fin d) (hd : 0 < d) :
    RowRestrictedX E i ↔
      ∀ q : Fin (d * d),
        Pauli.hasXComponent (E q) = true → q.val / d = i.val := by
  constructor
  · intro hrow q hx
    -- Suppose q.val / d ≠ i.val. Set i' := qubitRow q, j := qubitCol q.
    -- Then i' ≠ i and toIdx d i' j = q, so by hrow we get hasX (E q) = false,
    -- contradicting hx.
    have hq_eq : toIdx d (qubitRow d q) (qubitCol d q hd) = q :=
      toIdx_qubitRow_qubitCol d q hd
    -- We want to derive `q.val / d = i.val` from `hx`. The forward direction
    -- proceeds by case analysis on whether `qubitRow d q = i`.
    by_cases h_eq : qubitRow d q = i
    · exact Fin.val_eq_of_eq h_eq
    · -- Contradiction: hrow says hasX is false at toIdx d (qubitRow d q) ...
      have h_false : Pauli.hasXComponent (E (toIdx d (qubitRow d q) (qubitCol d q hd))) = false :=
        hrow (qubitRow d q) (qubitCol d q hd) h_eq
      rw [hq_eq] at h_false
      -- Now hx : has = true and h_false : has = false → ⊥, then ex falso
      exact absurd (h_false.symm.trans hx) (by decide)
  · intro hpt i' j hi'
    -- Suppose hasX (E (toIdx d i' j)) = true. Then by hpt, (toIdx d i' j).val / d = i.val.
    -- But (toIdx d i' j).val / d = i'.val (since toIdx d i' j = ⟨d*i'+j, _⟩
    -- and d * i' + j divided by d (with j < d) is i').
    -- So i'.val = i.val, contradicting i' ≠ i.
    cases hcase : Pauli.hasXComponent (E (toIdx d i' j)) with
    | false => rfl
    | true =>
      exfalso
      have hpt' : (toIdx d i' j).val / d = i.val := hpt (toIdx d i' j) hcase
      have htoIdx_val : (toIdx d i' j).val = d * i'.val + j.val := rfl
      have hjlt : j.val < d := j.isLt
      have hdiv : (d * i'.val + j.val) / d = i'.val := by
        rw [Nat.mul_add_div hd, Nat.div_eq_of_lt hjlt, Nat.add_zero]
      rw [htoIdx_val, hdiv] at hpt'
      exact hi' (Fin.ext hpt')

/-- Bridge from `RowRestrictedX E i` to a Finset image subset:
    the image of qubits with X-component under `(·.val / d)` is contained
    in `{i.val}`. -/
theorem RowRestrictedX_iff_filter_image_subset {d : Nat} (E : ErrorVec (d * d))
    (i : Fin d) (hd : 0 < d) :
    RowRestrictedX E i ↔
      (Finset.univ.filter fun q : Fin (d * d) =>
        Pauli.hasXComponent (E q) = true).image (fun q => q.val / d) ⊆
        ({i.val} : Finset Nat) := by
  rw [RowRestrictedX_iff_pointwise E i hd]
  constructor
  · intro hpt r hr
    rcases Finset.mem_image.mp hr with ⟨q, hq, hrq⟩
    rw [Finset.mem_filter] at hq
    have : q.val / d = i.val := hpt q hq.2
    rw [← hrq, this]
    exact Finset.mem_singleton.mpr rfl
  · intro hsub q hx
    have hmem : q.val / d ∈
        ((Finset.univ.filter fun q : Fin (d * d) =>
          Pauli.hasXComponent (E q) = true).image (fun q => q.val / d)) := by
      apply Finset.mem_image.mpr
      exact ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩
    have : q.val / d ∈ ({i.val} : Finset Nat) := hsub hmem
    exact Finset.mem_singleton.mp this

/-- `ColRestrictedZ E j` is equivalent to "every qubit with non-zero
    Z-component has column index `j.val`". -/
theorem ColRestrictedZ_iff_pointwise {d : Nat} (E : ErrorVec (d * d))
    (j : Fin d) (hd : 0 < d) :
    ColRestrictedZ E j ↔
      ∀ q : Fin (d * d),
        Pauli.hasZComponent (E q) = true → q.val % d = j.val := by
  constructor
  · intro hcol q hz
    by_cases h_eq : qubitCol d q hd = j
    · exact Fin.val_eq_of_eq h_eq
    · have hq_eq : toIdx d (qubitRow d q) (qubitCol d q hd) = q :=
        toIdx_qubitRow_qubitCol d q hd
      have h_false : Pauli.hasZComponent (E (toIdx d (qubitRow d q) (qubitCol d q hd))) = false :=
        hcol (qubitRow d q) (qubitCol d q hd) h_eq
      rw [hq_eq] at h_false
      exact absurd (h_false.symm.trans hz) (by decide)
  · intro hpt i j' hj'
    cases hcase : Pauli.hasZComponent (E (toIdx d i j')) with
    | false => rfl
    | true =>
      exfalso
      have hpt' : (toIdx d i j').val % d = j.val := hpt (toIdx d i j') hcase
      have htoIdx_val : (toIdx d i j').val = d * i.val + j'.val := rfl
      have hjlt : j'.val < d := j'.isLt
      have hmod : (d * i.val + j'.val) % d = j'.val := by
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hjlt]
      rw [htoIdx_val, hmod] at hpt'
      exact hj' (Fin.ext hpt')

/-- Bridge from `ColRestrictedZ E j` to a Finset image subset. -/
theorem ColRestrictedZ_iff_filter_image_subset {d : Nat} (E : ErrorVec (d * d))
    (j : Fin d) (hd : 0 < d) :
    ColRestrictedZ E j ↔
      (Finset.univ.filter fun q : Fin (d * d) =>
        Pauli.hasZComponent (E q) = true).image (fun q => q.val % d) ⊆
        ({j.val} : Finset Nat) := by
  rw [ColRestrictedZ_iff_pointwise E j hd]
  constructor
  · intro hpt c hc
    rcases Finset.mem_image.mp hc with ⟨q, hq, hcq⟩
    rw [Finset.mem_filter] at hq
    have : q.val % d = j.val := hpt q hq.2
    rw [← hcq, this]
    exact Finset.mem_singleton.mpr rfl
  · intro hsub q hz
    have hmem : q.val % d ∈
        ((Finset.univ.filter fun q : Fin (d * d) =>
          Pauli.hasZComponent (E q) = true).image (fun q => q.val % d)) := by
      apply Finset.mem_image.mpr
      exact ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩, rfl⟩
    have : q.val % d ∈ ({j.val} : Finset Nat) := hsub hmem
    exact Finset.mem_singleton.mp this

/-! ## Hook-alignment bridges -/

/-- `HookAlignedX e_B` implies the image of its X-support under
    `(·.val / d)` has at most one element. This is the
    "`groupsX`-style bound" of the `hook_spread_bound` field. -/
theorem HookAlignedX_implies_filter_image_card_le_one {d : Nat}
    (e_B : ErrorVec (d * d)) (hd : 0 < d) :
    HookAlignedX e_B →
      ((Finset.univ.filter fun q : Fin (d * d) =>
        Pauli.hasXComponent (e_B q) = true).image (fun q => q.val / d)).card ≤ 1 := by
  intro h
  obtain ⟨i, hi⟩ := h
  have hsub := (RowRestrictedX_iff_filter_image_subset e_B i hd).mp hi
  calc ((Finset.univ.filter fun q : Fin (d * d) =>
          Pauli.hasXComponent (e_B q) = true).image (fun q => q.val / d)).card
      ≤ ({i.val} : Finset Nat).card := Finset.card_le_card hsub
    _ = 1 := Finset.card_singleton _

/-- `HookAlignedZ e_B` implies the image of its Z-support under
    `(·.val % d)` has at most one element (column mirror). -/
theorem HookAlignedZ_implies_filter_image_card_le_one {d : Nat}
    (e_B : ErrorVec (d * d)) (hd : 0 < d) :
    HookAlignedZ e_B →
      ((Finset.univ.filter fun q : Fin (d * d) =>
        Pauli.hasZComponent (e_B q) = true).image (fun q => q.val % d)).card ≤ 1 := by
  intro h
  obtain ⟨j, hj⟩ := h
  have hsub := (ColRestrictedZ_iff_filter_image_subset e_B j hd).mp hj
  calc ((Finset.univ.filter fun q : Fin (d * d) =>
          Pauli.hasZComponent (e_B q) = true).image (fun q => q.val % d)).card
      ≤ ({j.val} : Finset Nat).card := Finset.card_le_card hsub
    _ = 1 := Finset.card_singleton _

/-! ## TouchesEveryRow / TouchesEveryCol bridges -/

/-- `TouchesEveryRowX E` is equivalent to `projRowsX E = d`. -/
theorem TouchesEveryRowX_iff_projRowsX_eq_d {d : Nat} (E : ErrorVec (d * d)) :
    TouchesEveryRowX E ↔ projRowsX E = d := by
  unfold projRowsX TouchesEveryRowX
  constructor
  · intro htouch
    have hall : (Finset.univ.filter fun i : Fin d =>
        ∃ j : Fin d, Pauli.hasXComponent (E (toIdx d i j)) = true) = Finset.univ := by
      apply Finset.ext
      intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact htouch i
    rw [hall, Finset.card_univ, Fintype.card_fin]
  · intro hcard i
    have h_univ : (Finset.univ.filter fun i : Fin d =>
        ∃ j : Fin d, Pauli.hasXComponent (E (toIdx d i j)) = true) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [hcard, Fintype.card_fin]
    have hmem : i ∈ (Finset.univ.filter fun i : Fin d =>
        ∃ j : Fin d, Pauli.hasXComponent (E (toIdx d i j)) = true) := by
      rw [h_univ]; exact Finset.mem_univ _
    exact (Finset.mem_filter.mp hmem).2



/-- `TouchesEveryColZ E` is equivalent to `projColsZ E = d`. -/
theorem TouchesEveryColZ_iff_projColsZ_eq_d {d : Nat} (E : ErrorVec (d * d)) :
    TouchesEveryColZ E ↔ projColsZ E = d := by
  unfold projColsZ TouchesEveryColZ
  constructor
  · intro htouch
    have hall : (Finset.univ.filter fun j : Fin d =>
        ∃ i : Fin d, Pauli.hasZComponent (E (toIdx d i j)) = true) = Finset.univ := by
      apply Finset.ext
      intro j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact htouch j
    rw [hall, Finset.card_univ, Fintype.card_fin]
  · intro hcard j
    have h_univ : (Finset.univ.filter fun j : Fin d =>
        ∃ i : Fin d, Pauli.hasZComponent (E (toIdx d i j)) = true) = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [hcard, Fintype.card_fin]
    have hmem : j ∈ (Finset.univ.filter fun j : Fin d =>
        ∃ i : Fin d, Pauli.hasZComponent (E (toIdx d i j)) = true) := by
      rw [h_univ]; exact Finset.mem_univ _
    exact (Finset.mem_filter.mp hmem).2

/-! ## Syndrome bridges -/

/-- `SameSyndrome P E F` is equivalent to "every stabilizer parity on the
    product `E · F` is false", i.e. `E · F` lies in the normalizer (at the
    parity level). Uses `ErrorVec.parity_mul_right`. -/
theorem SameSyndrome_iff_normalizer (P : QECParams) (E F : ErrorVec P.n) :
    SameSyndrome P E F ↔
      ∀ i : Fin P.numStab,
        ErrorVec.parity (P.stabilizers i) (ErrorVec.mul E F) = false := by
  unfold SameSyndrome
  constructor
  · intro hsame i
    have hxor := ErrorVec.parity_mul_right (P.stabilizers i) E F
    rw [hxor, hsame i]
    -- xor b b = false
    cases (ErrorVec.parity (P.stabilizers i) F) <;> rfl
  · intro hnorm i
    have hxor := ErrorVec.parity_mul_right (P.stabilizers i) E F
    have hzero := hnorm i
    rw [hzero] at hxor
    -- xor (parity S E) (parity S F) = false  →  parity S E = parity S F
    -- Case-analyse the two booleans.
    cases h1 : ErrorVec.parity (P.stabilizers i) E <;>
    cases h2 : ErrorVec.parity (P.stabilizers i) F <;>
    rw [h1, h2] at hxor <;>
    first
      | rfl
      | (exact (Bool.noConfusion hxor))

/-! ## Budget bridge -/

/-- `FaultBudget P s t` is equivalent to `s.C ≤ P.C_budget - t` whenever
    `t ≤ P.C_budget`. The Nat-subtraction form is the one that appears in
    `Phi`-style barrier potentials. -/
theorem FaultBudget_iff_le_sub (P : QECParams) (s : QStab.State P) (t : Nat)
    (ht : t ≤ P.C_budget) :
    FaultBudget P s t ↔ s.C ≤ P.C_budget - t := by
  unfold FaultBudget
  constructor
  · intro h; omega
  · intro h; omega

end QStab.Paper.PredicateBridge
