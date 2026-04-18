import QStab.Examples.SurfaceGeometry
import QStab.Invariant

/-! # General d×d NZ surface code distance proof

Defines `NZSurfaceSpec d` — an axiomatic specification of the properties a d×d
rotated surface code satisfies — and proves the distance theorem `C_budget − C ≥ d`
from these axioms alone.

The existing d=3 and d=4 concrete proofs in `SurfaceVerification.lean` remain
intact; this file is purely additive.

## Architecture

1. `NZSurfaceSpec d` bundles:
   - A `QECParams` with `n = d * d`
   - A logical-Z operator and d row-cut operators
   - Telescoping: each row-cut differs from the previous by a Z-type stabilizer product
   - Row-cut 0 = logical Z; row-cut structure (Z on row i, I elsewhere)
   - Logical Z is in the normalizer
   - Stabilizer generators pairwise commute (abelianness)

2. General lemmas proved from the spec:
   - `rowCut_stabEquiv_logicalZ`: every row-cut ≡ logicalZ (mod S)
   - `parity_rowCut_true_implies_row_has_X`: parity(Ẑ_i, F) = true → row i has X
   - `topological_lower_bound_general`: projRowsX(S·E) ≥ d
   - `projRowsX_update_le_general`: single-qubit perturbation adds ≤ 1 row

3. The general perpendicular spread invariant and main theorem.
-/

open QStab QStab.Examples

/-! ## Utility definitions (general, code-agnostic)

These mirror definitions in SurfaceVerification.lean but are defined here
to avoid importing the d=3 proof file with its heavy native_decide proofs. -/

namespace QStab

/-- `s` is a Z-type stabilizer: all non-identity positions are `Z`. -/
def isZType' {n : Nat} (s : ErrorVec n) : Bool :=
  decide (∀ i : Fin n, s i = Pauli.I ∨ s i = Pauli.Z)

/-- Last round coordinate component. -/
def lastRound' (P : QECParams) : Fin P.R :=
  ⟨P.R - 1, Nat.sub_lt P.hR (by decide)⟩

/-- Final-data detector for Z-type stab `sIdx` (memory_z convention). -/
def finalDataDetector' (P : QECParams) (st : State P) (sIdx : Fin P.numStab) : Bool :=
  xor (st.G sIdx (lastRound' P))
      (ErrorVec.parity (P.stabilizers sIdx) st.E_tilde)

/-- All Z-type stabilizer final-data detectors read 0. -/
def allZTypeFinalDataDetectorsZero' (P : QECParams) (st : State P) : Bool :=
  decide (∀ sIdx : Fin P.numStab,
    isZType' (P.stabilizers sIdx) = true → finalDataDetector' P st sIdx = false)

/-- Every stabilizer generator commutes with `E` (zero syndrome). -/
def allGZero' (P : QECParams) (s : State P) : Bool :=
  decide (∀ x : Fin P.numStab, ∀ y : Fin P.R, s.G x y = false)

/-- Stim-equivalent undetected logical error predicate (v2). -/
def isUndetectedLogicalError_v2' (P : QECParams) (L_Z : ErrorVec P.n)
    (st : State P) : Bool :=
  allGZero' P st
  && allZTypeFinalDataDetectorsZero' P st
  && ErrorVec.parity L_Z st.E_tilde

/-- Parity is symmetric. -/
theorem ErrorVec.parity_symm {n : Nat} (a b : ErrorVec n) :
    ErrorVec.parity a b = ErrorVec.parity b a := by
  unfold ErrorVec.parity
  have h_eq : (Finset.univ.filter fun i : Fin n =>
                ErrorVec.Pauli.anticommutes (a i) (b i) = true)
            = (Finset.univ.filter fun i : Fin n =>
                ErrorVec.Pauli.anticommutes (b i) (a i) = true) := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Pauli.anticommutes_symm]
  rw [h_eq]

end QStab

namespace QStab.Examples.SurfaceGeneral

/-! ## ErrorVec.mul associativity -/

/-- ErrorVec.mul is associative (Pauli.mul is associative). -/
theorem ErrorVec.mul_assoc' {n : Nat} (a b c : ErrorVec n) :
    ErrorVec.mul (ErrorVec.mul a b) c = ErrorVec.mul a (ErrorVec.mul b c) := by
  funext i
  show Pauli.mul (Pauli.mul (a i) (b i)) (c i) = Pauli.mul (a i) (Pauli.mul (b i) (c i))
  cases (a i) <;> cases (b i) <;> cases (c i) <;> rfl

/-! ## Axiomatic specification -/

/-- Axiomatic specification of a d×d rotated surface code for the NZ distance proof.
    Bundles the geometric and algebraic properties that the proof uses. -/
structure NZSurfaceSpec (d : Nat) where
  /-- The QEC parameters for this code -/
  params : QECParams
  /-- The code has d² physical qubits -/
  hn : params.n = d * d
  /-- d is positive -/
  hd_pos : 0 < d
  /-- The logical Z operator -/
  logicalZ : ErrorVec params.n
  /-- Row-cut operators, indexed by Fin d.
      Row-cut i is Z on all qubits in row i, I elsewhere. -/
  rowCut : Fin d → ErrorVec params.n
  /-- Row-cut 0 equals logical Z -/
  rowCut_zero : rowCut ⟨0, hd_pos⟩ = logicalZ
  /-- Telescoping: consecutive row-cuts differ by a Z-type stabilizer product.
      rowCut (i+1) = S_i · rowCut i, where S_i is a product of Z-type stabilizers. -/
  rowCut_succ : ∀ (i : Fin d) (hi : i.val + 1 < d),
    ∃ S, InStab params S ∧
      (∀ q : Fin params.n, S q = .I ∨ S q = .Z) ∧
      rowCut ⟨i.val + 1, hi⟩ = ErrorVec.mul S (rowCut i)
  /-- Logical Z is in the normalizer: commutes with every stabilizer generator -/
  logicalZ_normalizer : ∀ i : Fin params.numStab,
    ErrorVec.parity (params.stabilizers i) logicalZ = false
  /-- Row-cut structure: rowCut i has Z on qubits in row i, I elsewhere.
      Here "row i" means qubit q with q.val / d = i.val (using the cast). -/
  rowCut_spec : ∀ (i : Fin d) (q : Fin params.n),
    rowCut i q = if q.val / d = i.val then .Z else .I
  /-- Stabilizer generators pairwise commute (the stabilizer group is abelian). -/
  stab_commute : ∀ i j : Fin params.numStab,
    ErrorVec.parity (params.stabilizers i) (params.stabilizers j) = false
  /-- Hook alignment: every back-action error in B¹(T_s) increases the X-row count
      by at most 1, after optimal stabilizer correction. This is the key NZ-specific
      property: X-type hooks are horizontal pairs (same row), Z-type hooks have no
      X-component, and weight-3 hooks are equivalent to single-qubit errors mod S.
      Paper: Lemma NZHookPerturb + Lemma StabAbsorb. -/
  hook_spread_bound : ∀ (s_idx : Fin params.numStab) (e_B : ErrorVec params.n),
    e_B ∈ params.backActionSet s_idx →
    ∀ (E : ErrorVec params.n) (S_wit : ErrorVec params.n),
      InStab params S_wit →
      ∃ S_wit' : ErrorVec params.n, InStab params S_wit' ∧
        (Finset.univ.filter fun row : Fin d =>
          ∃ q : Fin params.n, q.val / d = row.val ∧
            Pauli.hasXComponent (ErrorVec.mul S_wit' (ErrorVec.mul e_B E) q) = true).card
        ≤ (Finset.univ.filter fun row : Fin d =>
          ∃ q : Fin params.n, q.val / d = row.val ∧
            Pauli.hasXComponent (ErrorVec.mul S_wit E q) = true).card + 1

/-! ## Row-cut stabilizer equivalences (general) -/

variable {d : Nat}

/-- Every row-cut is stabilizer-equivalent to logicalZ.
    Proved by strong induction on i.val using the telescoping axiom. -/
theorem rowCut_stabEquiv_logicalZ (spec : NZSurfaceSpec d) (i : Fin d) :
    ∃ S_i : ErrorVec spec.params.n, InStab spec.params S_i ∧
      spec.rowCut i = ErrorVec.mul S_i spec.logicalZ := by
  -- Induction on i.val with well-founded recursion
  obtain ⟨iv, hiv⟩ := i
  induction iv with
  | zero =>
    exact ⟨ErrorVec.identity spec.params.n, InStab.identity, by
      rw [ErrorVec.mul_identity_left]; exact spec.rowCut_zero⟩
  | succ k ih =>
    -- ih gives us the result for ⟨k, _⟩
    have hk_lt : k < d := by omega
    have ⟨S_prev, hS_prev_stab, hS_prev_eq⟩ := ih hk_lt
    -- Telescoping gives rowCut (k+1) = S_step · rowCut k
    have ⟨S_step, hS_step_stab, _, hS_step_eq⟩ :=
      spec.rowCut_succ ⟨k, hk_lt⟩ hiv
    -- rowCut (k+1) = S_step · rowCut k = S_step · (S_prev · logicalZ)
    --             = (S_step · S_prev) · logicalZ
    have hfin_eq : (⟨k + 1, hiv⟩ : Fin d) = ⟨k + 1, hiv⟩ := rfl
    rw [hS_prev_eq] at hS_step_eq
    exact ⟨ErrorVec.mul S_step S_prev,
           InStab.mul hS_step_stab hS_prev_stab,
           by rw [hS_step_eq, ErrorVec.mul_assoc']⟩

/-! ## Generator commutativity with InStab elements -/

/-- Every stabilizer generator commutes with every element of InStab.
    Uses the abelianness axiom. -/
theorem parity_generator_InStab (spec : NZSurfaceSpec d)
    (i : Fin spec.params.numStab)
    {S : ErrorVec spec.params.n} (hS : InStab spec.params S) :
    ErrorVec.parity (spec.params.stabilizers i) S = false := by
  rw [ErrorVec.parity_symm]
  exact InStab.parity_of_normalizer
          (fun j => spec.stab_commute j i) hS

/-! ## Combinatorial lemma: parity(rowCut_i, F) = true implies row i has X -/

/-- If parity(rowCut i, F) = true, then some qubit in row i of F has X-component.
    Proof by contrapositive. -/
theorem parity_rowCut_true_implies_row_has_X
    (spec : NZSurfaceSpec d)
    (F : ErrorVec spec.params.n) (i : Fin d) :
    ErrorVec.parity (spec.rowCut i) F = true →
    ∃ q : Fin spec.params.n, q.val / d = i.val ∧
      Pauli.hasXComponent (F q) = true := by
  intro hpar
  by_contra h_none
  push_neg at h_none
  have h_false : ErrorVec.parity (spec.rowCut i) F = false := by
    unfold ErrorVec.parity
    suffices h : (Finset.univ.filter fun q : Fin spec.params.n =>
        ErrorVec.Pauli.anticommutes (spec.rowCut i q) (F q) = true).card = 0 by
      rw [h]; rfl
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro q _
    rw [spec.rowCut_spec]
    by_cases hrow : q.val / d = i.val
    · -- q is in row i. rowCut i q = Z. anticommutes Z (F q) = hasXComponent (F q)
      rw [if_pos hrow, Pauli.anticommutes_Z_eq_hasXComponent]
      exact h_none q hrow
    · -- q not in row i. rowCut i q = I.
      rw [if_neg hrow]
      simp [Pauli.anticommutes_I_left]
  rw [h_false] at hpar
  exact absurd hpar (by decide)

/-! ## General single-qubit perturbation lemma -/

/-- Single-qubit perturbation adds at most 1 to projRowsX.
    General version parameterized by d. -/
theorem projRowsX_update_le_general (d_val : Nat) (E : ErrorVec (d_val * d_val))
    (q : Fin (d_val * d_val)) (p : Pauli) :
    projRowsX (d := d_val) (ErrorVec.update E q p)
      ≤ projRowsX (d := d_val) E + 1 := by
  let qRow : Fin d_val := ⟨q.val / d_val, by
    have := q.isLt
    exact Nat.div_lt_of_lt_mul this⟩
  have h_toIdx_div : ∀ (i : Fin d_val) (j : Fin d_val),
      (toIdx d_val i j).val / d_val = i.val := by
    intro i j
    show (d_val * i.val + j.val) / d_val = i.val
    have hj : j.val < d_val := j.isLt
    have hd : 0 < d_val := by omega
    rw [Nat.mul_add_div hd, Nat.div_eq_of_lt hj, Nat.add_zero]
  have h_idx_neq : ∀ (i : Fin d_val) (j : Fin d_val), i ≠ qRow → toIdx d_val i j ≠ q := by
    intro i j hi hEq
    apply hi; apply Fin.ext
    have hEq' : (toIdx d_val i j).val = q.val := congr_arg Fin.val hEq
    rw [← h_toIdx_div i j, hEq']
  have h_subset :
      (Finset.univ.filter fun i : Fin d_val =>
        ∃ j : Fin d_val,
          Pauli.hasXComponent (ErrorVec.update E q p (toIdx d_val i j)) = true)
      ⊆ (Finset.univ.filter fun i : Fin d_val =>
          ∃ j : Fin d_val, Pauli.hasXComponent (E (toIdx d_val i j)) = true)
        ∪ {qRow} := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
               Finset.mem_singleton] at hi ⊢
    by_cases hqR : i = qRow
    · right; exact hqR
    · left
      obtain ⟨j, hj⟩ := hi
      refine ⟨j, ?_⟩
      have h_neq := h_idx_neq i j hqR
      have h_update : ErrorVec.update E q p (toIdx d_val i j) = E (toIdx d_val i j) := by
        show Function.update E q (Pauli.mul p (E q)) (toIdx d_val i j)
             = E (toIdx d_val i j)
        exact Function.update_of_ne h_neq _ _
      rw [h_update] at hj
      exact hj
  calc projRowsX (d := d_val) (ErrorVec.update E q p)
      ≤ ((Finset.univ.filter fun i : Fin d_val =>
            ∃ j : Fin d_val, Pauli.hasXComponent (E (toIdx d_val i j)) = true)
          ∪ {qRow}).card
        := Finset.card_le_card h_subset
    _ ≤ (Finset.univ.filter fun i : Fin d_val =>
            ∃ j : Fin d_val, Pauli.hasXComponent (E (toIdx d_val i j)) = true).card
        + ({qRow} : Finset (Fin d_val)).card
        := Finset.card_union_le _ _
    _ = projRowsX (d := d_val) E + 1 := by simp [projRowsX]

/-! ## Key parity transfer lemmas -/

/-- parity(logicalZ, S · E) = parity(logicalZ, E) when S ∈ InStab
    and logicalZ is in the normalizer. -/
theorem parity_logicalZ_mul_InStab (spec : NZSurfaceSpec d)
    (E : ErrorVec spec.params.n)
    {S : ErrorVec spec.params.n} (hS : InStab spec.params S) :
    ErrorVec.parity spec.logicalZ (ErrorVec.mul S E) =
    ErrorVec.parity spec.logicalZ E := by
  rw [ErrorVec.parity_mul_right]
  have h_ZS : ErrorVec.parity spec.logicalZ S = false := by
    rw [ErrorVec.parity_symm]
    exact InStab.parity_of_normalizer spec.logicalZ_normalizer hS
  rw [h_ZS]
  simp [xor]

/-- Each row-cut has parity true against S · E when logicalZ has parity true
    against E, and S is in InStab. Uses telescoping + normalizer + abelianness.

    The key subtlety: the telescoping witnesses S_i are products of generators,
    so parity(S_i, mul S E) = 0 follows from abelianness + zero syndrome. But
    the hypothesis `hZSyn` only provides zero Z-type syndrome, not full zero
    syndrome. This is sufficient because the telescoping witnesses are
    themselves Z-type (only I/Z entries), so their parity with anything only
    depends on X-components — which means we need the FULL syndrome to be zero,
    or we need a more refined argument. In fact, for the row-cut argument,
    S_i is in InStab, so by parity_of_normalizer it suffices that all generators
    have zero parity against mul S E. This requires FULL zero syndrome.

    In the d=3 proof, only Z-type syndrome was needed because the specific
    witnesses happened to decompose into Z-type generators. For the general
    case, we assume full zero syndrome (which holds when considering only
    Z-type back-actions as in the NZ scheduling). -/
theorem parity_rowCut_of_logicalZ_parity
    (spec : NZSurfaceSpec d)
    (E : ErrorVec spec.params.n) (i : Fin d)
    (hSyn : ∀ j : Fin spec.params.numStab,
             ErrorVec.parity (spec.params.stabilizers j) E = false)
    (hLog : ErrorVec.parity spec.logicalZ E = true)
    {S : ErrorVec spec.params.n} (hS : InStab spec.params S) :
    ErrorVec.parity (spec.rowCut i) (ErrorVec.mul S E) = true := by
  -- rowCut i = S_i · logicalZ by telescoping
  obtain ⟨S_i, hS_i_stab, hS_i_eq⟩ := rowCut_stabEquiv_logicalZ spec i
  rw [hS_i_eq]
  -- parity(S_i · logicalZ, S · E) = parity(S_i, S · E) ⊕ parity(logicalZ, S · E)
  rw [ErrorVec.parity_mul_left]
  -- parity(logicalZ, S · E) = parity(logicalZ, E) = true
  rw [parity_logicalZ_mul_InStab spec E hS, hLog]
  -- parity(S_i, S · E) = false
  have h_Si_zero : ErrorVec.parity S_i (ErrorVec.mul S E) = false := by
    rw [ErrorVec.parity_mul_right]
    -- parity(S_i, S) = false
    -- parity_of_normalizer: (∀ j, parity(stab_j, S) = false) → InStab S_i → parity(S_i, S) = false
    -- We have InStab S_i (hS_i_stab) and need ∀ j, parity(stab_j, S) = false.
    -- That's parity_generator_InStab spec j hS.
    have h1 : ErrorVec.parity S_i S = false :=
      InStab.parity_of_normalizer (fun j => parity_generator_InStab spec j hS) hS_i_stab
    -- parity(S_i, E) = false
    -- parity_of_normalizer: (∀ j, parity(stab_j, E) = false) → InStab S_i → parity(S_i, E) = false
    have h2 : ErrorVec.parity S_i E = false :=
      InStab.parity_of_normalizer hSyn hS_i_stab
    rw [h1, h2]; rfl
  rw [h_Si_zero]; rfl

/-- **Topological lower bound (general d, full syndrome version).**
    For any error E with zero syndrome and parity(logicalZ, E) = true,
    every stabilizer representative has projRowsX ≥ d (working in n = d*d). -/
theorem topological_lower_bound_general
    (spec : NZSurfaceSpec d)
    (E : ErrorVec spec.params.n)
    (hSyn : ∀ i : Fin spec.params.numStab,
             ErrorVec.parity (spec.params.stabilizers i) E = false)
    (hLog : ErrorVec.parity spec.logicalZ E = true)
    {S : ErrorVec spec.params.n} (hS : InStab spec.params S) :
    -- We express projRowsX ≥ d via the cast from spec.hn
    d ≤ (Finset.univ.filter fun row : Fin d =>
      ∃ q : Fin spec.params.n, q.val / d = row.val ∧
        Pauli.hasXComponent (ErrorVec.mul S E q) = true).card := by
  -- Every row has an X-component, so the filter is all of Fin d.
  suffices h_all : ∀ row : Fin d,
      ∃ q : Fin spec.params.n, q.val / d = row.val ∧
        Pauli.hasXComponent (ErrorVec.mul S E q) = true by
    have h_univ : (Finset.univ.filter fun row : Fin d =>
        ∃ q : Fin spec.params.n, q.val / d = row.val ∧
          Pauli.hasXComponent (ErrorVec.mul S E q) = true)
        = Finset.univ := by
      apply Finset.ext
      intro row
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact h_all row
    rw [h_univ, Finset.card_univ, Fintype.card_fin]
  -- For each row, parity(rowCut row, mul S E) = true
  intro row
  have h_par := parity_rowCut_of_logicalZ_parity spec E row hSyn hLog hS
  exact parity_rowCut_true_implies_row_has_X spec (ErrorVec.mul S E) row h_par

/-! ## Perpendicular spread invariant (general) -/

/-- The perpendicular spread invariant stated directly on spec.params.
    Note: we express the bound in additive form to avoid Nat subtraction. -/
def PerpSpreadX (spec : NZSurfaceSpec d) (s : State spec.params) : Prop :=
  ∃ S_wit : ErrorVec spec.params.n,
    InStab spec.params S_wit ∧
    (Finset.univ.filter fun row : Fin d =>
      ∃ q : Fin spec.params.n, q.val / d = row.val ∧
        Pauli.hasXComponent (ErrorVec.mul S_wit s.E_tilde q) = true).card
    + s.C ≤ spec.params.C_budget

/-- PerpSpreadX holds at init. -/
theorem PerpSpreadX_init (spec : NZSurfaceSpec d) :
    PerpSpreadX spec (State.init spec.params) := by
  refine ⟨ErrorVec.identity spec.params.n, InStab.identity, ?_⟩
  -- At init: E_tilde = identity, C = C_budget
  -- mul identity identity = identity, so no row has X-component, card = 0
  have hC : (State.init spec.params).C = spec.params.C_budget := rfl
  have hE : (State.init spec.params).E_tilde = ErrorVec.identity spec.params.n := rfl
  rw [hC, hE]
  suffices h : (Finset.univ.filter fun row : Fin d =>
      ∃ q : Fin spec.params.n, q.val / d = row.val ∧
        Pauli.hasXComponent (ErrorVec.mul (ErrorVec.identity spec.params.n)
          (ErrorVec.identity spec.params.n) q) = true).card = 0 by
    omega
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro row _
  push_neg
  intro q _
  -- mul identity identity = identity, and hasXComponent I = false
  have : ErrorVec.mul (ErrorVec.identity spec.params.n)
    (ErrorVec.identity spec.params.n) q = Pauli.I := rfl
  rw [this]
  decide

/-- Helper: if two functions agree everywhere except possibly at index `i`,
    then the row-filter card for the new function is at most 1 more
    than for the old function (only the row containing `i` can be new). -/
private theorem row_filter_update_le (spec : NZSurfaceSpec d)
    (F G : ErrorVec spec.params.n) (i : Fin spec.params.n)
    (h_ne : ∀ q : Fin spec.params.n, q ≠ i → F q = G q) :
    (Finset.univ.filter fun row : Fin d =>
      ∃ q : Fin spec.params.n, q.val / d = row.val ∧
        Pauli.hasXComponent (F q) = true).card ≤
    (Finset.univ.filter fun row : Fin d =>
      ∃ q : Fin spec.params.n, q.val / d = row.val ∧
        Pauli.hasXComponent (G q) = true).card + 1 := by
  have i_row_lt : i.val / d < d :=
    Nat.div_lt_of_lt_mul (spec.hn ▸ i.isLt)
  set iRow : Fin d := ⟨i.val / d, i_row_lt⟩
  set S_new := Finset.univ.filter fun row : Fin d =>
    ∃ q : Fin spec.params.n, q.val / d = row.val ∧
      Pauli.hasXComponent (F q) = true
  set S_old := Finset.univ.filter fun row : Fin d =>
    ∃ q : Fin spec.params.n, q.val / d = row.val ∧
      Pauli.hasXComponent (G q) = true
  -- S_new ⊆ S_old ∪ {iRow}
  have h_sub : S_new ⊆ S_old ∪ {iRow} := by
    intro row h_mem
    have h_mem' := (Finset.mem_filter.mp h_mem).2
    obtain ⟨q, hq_row, hq_has⟩ := h_mem'
    by_cases hqi : q = i
    · apply Finset.mem_union_right
      subst hqi
      exact Finset.mem_singleton.mpr (Fin.ext (Eq.symm hq_row))
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        q, hq_row, by rw [← h_ne q hqi]; exact hq_has⟩
  calc S_new.card
      ≤ (S_old ∪ {iRow}).card := Finset.card_le_card h_sub
    _ ≤ S_old.card + ({iRow} : Finset (Fin d)).card := Finset.card_union_le _ _
    _ = S_old.card + 1 := by simp

/-- PerpSpreadX is preserved by each active→active transition.
    The Type-II case uses the hook_spread_bound axiom of NZSurfaceSpec. -/
theorem PerpSpreadX_preservation (spec : NZSurfaceSpec d)
    (s s' : State spec.params)
    (hinv : PerpSpreadX spec s)
    (hstep : Step spec.params (.active s) (.active s')) :
    PerpSpreadX spec s' := by
  obtain ⟨S_wit, hS_stab, hbound⟩ := hinv
  cases hstep with
  | type0 _ i p _ hC =>
    refine ⟨S_wit, hS_stab, ?_⟩
    -- mul S (update E i p) q = mul S E q for q ≠ i (update only changes position i).
    -- So row-filter grows by at most 1 row (the row of i). C shrinks by 1.
    have i_row_lt : i.val / d < d :=
      Nat.div_lt_of_lt_mul (spec.hn ▸ i.isLt)
    -- Key: for q ≠ i, the pointwise mul is unchanged.
    -- For q ≠ i: update doesn't change position q, so mul is unchanged.
    have h_mul_ne : ∀ q : Fin spec.params.n, q ≠ i →
        ErrorVec.mul S_wit (ErrorVec.update s.E_tilde i p) q =
        ErrorVec.mul S_wit s.E_tilde q := by
      intro q hq; simp [ErrorVec.mul, ErrorVec.update, Function.update, dif_neg hq]
    have h_card := row_filter_update_le spec
      (ErrorVec.mul S_wit (ErrorVec.update s.E_tilde i p))
      (ErrorVec.mul S_wit s.E_tilde) i h_mul_ne
    -- h_card: new_card ≤ old_card + 1
    -- hbound: old_card + s.C ≤ C_budget
    -- hC: 0 < s.C
    -- goal: new_card + (s.C - 1) ≤ C_budget
    -- new_card + (s.C - 1) ≤ (old_card + 1) + (s.C - 1) = old_card + s.C ≤ C_budget
    -- new_card + (C-1) ≤ (old_card+1) + (C-1) ≤ old_card + C ≤ budget
    have hC_pos : 1 ≤ s.C := hC
    have h1 : (Finset.univ.filter fun row : Fin d => ∃ q, q.val / d = row.val ∧
        Pauli.hasXComponent (ErrorVec.mul S_wit (ErrorVec.update s.E_tilde i p) q) = true).card
      + (s.C - 1)
      ≤ ((Finset.univ.filter fun row : Fin d => ∃ q, q.val / d = row.val ∧
        Pauli.hasXComponent (ErrorVec.mul S_wit s.E_tilde q) = true).card + 1)
      + (s.C - 1) := Nat.add_le_add_right h_card _
    -- Combine: new_card + (C-1) ≤ old_card + C ≤ budget
    have key : ∀ a b C : Nat, 1 ≤ C → a ≤ b + 1 → b + C ≤ spec.params.C_budget →
        a + (C - 1) ≤ spec.params.C_budget := by omega
    exact key _ _ _ hC_pos h_card hbound
  | type1 _ i p _ hC =>
    refine ⟨S_wit, hS_stab, ?_⟩
    have i_row_lt : i.val / d < d :=
      Nat.div_lt_of_lt_mul (spec.hn ▸ i.isLt)
    have h_mul_ne : ∀ q : Fin spec.params.n, q ≠ i →
        ErrorVec.mul S_wit (ErrorVec.update s.E_tilde i p) q =
        ErrorVec.mul S_wit s.E_tilde q := by
      intro q hq; simp [ErrorVec.mul, ErrorVec.update, Function.update, dif_neg hq]
    have h_card := row_filter_update_le spec
      (ErrorVec.mul S_wit (ErrorVec.update s.E_tilde i p))
      (ErrorVec.mul S_wit s.E_tilde) i h_mul_ne
    -- new_card + (C-1) ≤ (old_card+1) + (C-1) ≤ old_card + C ≤ budget
    have hC_pos : 1 ≤ s.C := hC
    have h1 : (Finset.univ.filter fun row : Fin d => ∃ q, q.val / d = row.val ∧
        Pauli.hasXComponent (ErrorVec.mul S_wit (ErrorVec.update s.E_tilde i p) q) = true).card
      + (s.C - 1)
      ≤ ((Finset.univ.filter fun row : Fin d => ∃ q, q.val / d = row.val ∧
        Pauli.hasXComponent (ErrorVec.mul S_wit s.E_tilde q) = true).card + 1)
      + (s.C - 1) := Nat.add_le_add_right h_card _
    -- Combine: new_card + (C-1) ≤ old_card + C ≤ budget
    have key : ∀ a b C : Nat, 1 ≤ C → a ≤ b + 1 → b + C ≤ spec.params.C_budget →
        a + (C - 1) ≤ spec.params.C_budget := by omega
    exact key _ _ _ hC_pos h_card hbound
  | type2 _ e he _ hC =>
    -- Use the hook_spread_bound axiom: e_B ∈ B¹(T_s) → row count grows by ≤ 1
    obtain ⟨S_wit', hS_stab', hcard_le⟩ :=
      spec.hook_spread_bound s.coord.x e he s.E_tilde S_wit hS_stab
    refine ⟨S_wit', hS_stab', ?_⟩
    -- hcard_le: new_card ≤ old_card + 1
    -- hbound: old_card + s.C ≤ C_budget
    -- hC: 0 < s.C
    -- goal: new_card + (s.C - 1) ≤ C_budget
    have hC_pos : 1 ≤ s.C := hC
    omega
  | type3 _ hC =>
    refine ⟨S_wit, hS_stab, ?_⟩
    -- E_tilde unchanged, C decreases by 1
    show (Finset.univ.filter fun row : Fin d =>
        ∃ q : Fin spec.params.n, q.val / d = row.val ∧
          Pauli.hasXComponent (ErrorVec.mul S_wit s.E_tilde q) = true).card
      + (s.C - 1) ≤ spec.params.C_budget
    omega
  | measure _ nc _ =>
    refine ⟨S_wit, hS_stab, ?_⟩
    rw [measureStep_E_tilde, measureStep_C]
    exact hbound

/-- Package into the Invariant framework. -/
def PerpSpreadX_Invariant (spec : NZSurfaceSpec d) : Invariant spec.params where
  holds := PerpSpreadX spec
  holds_init := PerpSpreadX_init spec
  preservation := PerpSpreadX_preservation spec

/-! ## v2 implies zero Z-type syndrome (general) -/

/-- v2 directly implies zero Z-type syndrome. -/
theorem v2_implies_zero_Z_syndrome_general (spec : NZSurfaceSpec d)
    (s : State spec.params)
    (hv2 : isUndetectedLogicalError_v2' spec.params spec.logicalZ s = true) :
    ∀ i : Fin spec.params.numStab,
      isZType' (spec.params.stabilizers i) = true →
      ErrorVec.parity (spec.params.stabilizers i) s.E_tilde = false := by
  intro i hZ
  unfold isUndetectedLogicalError_v2' at hv2
  simp only [Bool.and_eq_true] at hv2
  obtain ⟨⟨hG, hDet⟩, _⟩ := hv2
  unfold allGZero' at hG
  unfold allZTypeFinalDataDetectorsZero' at hDet
  simp only [decide_eq_true_eq] at hG hDet
  have h_G_i : s.G i (lastRound' spec.params) = false := hG i (lastRound' spec.params)
  have h_det_i : finalDataDetector' spec.params s i = false := hDet i hZ
  unfold finalDataDetector' at h_det_i
  rw [h_G_i] at h_det_i
  simpa using h_det_i

/-! ## Main theorem (general d)

The full proof requires connecting the Z-type-only syndrome hypothesis to the
full syndrome hypothesis needed by the topological lower bound. For codes
where all stabilizers are Z-type in the relevant decomposition, the Z-type
syndrome suffices. For the general case, we need the stronger hypothesis
or a more refined InStab decomposition argument.

We provide two versions:
1. A version with full zero syndrome (cleaner, fully proved modulo sorry
   in preservation)
2. A version with v2 hypothesis (requires the bridge from Z-type to full) -/

/-- **Main theorem (full syndrome version).** For any d×d surface code
    satisfying NZSurfaceSpec, if at a reachable state E has zero syndrome
    and parity(logicalZ, E) = true, then C_budget − C ≥ d. -/
theorem nz_distance_ge_d_full_syndrome (spec : NZSurfaceSpec d)
    (s : State spec.params)
    (hreach : MultiStep spec.params (.active (State.init spec.params)) (.active s))
    (hSyn : ∀ i : Fin spec.params.numStab,
             ErrorVec.parity (spec.params.stabilizers i) s.E_tilde = false)
    (hLog : ErrorVec.parity spec.logicalZ s.E_tilde = true) :
    spec.params.C_budget - s.C ≥ d := by
  -- Step 1: PerpSpreadX invariant holds at s.
  have hinv : PerpSpreadX spec s :=
    (PerpSpreadX_Invariant spec).holds_of_reachable s hreach
  obtain ⟨S_wit, hS_stab, hbound⟩ := hinv
  -- Step 2: Topological lower bound gives row count ≥ d.
  have hTLB := topological_lower_bound_general spec s.E_tilde hSyn hLog hS_stab
  -- Step 3: Combine.
  omega

/-- **Main theorem (v2 version).** Requires the bridge from Z-type syndrome
    to full syndrome. For the NZ-scheduled surface code, this bridge holds
    because the v2 predicate's final-data detectors give zero Z-type syndrome,
    and the row-cut witnesses are Z-type products.

    For the general case, we add the hypothesis that all stabilizers are
    Z-type-detectable from v2 (which holds for rotated surface codes). -/
theorem nz_distance_ge_d_v2 (spec : NZSurfaceSpec d)
    (s : State spec.params)
    (hreach : MultiStep spec.params (.active (State.init spec.params)) (.active s))
    (hv2 : isUndetectedLogicalError_v2' spec.params spec.logicalZ s = true)
    -- Bridge: v2 implies full zero syndrome (code-specific, holds for surface codes)
    (hbridge : ∀ i : Fin spec.params.numStab,
               ErrorVec.parity (spec.params.stabilizers i) s.E_tilde = false) :
    spec.params.C_budget - s.C ≥ d := by
  have hLog : ErrorVec.parity spec.logicalZ s.E_tilde = true := by
    unfold isUndetectedLogicalError_v2' at hv2
    simp only [Bool.and_eq_true] at hv2
    exact hv2.2
  exact nz_distance_ge_d_full_syndrome spec s hreach hbridge hLog

/-! ## d=3 instantiation witness -/

namespace D3Witness

open SurfaceD3

/-- The d=3 row-cut operators as Fin 3 → ErrorVec 9. -/
def rowCutFin : Fin 3 → ErrorVec 9
  | ⟨0, _⟩ => SurfaceD3.rowCut 1
  | ⟨1, _⟩ => SurfaceD3.rowCut 2
  | ⟨2, _⟩ => SurfaceD3.rowCut 3

theorem rowCutFin_zero : rowCutFin ⟨0, by decide⟩ = SurfaceD3.logicalZ := by
  show SurfaceD3.rowCut 1 = SurfaceD3.logicalZ
  funext i; fin_cases i <;> rfl

theorem rowCutFin_succ_0 :
    ∃ S, InStab SurfaceD3.code S ∧
      (∀ q : Fin 9, S q = .I ∨ S q = .Z) ∧
      rowCutFin ⟨1, by decide⟩ = ErrorVec.mul S (rowCutFin ⟨0, by decide⟩) := by
  refine ⟨ErrorVec.mul SurfaceD3.s1 SurfaceD3.s6,
          InStab.mul
            (InStab.gen (⟨0, by decide⟩ : Fin SurfaceD3.code.numStab))
            (InStab.gen (⟨5, by decide⟩ : Fin SurfaceD3.code.numStab)),
          ?_, ?_⟩
  · decide
  · funext q; fin_cases q <;> rfl

theorem rowCutFin_succ_1 :
    ∃ S, InStab SurfaceD3.code S ∧
      (∀ q : Fin 9, S q = .I ∨ S q = .Z) ∧
      rowCutFin ⟨2, by decide⟩ = ErrorVec.mul S (rowCutFin ⟨1, by decide⟩) := by
  refine ⟨ErrorVec.mul SurfaceD3.s4 SurfaceD3.s7,
          InStab.mul
            (InStab.gen (⟨3, by decide⟩ : Fin SurfaceD3.code.numStab))
            (InStab.gen (⟨6, by decide⟩ : Fin SurfaceD3.code.numStab)),
          ?_, ?_⟩
  · decide
  · funext q; fin_cases q <;> rfl

theorem logicalZ_norm : ∀ i : Fin SurfaceD3.code.numStab,
    ErrorVec.parity (SurfaceD3.code.stabilizers i) SurfaceD3.logicalZ = false := by
  decide

theorem rowCutFin_spec : ∀ (i : Fin 3) (q : Fin 9),
    rowCutFin i q = if q.val / 3 = i.val then .Z else .I := by
  decide

theorem stab_commute_d3 : ∀ i j : Fin SurfaceD3.code.numStab,
    ErrorVec.parity (SurfaceD3.code.stabilizers i) (SurfaceD3.code.stabilizers j) = false := by
  decide

/-- The d=3 NZSurfaceSpec instance.
    hook_spread_bound is vacuously true since backActionSet = ∅ in the d=3 code.
    The concrete hook geometry is verified separately in SurfaceVerification.lean. -/
def nzSpec : NZSurfaceSpec 3 where
  params := SurfaceD3.code
  hn := by decide
  hd_pos := by decide
  logicalZ := SurfaceD3.logicalZ
  rowCut := rowCutFin
  rowCut_zero := rowCutFin_zero
  rowCut_succ := fun ⟨iv, hiv_lt⟩ hi => by
    match iv, hiv_lt, hi with
    | 0, _, _ => exact rowCutFin_succ_0
    | 1, _, _ => exact rowCutFin_succ_1
  logicalZ_normalizer := logicalZ_norm
  rowCut_spec := rowCutFin_spec
  stab_commute := stab_commute_d3
  hook_spread_bound := fun _ _ h => h.elim

end D3Witness

/-! ## d=4 instantiation witness -/

namespace D4Witness

open SurfaceD4

/-- The d=4 row-cut operators as Fin 4 → ErrorVec 16. -/
def rowCutFin : Fin 4 → ErrorVec 16
  | ⟨0, _⟩ => SurfaceD4.rowCut 1
  | ⟨1, _⟩ => SurfaceD4.rowCut 2
  | ⟨2, _⟩ => SurfaceD4.rowCut 3
  | ⟨3, _⟩ => SurfaceD4.rowCut 4

theorem rowCutFin_zero : rowCutFin ⟨0, by decide⟩ = SurfaceD4.logicalZ := by
  show SurfaceD4.rowCut 1 = SurfaceD4.logicalZ
  funext i; fin_cases i <;> rfl

theorem rowCutFin_succ_0 :
    ∃ S, InStab SurfaceD4.code S ∧
      (∀ q : Fin 16, S q = .I ∨ S q = .Z) ∧
      rowCutFin ⟨1, by decide⟩ = ErrorVec.mul S (rowCutFin ⟨0, by decide⟩) := by
  refine ⟨ErrorVec.mul SurfaceD4.s1 SurfaceD4.s2,
          InStab.mul
            (InStab.gen (⟨0, by decide⟩ : Fin SurfaceD4.code.numStab))
            (InStab.gen (⟨1, by decide⟩ : Fin SurfaceD4.code.numStab)),
          ?_, ?_⟩
  · decide
  · funext q; fin_cases q <;> rfl

theorem rowCutFin_succ_1 :
    ∃ S, InStab SurfaceD4.code S ∧
      (∀ q : Fin 16, S q = .I ∨ S q = .Z) ∧
      rowCutFin ⟨2, by decide⟩ = ErrorVec.mul S (rowCutFin ⟨1, by decide⟩) := by
  refine ⟨ErrorVec.mul SurfaceD4.s3 (ErrorVec.mul SurfaceD4.s10 SurfaceD4.s11),
          InStab.mul
            (InStab.gen (⟨2, by decide⟩ : Fin SurfaceD4.code.numStab))
            (InStab.mul
              (InStab.gen (⟨9, by decide⟩ : Fin SurfaceD4.code.numStab))
              (InStab.gen (⟨10, by decide⟩ : Fin SurfaceD4.code.numStab))),
          ?_, ?_⟩
  · decide
  · funext q; fin_cases q <;> rfl

theorem rowCutFin_succ_2 :
    ∃ S, InStab SurfaceD4.code S ∧
      (∀ q : Fin 16, S q = .I ∨ S q = .Z) ∧
      rowCutFin ⟨3, by decide⟩ = ErrorVec.mul S (rowCutFin ⟨2, by decide⟩) := by
  refine ⟨ErrorVec.mul SurfaceD4.s4 SurfaceD4.s5,
          InStab.mul
            (InStab.gen (⟨3, by decide⟩ : Fin SurfaceD4.code.numStab))
            (InStab.gen (⟨4, by decide⟩ : Fin SurfaceD4.code.numStab)),
          ?_, ?_⟩
  · decide
  · funext q; fin_cases q <;> rfl

theorem logicalZ_norm : ∀ i : Fin SurfaceD4.code.numStab,
    ErrorVec.parity (SurfaceD4.code.stabilizers i) SurfaceD4.logicalZ = false := by
  decide

theorem rowCutFin_spec : ∀ (i : Fin 4) (q : Fin 16),
    rowCutFin i q = if q.val / 4 = i.val then .Z else .I := by
  decide

theorem stab_commute_d4 : ∀ i j : Fin SurfaceD4.code.numStab,
    ErrorVec.parity (SurfaceD4.code.stabilizers i) (SurfaceD4.code.stabilizers j) = false := by
  decide

/-- The d=4 NZSurfaceSpec instance.
    hook_spread_bound is vacuously true since backActionSet = ∅ in the d=4 code. -/
def nzSpec : NZSurfaceSpec 4 where
  params := SurfaceD4.code
  hn := by decide
  hd_pos := by decide
  logicalZ := SurfaceD4.logicalZ
  rowCut := rowCutFin
  rowCut_zero := rowCutFin_zero
  rowCut_succ := fun ⟨iv, hiv_lt⟩ hi => by
    match iv, hiv_lt, hi with
    | 0, _, _ => exact rowCutFin_succ_0
    | 1, _, _ => exact rowCutFin_succ_1
    | 2, _, _ => exact rowCutFin_succ_2
  logicalZ_normalizer := logicalZ_norm
  rowCut_spec := rowCutFin_spec
  stab_commute := stab_commute_d4
  hook_spread_bound := fun _ _ h => h.elim

end D4Witness

end QStab.Examples.SurfaceGeneral
