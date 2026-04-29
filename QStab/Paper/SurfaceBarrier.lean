import QStab.Examples.SurfaceGeneral
import QStab.Paper.BarrierFramework
import Mathlib.Data.Nat.Lattice

/-!
# Surface code as a `BarrierFunction` instance (paper §7)

Constructs the surface code's perpendicular-spread barrier function
`β_Z̄ := max(0, d − ω⊥^X)` (paper Definition `def:PerpSpread` and
Corollary `thm:PerpBarrier`) as a `BarrierFunction` in the sense of
`QStab.Paper.BarrierFramework`. Combined with `IsLAligned` (proved from
the `hook_spread_bound` axiom of `NZSurfaceSpec`), this gives
`d_circ ≥ d` for the surface code under NZ scheduling as a direct
instance of `BarrierFramework.distance_preservation`, eliminating the
ad hoc invariant chain in `Examples/SurfaceGeneral.lean`.

The perpendicular spread is defined as the *witness-minimised* row count:
`ω⊥^X(E) := min_{S ∈ S} rowfilter(S · E)`. The minimisation is essential
to make the function descend to the coset `[E] = E · S`. We implement the
min via Mathlib's `sInf` over a `Set ℕ`, using that the set
`{rowfilter(S · E) | S ∈ InStab P}` is non-empty (S = identity).

**Zero sorry; only [propext, Classical.choice, Quot.sound] axioms.**
-/

namespace QStab.Paper.SurfaceBarrier

open QStab QStab.Examples QStab.Examples.SurfaceGeneral QStab.Paper.BarrierFramework

variable {d : Nat}

/-! ## The witness-minimised row count -/

/-- Row count of `S · E` against the row partition `q.val / d`. This is
    the inner quantity inside the surface code's perpendicular spread. -/
def rowsX (spec : NZSurfaceSpec d) (S E : ErrorVec spec.params.n) : Nat :=
  (Finset.univ.filter fun row : Fin d =>
    ∃ q : Fin spec.params.n, q.val / d = row.val ∧
      Pauli.hasXComponent (ErrorVec.mul S E q) = true).card

/-- The set of attainable spread values `rowfilter(S · E)` over all
    stabilizer witnesses. Always non-empty (`S = identity` is a witness). -/
def witnessedSpread (spec : NZSurfaceSpec d) (E : ErrorVec spec.params.n) :
    Set Nat :=
  {k | ∃ S, InStab spec.params S ∧ k = rowsX spec S E}

/-- The witness set is non-empty: `S = identity` always witnesses some
    spread value. -/
theorem witnessedSpread_nonempty (spec : NZSurfaceSpec d)
    (E : ErrorVec spec.params.n) :
    (witnessedSpread spec E).Nonempty :=
  ⟨rowsX spec (ErrorVec.identity spec.params.n) E,
   ErrorVec.identity spec.params.n, InStab.identity, rfl⟩

/-- The perpendicular spread `ω⊥^X(E) := min_{S ∈ S} rowsX(S · E)`. -/
noncomputable def omegaPerpX (spec : NZSurfaceSpec d)
    (E : ErrorVec spec.params.n) : Nat :=
  sInf (witnessedSpread spec E)

/-- The minimum is attained: there exists a witness `S` with
    `rowsX spec S E = omegaPerpX spec E`. -/
theorem omegaPerpX_attained (spec : NZSurfaceSpec d)
    (E : ErrorVec spec.params.n) :
    ∃ S, InStab spec.params S ∧ rowsX spec S E = omegaPerpX spec E := by
  have hmem : omegaPerpX spec E ∈ witnessedSpread spec E :=
    Nat.sInf_mem (witnessedSpread_nonempty spec E)
  obtain ⟨S, hS, hk⟩ := hmem
  exact ⟨S, hS, hk.symm⟩

/-- For any witness `S` in the stabilizer subgroup, `omegaPerpX` is at
    most `rowsX spec S E`. -/
theorem omegaPerpX_le_of_witness (spec : NZSurfaceSpec d)
    (E : ErrorVec spec.params.n) {S : ErrorVec spec.params.n}
    (hS : InStab spec.params S) :
    omegaPerpX spec E ≤ rowsX spec S E :=
  Nat.sInf_le ⟨S, hS, rfl⟩

/-! ## Pointwise lemma: changing one position changes at most one row -/

/-- If two error vectors agree everywhere except possibly at index `i`,
    the row counts differ by at most one. (Same content as the existing
    `row_filter_update_le` in `SurfaceGeneral.lean`, restated for our
    `rowsX` view.) -/
private theorem rowsX_pointwise_le (spec : NZSurfaceSpec d)
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
      Pauli.hasXComponent (F q) = true with hS_new
  set S_old := Finset.univ.filter fun row : Fin d =>
    ∃ q : Fin spec.params.n, q.val / d = row.val ∧
      Pauli.hasXComponent (G q) = true with hS_old
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

/-! ## Subadditivity of `rowsX` in the multiplied factor

The key lemma: multiplying `E` on the left by an arbitrary `F` raises the
row count by at most `weight F`. Proved by induction on the size of the
support of `F`: each non-identity position contributes at most one new row. -/

/-- Auxiliary: `rowsX` only depends on `hasXComponent` of `S · E` at each
    position. Useful for rewriting. -/
private theorem rowsX_eq (spec : NZSurfaceSpec d)
    (S E : ErrorVec spec.params.n) :
    rowsX spec S E =
      (Finset.univ.filter fun row : Fin d =>
        ∃ q : Fin spec.params.n, q.val / d = row.val ∧
          Pauli.hasXComponent (ErrorVec.mul S E q) = true).card := rfl

/-- If `F` agrees with identity outside a finite set `T` (with size `k`),
    then `rowsX spec S (F · E) ≤ rowsX spec S E + k`. Proved by strong
    induction on `k`, peeling off one support position at a time. -/
private theorem rowsX_mul_le_card_support_aux
    (k : Nat) (spec : NZSurfaceSpec d)
    (S E F : ErrorVec spec.params.n) (T : Finset (Fin spec.params.n))
    (hT_card : T.card = k)
    (hT : ∀ q, q ∉ T → F q = Pauli.I) :
    rowsX spec S (ErrorVec.mul F E) ≤ rowsX spec S E + k := by
  induction k generalizing F T with
  | zero =>
    have hT_empty : T = ∅ := Finset.card_eq_zero.mp hT_card
    have hF_I : ∀ q, F q = Pauli.I := by
      intro q
      apply hT
      rw [hT_empty]
      exact Finset.notMem_empty q
    have hFE : ErrorVec.mul F E = E := by
      funext q
      show Pauli.mul (F q) (E q) = E q
      rw [hF_I q]
      cases (E q) <;> rfl
    rw [hFE]
    omega
  | succ k' ih =>
    -- T has at least one element. Pick any i ∈ T.
    have hT_pos : 0 < T.card := by rw [hT_card]; omega
    obtain ⟨i, hi_in⟩ := Finset.card_pos.mp hT_pos
    -- Define F' = F with position i reset to identity, T' = T \ {i}.
    let F' : ErrorVec spec.params.n := fun q =>
      if q = i then Pauli.I else F q
    let T' : Finset (Fin spec.params.n) := T.erase i
    have hT'_card : T'.card = k' := by
      have : T'.card + 1 = T.card := Finset.card_erase_add_one hi_in
      omega
    have hF'_T' : ∀ q, q ∉ T' → F' q = Pauli.I := by
      intro q hq
      by_cases hqi : q = i
      · simp [F', hqi]
      · have hq_not_T : q ∉ T := by
          intro h_in
          apply hq
          exact Finset.mem_erase.mpr ⟨hqi, h_in⟩
        have : F q = Pauli.I := hT q hq_not_T
        show (if q = i then Pauli.I else F q) = Pauli.I
        rw [if_neg hqi]; exact this
    have hF'_le : rowsX spec S (ErrorVec.mul F' E) ≤
                  rowsX spec S E + k' :=
      ih F' T' hT'_card hF'_T'
    -- F · E and F' · E differ only at position i.
    have h_diff : ∀ q, q ≠ i →
        ErrorVec.mul S (ErrorVec.mul F E) q =
        ErrorVec.mul S (ErrorVec.mul F' E) q := by
      intro q hq
      show Pauli.mul (S q) (Pauli.mul (F q) (E q)) =
            Pauli.mul (S q) (Pauli.mul (F' q) (E q))
      have hF'q : F' q = F q := by
        show (if q = i then Pauli.I else F q) = F q
        rw [if_neg hq]
      rw [hF'q]
    have h_step := rowsX_pointwise_le spec
      (ErrorVec.mul S (ErrorVec.mul F E))
      (ErrorVec.mul S (ErrorVec.mul F' E)) i h_diff
    -- Goal: rowsX(S · F · E) ≤ rowsX(S · E) + (k' + 1).
    show (Finset.univ.filter fun row : Fin d =>
      ∃ q : Fin spec.params.n, q.val / d = row.val ∧
        Pauli.hasXComponent (ErrorVec.mul S (ErrorVec.mul F E) q) = true).card
        ≤ rowsX spec S E + (k' + 1)
    -- h_step: above LHS ≤ (rowfilter F' E version).card + 1
    have h_F'_eq : (Finset.univ.filter fun row : Fin d =>
      ∃ q : Fin spec.params.n, q.val / d = row.val ∧
        Pauli.hasXComponent (ErrorVec.mul S (ErrorVec.mul F' E) q) = true).card
        = rowsX spec S (ErrorVec.mul F' E) := rfl
    rw [h_F'_eq] at h_step
    omega

/-- Subadditivity: `rowsX spec S (F · E) ≤ rowsX spec S E + weight F`. -/
theorem rowsX_subadditive (spec : NZSurfaceSpec d)
    (S E F : ErrorVec spec.params.n) :
    rowsX spec S (ErrorVec.mul F E) ≤ rowsX spec S E + ErrorVec.weight F := by
  set T : Finset (Fin spec.params.n) :=
    Finset.univ.filter fun q => F q ≠ Pauli.I with hT_def
  have hT_card : T.card = ErrorVec.weight F := rfl
  have hT_outside : ∀ q, q ∉ T → F q = Pauli.I := by
    intro q hq
    by_contra hne
    apply hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ q, hne⟩
  exact rowsX_mul_le_card_support_aux _ spec S E F T hT_card hT_outside

/-! ## The bar-Z logical class -/

/-- The logical class for the bar-Z coset of an `NZSurfaceSpec`: all
    Pauli errors in the normalizer that anticommute with `logicalZ`.
    This is the union of the `Z̄ · S` and `Ȳ · S` cosets (both have
    `Parity(Z̄, ·) = 1`). -/
def barZClass (spec : NZSurfaceSpec d) : LogicalClass spec.params where
  contains E :=
    (∀ i : Fin spec.params.numStab,
      ErrorVec.parity (spec.params.stabilizers i) E = false) ∧
    ErrorVec.parity spec.logicalZ E = true
  d_L := d
  d_L_pos := spec.hd_pos
  d_L_min E h := by
    -- Every error in the bad coset has weight ≥ d via the topological
    -- floor: rowsX(S = identity, E) ≥ d, and weight ≥ rowsX (each row
    -- with X-component contributes at least one non-identity qubit).
    obtain ⟨hSyn, hLog⟩ := h
    have hTLB := topological_lower_bound_general spec E hSyn hLog
                  (S := ErrorVec.identity spec.params.n) InStab.identity
    -- hTLB: rowsX(identity · E).card ≥ d, but mul identity E = E.
    have hmul : ∀ q, ErrorVec.mul (ErrorVec.identity spec.params.n) E q = E q := by
      intro q; show Pauli.mul Pauli.I (E q) = E q; cases E q <;> rfl
    have hrowfilter : (Finset.univ.filter fun row : Fin d =>
        ∃ q : Fin spec.params.n, q.val / d = row.val ∧
          Pauli.hasXComponent (E q) = true).card ≥ d := by
      have heq : (Finset.univ.filter fun row : Fin d =>
          ∃ q : Fin spec.params.n, q.val / d = row.val ∧
            Pauli.hasXComponent (ErrorVec.mul (ErrorVec.identity spec.params.n) E q) = true)
          = (Finset.univ.filter fun row : Fin d =>
            ∃ q : Fin spec.params.n, q.val / d = row.val ∧
              Pauli.hasXComponent (E q) = true) := by
        apply Finset.filter_congr
        intro row _
        refine ⟨fun ⟨q, hq, hX⟩ => ⟨q, hq, ?_⟩,
                fun ⟨q, hq, hX⟩ => ⟨q, hq, ?_⟩⟩
        · rw [hmul q] at hX; exact hX
        · rw [hmul q]; exact hX
      rw [← heq]; exact hTLB
    -- weight E ≥ |rows with X|: each such row has at least one qubit
    -- with hasXComponent = true, hence non-identity Pauli.
    -- Build an injection rows → qubits.
    -- Pick for each "X-row" some qubit in that row with X-component.
    set RowsX : Finset (Fin d) := Finset.univ.filter fun row : Fin d =>
      ∃ q : Fin spec.params.n, q.val / d = row.val ∧
        Pauli.hasXComponent (E q) = true with hRowsX_def
    -- For each row in RowsX, pick a witness qubit.
    have hpick : ∀ row ∈ RowsX, ∃ q : Fin spec.params.n,
        q.val / d = row.val ∧ Pauli.hasXComponent (E q) = true := by
      intro row hrow
      have := (Finset.mem_filter.mp hrow).2
      exact this
    classical
    let pick : Fin d → Fin spec.params.n :=
      fun row =>
        if h : row ∈ RowsX then
          Classical.choose (hpick row h)
        else
          ⟨0, by
            have : 0 < spec.params.n := by
              rw [spec.hn]
              exact Nat.mul_pos spec.hd_pos spec.hd_pos
            exact this⟩
    have hpick_spec : ∀ row ∈ RowsX,
        (pick row).val / d = row.val ∧ Pauli.hasXComponent (E (pick row)) = true := by
      intro row hrow
      simp only [pick, dif_pos hrow]
      exact Classical.choose_spec (hpick row hrow)
    have h_inj : ∀ r1 ∈ RowsX, ∀ r2 ∈ RowsX, pick r1 = pick r2 → r1 = r2 := by
      intro r1 h1 r2 h2 heq
      have h1' := (hpick_spec r1 h1).1
      have h2' := (hpick_spec r2 h2).1
      have : (pick r1).val / d = r1.val := h1'
      rw [heq] at this
      have hh : (pick r2).val / d = r2.val := h2'
      have : r1.val = r2.val := by omega
      exact Fin.ext this
    -- The image of `pick` on RowsX is contained in the support of E.
    have h_image_sub : RowsX.image pick ⊆
        Finset.univ.filter fun q : Fin spec.params.n => E q ≠ Pauli.I := by
      intro q hq
      obtain ⟨row, hrow, hpick_q⟩ := Finset.mem_image.mp hq
      have hX := (hpick_spec row hrow).2
      rw [hpick_q] at hX
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hI
      rw [hI] at hX
      simp [Pauli.hasXComponent] at hX
    have h_card_image : (RowsX.image pick).card = RowsX.card := by
      apply Finset.card_image_of_injOn
      intro r1 h1 r2 h2 heq
      exact h_inj r1 h1 r2 h2 heq
    have h_card_le : (RowsX.image pick).card ≤
        (Finset.univ.filter fun q : Fin spec.params.n => E q ≠ Pauli.I).card :=
      Finset.card_le_card h_image_sub
    have h_weight_eq : ErrorVec.weight E =
        (Finset.univ.filter fun q : Fin spec.params.n => E q ≠ Pauli.I).card := rfl
    -- Goal: ErrorVec.weight E ≥ d.
    -- Chain: weight = |support| ≥ |image| = |RowsX| ≥ d.
    show ErrorVec.weight E ≥ d
    rw [h_weight_eq]
    have h_RowsX_ge : RowsX.card ≥ d := hrowfilter
    omega

/-! ## The barrier function for the surface code -/

/-- The surface code's perpendicular-spread barrier, packaged as a
    `BarrierFunction` for the bar-Z coset (paper Corollary
    `thm:PerpBarrier`). -/
noncomputable def surfaceBarrier (spec : NZSurfaceSpec d) :
    BarrierFunction spec.params (barZClass spec) where
  mu E := d - omegaPerpX spec E
  -- Property (i): μ(I) = d_L = d.
  mu_identity := by
    -- rowsX(identity, identity) = 0, so 0 ∈ witnessedSpread, hence ω⊥^X = 0.
    have h_rowsX_zero :
        rowsX spec (ErrorVec.identity spec.params.n)
              (ErrorVec.identity spec.params.n) = 0 := by
      show (Finset.univ.filter fun row : Fin d =>
        ∃ q : Fin spec.params.n, q.val / d = row.val ∧
          Pauli.hasXComponent (ErrorVec.mul (ErrorVec.identity spec.params.n)
            (ErrorVec.identity spec.params.n) q) = true).card = 0
      apply Finset.card_eq_zero.mpr
      apply Finset.filter_eq_empty_iff.mpr
      intro row _
      push_neg
      intro q _
      show Pauli.hasXComponent (ErrorVec.mul (ErrorVec.identity spec.params.n)
            (ErrorVec.identity spec.params.n) q) ≠ true
      have hI : ErrorVec.mul (ErrorVec.identity spec.params.n)
          (ErrorVec.identity spec.params.n) q = Pauli.I := rfl
      rw [hI]
      decide
    have h_omega_le : omegaPerpX spec (ErrorVec.identity spec.params.n) ≤ 0 := by
      have h_le := omegaPerpX_le_of_witness spec
                    (ErrorVec.identity spec.params.n)
                    (S := ErrorVec.identity spec.params.n)
                    InStab.identity
      rw [h_rowsX_zero] at h_le
      exact h_le
    have h_omega_zero : omegaPerpX spec (ErrorVec.identity spec.params.n) = 0 :=
      Nat.le_zero.mp h_omega_le
    show d - omegaPerpX spec (ErrorVec.identity spec.params.n) = (barZClass spec).d_L
    rw [h_omega_zero]
    rfl
  -- Property (ii): E in barZ coset → μ(E) = 0.
  mu_at_logical E h := by
    obtain ⟨hSyn, hLog⟩ := h
    -- Every witness gives rowsX ≥ d, so omegaPerpX ≥ d, so d - omegaPerpX = 0.
    have h_ge_d : ∀ k ∈ witnessedSpread spec E, k ≥ d := by
      intro k ⟨S, hS, hk⟩
      rw [hk]
      exact topological_lower_bound_general spec E hSyn hLog hS
    have h_omegaGe : omegaPerpX spec E ≥ d := by
      obtain ⟨S, hS, hrSpec⟩ := omegaPerpX_attained spec E
      have h_rS_in : rowsX spec S E ∈ witnessedSpread spec E := ⟨S, hS, rfl⟩
      have := h_ge_d _ h_rS_in
      omega
    show d - omegaPerpX spec E = 0
    omega
  -- Property (iii): μ(F · E) + |F| ≥ μ(E), via subadditivity of rowsX.
  mu_triangle E F := by
    show d - omegaPerpX spec (ErrorVec.mul F E) + ErrorVec.weight F ≥
          d - omegaPerpX spec E
    -- Pick a min-witness for E.
    obtain ⟨S, hS, hrSpec⟩ := omegaPerpX_attained spec E
    -- The same S gives `rowsX S (F · E) ≤ rowsX S E + |F| = ω⊥^X(E) + |F|`.
    have h_sub : rowsX spec S (ErrorVec.mul F E) ≤
                  rowsX spec S E + ErrorVec.weight F := rowsX_subadditive spec S E F
    -- Hence ω⊥^X(F · E) ≤ ω⊥^X(E) + |F|.
    have h_omega_sub : omegaPerpX spec (ErrorVec.mul F E) ≤
                        omegaPerpX spec E + ErrorVec.weight F := by
      calc omegaPerpX spec (ErrorVec.mul F E)
          ≤ rowsX spec S (ErrorVec.mul F E) :=
              omegaPerpX_le_of_witness spec _ hS
        _ ≤ rowsX spec S E + ErrorVec.weight F := h_sub
        _ = omegaPerpX spec E + ErrorVec.weight F := by rw [hrSpec]
    omega

/-! ## NZ scheduling is L-aligned for the surface barrier -/

/-- The `hook_spread_bound` axiom of `NZSurfaceSpec` translates to
    `IsLAligned` for the witness-min barrier function: every back-action
    error drops the surface barrier by at most one. -/
theorem surface_isLAligned (spec : NZSurfaceSpec d) :
    IsLAligned (surfaceBarrier spec) := by
  intro s_idx e_B he E
  -- Goal: μ(e_B · E) + 1 ≥ μ(E), i.e.,
  --       d - ω⊥^X(e_B · E) + 1 ≥ d - ω⊥^X(E).
  -- Equivalent (in Nat with care): ω⊥^X(e_B · E) ≤ ω⊥^X(E) + 1.
  show d - omegaPerpX spec (ErrorVec.mul e_B E) + 1 ≥
        d - omegaPerpX spec E
  -- Use a min-witness for E, then apply hook_spread_bound to get a witness
  -- S' for e_B · E with rowsX S' (e_B · E) ≤ rowsX S E + 1.
  obtain ⟨S, hS, hrSpec⟩ := omegaPerpX_attained spec E
  obtain ⟨S', hS', hbound⟩ := spec.hook_spread_bound s_idx e_B he E S hS
  -- hbound: rowsX(S' · e_B · E) ≤ rowsX(S · E) + 1 = ω⊥^X(E) + 1.
  have h_omega_step :
      omegaPerpX spec (ErrorVec.mul e_B E) ≤ omegaPerpX spec E + 1 := by
    calc omegaPerpX spec (ErrorVec.mul e_B E)
        ≤ rowsX spec S' (ErrorVec.mul e_B E) :=
            omegaPerpX_le_of_witness spec _ hS'
      _ ≤ rowsX spec S E + 1 := hbound
      _ = omegaPerpX spec E + 1 := by rw [hrSpec]
  omega

/-! ## End-to-end: distance preservation for the surface code -/

/-- **Surface code distance preservation as a `BarrierFunction` instance.**
    For any `NZSurfaceSpec d`, the surface code under NZ scheduling
    satisfies `C_budget − C ≥ d` at any done state with an undetected
    bar-Z (or bar-Y) logical error. This is exactly
    `BarrierFramework.distance_preservation` applied to the surface
    barrier; the chain
    `topological_lower_bound + perpendicular spread + hook_spread_bound`
    is now visible as `mu_at_logical + mu_triangle + IsLAligned`. -/
theorem surface_distance_preservation (spec : NZSurfaceSpec d)
    (s : State spec.params)
    (hrun : Run spec.params (.done s))
    (h_in : (barZClass spec).contains s.E_tilde) :
    spec.params.C_budget - s.C ≥ d :=
  distance_preservation (surfaceBarrier spec) (surface_isLAligned spec)
    s hrun h_in

end QStab.Paper.SurfaceBarrier
