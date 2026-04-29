import QStab.Examples.SurfaceGeneral
import QStab.Paper.BarrierFramework
import Mathlib.Data.Nat.Lattice

/-!
# Aligned codes as `BarrierFunction` instances (paper §6.5 generic case)

Constructs the perpendicular/column-spread barrier function
`β_Z̄ := max(0, d − ω(E))` as a `BarrierFunction` for any code
satisfying `AlignedCodeSpec d`. Applies uniformly to:

* the rotated surface code under NZ scheduling (rows as groups,
  see `Paper/SurfaceBarrier.lean`);
* hypergraph-product codes under any scheduling (Sector-1 columns
  as groups, see `Paper/HGPBarrier.lean`).

The "spread" function ω(E) := min over S ∈ Stab of |groups with
X-component in S·E| is implemented via `Nat.sInf` over the witness
set, using that the set is non-empty (`S = identity`) and the
minimum is attained.

**Zero sorry; only [propext, Classical.choice, Quot.sound] axioms.**
-/

namespace QStab.Paper.AlignedBarrier

open QStab QStab.Examples QStab.Examples.SurfaceGeneral QStab.Paper.BarrierFramework

variable {d : Nat}

/-! ## The witness-minimised group count -/

/-- Group count of `S · E` against the partition `spec.group`. -/
def groupsX (spec : AlignedCodeSpec d) (S E : ErrorVec spec.params.n) : Nat :=
  (Finset.univ.filter fun g : Fin d =>
    ∃ q : Fin spec.params.n, spec.group q = g ∧
      Pauli.hasXComponent (ErrorVec.mul S E q) = true).card

/-- The set of attainable spread values `groupsX(S, E)` over all
    stabilizer witnesses. Always non-empty (`S = identity`). -/
def witnessedSpread (spec : AlignedCodeSpec d) (E : ErrorVec spec.params.n) :
    Set Nat :=
  {k | ∃ S, InStab spec.params S ∧ k = groupsX spec S E}

/-- The witness set is non-empty: `S = identity` always witnesses some
    spread value. -/
theorem witnessedSpread_nonempty (spec : AlignedCodeSpec d)
    (E : ErrorVec spec.params.n) :
    (witnessedSpread spec E).Nonempty :=
  ⟨groupsX spec (ErrorVec.identity spec.params.n) E,
   ErrorVec.identity spec.params.n, InStab.identity, rfl⟩

/-- The aligned spread `ω(E) := min_{S ∈ S} groupsX(S, E)`. -/
noncomputable def omegaGroup (spec : AlignedCodeSpec d)
    (E : ErrorVec spec.params.n) : Nat :=
  sInf (witnessedSpread spec E)

/-- The minimum is attained: there exists a witness `S` with
    `groupsX spec S E = omegaGroup spec E`. -/
theorem omegaGroup_attained (spec : AlignedCodeSpec d)
    (E : ErrorVec spec.params.n) :
    ∃ S, InStab spec.params S ∧ groupsX spec S E = omegaGroup spec E := by
  have hmem : omegaGroup spec E ∈ witnessedSpread spec E :=
    Nat.sInf_mem (witnessedSpread_nonempty spec E)
  obtain ⟨S, hS, hk⟩ := hmem
  exact ⟨S, hS, hk.symm⟩

/-- For any witness `S` in the stabilizer subgroup, `omegaGroup` is at
    most `groupsX spec S E`. -/
theorem omegaGroup_le_of_witness (spec : AlignedCodeSpec d)
    (E : ErrorVec spec.params.n) {S : ErrorVec spec.params.n}
    (hS : InStab spec.params S) :
    omegaGroup spec E ≤ groupsX spec S E :=
  Nat.sInf_le ⟨S, hS, rfl⟩

/-! ## Pointwise lemma: changing one position changes at most one group -/

/-- If two error vectors agree everywhere except possibly at index `i`,
    the group counts differ by at most one. -/
private theorem groupsX_pointwise_le (spec : AlignedCodeSpec d)
    (F G : ErrorVec spec.params.n) (i : Fin spec.params.n)
    (h_ne : ∀ q : Fin spec.params.n, q ≠ i → F q = G q) :
    (Finset.univ.filter fun g : Fin d =>
      ∃ q : Fin spec.params.n, spec.group q = g ∧
        Pauli.hasXComponent (F q) = true).card ≤
    (Finset.univ.filter fun g : Fin d =>
      ∃ q : Fin spec.params.n, spec.group q = g ∧
        Pauli.hasXComponent (G q) = true).card + 1 := by
  set iGrp : Fin d := spec.group i
  set S_new := Finset.univ.filter fun g : Fin d =>
    ∃ q : Fin spec.params.n, spec.group q = g ∧
      Pauli.hasXComponent (F q) = true with hS_new
  set S_old := Finset.univ.filter fun g : Fin d =>
    ∃ q : Fin spec.params.n, spec.group q = g ∧
      Pauli.hasXComponent (G q) = true with hS_old
  have h_sub : S_new ⊆ S_old ∪ {iGrp} := by
    intro g h_mem
    have h_mem' := (Finset.mem_filter.mp h_mem).2
    obtain ⟨q, hq_grp, hq_has⟩ := h_mem'
    by_cases hqi : q = i
    · apply Finset.mem_union_right
      subst hqi
      exact Finset.mem_singleton.mpr (Eq.symm hq_grp)
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        q, hq_grp, by rw [← h_ne q hqi]; exact hq_has⟩
  calc S_new.card
      ≤ (S_old ∪ {iGrp}).card := Finset.card_le_card h_sub
    _ ≤ S_old.card + ({iGrp} : Finset (Fin d)).card := Finset.card_union_le _ _
    _ = S_old.card + 1 := by simp

/-! ## Subadditivity of `groupsX` in the multiplied factor -/

/-- If `F` is identity outside a finite set `T` (with size `k`), then
    `groupsX spec S (F · E) ≤ groupsX spec S E + k`. By induction on `k`. -/
private theorem groupsX_mul_le_card_support_aux
    (k : Nat) (spec : AlignedCodeSpec d)
    (S E F : ErrorVec spec.params.n) (T : Finset (Fin spec.params.n))
    (hT_card : T.card = k)
    (hT : ∀ q, q ∉ T → F q = Pauli.I) :
    groupsX spec S (ErrorVec.mul F E) ≤ groupsX spec S E + k := by
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
    have hT_pos : 0 < T.card := by rw [hT_card]; omega
    obtain ⟨i, hi_in⟩ := Finset.card_pos.mp hT_pos
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
    have hF'_le : groupsX spec S (ErrorVec.mul F' E) ≤
                  groupsX spec S E + k' :=
      ih F' T' hT'_card hF'_T'
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
    have h_step := groupsX_pointwise_le spec
      (ErrorVec.mul S (ErrorVec.mul F E))
      (ErrorVec.mul S (ErrorVec.mul F' E)) i h_diff
    show (Finset.univ.filter fun g : Fin d =>
      ∃ q : Fin spec.params.n, spec.group q = g ∧
        Pauli.hasXComponent (ErrorVec.mul S (ErrorVec.mul F E) q) = true).card
        ≤ groupsX spec S E + (k' + 1)
    have h_F'_eq : (Finset.univ.filter fun g : Fin d =>
      ∃ q : Fin spec.params.n, spec.group q = g ∧
        Pauli.hasXComponent (ErrorVec.mul S (ErrorVec.mul F' E) q) = true).card
        = groupsX spec S (ErrorVec.mul F' E) := rfl
    rw [h_F'_eq] at h_step
    omega

/-- Subadditivity: `groupsX spec S (F · E) ≤ groupsX spec S E + weight F`. -/
theorem groupsX_subadditive (spec : AlignedCodeSpec d)
    (S E F : ErrorVec spec.params.n) :
    groupsX spec S (ErrorVec.mul F E) ≤ groupsX spec S E + ErrorVec.weight F := by
  set T : Finset (Fin spec.params.n) :=
    Finset.univ.filter fun q => F q ≠ Pauli.I with hT_def
  have hT_card : T.card = ErrorVec.weight F := rfl
  have hT_outside : ∀ q, q ∉ T → F q = Pauli.I := by
    intro q hq
    by_contra hne
    apply hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ q, hne⟩
  exact groupsX_mul_le_card_support_aux _ spec S E F T hT_card hT_outside

/-! ## The bar-Z logical class for an aligned code -/

/-- The logical class for the bar-Z coset of an `AlignedCodeSpec`: all
    Pauli errors in the normalizer that anticommute with `logicalZ`.
    Both bar-Z and bar-Y cosets satisfy this. -/
def barZClass (spec : AlignedCodeSpec d) : LogicalClass spec.params where
  contains E :=
    (∀ i : Fin spec.params.numStab,
      ErrorVec.parity (spec.params.stabilizers i) E = false) ∧
    ErrorVec.parity spec.logicalZ E = true
  d_L := d
  d_L_pos := spec.hd_pos
  d_L_min E h := by
    obtain ⟨hSyn, hLog⟩ := h
    have hTLB := topological_lower_bound_aligned spec E hSyn hLog
                  (S := ErrorVec.identity spec.params.n) InStab.identity
    have hmul : ∀ q, ErrorVec.mul (ErrorVec.identity spec.params.n) E q = E q := by
      intro q; show Pauli.mul Pauli.I (E q) = E q; cases E q <;> rfl
    have hgroupcount : (Finset.univ.filter fun g : Fin d =>
        ∃ q : Fin spec.params.n, spec.group q = g ∧
          Pauli.hasXComponent (E q) = true).card ≥ d := by
      have heq : (Finset.univ.filter fun g : Fin d =>
          ∃ q : Fin spec.params.n, spec.group q = g ∧
            Pauli.hasXComponent (ErrorVec.mul (ErrorVec.identity spec.params.n) E q) = true)
          = (Finset.univ.filter fun g : Fin d =>
            ∃ q : Fin spec.params.n, spec.group q = g ∧
              Pauli.hasXComponent (E q) = true) := by
        apply Finset.filter_congr
        intro g _
        refine ⟨fun ⟨q, hq, hX⟩ => ⟨q, hq, ?_⟩,
                fun ⟨q, hq, hX⟩ => ⟨q, hq, ?_⟩⟩
        · rw [hmul q] at hX; exact hX
        · rw [hmul q]; exact hX
      rw [← heq]; exact hTLB
    -- Bridge "groups with X" to "support of E" via the image of the
    -- subset {q | hasX(E q)} under spec.group.
    set GroupsX : Finset (Fin d) := Finset.univ.filter fun g : Fin d =>
      ∃ q : Fin spec.params.n, spec.group q = g ∧
        Pauli.hasXComponent (E q) = true with hGroupsX_def
    set SupportX : Finset (Fin spec.params.n) := Finset.univ.filter fun q =>
      Pauli.hasXComponent (E q) = true with hSupportX_def
    -- GroupsX is the image of SupportX under spec.group.
    have h_image_eq : GroupsX = SupportX.image spec.group := by
      apply Finset.ext
      intro g
      simp only [hGroupsX_def, hSupportX_def, Finset.mem_filter, Finset.mem_univ,
                 true_and, Finset.mem_image]
      constructor
      · rintro ⟨q, hg, hX⟩; exact ⟨q, hX, hg⟩
      · rintro ⟨q, hX, hg⟩; exact ⟨q, hg, hX⟩
    -- |GroupsX| ≤ |SupportX| by Finset.card_image_le.
    have h_groupsX_le_supportX : GroupsX.card ≤ SupportX.card := by
      rw [h_image_eq]; exact Finset.card_image_le
    -- SupportX ⊆ {q | E q ≠ I} since hasXComp implies non-identity.
    have h_supportX_sub : SupportX ⊆
        Finset.univ.filter fun q : Fin spec.params.n => E q ≠ Pauli.I := by
      intro q hq
      have hX : Pauli.hasXComponent (E q) = true := (Finset.mem_filter.mp hq).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hI
      rw [hI] at hX
      simp [Pauli.hasXComponent] at hX
    have h_supportX_le_weight : SupportX.card ≤ ErrorVec.weight E := by
      have h_w_eq : ErrorVec.weight E =
          (Finset.univ.filter fun q : Fin spec.params.n => E q ≠ Pauli.I).card := rfl
      rw [h_w_eq]
      exact Finset.card_le_card h_supportX_sub
    -- Chain: d ≤ |GroupsX| ≤ |SupportX| ≤ weight E.
    show ErrorVec.weight E ≥ d
    have h_GroupsX_ge : GroupsX.card ≥ d := hgroupcount
    omega

/-! ## The barrier function for an aligned code -/

/-- The aligned-code spread barrier as a `BarrierFunction` for the bar-Z
    coset (paper Corollary `thm:PerpBarrier` / `thm:HGPColBarrier`). -/
noncomputable def alignedBarrier (spec : AlignedCodeSpec d) :
    BarrierFunction spec.params (barZClass spec) where
  mu E := d - omegaGroup spec E
  mu_identity := by
    have h_groupsX_zero :
        groupsX spec (ErrorVec.identity spec.params.n)
                (ErrorVec.identity spec.params.n) = 0 := by
      show (Finset.univ.filter fun g : Fin d =>
        ∃ q : Fin spec.params.n, spec.group q = g ∧
          Pauli.hasXComponent (ErrorVec.mul (ErrorVec.identity spec.params.n)
            (ErrorVec.identity spec.params.n) q) = true).card = 0
      apply Finset.card_eq_zero.mpr
      apply Finset.filter_eq_empty_iff.mpr
      intro g _
      push_neg
      intro q _
      show Pauli.hasXComponent (ErrorVec.mul (ErrorVec.identity spec.params.n)
            (ErrorVec.identity spec.params.n) q) ≠ true
      have hI : ErrorVec.mul (ErrorVec.identity spec.params.n)
          (ErrorVec.identity spec.params.n) q = Pauli.I := rfl
      rw [hI]
      decide
    have h_omega_le : omegaGroup spec (ErrorVec.identity spec.params.n) ≤ 0 := by
      have h_le := omegaGroup_le_of_witness spec
                    (ErrorVec.identity spec.params.n)
                    (S := ErrorVec.identity spec.params.n)
                    InStab.identity
      rw [h_groupsX_zero] at h_le
      exact h_le
    have h_omega_zero : omegaGroup spec (ErrorVec.identity spec.params.n) = 0 :=
      Nat.le_zero.mp h_omega_le
    show d - omegaGroup spec (ErrorVec.identity spec.params.n) =
          (barZClass spec).d_L
    rw [h_omega_zero]
    rfl
  mu_at_logical E h := by
    obtain ⟨hSyn, hLog⟩ := h
    have h_ge_d : ∀ k ∈ witnessedSpread spec E, k ≥ d := by
      intro k ⟨S, hS, hk⟩
      rw [hk]
      exact topological_lower_bound_aligned spec E hSyn hLog hS
    have h_omegaGe : omegaGroup spec E ≥ d := by
      obtain ⟨S, hS, hrSpec⟩ := omegaGroup_attained spec E
      have h_in : groupsX spec S E ∈ witnessedSpread spec E := ⟨S, hS, rfl⟩
      have := h_ge_d _ h_in
      omega
    show d - omegaGroup spec E = 0
    omega
  mu_triangle E F := by
    show d - omegaGroup spec (ErrorVec.mul F E) + ErrorVec.weight F ≥
          d - omegaGroup spec E
    obtain ⟨S, hS, hrSpec⟩ := omegaGroup_attained spec E
    have h_sub : groupsX spec S (ErrorVec.mul F E) ≤
                  groupsX spec S E + ErrorVec.weight F :=
      groupsX_subadditive spec S E F
    have h_omega_sub : omegaGroup spec (ErrorVec.mul F E) ≤
                        omegaGroup spec E + ErrorVec.weight F := by
      calc omegaGroup spec (ErrorVec.mul F E)
          ≤ groupsX spec S (ErrorVec.mul F E) :=
              omegaGroup_le_of_witness spec _ hS
        _ ≤ groupsX spec S E + ErrorVec.weight F := h_sub
        _ = omegaGroup spec E + ErrorVec.weight F := by rw [hrSpec]
    omega

/-! ## L-alignment from `hook_spread_bound` -/

/-- The `hook_spread_bound` axiom of `AlignedCodeSpec` translates to
    `IsLAligned` for the witness-min barrier function. -/
theorem aligned_isLAligned (spec : AlignedCodeSpec d) :
    IsLAligned (alignedBarrier spec) := by
  intro s_idx e_B he E
  show d - omegaGroup spec (ErrorVec.mul e_B E) + 1 ≥
        d - omegaGroup spec E
  obtain ⟨S, hS, hrSpec⟩ := omegaGroup_attained spec E
  obtain ⟨S', hS', hbound⟩ := spec.hook_spread_bound s_idx e_B he E S hS
  have h_omega_step :
      omegaGroup spec (ErrorVec.mul e_B E) ≤ omegaGroup spec E + 1 := by
    calc omegaGroup spec (ErrorVec.mul e_B E)
        ≤ groupsX spec S' (ErrorVec.mul e_B E) :=
            omegaGroup_le_of_witness spec _ hS'
      _ ≤ groupsX spec S E + 1 := hbound
      _ = omegaGroup spec E + 1 := by rw [hrSpec]
  omega

/-! ## End-to-end: distance preservation for any aligned code -/

/-- **Distance preservation as a `BarrierFunction` instance, generic
    over `AlignedCodeSpec`.** Any code satisfying the aligned-code
    framework has `C_budget − C ≥ d` at any done state with an
    undetected bar-Z (or bar-Y) logical error. Specialised to
    surface (NZ scheduling) and HGP codes in the corresponding files. -/
theorem aligned_distance_preservation (spec : AlignedCodeSpec d)
    (s : State spec.params)
    (hrun : Run spec.params (.done s))
    (h_in : (barZClass spec).contains s.E_tilde) :
    spec.params.C_budget - s.C ≥ d :=
  distance_preservation (alignedBarrier spec)
    (aligned_isLAligned spec) s hrun h_in

end QStab.Paper.AlignedBarrier
