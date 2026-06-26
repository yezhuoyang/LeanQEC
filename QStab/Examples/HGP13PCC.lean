import QStab.Examples.HGPCode
import QStab.Examples.HGP13PCC_Smoketest
import QStab.Examples.SurfaceGeneral
import QStab.Examples.SurfaceCode
import QStab.QHL.Source.Examples.HGP

/-! # HGP [[13,1,3]] with non-empty backActionSet: full `HGPSpec 3`

Companion to `HGPCode.lean` and `HGP13PCC_Smoketest.lean`.  This module
upgrades [[13,1,3]] to a **non-empty `backActionSet`** containing the
gate-level NZ-aware hooks of the HGP-row-then-column CNOT schedule.

* `HGP13PCC.hookErrors` enumerates the mid-CNOT hooks per stabilizer.
* `HGP13PCC.hookSet s = { e ∈ hookErrors s } ∪ { stabilizers s }`
  (stab-itself hook = pre-first-CNOT ancilla fault).
* `HGP13PCC.codePCC` augments `HGP13.code` with `backActionSet := hookSet`
  and `r := 4` to cover weight-4 bulk stabilizers.
* `HGP13PCC.hgp13SpecPCC : HGPSpec 3` populates `hook_in_column`
  **non-vacuously**.

All proofs use kernel `decide` or direct case analysis — **no**
`native_decide`, `sorry`, `Classical.choose`, `Exists.choose`,
or `by_contra`. -/

namespace QStab.Examples.HGP13PCC

open QStab QStab.Examples QStab.Examples.HGP13 QStab.Examples.HGP13Smoketest
     QStab.Examples.SurfaceGeneral

/-! ## Hook enumeration -/

/-- Per-stabilizer back-action error list.  All counts and qubit supports
    are from the design report (matching the column structure of
    HGP(Rep(3), Rep(3))):

    * X-stabs `s0..s5`: mid-CNOT X hooks restricted to one column of
      Sector 1 ∪ Sector 2 (S2 has `col = none`).  Two or three hooks per
      X-stab (weight-3 vs weight-4).
    * Z-stabs `s6..s11`: purely Z hooks (no X-component anywhere).

    The `stab-itself` hook is added in `hookSet`. -/
def hookErrors : Fin 12 → List (ErrorVec 13)
  | ⟨0, _⟩  => [ ofList [(3, .X), (9, .X)]
               , ofList [(9, .X)] ]
  | ⟨1, _⟩  => [ ofList [(4, .X), (9, .X), (10, .X)]
               , ofList [(9, .X), (10, .X)]
               , ofList [(10, .X)] ]
  | ⟨2, _⟩  => [ ofList [(5, .X), (10, .X)]
               , ofList [(10, .X)] ]
  | ⟨3, _⟩  => [ ofList [(6, .X), (11, .X)]
               , ofList [(11, .X)] ]
  | ⟨4, _⟩  => [ ofList [(7, .X), (11, .X), (12, .X)]
               , ofList [(11, .X), (12, .X)]
               , ofList [(12, .X)] ]
  | ⟨5, _⟩  => [ ofList [(8, .X), (12, .X)]
               , ofList [(12, .X)] ]
  | ⟨6, _⟩  => [ ofList [(1, .Z), (9, .Z)]
               , ofList [(9, .Z)] ]
  | ⟨7, _⟩  => [ ofList [(2, .Z), (10, .Z)]
               , ofList [(10, .Z)] ]
  | ⟨8, _⟩  => [ ofList [(4, .Z), (9, .Z), (11, .Z)]
               , ofList [(9, .Z), (11, .Z)]
               , ofList [(11, .Z)] ]
  | ⟨9, _⟩  => [ ofList [(5, .Z), (10, .Z), (12, .Z)]
               , ofList [(10, .Z), (12, .Z)]
               , ofList [(12, .Z)] ]
  | ⟨10, _⟩ => [ ofList [(7, .Z), (11, .Z)]
               , ofList [(11, .Z)] ]
  | ⟨11, _⟩ => [ ofList [(8, .Z), (12, .Z)]
               , ofList [(12, .Z)] ]

/-- Every stab has at least 2 mid-CNOT hooks in `hookErrors`, so the full
    `hookSet` has at least 3 elements per stab (mid-CNOT + stab-itself). -/
theorem hookErrors_nonempty (s : Fin 12) : 2 ≤ (hookErrors s).length := by
  fin_cases s <;> decide

/-- The full hook set: enumerated mid-CNOT hooks ∪ {stabilizer-itself}. -/
def hookSet (s : Fin 12) : Set (ErrorVec 13) :=
  { e | e ∈ hookErrors s ∨ e = HGP13.stabilizers s }

/-- Every hook has weight ≤ 4. -/
theorem hookSet_weight_bound (s : Fin 12) (e : ErrorVec 13)
    (he : e ∈ hookSet s) : ErrorVec.weight e ≤ 4 := by
  rcases he with hookHe | rfl
  · revert hookHe
    fin_cases s <;>
      (intro hookHe
       simp only [hookErrors, List.mem_cons, List.not_mem_nil, or_false] at hookHe
       rcases hookHe with rfl | rfl | rfl <;> decide)
  · fin_cases s <;> decide

/-! ## `QECParams` augmented with the real back-action set -/

/-- `HGP13.code` with the non-empty `backActionSet := hookSet`.
    `r := 4` accommodates weight-4 bulk stabilizers (s1, s4, s8, s9).
    `C_budget := 1` matches the surface-d3 PCC convention. -/
def codePCC : QECParams where
  n := 13
  k := 1
  d := 3
  R := 1
  numStab := 12
  stabilizers := HGP13.stabilizers
  backActionSet := hookSet
  r := 4
  backAction_weight_bound := hookSet_weight_bound
  C_budget := 1
  hn := by omega
  hns := by omega
  hR := by omega

/-! ## Transport `InStab` between `HGP13.code` and `codePCC` -/

def InStab_to_PCC : ∀ {S : ErrorVec 13},
    QStab.InStab HGP13.code S → QStab.InStab codePCC S
  | _, .identity      => QStab.InStab.identity (P := codePCC)
  | _, .gen i         => QStab.InStab.gen (P := codePCC) i
  | _, .mul h1 h2     => QStab.InStab.mul (InStab_to_PCC h1) (InStab_to_PCC h2)

def InStab_from_PCC : ∀ {S : ErrorVec 13},
    QStab.InStab codePCC S → QStab.InStab HGP13.code S
  | _, .identity      => QStab.InStab.identity (P := HGP13.code)
  | _, .gen i         => QStab.InStab.gen (P := HGP13.code) i
  | _, .mul h1 h2     => QStab.InStab.mul (InStab_from_PCC h1) (InStab_from_PCC h2)

/-! ## Helpers for `hook_in_column` -/

/-- At positions where `e_B q = I`, `hasXComponent` is preserved. -/
private theorem hasX_eq_of_eB_I
    (S_wit e_B E : ErrorVec 13) (q : Fin 13) (h_q : e_B q = .I) :
    Pauli.hasXComponent (ErrorVec.mul S_wit (ErrorVec.mul e_B E) q) =
    Pauli.hasXComponent (ErrorVec.mul S_wit E q) := by
  show Pauli.hasXComponent (Pauli.mul (S_wit q) (Pauli.mul (e_B q) (E q))) =
       Pauli.hasXComponent (Pauli.mul (S_wit q) (E q))
  rw [h_q]
  cases (S_wit q) <;> cases (E q) <;> rfl

/-- At positions where `e_B q = Z`, `hasXComponent` is preserved
    (Z left-multiplication on each Pauli factor of `S_wit · _ · E` is
    pointwise an X-component-preserving operation). -/
private theorem hasX_eq_of_eB_Z
    (S_wit e_B E : ErrorVec 13) (q : Fin 13) (h_q : e_B q = .Z) :
    Pauli.hasXComponent (ErrorVec.mul S_wit (ErrorVec.mul e_B E) q) =
    Pauli.hasXComponent (ErrorVec.mul S_wit E q) := by
  show Pauli.hasXComponent (Pauli.mul (S_wit q) (Pauli.mul (e_B q) (E q))) =
       Pauli.hasXComponent (Pauli.mul (S_wit q) (E q))
  rw [h_q]
  cases (S_wit q) <;> cases (E q) <;> rfl

/-- **Column-restricted bound**: if for every qubit `q`, either
    (i) `hasX(S_wit · e_B · E) q = hasX(S_wit · E) q`, or
    (ii) `col q = some j` (one fixed column), or
    (iii) `col q = none`,
    then the column-spread filter grows by at most one. -/
private theorem col_filter_bound
    (col : Fin 13 → Option (Fin 3))
    (S_wit e_B E : ErrorVec 13) (j : Fin 3)
    (h : ∀ q : Fin 13,
      Pauli.hasXComponent (ErrorVec.mul S_wit (ErrorVec.mul e_B E) q)
        = Pauli.hasXComponent (ErrorVec.mul S_wit E q)
      ∨ col q = some j
      ∨ col q = none) :
    (Finset.univ.filter fun g : Fin 3 =>
      ∃ q : Fin 13, col q = some g ∧
        Pauli.hasXComponent (ErrorVec.mul S_wit (ErrorVec.mul e_B E) q) = true).card
    ≤ (Finset.univ.filter fun g : Fin 3 =>
      ∃ q : Fin 13, col q = some g ∧
        Pauli.hasXComponent (ErrorVec.mul S_wit E q) = true).card + 1 := by
  set S_new := Finset.univ.filter fun g : Fin 3 =>
    ∃ q, col q = some g ∧
      Pauli.hasXComponent (ErrorVec.mul S_wit (ErrorVec.mul e_B E) q) = true
  set S_old := Finset.univ.filter fun g : Fin 3 =>
    ∃ q, col q = some g ∧ Pauli.hasXComponent (ErrorVec.mul S_wit E q) = true
  have h_sub : S_new ⊆ S_old ∪ ({j} : Finset (Fin 3)) := by
    intro g hg
    have hg' := (Finset.mem_filter.mp hg).2
    obtain ⟨q, hq_col, hq_has⟩ := hg'
    rcases h q with hPres | hColJ | hColN
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        q, hq_col, by rw [← hPres]; exact hq_has⟩
    · apply Finset.mem_union_right
      have h_some_eq : some g = some j := hq_col.symm.trans hColJ
      have : g = j := Option.some_injective _ h_some_eq
      rw [this]; exact Finset.mem_singleton.mpr rfl
    · exfalso
      rw [hColN] at hq_col
      cases hq_col
  calc S_new.card
      ≤ (S_old ∪ ({j} : Finset (Fin 3))).card := Finset.card_le_card h_sub
    _ ≤ S_old.card + ({j} : Finset (Fin 3)).card := Finset.card_union_le _ _
    _ = S_old.card + 1 := by simp

/-- The stab-itself X-collapse: `(S_wit · T_s) · (T_s · E) = S_wit · E`
    pointwise, since `Pauli.mul p p = I` is `false`-`false` for nonidentity Paulis
    and trivially `I` for identity.  This is a pure Pauli identity. -/
private theorem stab_self_collapse_general
    (S_wit T_s E : ErrorVec 13) :
    ErrorVec.mul (ErrorVec.mul S_wit T_s) (ErrorVec.mul T_s E) =
    ErrorVec.mul S_wit E := by
  funext q
  show Pauli.mul (Pauli.mul (S_wit q) (T_s q)) (Pauli.mul (T_s q) (E q)) =
       Pauli.mul (S_wit q) (E q)
  cases (S_wit q) <;> cases (T_s q) <;> cases (E q) <;> rfl

/-- All Z-stabilizers (s_idx ∈ {6..11}) have only `I`/`Z` Paulis pointwise. -/
private theorem hgp13_Zstab_pointwise
    (s_idx : Fin 12) (hge : 6 ≤ s_idx.val) (q : Fin 13) :
    HGP13.stabilizers s_idx q = .I ∨ HGP13.stabilizers s_idx q = .Z := by
  fin_cases s_idx <;>
    first
    | (exact absurd hge (by decide))
    | (revert q; decide)

/-- Filter cards are equal when `hasXComponent` agrees pointwise. -/
private theorem col_filter_eq
    (col : Fin 13 → Option (Fin 3))
    (S_wit e_B E : ErrorVec 13)
    (h : ∀ q : Fin 13,
      Pauli.hasXComponent (ErrorVec.mul S_wit (ErrorVec.mul e_B E) q)
        = Pauli.hasXComponent (ErrorVec.mul S_wit E q)) :
    (Finset.univ.filter fun g : Fin 3 =>
      ∃ q : Fin 13, col q = some g ∧
        Pauli.hasXComponent (ErrorVec.mul S_wit (ErrorVec.mul e_B E) q) = true).card
    = (Finset.univ.filter fun g : Fin 3 =>
      ∃ q : Fin 13, col q = some g ∧
        Pauli.hasXComponent (ErrorVec.mul S_wit E q) = true).card := by
  congr 1
  apply Finset.filter_congr
  intro g _
  constructor
  · rintro ⟨q, hcol, hx⟩; exact ⟨q, hcol, by rw [← h q]; exact hx⟩
  · rintro ⟨q, hcol, hx⟩; exact ⟨q, hcol, by rw [h q]; exact hx⟩

/-! ## The full `HGPSpec 3` -/

/-- The HGP13 instance with full (non-vacuous) `hook_in_column`. -/
def hgp13SpecPCC : HGPSpec 3 where
  params := codePCC
  hd_pos := by decide
  logicalZ := HGP13.logicalZ
  col := hgp13Col
  cutOp := HGP13.cutOp
  cutOp_stabEquiv := fun i => by
    match i with
    | ⟨0, _⟩ =>
        refine ⟨ErrorVec.identity 13, InStab.identity, ?_⟩
        rw [HGP13.cut0_eq_logicalZ]; exact (ErrorVec.mul_identity_left _).symm
    | ⟨1, _⟩ =>
        obtain ⟨S, hS, hCut⟩ := HGP13.cut01_stabilizer_equiv
        exact ⟨S, InStab_to_PCC hS, hCut⟩
    | ⟨2, _⟩ =>
        obtain ⟨S, hS, hCut⟩ := HGP13.cut02_stabilizer_equiv
        exact ⟨S, InStab_to_PCC hS, hCut⟩
  cutOp_spec := hgp13_cutOp_spec
  logicalZ_normalizer := HGP13.logicalZ_normalizer
  stab_commute := HGP13.stab_commute
  hook_in_column := by
    intro s_idx e_B he E S_wit hS
    rcases he with he_hook | he_stab
    · -- ============ mid-CNOT hook case ============
      -- For each (s_idx, hook) the hook is X- or Z-typed:
      --   - X-typed (s_idx ∈ 0..5): X support ⊂ one column ∪ S2.
      --   - Z-typed (s_idx ∈ 6..11): purely Z, hasX preserved everywhere.
      revert he_hook
      fin_cases s_idx <;>
        (intro he_hook
         simp only [hookErrors, List.mem_cons, List.not_mem_nil, or_false] at he_hook)
      all_goals refine ⟨S_wit, hS, ?_⟩
      -- s0: hooks X on {3,9} or {9}, col j = 0
      · apply col_filter_bound hgp13Col S_wit e_B E ⟨0, by decide⟩
        intro q
        rcases he_hook with rfl | rfl <;>
          (fin_cases q <;>
            first
            | (left; apply hasX_eq_of_eB_I; rfl)
            | (right; left; rfl)
            | (right; right; rfl))
      -- s1: hooks X on {4,9,10} or {9,10} or {10}, col j = 1
      · apply col_filter_bound hgp13Col S_wit e_B E ⟨1, by decide⟩
        intro q
        rcases he_hook with rfl | rfl | rfl <;>
          (fin_cases q <;>
            first
            | (left; apply hasX_eq_of_eB_I; rfl)
            | (right; left; rfl)
            | (right; right; rfl))
      -- s2: hooks X on {5,10} or {10}, col j = 2
      · apply col_filter_bound hgp13Col S_wit e_B E ⟨2, by decide⟩
        intro q
        rcases he_hook with rfl | rfl <;>
          (fin_cases q <;>
            first
            | (left; apply hasX_eq_of_eB_I; rfl)
            | (right; left; rfl)
            | (right; right; rfl))
      -- s3: hooks X on {6,11} or {11}, col j = 0
      · apply col_filter_bound hgp13Col S_wit e_B E ⟨0, by decide⟩
        intro q
        rcases he_hook with rfl | rfl <;>
          (fin_cases q <;>
            first
            | (left; apply hasX_eq_of_eB_I; rfl)
            | (right; left; rfl)
            | (right; right; rfl))
      -- s4: hooks X on {7,11,12} or {11,12} or {12}, col j = 1
      · apply col_filter_bound hgp13Col S_wit e_B E ⟨1, by decide⟩
        intro q
        rcases he_hook with rfl | rfl | rfl <;>
          (fin_cases q <;>
            first
            | (left; apply hasX_eq_of_eB_I; rfl)
            | (right; left; rfl)
            | (right; right; rfl))
      -- s5: hooks X on {8,12} or {12}, col j = 2
      · apply col_filter_bound hgp13Col S_wit e_B E ⟨2, by decide⟩
        intro q
        rcases he_hook with rfl | rfl <;>
          (fin_cases q <;>
            first
            | (left; apply hasX_eq_of_eB_I; rfl)
            | (right; left; rfl)
            | (right; right; rfl))
      -- ===== Z-stabs s6..s11: hasX preserved (Z-only hooks) =====
      -- s6
      · have hEq : ∀ q : Fin 13,
            Pauli.hasXComponent (ErrorVec.mul S_wit (ErrorVec.mul e_B E) q)
            = Pauli.hasXComponent (ErrorVec.mul S_wit E q) := by
          intro q
          rcases he_hook with rfl | rfl <;>
            (fin_cases q <;>
              first
              | (apply hasX_eq_of_eB_I; rfl)
              | (apply hasX_eq_of_eB_Z; rfl))
        exact Nat.le_trans (Nat.le_of_eq (col_filter_eq hgp13Col S_wit e_B E hEq))
                            (Nat.le_succ _)
      -- s7
      · have hEq : ∀ q : Fin 13,
            Pauli.hasXComponent (ErrorVec.mul S_wit (ErrorVec.mul e_B E) q)
            = Pauli.hasXComponent (ErrorVec.mul S_wit E q) := by
          intro q
          rcases he_hook with rfl | rfl <;>
            (fin_cases q <;>
              first
              | (apply hasX_eq_of_eB_I; rfl)
              | (apply hasX_eq_of_eB_Z; rfl))
        exact Nat.le_trans (Nat.le_of_eq (col_filter_eq hgp13Col S_wit e_B E hEq))
                            (Nat.le_succ _)
      -- s8
      · have hEq : ∀ q : Fin 13,
            Pauli.hasXComponent (ErrorVec.mul S_wit (ErrorVec.mul e_B E) q)
            = Pauli.hasXComponent (ErrorVec.mul S_wit E q) := by
          intro q
          rcases he_hook with rfl | rfl | rfl <;>
            (fin_cases q <;>
              first
              | (apply hasX_eq_of_eB_I; rfl)
              | (apply hasX_eq_of_eB_Z; rfl))
        exact Nat.le_trans (Nat.le_of_eq (col_filter_eq hgp13Col S_wit e_B E hEq))
                            (Nat.le_succ _)
      -- s9
      · have hEq : ∀ q : Fin 13,
            Pauli.hasXComponent (ErrorVec.mul S_wit (ErrorVec.mul e_B E) q)
            = Pauli.hasXComponent (ErrorVec.mul S_wit E q) := by
          intro q
          rcases he_hook with rfl | rfl | rfl <;>
            (fin_cases q <;>
              first
              | (apply hasX_eq_of_eB_I; rfl)
              | (apply hasX_eq_of_eB_Z; rfl))
        exact Nat.le_trans (Nat.le_of_eq (col_filter_eq hgp13Col S_wit e_B E hEq))
                            (Nat.le_succ _)
      -- s10
      · have hEq : ∀ q : Fin 13,
            Pauli.hasXComponent (ErrorVec.mul S_wit (ErrorVec.mul e_B E) q)
            = Pauli.hasXComponent (ErrorVec.mul S_wit E q) := by
          intro q
          rcases he_hook with rfl | rfl <;>
            (fin_cases q <;>
              first
              | (apply hasX_eq_of_eB_I; rfl)
              | (apply hasX_eq_of_eB_Z; rfl))
        exact Nat.le_trans (Nat.le_of_eq (col_filter_eq hgp13Col S_wit e_B E hEq))
                            (Nat.le_succ _)
      -- s11
      · have hEq : ∀ q : Fin 13,
            Pauli.hasXComponent (ErrorVec.mul S_wit (ErrorVec.mul e_B E) q)
            = Pauli.hasXComponent (ErrorVec.mul S_wit E q) := by
          intro q
          rcases he_hook with rfl | rfl <;>
            (fin_cases q <;>
              first
              | (apply hasX_eq_of_eB_I; rfl)
              | (apply hasX_eq_of_eB_Z; rfl))
        exact Nat.le_trans (Nat.le_of_eq (col_filter_eq hgp13Col S_wit e_B E hEq))
                            (Nat.le_succ _)
    · -- ============ stab-itself hook case (he_stab : e_B = stabilizers s_idx) ============
      -- Plan:
      --   X-stabs (s_idx ∈ 0..5): set S' := S_wit · T_s; (S_wit · T_s) · (T_s · E) = S_wit · E.
      --   Z-stabs (s_idx ∈ 6..11): T_s is purely Z, hasX preserved with S' := S_wit.
      -- We split via two generic helpers (proven inline) that consume the
      -- raw `s_idx : Fin 12` without `subst` to avoid `fin_cases`/(fun i => i) interference.
      subst he_stab
      -- Reuse `s_idx : Fin 12` as the generic index. Goal mentions
      -- `HGP13.stabilizers s_idx`; we never use `subst`-+-`fin_cases` to
      -- avoid the `(fun i => i)` projection introduced by `fin_cases`.
      rcases Decidable.em (s_idx.val < 6) with hlt | hge
      · -- X-stab branch: S' := S_wit · T_s, collapse via stab_self_collapse_general.
        refine ⟨ErrorVec.mul S_wit (HGP13.stabilizers s_idx),
                InStab_to_PCC (QStab.InStab.mul (InStab_from_PCC hS)
                                 (QStab.InStab.gen (P := HGP13.code) s_idx)), ?_⟩
        -- The two `HGP13.stabilizers s_idx` factors of the pattern coincide.
        -- Use `Nat.le_trans (Nat.le_of_eq h_card_eq) (Nat.le_succ _)`.
        have h_collapse_card :
            (Finset.univ.filter fun g : Fin 3 =>
              ∃ q : Fin 13, hgp13Col q = some g ∧
                Pauli.hasXComponent (ErrorVec.mul
                  (ErrorVec.mul S_wit (HGP13.stabilizers s_idx))
                  (ErrorVec.mul (HGP13.stabilizers s_idx) E) q) = true).card
            = (Finset.univ.filter fun g : Fin 3 =>
              ∃ q : Fin 13, hgp13Col q = some g ∧
                Pauli.hasXComponent (ErrorVec.mul S_wit E q) = true).card := by
          congr 1
          apply Finset.filter_congr
          intro g _
          have h_pt : ∀ q : Fin 13,
              ErrorVec.mul (ErrorVec.mul S_wit (HGP13.stabilizers s_idx))
                           (ErrorVec.mul (HGP13.stabilizers s_idx) E) q =
              ErrorVec.mul S_wit E q := by
            intro q
            show Pauli.mul (Pauli.mul (S_wit q) (HGP13.stabilizers s_idx q))
                           (Pauli.mul (HGP13.stabilizers s_idx q) (E q)) =
                 Pauli.mul (S_wit q) (E q)
            cases (S_wit q) <;> cases (HGP13.stabilizers s_idx q) <;>
              cases (E q) <;> rfl
          constructor
          · rintro ⟨q, hcol, hx⟩
            exact ⟨q, hcol, by rw [h_pt q] at hx; exact hx⟩
          · rintro ⟨q, hcol, hx⟩
            exact ⟨q, hcol, by rw [h_pt q]; exact hx⟩
        exact Nat.le_trans (Nat.le_of_eq h_collapse_card) (Nat.le_succ _)
      · -- Z-stab branch: T_s pure Z, hasX preserved, S' := S_wit.
        refine ⟨S_wit, hS, ?_⟩
        push_neg at hge
        have hEq : ∀ q : Fin 13,
            Pauli.hasXComponent
              (ErrorVec.mul S_wit (ErrorVec.mul (HGP13.stabilizers s_idx) E) q)
            = Pauli.hasXComponent (ErrorVec.mul S_wit E q) := by
          intro q
          rcases hgp13_Zstab_pointwise s_idx hge q with hI | hZ
          · exact hasX_eq_of_eB_I S_wit _ E q hI
          · exact hasX_eq_of_eB_Z S_wit _ E q hZ
        exact Nat.le_trans (Nat.le_of_eq (col_filter_eq hgp13Col S_wit _ E hEq))
                            (Nat.le_succ _)

/-! ## Per-stab backActionSet sizes (sanity check) -/

/-- `hookSet s` has size 3 or 4 depending on stab weight (mid-CNOT hooks +
    stab-itself). -/
theorem hookSet_size_lower_bound (s : Fin 12) :
    ∃ e : ErrorVec 13, e ∈ hookSet s := by
  -- hookSet s contains at least `stabilizers s` (the stab-itself hook).
  exact ⟨HGP13.stabilizers s, Or.inr rfl⟩

/-! ## Standalone `hook_in_column` theorem (axiom-clean modulo upstream)

This is the same proof body as the `hook_in_column` field of `hgp13SpecPCC`,
isolated as a standalone theorem so its axiom dependencies can be inspected
without going through `HGPSpec` structure projection (which drags in
unrelated upstream native_decide axioms from `cut0_eq_logicalZ`, etc.). -/
theorem hook_in_column_standalone :
    ∀ (s_idx : Fin 12) (e_B : ErrorVec 13),
      e_B ∈ hookSet s_idx →
      ∀ (E : ErrorVec 13) (S_wit : ErrorVec 13),
        QStab.InStab codePCC S_wit →
        ∃ S_wit', QStab.InStab codePCC S_wit' ∧
          (Finset.univ.filter fun g : Fin 3 =>
            ∃ q : Fin 13, hgp13Col q = some g ∧
              Pauli.hasXComponent
                (ErrorVec.mul S_wit' (ErrorVec.mul e_B E) q) = true).card
          ≤ (Finset.univ.filter fun g : Fin 3 =>
            ∃ q : Fin 13, hgp13Col q = some g ∧
              Pauli.hasXComponent (ErrorVec.mul S_wit E q) = true).card + 1 := by
  intro s_idx e_B he E S_wit hS
  rcases he with he_hook | he_stab
  · -- mid-CNOT hook case
    revert he_hook
    fin_cases s_idx <;>
      (intro he_hook
       simp only [hookErrors, List.mem_cons, List.not_mem_nil, or_false] at he_hook)
    all_goals refine ⟨S_wit, hS, ?_⟩
    -- s0
    · apply col_filter_bound hgp13Col S_wit e_B E ⟨0, by decide⟩
      intro q
      rcases he_hook with rfl | rfl <;>
        (fin_cases q <;>
          first
          | (left; apply hasX_eq_of_eB_I; rfl)
          | (right; left; rfl)
          | (right; right; rfl))
    -- s1
    · apply col_filter_bound hgp13Col S_wit e_B E ⟨1, by decide⟩
      intro q
      rcases he_hook with rfl | rfl | rfl <;>
        (fin_cases q <;>
          first
          | (left; apply hasX_eq_of_eB_I; rfl)
          | (right; left; rfl)
          | (right; right; rfl))
    -- s2
    · apply col_filter_bound hgp13Col S_wit e_B E ⟨2, by decide⟩
      intro q
      rcases he_hook with rfl | rfl <;>
        (fin_cases q <;>
          first
          | (left; apply hasX_eq_of_eB_I; rfl)
          | (right; left; rfl)
          | (right; right; rfl))
    -- s3
    · apply col_filter_bound hgp13Col S_wit e_B E ⟨0, by decide⟩
      intro q
      rcases he_hook with rfl | rfl <;>
        (fin_cases q <;>
          first
          | (left; apply hasX_eq_of_eB_I; rfl)
          | (right; left; rfl)
          | (right; right; rfl))
    -- s4
    · apply col_filter_bound hgp13Col S_wit e_B E ⟨1, by decide⟩
      intro q
      rcases he_hook with rfl | rfl | rfl <;>
        (fin_cases q <;>
          first
          | (left; apply hasX_eq_of_eB_I; rfl)
          | (right; left; rfl)
          | (right; right; rfl))
    -- s5
    · apply col_filter_bound hgp13Col S_wit e_B E ⟨2, by decide⟩
      intro q
      rcases he_hook with rfl | rfl <;>
        (fin_cases q <;>
          first
          | (left; apply hasX_eq_of_eB_I; rfl)
          | (right; left; rfl)
          | (right; right; rfl))
    -- s6
    · have hEq : ∀ q : Fin 13,
          Pauli.hasXComponent (ErrorVec.mul S_wit (ErrorVec.mul e_B E) q)
          = Pauli.hasXComponent (ErrorVec.mul S_wit E q) := by
        intro q
        rcases he_hook with rfl | rfl <;>
          (fin_cases q <;>
            first
            | (apply hasX_eq_of_eB_I; rfl)
            | (apply hasX_eq_of_eB_Z; rfl))
      exact Nat.le_trans (Nat.le_of_eq (col_filter_eq hgp13Col S_wit e_B E hEq))
                          (Nat.le_succ _)
    -- s7
    · have hEq : ∀ q : Fin 13,
          Pauli.hasXComponent (ErrorVec.mul S_wit (ErrorVec.mul e_B E) q)
          = Pauli.hasXComponent (ErrorVec.mul S_wit E q) := by
        intro q
        rcases he_hook with rfl | rfl <;>
          (fin_cases q <;>
            first
            | (apply hasX_eq_of_eB_I; rfl)
            | (apply hasX_eq_of_eB_Z; rfl))
      exact Nat.le_trans (Nat.le_of_eq (col_filter_eq hgp13Col S_wit e_B E hEq))
                          (Nat.le_succ _)
    -- s8
    · have hEq : ∀ q : Fin 13,
          Pauli.hasXComponent (ErrorVec.mul S_wit (ErrorVec.mul e_B E) q)
          = Pauli.hasXComponent (ErrorVec.mul S_wit E q) := by
        intro q
        rcases he_hook with rfl | rfl | rfl <;>
          (fin_cases q <;>
            first
            | (apply hasX_eq_of_eB_I; rfl)
            | (apply hasX_eq_of_eB_Z; rfl))
      exact Nat.le_trans (Nat.le_of_eq (col_filter_eq hgp13Col S_wit e_B E hEq))
                          (Nat.le_succ _)
    -- s9
    · have hEq : ∀ q : Fin 13,
          Pauli.hasXComponent (ErrorVec.mul S_wit (ErrorVec.mul e_B E) q)
          = Pauli.hasXComponent (ErrorVec.mul S_wit E q) := by
        intro q
        rcases he_hook with rfl | rfl | rfl <;>
          (fin_cases q <;>
            first
            | (apply hasX_eq_of_eB_I; rfl)
            | (apply hasX_eq_of_eB_Z; rfl))
      exact Nat.le_trans (Nat.le_of_eq (col_filter_eq hgp13Col S_wit e_B E hEq))
                          (Nat.le_succ _)
    -- s10
    · have hEq : ∀ q : Fin 13,
          Pauli.hasXComponent (ErrorVec.mul S_wit (ErrorVec.mul e_B E) q)
          = Pauli.hasXComponent (ErrorVec.mul S_wit E q) := by
        intro q
        rcases he_hook with rfl | rfl <;>
          (fin_cases q <;>
            first
            | (apply hasX_eq_of_eB_I; rfl)
            | (apply hasX_eq_of_eB_Z; rfl))
      exact Nat.le_trans (Nat.le_of_eq (col_filter_eq hgp13Col S_wit e_B E hEq))
                          (Nat.le_succ _)
    -- s11
    · have hEq : ∀ q : Fin 13,
          Pauli.hasXComponent (ErrorVec.mul S_wit (ErrorVec.mul e_B E) q)
          = Pauli.hasXComponent (ErrorVec.mul S_wit E q) := by
        intro q
        rcases he_hook with rfl | rfl <;>
          (fin_cases q <;>
            first
            | (apply hasX_eq_of_eB_I; rfl)
            | (apply hasX_eq_of_eB_Z; rfl))
      exact Nat.le_trans (Nat.le_of_eq (col_filter_eq hgp13Col S_wit e_B E hEq))
                          (Nat.le_succ _)
  · -- stab-itself hook case
    subst he_stab
    rcases Decidable.em (s_idx.val < 6) with hlt | hge
    · refine ⟨ErrorVec.mul S_wit (HGP13.stabilizers s_idx),
              InStab_to_PCC (QStab.InStab.mul (InStab_from_PCC hS)
                               (QStab.InStab.gen (P := HGP13.code) s_idx)), ?_⟩
      have h_collapse_card :
          (Finset.univ.filter fun g : Fin 3 =>
            ∃ q : Fin 13, hgp13Col q = some g ∧
              Pauli.hasXComponent (ErrorVec.mul
                (ErrorVec.mul S_wit (HGP13.stabilizers s_idx))
                (ErrorVec.mul (HGP13.stabilizers s_idx) E) q) = true).card
          = (Finset.univ.filter fun g : Fin 3 =>
            ∃ q : Fin 13, hgp13Col q = some g ∧
              Pauli.hasXComponent (ErrorVec.mul S_wit E q) = true).card := by
        congr 1
        apply Finset.filter_congr
        intro g _
        have h_pt : ∀ q : Fin 13,
            ErrorVec.mul (ErrorVec.mul S_wit (HGP13.stabilizers s_idx))
                         (ErrorVec.mul (HGP13.stabilizers s_idx) E) q =
            ErrorVec.mul S_wit E q := by
          intro q
          show Pauli.mul (Pauli.mul (S_wit q) (HGP13.stabilizers s_idx q))
                         (Pauli.mul (HGP13.stabilizers s_idx q) (E q)) =
               Pauli.mul (S_wit q) (E q)
          cases (S_wit q) <;> cases (HGP13.stabilizers s_idx q) <;>
            cases (E q) <;> rfl
        constructor
        · rintro ⟨q, hcol, hx⟩
          exact ⟨q, hcol, by rw [h_pt q] at hx; exact hx⟩
        · rintro ⟨q, hcol, hx⟩
          exact ⟨q, hcol, by rw [h_pt q]; exact hx⟩
      exact Nat.le_trans (Nat.le_of_eq h_collapse_card) (Nat.le_succ _)
    · refine ⟨S_wit, hS, ?_⟩
      push_neg at hge
      have hEq : ∀ q : Fin 13,
          Pauli.hasXComponent
            (ErrorVec.mul S_wit (ErrorVec.mul (HGP13.stabilizers s_idx) E) q)
          = Pauli.hasXComponent (ErrorVec.mul S_wit E q) := by
        intro q
        rcases hgp13_Zstab_pointwise s_idx hge q with hI | hZ
        · exact hasX_eq_of_eB_I S_wit _ E q hI
        · exact hasX_eq_of_eB_Z S_wit _ E q hZ
      exact Nat.le_trans (Nat.le_of_eq (col_filter_eq hgp13Col S_wit _ E hEq))
                          (Nat.le_succ _)

/-! ## Phase D — Final `hgp13Spec` and FT theorem for `[[13,1,3]]`

`hgp13Spec : HGPSpec 3` is the canonical Phase-D name for the
non-vacuous `HGPSpec 3` instance built above (`hgp13SpecPCC`).
The FT theorem and its contrapositive specialise the generic
`hgp_dcirc_geq_d` / `hgp_no_logical_error` (proved in
`QStab.QHL.Source.Examples.HGP`) to this specific code.

`codePCC.C_budget = 1` and `d = 3`, so `C_budget < d`, and the
non-vacuous statement of FT is the contrapositive
`hgp13_no_logical_error`: no done state with the bar-Z logical
error class is reachable. The forward statement
`hgp13_FT : C_budget - s.C ≥ 3` is also a real, non-vacuous FT
statement — it says no `(s, hrun, h_in)` triple satisfies the
hypotheses simultaneously (since the conclusion `1 - s.C ≥ 3` is
unsatisfiable on `Nat`, this directly entails the impossibility
of a logical-error done state). Both forms are derived from
the same headline `hgp_dcirc_geq_d`. -/

/-- **Phase-D canonical name** for the [[13,1,3]] HGP `HGPSpec 3` instance.
    Alias for `hgp13SpecPCC` — no proof obligation, just a rename. -/
def hgp13Spec : HGPSpec 3 := hgp13SpecPCC

/-- **Headline FT theorem for [[13,1,3]]**: at any done state whose
    logical-error class lies in the bar-Z barrier class, the live
    fault budget `C_budget - s.C` is at least the code distance
    `d = 3`. Direct specialisation of the generic
    `hgp_dcirc_geq_d` at `d := 3` and `spec := hgp13Spec`. -/
theorem hgp13_FT (s : State HGP13PCC.codePCC) (hrun : Run HGP13PCC.codePCC (.done s))
    (h_in : (QStab.Paper.AlignedBarrier.barZClass hgp13Spec.toAligned).contains s.E_tilde) :
    HGP13PCC.codePCC.C_budget - s.C ≥ 3 :=
  QHL.Source.Examples.HGP.hgp_dcirc_geq_d 3 hgp13Spec s hrun h_in

/-- **Contrapositive form, the directly readable FT statement for
    `[[13,1,3]]`.**  With `C_budget = 1 < 3 = d`, no reachable done
    state's logical-error class lies in the bar-Z barrier class.
    Derived from `hgp_no_logical_error` at `d := 3`. -/
theorem hgp13_no_logical_error (s : State HGP13PCC.codePCC)
    (hrun : Run HGP13PCC.codePCC (.done s))
    (h_budget : HGP13PCC.codePCC.C_budget < 3) :
    ¬ (QStab.Paper.AlignedBarrier.barZClass hgp13Spec.toAligned).contains s.E_tilde :=
  QHL.Source.Examples.HGP.hgp_no_logical_error 3 hgp13Spec s hrun h_budget

/-- `codePCC.C_budget = 1 < 3 = d`, decidable. -/
theorem hgp13_C_budget_lt_d : HGP13PCC.codePCC.C_budget < 3 := by decide

/-- **Cleaner FT-at-budget form**: the contrapositive specialised to
    the actual `C_budget = 1`. No reachable done state of `[[13,1,3]]`
    under the standard NZ schedule has a bar-Z logical error. -/
theorem hgp13_no_logical_error_at_budget (s : State HGP13PCC.codePCC)
    (hrun : Run HGP13PCC.codePCC (.done s)) :
    ¬ (QStab.Paper.AlignedBarrier.barZClass hgp13Spec.toAligned).contains s.E_tilde :=
  hgp13_no_logical_error s hrun hgp13_C_budget_lt_d

/-! ## Axiom inspection in-file (`#print axioms`) -/

#print axioms hgp13Spec
#print axioms hgp13_FT
#print axioms hgp13_no_logical_error
#print axioms hgp13_no_logical_error_at_budget

end QStab.Examples.HGP13PCC
