import QStab.Paper.HookShape
import QStab.Examples.SurfaceParametric
import QStab.Examples.SurfaceHookErrors
import QStab.Examples.SurfaceGeometry
import QStab.Paper.Predicates

/-!
# Phase 4: parametric `surfaceAssignShape` classifier

This file lifts the d=3 hand-tabulated classifier `surfaceD3HookShape`
to an arbitrary odd code distance `d : Nat` with `0 < d` and
`d % 2 = 1`.

The classifier is purely structural: it inspects the residual
back-action vector `e_B : ErrorVec (d * d)` and returns a `HookShape d`
based on whether the X / Z supports are pure (i.e. all nontrivial
cells carry only `X` or only `Z`) and on the weight cutoff `d + 1`
that distinguishes a single-direction hook from a stabilizer-
equivalent residue.

## Design

The d=3 prototype `surfaceD3HookShape` is a 16-branch literal table
that does not generalise. Phase 4 replaces it with a finite case
analysis on:

* `e_B` is identity everywhere -> `identity` pattern,
* weight exceeds `d` -> `fullStab` pattern,
* all Z components absent -> `xInRows` with rowSet = `surfaceXRows e_B`,
* all X components absent -> `zInCols` with colSet = `surfaceZCols e_B`,
* mixed X+Z support -> `fullStab` (fallthrough).

Each branch is decidable, so the classifier is computable and
kernel-`decide`-able.

At `d = 3` this reproduces `surfaceD3HookShape` on every member of
the validated 16-element list `surfaceD3Hooks16`, giving a sanity
check against the Stim-validated d=3 reference.

## Discipline

* No `sorry`, no `native_decide`, no `Classical.choose`,
  no `Exists.choose`, no `by_contra`.
* `decide` (kernel) is used on small finite goals.
* Every branch returns a closed `HookShape d` term.
-/

namespace QStab.Paper

open QStab.Examples

/-! ## The parametric X-row / Z-column finsets -/

/-- The set of grid rows in which `e_B` exhibits an `X`-component. -/
def surfaceXRows {d : Nat} (e_B : ErrorVec (d * d)) : Finset (Fin d) :=
  Finset.univ.filter fun i : Fin d =>
    ∃ j : Fin d, Pauli.hasXComponent (e_B (toIdx d i j)) = true

/-- The set of grid columns in which `e_B` exhibits a `Z`-component. -/
def surfaceZCols {d : Nat} (e_B : ErrorVec (d * d)) : Finset (Fin d) :=
  Finset.univ.filter fun j : Fin d =>
    ∃ i : Fin d, Pauli.hasZComponent (e_B (toIdx d i j)) = true

/-! ## The parametric classifier

The classifier consumes an arbitrary `e_B : ErrorVec (d * d)` and
returns a `HookShape d` chosen by a fixed if-then-else cascade. Each
guard predicate is decidable over the finite domain `Fin (d * d)`,
so the whole function reduces by kernel `decide`. -/

/-- Parametric surface-code hook classifier.

* `identity`  - `e_B` is the all-`I` vector.
* `fullStab`  - `e_B` has weight at least `d + 1` (treated as a bulk
                 stabilizer residue, modulo stabilizers).
* `xInRows`   - no `Z`-component anywhere; row set = `surfaceXRows e_B`.
* `zInCols`   - no `X`-component anywhere; col set = `surfaceZCols e_B`.
* `fullStab`  - fall-through for mixed X+Z support.

The `hd : 0 < d` and `hodd : d % 2 = 1` parameters carry the
geometric requirements of the rotated surface code; they are not
consumed by the if-cascade itself but propagate downstream into the
spec-instance constructors that quantify over the same `d`. -/
def surfaceAssignShape (d : Nat) (_hd : 0 < d) (_hodd : d % 2 = 1)
    (e_B : ErrorVec (d * d)) : HookShape d :=
  if (∀ q : Fin (d * d), e_B q = Pauli.I) then
    HookShape.identityShape d
  else if ErrorVec.weight e_B ≥ d + 1 then
    HookShape.ofStab
  else if (∀ q : Fin (d * d), Pauli.hasZComponent (e_B q) = false) then
    HookShape.ofRows (surfaceXRows e_B)
  else if (∀ q : Fin (d * d), Pauli.hasXComponent (e_B q) = false) then
    HookShape.ofCols (surfaceZCols e_B)
  else
    HookShape.ofStab

/-! ## Helper lemmas

Each lemma extracts information from the *pattern* the classifier
produces. The proofs walk the four-step if-cascade explicitly, using
`HookPattern.noConfusion` (kernel reasoning, no axioms) to discharge
the impossible-pattern branches. -/

/-- `identity` pattern iff `e_B` is identity everywhere. -/
theorem surfaceAssignShape_identity_iff
    (d : Nat) (hd : 0 < d) (hodd : d % 2 = 1) (e_B : ErrorVec (d * d)) :
    (surfaceAssignShape d hd hodd e_B).pattern = HookPattern.identity ↔
      (∀ q : Fin (d * d), e_B q = Pauli.I) := by
  unfold surfaceAssignShape
  by_cases h_id : (∀ q : Fin (d * d), e_B q = Pauli.I)
  · simp [h_id, HookShape.identityShape]
  · simp only [if_neg h_id]
    by_cases h_w : ErrorVec.weight e_B ≥ d + 1
    · simp [h_w, HookShape.ofStab, h_id]
    · simp only [if_neg h_w]
      by_cases h_x : (∀ q : Fin (d * d), Pauli.hasZComponent (e_B q) = false)
      · simp [h_x, HookShape.ofRows, h_id]
      · simp only [if_neg h_x]
        by_cases h_z : (∀ q : Fin (d * d), Pauli.hasXComponent (e_B q) = false)
        · simp [h_z, HookShape.ofCols, h_id]
        · simp [h_z, HookShape.ofStab, h_id]

/-- If the classifier returns `xInRows` then `e_B` has no `Z`-component. -/
theorem surfaceAssignShape_xInRows_implies_no_Z
    (d : Nat) (hd : 0 < d) (hodd : d % 2 = 1) (e_B : ErrorVec (d * d))
    (h : (surfaceAssignShape d hd hodd e_B).pattern = HookPattern.xInRows) :
    ∀ q : Fin (d * d), Pauli.hasZComponent (e_B q) = false := by
  unfold surfaceAssignShape at h
  by_cases h_id : (∀ q : Fin (d * d), e_B q = Pauli.I)
  · -- identity branch: pattern would be `identity`, contradicting `xInRows`.
    rw [if_pos h_id] at h
    exact HookPattern.noConfusion h
  · rw [if_neg h_id] at h
    by_cases h_w : ErrorVec.weight e_B ≥ d + 1
    · rw [if_pos h_w] at h
      exact HookPattern.noConfusion h
    · rw [if_neg h_w] at h
      by_cases h_x : (∀ q : Fin (d * d), Pauli.hasZComponent (e_B q) = false)
      · exact h_x
      · rw [if_neg h_x] at h
        by_cases h_z : (∀ q : Fin (d * d), Pauli.hasXComponent (e_B q) = false)
        · rw [if_pos h_z] at h
          exact HookPattern.noConfusion h
        · rw [if_neg h_z] at h
          exact HookPattern.noConfusion h

/-- Symmetric: if the classifier returns `zInCols` then `e_B` has no
    `X`-component. -/
theorem surfaceAssignShape_zInCols_implies_no_X
    (d : Nat) (hd : 0 < d) (hodd : d % 2 = 1) (e_B : ErrorVec (d * d))
    (h : (surfaceAssignShape d hd hodd e_B).pattern = HookPattern.zInCols) :
    ∀ q : Fin (d * d), Pauli.hasXComponent (e_B q) = false := by
  unfold surfaceAssignShape at h
  by_cases h_id : (∀ q : Fin (d * d), e_B q = Pauli.I)
  · rw [if_pos h_id] at h
    exact HookPattern.noConfusion h
  · rw [if_neg h_id] at h
    by_cases h_w : ErrorVec.weight e_B ≥ d + 1
    · rw [if_pos h_w] at h
      exact HookPattern.noConfusion h
    · rw [if_neg h_w] at h
      by_cases h_x : (∀ q : Fin (d * d), Pauli.hasZComponent (e_B q) = false)
      · rw [if_pos h_x] at h
        exact HookPattern.noConfusion h
      · rw [if_neg h_x] at h
        by_cases h_z : (∀ q : Fin (d * d), Pauli.hasXComponent (e_B q) = false)
        · exact h_z
        · rw [if_neg h_z] at h
          exact HookPattern.noConfusion h

/-- If the classifier returns `xInRows`, the resulting `rowSet` equals
    the `surfaceXRows` Finset. -/
theorem surfaceAssignShape_rowSet_xInRows
    (d : Nat) (hd : 0 < d) (hodd : d % 2 = 1) (e_B : ErrorVec (d * d))
    (h : (surfaceAssignShape d hd hodd e_B).pattern = HookPattern.xInRows) :
    (surfaceAssignShape d hd hodd e_B).rowSet = surfaceXRows e_B := by
  unfold surfaceAssignShape at h ⊢
  by_cases h_id : (∀ q : Fin (d * d), e_B q = Pauli.I)
  · rw [if_pos h_id] at h
    exact HookPattern.noConfusion h
  · rw [if_neg h_id] at h ⊢
    by_cases h_w : ErrorVec.weight e_B ≥ d + 1
    · rw [if_pos h_w] at h
      exact HookPattern.noConfusion h
    · rw [if_neg h_w] at h ⊢
      by_cases h_x : (∀ q : Fin (d * d), Pauli.hasZComponent (e_B q) = false)
      · rw [if_pos h_x]; rfl
      · rw [if_neg h_x] at h
        by_cases h_z : (∀ q : Fin (d * d), Pauli.hasXComponent (e_B q) = false)
        · rw [if_pos h_z] at h
          exact HookPattern.noConfusion h
        · rw [if_neg h_z] at h
          exact HookPattern.noConfusion h

/-- Symmetric: if the classifier returns `zInCols`, the resulting
    `colSet` equals the `surfaceZCols` Finset. -/
theorem surfaceAssignShape_colSet_zInCols
    (d : Nat) (hd : 0 < d) (hodd : d % 2 = 1) (e_B : ErrorVec (d * d))
    (h : (surfaceAssignShape d hd hodd e_B).pattern = HookPattern.zInCols) :
    (surfaceAssignShape d hd hodd e_B).colSet = surfaceZCols e_B := by
  unfold surfaceAssignShape at h ⊢
  by_cases h_id : (∀ q : Fin (d * d), e_B q = Pauli.I)
  · rw [if_pos h_id] at h
    exact HookPattern.noConfusion h
  · rw [if_neg h_id] at h ⊢
    by_cases h_w : ErrorVec.weight e_B ≥ d + 1
    · rw [if_pos h_w] at h
      exact HookPattern.noConfusion h
    · rw [if_neg h_w] at h ⊢
      by_cases h_x : (∀ q : Fin (d * d), Pauli.hasZComponent (e_B q) = false)
      · rw [if_pos h_x] at h
        exact HookPattern.noConfusion h
      · rw [if_neg h_x] at h ⊢
        by_cases h_z : (∀ q : Fin (d * d), Pauli.hasXComponent (e_B q) = false)
        · rw [if_pos h_z]; rfl
        · rw [if_neg h_z] at h
          exact HookPattern.noConfusion h

/-! ## d=3 sanity: parametric classifier agrees with the legacy table

The parametric `surfaceAssignShape (d := 3)` and the legacy
`surfaceD3HookShape` are two independent classifiers; they must
agree on every member of `surfaceD3Hooks16`. We discharge by
`fin_cases` over the 16-element list followed by kernel `decide` --
the same discipline as the legacy headline
`surfaceD3_nz_hook_has_shape`. -/

/-- At `d = 3`, the parametric classifier returns the same `HookShape 3`
    as the legacy `surfaceD3HookShape` on every member of the validated
    16-element NZ hook list. -/
theorem surfaceAssignShape_d3_eq_legacy_on_hooks :
    ∀ e ∈ surfaceD3Hooks16,
      surfaceAssignShape 3 (by decide) (by decide) e
        = surfaceD3HookShape e := by
  intro e he
  fin_cases he <;> decide

/-! ### `#eval` smoke checks (each reduces to a closed literal) -/

/-- The first weight-2 X hook classifies as `xInRows`. -/
example :
    (surfaceAssignShape 3 (by decide) (by decide)
        (ofList [(7, .X), (8, .X)] : ErrorVec 9)).pattern
      = HookPattern.xInRows := by decide

/-- The first weight-3 Z hook classifies as `zInCols`. -/
example :
    (surfaceAssignShape 3 (by decide) (by decide)
        (ofList [(5, .Z), (7, .Z), (8, .Z)] : ErrorVec 9)).pattern
      = HookPattern.zInCols := by decide

/-- The first weight-4 bulk stabilizer classifies as `fullStab`. -/
example :
    (surfaceAssignShape 3 (by decide) (by decide)
        (ofList [(4, .Z), (5, .Z), (7, .Z), (8, .Z)] : ErrorVec 9)).pattern
      = HookPattern.fullStab := by decide

/-- The identity vector classifies as `identity`. -/
example :
    (surfaceAssignShape 3 (by decide) (by decide)
        (ErrorVec.identity 9)).pattern
      = HookPattern.identity := by decide

/-! ## Per-pattern `HookShapeOf` lemmas

Below we factor `HookShapeOf e_B (surfaceAssignShape d hd hodd e_B)` into
four per-pattern lemmas, one per branch of the if-cascade. The dispatcher
that closes the headline `SpecHasNZHookShape` then case-splits on
`isXStab d s ∨ isZStab d s` plus the weight cutoff and feeds each case
to the appropriate per-pattern lemma. -/

/-- **Pattern 1: identity.** If `e_B` is the identity vector pointwise,
then `surfaceAssignShape` returns `identityShape d` and `HookShapeOf`
holds by definition. -/
theorem nz_hook_has_shape_identity_case
    (d : Nat) (hd : 0 < d) (hodd : d % 2 = 1) (e_B : ErrorVec (d * d))
    (h_id : ∀ q, e_B q = Pauli.I) :
    HookShapeOf e_B (surfaceAssignShape d hd hodd e_B) := by
  -- The cascade's first branch fires, producing `identityShape d`.
  unfold surfaceAssignShape
  rw [if_pos h_id]
  -- `HookShapeOf e_B (identityShape d) ↔ ∀ q, e_B q = I`.
  exact (HookShapeOf_identityShape_iff d e_B).mpr h_id

/-- **Pattern 2: fullStab (weight-cutoff branch).** If `e_B` has weight at
least `d + 1`, then `surfaceAssignShape` returns `HookShape.ofStab` (the
fullStab pattern) and `HookShapeOf` is vacuously `True`. -/
theorem nz_hook_has_shape_fullStab_case
    (d : Nat) (hd : 0 < d) (hodd : d % 2 = 1) (e_B : ErrorVec (d * d))
    (h_w : ErrorVec.weight e_B ≥ d + 1) :
    HookShapeOf e_B (surfaceAssignShape d hd hodd e_B) := by
  -- First, weight ≥ d + 1 ≥ 1 implies `e_B` is not identity.
  have h_ni : ¬ ∀ q, e_B q = Pauli.I := by
    intro h_id
    -- weight (identity) = 0 < d + 1.
    have h_w0 : ErrorVec.weight e_B = 0 := by
      unfold ErrorVec.weight
      apply Finset.card_eq_zero.mpr
      rw [Finset.filter_eq_empty_iff]
      intro q _
      simp [h_id q]
    omega
  -- Cascade enters Branch 2 (`weight ≥ d+1`) and returns `ofStab`.
  unfold surfaceAssignShape
  rw [if_neg h_ni, if_pos h_w]
  -- `HookShapeOf e_B (ofStab _) ` is `True` for the fullStab pattern.
  trivial

/-- **Pattern 3: xInRows.** If `e_B` is non-identity, has weight `< d + 1`,
and has no Z-component anywhere, then `surfaceAssignShape` returns
`HookShape.ofRows (surfaceXRows e_B)` and `HookShapeOf` holds with that
row support. -/
theorem nz_hook_has_shape_xInRows_case
    (d : Nat) (hd : 0 < d) (hodd : d % 2 = 1) (e_B : ErrorVec (d * d))
    (h_ni : ¬ ∀ q, e_B q = Pauli.I)
    (h_lt : ErrorVec.weight e_B < d + 1)
    (h_noZ : ∀ q, Pauli.hasZComponent (e_B q) = false) :
    HookShapeOf e_B (surfaceAssignShape d hd hodd e_B) := by
  -- Cascade: Branch 1 fails (h_ni), Branch 2 fails (h_lt), Branch 3 fires (h_noZ).
  have h_not_ge : ¬ ErrorVec.weight e_B ≥ d + 1 := by omega
  unfold surfaceAssignShape
  rw [if_neg h_ni, if_neg h_not_ge, if_pos h_noZ]
  -- Goal: `HookShapeOf e_B (HookShape.ofRows (surfaceXRows e_B))`. Two
  -- conjuncts: (i) no Z, (ii) X-bearing positions lie in (surfaceXRows e_B).image Fin.val.
  refine ⟨h_noZ, ?_⟩
  intro q hx
  -- Build the row witness ⟨q.val / d, _⟩ : Fin d.
  have hq_lt : q.val / d < d := Nat.div_lt_of_lt_mul q.isLt
  -- Build the column witness ⟨q.val % d, _⟩ : Fin d.
  have hc_lt : q.val % d < d := Nat.mod_lt _ hd
  set i : Fin d := ⟨q.val / d, hq_lt⟩ with hi_def
  set j : Fin d := ⟨q.val % d, hc_lt⟩ with hj_def
  -- `toIdx d i j = q` by `Nat.div_add_mod`.
  have h_eq : toIdx d i j = q := by
    apply Fin.ext
    show d * (q.val / d) + q.val % d = q.val
    exact Nat.div_add_mod q.val d
  -- `i ∈ surfaceXRows e_B`: witnessed by column `j`.
  have h_mem : i ∈ surfaceXRows e_B := by
    unfold surfaceXRows
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, j, ?_⟩
    rw [h_eq]
    exact hx
  -- Image under Fin.val maps i to q.val / d, which is what we need.
  apply Finset.mem_image.mpr
  exact ⟨i, h_mem, rfl⟩

/-- **Pattern 4: zInCols.** Symmetric to `xInRows`. If `e_B` is non-identity,
has weight `< d + 1`, has *some* Z-component (so Branch 3 of the cascade
does not fire), and has no X-component anywhere, then `surfaceAssignShape`
returns `HookShape.ofCols (surfaceZCols e_B)` and `HookShapeOf` holds. -/
theorem nz_hook_has_shape_zInCols_case
    (d : Nat) (hd : 0 < d) (hodd : d % 2 = 1) (e_B : ErrorVec (d * d))
    (h_ni : ¬ ∀ q, e_B q = Pauli.I)
    (h_lt : ErrorVec.weight e_B < d + 1)
    (h_hasZ : ¬ ∀ q, Pauli.hasZComponent (e_B q) = false)
    (h_noX : ∀ q, Pauli.hasXComponent (e_B q) = false) :
    HookShapeOf e_B (surfaceAssignShape d hd hodd e_B) := by
  have h_not_ge : ¬ ErrorVec.weight e_B ≥ d + 1 := by omega
  unfold surfaceAssignShape
  rw [if_neg h_ni, if_neg h_not_ge, if_neg h_hasZ, if_pos h_noX]
  -- Goal: `HookShapeOf e_B (HookShape.ofCols (surfaceZCols e_B))`.
  refine ⟨h_noX, ?_⟩
  intro q hz
  have hq_lt : q.val / d < d := Nat.div_lt_of_lt_mul q.isLt
  have hc_lt : q.val % d < d := Nat.mod_lt _ hd
  set i : Fin d := ⟨q.val / d, hq_lt⟩ with hi_def
  set j : Fin d := ⟨q.val % d, hc_lt⟩ with hj_def
  have h_eq : toIdx d i j = q := by
    apply Fin.ext
    show d * (q.val / d) + q.val % d = q.val
    exact Nat.div_add_mod q.val d
  have h_mem : j ∈ surfaceZCols e_B := by
    unfold surfaceZCols
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, i, ?_⟩
    rw [h_eq]
    exact hz
  apply Finset.mem_image.mpr
  exact ⟨j, h_mem, rfl⟩

/-! ## Headline: parametric `SpecHasNZHookShape` -/

/-- If `e_B` has no X-component and no Z-component anywhere, then every
entry is `Pauli.I`. -/
private lemma noXZ_implies_identity {d : Nat} (e_B : ErrorVec (d * d))
    (h_noX : ∀ q, Pauli.hasXComponent (e_B q) = false)
    (h_noZ : ∀ q, Pauli.hasZComponent (e_B q) = false) :
    ∀ q, e_B q = Pauli.I := by
  intro q
  -- Case-split on (e_B q). Only `Pauli.I` has both hasX = false AND hasZ = false.
  cases h : e_B q with
  | I => rfl
  | X =>
      have := h_noX q
      rw [h] at this
      simp [Pauli.hasXComponent] at this
  | Y =>
      have := h_noX q
      rw [h] at this
      simp [Pauli.hasXComponent] at this
  | Z =>
      have := h_noZ q
      rw [h] at this
      simp [Pauli.hasZComponent] at this

/-- For an X-stab hook `e_B`, the no-Z property holds (from
`mkSurfaceHookErrors_X_no_Z`). -/
private lemma xStab_hook_no_Z
    (d : Nat) (hd : 0 < d) (hodd : d % 2 = 1)
    (s : Fin (QStab.Examples.SurfaceParametric.numStabFormula d))
    (hxs : QStab.Examples.SurfaceParametric.isXStab d s) (e_B : ErrorVec (d * d))
    (he : e_B ∈ QStab.Examples.SurfaceParametric.mkSurfaceHookErrors d hd hodd s) :
    ∀ q, Pauli.hasZComponent (e_B q) = false :=
  QStab.Examples.SurfaceParametric.mkSurfaceHookErrors_X_no_Z d hd hodd s hxs e_B he

/-- For a Z-stab hook `e_B`, the no-X property holds (from
`mkSurfaceHookErrors_Z_no_X`). -/
private lemma zStab_hook_no_X
    (d : Nat) (hd : 0 < d) (hodd : d % 2 = 1)
    (s : Fin (QStab.Examples.SurfaceParametric.numStabFormula d))
    (hzs : QStab.Examples.SurfaceParametric.isZStab d s) (e_B : ErrorVec (d * d))
    (he : e_B ∈ QStab.Examples.SurfaceParametric.mkSurfaceHookErrors d hd hodd s) :
    ∀ q, Pauli.hasXComponent (e_B q) = false :=
  QStab.Examples.SurfaceParametric.mkSurfaceHookErrors_Z_no_X d hd hodd s hzs e_B he

/-- Every stabilizer index is either an X-stab or a Z-stab. -/
private lemma isXStab_or_isZStab
    (d : Nat) (s : Fin (QStab.Examples.SurfaceParametric.numStabFormula d)) :
    QStab.Examples.SurfaceParametric.isXStab d s ∨ QStab.Examples.SurfaceParametric.isZStab d s := by
  unfold QStab.Examples.SurfaceParametric.isXStab QStab.Examples.SurfaceParametric.isZStab
  -- `stabType d s.val` is either `X` or `Z` by definition (`split_ifs <;> simp`).
  simp only [QStab.Examples.SurfaceParametric.stabType]
  split_ifs <;> simp

/-- **Headline (parametric).** The parametric `surfaceAssignShape` is a
witness of `SpecHasNZHookShape` for the parametric rotated-surface-code
`QECParams` at any odd distance `d > 0`.

Dispatch outline:
* split `s` into X-stab / Z-stab via `isXStab_or_isZStab`;
* split `e_B` into identity vs non-identity;
* split non-identity into weight-`≥ d+1` (fullStab) vs weight-`< d+1`;
* in the latter case, apply the appropriate `xInRows` / `zInCols` lemma
  (the no-Z / no-X conjunct is supplied by Path A's
  `mkSurfaceHookErrors_X_no_Z` / `_Z_no_X`). -/
theorem surfaceParametric_nz_hook_has_shape
    (d : Nat) (hd : 0 < d) (hodd : d % 2 = 1) :
    SpecHasNZHookShape (QStab.Examples.SurfaceParametric.mkSurfaceQECParams d hd hodd) d
      (by simp [QStab.Examples.SurfaceParametric.mkSurfaceQECParams])
      (surfaceAssignShape d hd hodd) := by
  -- Unfold the obligation to its pointwise form.
  rw [SpecHasNZHookShape_iff]
  intro s e_B he
  -- `e_B ∈ backActionSet s` reduces to `e_B ∈ mkSurfaceHookErrors d hd hodd s`.
  have he' : e_B ∈ QStab.Examples.SurfaceParametric.mkSurfaceHookErrors d hd hodd s := he
  -- The `▸` over the definitional equality `(mkSurfaceQECParams …).n = d * d`
  -- reduces by `rfl`-substitution. We just need `HookShapeOf e_B …`.
  show HookShapeOf e_B (surfaceAssignShape d hd hodd e_B)
  -- First top-level split: identity or not.
  by_cases h_id : ∀ q, e_B q = Pauli.I
  · exact nz_hook_has_shape_identity_case d hd hodd e_B h_id
  -- Non-identity: split on the weight cutoff.
  by_cases h_w : ErrorVec.weight e_B ≥ d + 1
  · exact nz_hook_has_shape_fullStab_case d hd hodd e_B h_w
  -- Weight < d + 1: split on X-stab vs Z-stab to obtain purity.
  have h_lt : ErrorVec.weight e_B < d + 1 := by omega
  rcases isXStab_or_isZStab d s with hxs | hzs
  · -- X-stab: no Z-component anywhere → Branch 3 (xInRows).
    have h_noZ := xStab_hook_no_Z d hd hodd s hxs e_B he'
    exact nz_hook_has_shape_xInRows_case d hd hodd e_B h_id h_lt h_noZ
  · -- Z-stab: no X-component anywhere. Need to also show Branch 3 does
    -- *not* fire — i.e., there exists q with hasZ (e_B q) = true.
    have h_noX := zStab_hook_no_X d hd hodd s hzs e_B he'
    have h_hasZ : ¬ ∀ q, Pauli.hasZComponent (e_B q) = false := by
      intro h_noZ
      -- noX ∧ noZ → e_B = I pointwise → contradicts h_id.
      exact h_id (noXZ_implies_identity e_B h_noX h_noZ)
    exact nz_hook_has_shape_zInCols_case d hd hodd e_B h_id h_lt h_hasZ h_noX

/-! ### Axiom check for each per-pattern lemma + the headline. -/
#print axioms nz_hook_has_shape_identity_case
#print axioms nz_hook_has_shape_fullStab_case
#print axioms nz_hook_has_shape_xInRows_case
#print axioms nz_hook_has_shape_zInCols_case
#print axioms surfaceParametric_nz_hook_has_shape

end QStab.Paper
