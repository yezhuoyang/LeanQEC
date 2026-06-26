import QStab.Examples.SurfaceParametric
import QStab.Examples.SurfaceVerification

/-! # Parametric hook-error sets for the rotated surface code

This file defines `mkSurfaceHookErrors d hd hodd s : Finset (ErrorVec (d * d))`,
the **parametric NZ hook-error set** for stabilizer `s` of the rotated
surface code at distance `d`.

## Structure

Following `QStab/Examples/SurfaceVerification.lean:585-609` (the legacy
`SurfaceD3.hookErrors` table) and `notes/validate_PNZ_d3.py:607-614`
(`hooks_of_suffixes`), the hook errors for a stabilizer `T_s` of Pauli-kind
`P ∈ {X, Z}` and gate-order schedule
`support s = [q_0, q_1, ..., q_{k-1}]` are exactly the proper non-empty
**suffixes** of the schedule, each tagged with `P` at every position:

    hookErrors s = [ P at {q_1, ..., q_{k-1}}
                   , P at {q_2, ..., q_{k-1}}
                   , ...
                   , P at {q_{k-1}} ]

In the legacy `SurfaceD3PCC` instance the **stabilizer itself** is unioned
into the back-action set (so the bound `r := 4 = |support|` accommodates
the entire stabilizer as a worst-case error). We replicate that here:

    mkSurfaceHookErrors d hd hodd s =
        {proper-suffix hooks} ∪ {stabilizer T_s}

where the stabilizer `T_s` itself is the j = 0 suffix (the full support with
Pauli `P`) — i.e. it IS `mkSurfaceStabilizers d hd s`, since `mkSurfaceStabilizers`
already puts `P` on every support qubit.

## Schedule order (per `SurfaceD3Bundle.support0..7`)

For each stabilizer kind, the gate-schedule order is:
* `bulkZ r c`  -> [(r,c), (r+1,c), (r,c+1), (r+1,c+1)]    -- N-order (NW,SW,NE,SE)
* `bulkX r c`  -> [(r,c), (r,c+1), (r+1,c), (r+1,c+1)]    -- Z-order (NW,NE,SW,SE)
* `topX b`     -> [(0, 2*b), (0, 2*b+1)]
* `rightZ b`   -> [(2*b, d-1), (2*b+1, d-1)]
* `leftZ b`    -> [(2*b+1, 0), (2*b+2, 0)]
* `bottomX b`  -> [(d-1, 2*b+1), (d-1, 2*b+2)]

At `d = 3` these reproduce `support0..7` from `SurfaceD3Bundle` exactly.

## Discipline

* No `sorry`, `native_decide`, `Classical.choose`, `Exists.choose`, or
  `by_contra`.
* `decide` is used only for `Decidable` propositions over closed finite
  domains (membership in `Finset`s of small lists).
* `Finset.image` over `(List.range k).toFinset` gives a finite, decidable
  enumeration of suffixes.
-/

namespace QStab.Examples.SurfaceParametric

open QStab QStab.Examples

/-! ## Per-kind gate-order list (as `(row, col) : Nat × Nat`) -/

/-- The canonical NZ gate-schedule order for each stabilizer kind, as a list
    of grid coordinates `(row, col) : Nat × Nat`.

    * `bulkZ r c` uses **N-order** (NW, SW, NE, SE), matching `support0`/`support3`.
    * `bulkX r c` uses **Z-order** (NW, NE, SW, SE), matching `support1`/`support2`.
    * Boundaries are left-to-right (rows) or top-to-bottom (cols), matching
      `support4..7`. -/
def kindOrderRC (d : Nat) (k : StabKind) : List (Nat × Nat) :=
  match k with
  | .bulkZ r c => [(r, c), (r + 1, c), (r, c + 1), (r + 1, c + 1)]
  | .bulkX r c => [(r, c), (r, c + 1), (r + 1, c), (r + 1, c + 1)]
  | .topX b    => [(0, 2 * b), (0, 2 * b + 1)]
  | .rightZ b  => [(2 * b, d - 1), (2 * b + 1, d - 1)]
  | .leftZ b   => [(2 * b + 1, 0), (2 * b + 2, 0)]
  | .bottomX b => [(d - 1, 2 * b + 1), (d - 1, 2 * b + 2)]

/-- The Pauli kind (X or Z) of each stabilizer kind. Matches `stabType`. -/
def kindPauli : StabKind → Pauli
  | .bulkZ _ _ => Pauli.Z
  | .bulkX _ _ => Pauli.X
  | .topX _    => Pauli.X
  | .rightZ _  => Pauli.Z
  | .leftZ _   => Pauli.Z
  | .bottomX _ => Pauli.X

/-- The Pauli kind agrees with `stabType` whenever the kind decomposition
    matches the index decomposition. This is a consistency check; we do not
    rely on it in the headline definition. -/
theorem kindPauli_eq_stabType (d i : Nat) :
    kindPauli (classifyStab d i) = stabType d i := by
  simp only [kindPauli, classifyStab, stabType]
  split_ifs <;> rfl

/-! ## Hook construction (single suffix)

For a stabilizer kind `k`, distance `d`, and suffix start position `j`, the
hook error is the `ErrorVec (d * d)` that places `kindPauli k` at every qubit
whose `(row, col)` coordinate appears in `(kindOrderRC d k).drop j`, and
`Pauli.I` elsewhere.

The construction uses the `List.lookup`-style pattern of `ofList`: build a
list of `(qubitIndex, Pauli)` pairs from the suffix, then convert. -/

/-- The qubit index `Nat` for grid coordinate `(row, col)` at distance `d`. -/
def gridIdx (d row col : Nat) : Nat := d * row + col

/-- The list of `(qubitIndex, Pauli)` pairs for the `j`-th suffix of the
    schedule of kind `k`, all tagged with Pauli `kindPauli k`. -/
def suffixPairs (d : Nat) (k : StabKind) (j : Nat) : List (Nat × Pauli) :=
  ((kindOrderRC d k).drop j).map (fun rc => (gridIdx d rc.1 rc.2, kindPauli k))

/-- The `j`-th suffix hook for kind `k` at distance `d`, as an
    `ErrorVec (d * d)`. -/
def suffixHook (d : Nat) (k : StabKind) (j : Nat) : ErrorVec (d * d) :=
  ofList (suffixPairs d k j)

/-! ## The parametric hook-error set

Combine the proper suffix hooks (j = 1, ..., k-1) with the stabilizer itself
(the j = 0 hook, which by construction equals `mkSurfaceStabilizers d hd s`
on its support). -/

/-- The list of suffix indices for kind `k` at distance `d`, namely
    `[1, 2, ..., (kindOrderRC d k).length - 1]`. The empty list (no proper
    suffix) arises iff the schedule has length ≤ 1, which never happens for
    the standard rotated-surface-code kinds (all have length 2 or 4). -/
def suffixIndices (d : Nat) (k : StabKind) : List Nat :=
  List.range ((kindOrderRC d k).length - 1) |>.map (· + 1)

/-- The parametric hook-error set for stabilizer `s` of the rotated surface
    code at distance `d`. Contains the proper-suffix NZ hooks of the gate
    schedule plus the stabilizer itself.

    The signature takes `hodd : d % 2 = 1` for consistency with
    `stab_commute_parametric`; the construction does not actually depend on
    `hodd` (it is a paper-side enumeration, valid at every `d ≥ 3`). -/
def mkSurfaceHookErrors (d : Nat) (hd : 0 < d) (_hodd : d % 2 = 1)
    (s : Fin (numStabFormula d)) : Finset (ErrorVec (d * d)) :=
  let k := classifyStab d s.val
  let suffixHooks : Finset (ErrorVec (d * d)) :=
    (suffixIndices d k).toFinset.image (fun j => suffixHook d k j)
  suffixHooks ∪ ({mkSurfaceStabilizers d hd s} : Finset (ErrorVec (d * d)))

/-! ## Inspection `#eval`s

At `d = 3` the parametric hook-error set should be exactly the legacy
`SurfaceD3.hookErrors s ∪ {SurfaceD3.stabilizers s}` for every `s : Fin 8`.

The `#eval`s below reduce to closed `Finset` literals over `ErrorVec 9`,
demonstrating that `mkSurfaceHookErrors` is fully computable. -/

-- Cardinality at d=3 (matches the legacy hookErrors length + 1 for the stab):
-- 4 weight-4 stabs (s0..s3) → 3 suffix hooks + 1 stabilizer = 4 elements each.
-- 4 weight-2 stabs (s4..s7) → 1 suffix hook + 1 stabilizer = 2 elements each.

#eval (mkSurfaceHookErrors 3 (by decide) (by decide) ⟨0, by decide⟩).card   -- 4
#eval (mkSurfaceHookErrors 3 (by decide) (by decide) ⟨1, by decide⟩).card   -- 4
#eval (mkSurfaceHookErrors 3 (by decide) (by decide) ⟨2, by decide⟩).card   -- 4
#eval (mkSurfaceHookErrors 3 (by decide) (by decide) ⟨3, by decide⟩).card   -- 4
#eval (mkSurfaceHookErrors 3 (by decide) (by decide) ⟨4, by decide⟩).card   -- 2
#eval (mkSurfaceHookErrors 3 (by decide) (by decide) ⟨5, by decide⟩).card   -- 2
#eval (mkSurfaceHookErrors 3 (by decide) (by decide) ⟨6, by decide⟩).card   -- 2
#eval (mkSurfaceHookErrors 3 (by decide) (by decide) ⟨7, by decide⟩).card   -- 2

-- Inspection of a single weight-3 suffix hook (s0, j=1):
-- suffixHook 3 (.bulkZ 0 0) 1 should be ofList [(3,Z),(1,Z),(4,Z)]
-- (qubits 3=row1col0, 1=row0col1, 4=row1col1; the N-order suffix from pos 1).
#eval suffixHook 3 (StabKind.bulkZ 0 0) 1 ⟨3, by decide⟩  -- Pauli.Z
#eval suffixHook 3 (StabKind.bulkZ 0 0) 1 ⟨1, by decide⟩  -- Pauli.Z
#eval suffixHook 3 (StabKind.bulkZ 0 0) 1 ⟨4, by decide⟩  -- Pauli.Z
#eval suffixHook 3 (StabKind.bulkZ 0 0) 1 ⟨0, by decide⟩  -- Pauli.I (j=1 drops position 0)

-- d=5 weight-4 bulk: 3 suffix hooks + 1 stab = 4 elements (every bulk).
#eval (mkSurfaceHookErrors 5 (by decide) (by decide) ⟨0, by decide⟩).card   -- 4

-- d=5 top-X boundary (index 16, b=0): 1 suffix hook + 1 stab = 2 elements.
#eval (mkSurfaceHookErrors 5 (by decide) (by decide) ⟨16, by decide⟩).card  -- 2

/-! ## Cross-check at d = 3 against the legacy `SurfaceD3.hookErrors`

The legacy table at `SurfaceVerification.lean:612-636` enumerates the eight
per-stabilizer NZ-hook lists. Our parametric `mkSurfaceHookErrors` extends
each legacy list with the stabilizer itself, matching the `surfaceD3PCC.lean`
convention `hookSet := hookErrors ∪ {T_s}` (which is what gets fed into
`backActionSet`).

The headline cross-check is decidable on the finite d=3 domain: the legacy
list elements, lifted into a Finset via `List.toFinset`, plus the singleton
`{stabilizer s}`, equal the parametric `mkSurfaceHookErrors`. -/

/-! Note on the j = 0 suffix hook. The construction `suffixHook d k 0` builds
    an `ErrorVec` from `ofList` over the **full** schedule list with Pauli
    `kindPauli k` at every support qubit. By contrast `mkSurfaceStabilizers`
    builds the same vector by direct closed-form enumeration via
    `decodeStabPauliAt`. The two are **pointwise equal** but not definitionally
    equal (the former uses `List.lookup`; the latter uses arithmetic
    comparisons). We side-step this by taking the union with the explicit
    singleton `{mkSurfaceStabilizers d hd s}` in `mkSurfaceHookErrors`,
    rather than relying on `suffixHook d k 0` to match the stabilizer. The
    `Finset` therefore always contains the genuine stabilizer (under the
    `decodeStabPauliAt` encoding) plus the proper-suffix hooks. -/

/-- At d=3, stab 0 (bulk Z NW), the parametric hook set agrees with the
    legacy `SurfaceD3.hookErrors 0 ∪ {SurfaceD3.stabilizers 0}`. -/
example :
    mkSurfaceHookErrors 3 (by decide) (by decide) ⟨0, by decide⟩ =
    ((SurfaceD3.hookErrors ⟨0, by decide⟩).toFinset ∪
     {SurfaceD3.stabilizers ⟨0, by decide⟩}) := by
  decide

/-- At d=3, stab 1 (bulk X NE). -/
example :
    mkSurfaceHookErrors 3 (by decide) (by decide) ⟨1, by decide⟩ =
    ((SurfaceD3.hookErrors ⟨1, by decide⟩).toFinset ∪
     {SurfaceD3.stabilizers ⟨1, by decide⟩}) := by
  decide

/-- At d=3, stab 2 (bulk X SW). -/
example :
    mkSurfaceHookErrors 3 (by decide) (by decide) ⟨2, by decide⟩ =
    ((SurfaceD3.hookErrors ⟨2, by decide⟩).toFinset ∪
     {SurfaceD3.stabilizers ⟨2, by decide⟩}) := by
  decide

/-- At d=3, stab 3 (bulk Z SE). -/
example :
    mkSurfaceHookErrors 3 (by decide) (by decide) ⟨3, by decide⟩ =
    ((SurfaceD3.hookErrors ⟨3, by decide⟩).toFinset ∪
     {SurfaceD3.stabilizers ⟨3, by decide⟩}) := by
  decide

/-- At d=3, stab 4 (top-X boundary). -/
example :
    mkSurfaceHookErrors 3 (by decide) (by decide) ⟨4, by decide⟩ =
    ((SurfaceD3.hookErrors ⟨4, by decide⟩).toFinset ∪
     {SurfaceD3.stabilizers ⟨4, by decide⟩}) := by
  decide

/-- At d=3, stab 5 (right-Z boundary). -/
example :
    mkSurfaceHookErrors 3 (by decide) (by decide) ⟨5, by decide⟩ =
    ((SurfaceD3.hookErrors ⟨5, by decide⟩).toFinset ∪
     {SurfaceD3.stabilizers ⟨5, by decide⟩}) := by
  decide

/-- At d=3, stab 6 (left-Z boundary). -/
example :
    mkSurfaceHookErrors 3 (by decide) (by decide) ⟨6, by decide⟩ =
    ((SurfaceD3.hookErrors ⟨6, by decide⟩).toFinset ∪
     {SurfaceD3.stabilizers ⟨6, by decide⟩}) := by
  decide

/-- At d=3, stab 7 (bottom-X boundary). -/
example :
    mkSurfaceHookErrors 3 (by decide) (by decide) ⟨7, by decide⟩ =
    ((SurfaceD3.hookErrors ⟨7, by decide⟩).toFinset ∪
     {SurfaceD3.stabilizers ⟨7, by decide⟩}) := by
  decide

/-! ## Structural properties

The legacy file proves three structural facts about `hookErrors` (each by
`decide` at d=3). The parametric counterparts are stated below; we prove
the structural form via `Finset.card` and direct unfolding. -/

/-- Number of proper suffix hooks for each kind: bulks (length-4 schedule)
    give 3 hooks; boundaries (length-2 schedule) give 1. -/
theorem suffixIndices_length_bulk (d : Nat) (r c : Nat) :
    (suffixIndices d (.bulkZ r c)).length = 3 ∧
    (suffixIndices d (.bulkX r c)).length = 3 := by
  unfold suffixIndices kindOrderRC
  refine ⟨?_, ?_⟩ <;> simp

/-- Boundary kinds have a length-2 schedule, so exactly one proper suffix. -/
theorem suffixIndices_length_boundary (d : Nat) (b : Nat) :
    (suffixIndices d (.topX b)).length = 1 ∧
    (suffixIndices d (.rightZ b)).length = 1 ∧
    (suffixIndices d (.leftZ b)).length = 1 ∧
    (suffixIndices d (.bottomX b)).length = 1 := by
  unfold suffixIndices kindOrderRC
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

/-! ## d=5 / d=7 sanity inspection `#eval`s -/

-- d=5 bulks have 3 suffix hooks + 1 stab = 4 in the hook set.
#eval (suffixIndices 5 (.bulkZ 0 0)).length  -- 3
#eval (suffixIndices 5 (.bulkX 1 2)).length  -- 3
-- d=5 boundary has 1 suffix hook + 1 stab = 2 in the hook set.
#eval (suffixIndices 5 (.topX 0)).length     -- 1
#eval (suffixIndices 5 (.rightZ 1)).length   -- 1

-- d=7 spot checks.
#eval (suffixIndices 7 (.bulkZ 2 4)).length  -- 3
#eval (suffixIndices 7 (.bottomX 2)).length  -- 1

/-! ## Axiom check

The headline `mkSurfaceHookErrors` and its supporting structural theorems
are axiom-clean (only `propext` / `Classical.choice` / `Quot.sound` from
`mathlib`'s `Finset.image` decidability infrastructure). -/

#print axioms mkSurfaceHookErrors
#print axioms suffixHook
#print axioms suffixIndices
#print axioms kindOrderRC
#print axioms kindPauli
#print axioms suffixIndices_length_bulk
#print axioms suffixIndices_length_boundary
#print axioms kindPauli_eq_stabType

/-! ## Structural properties of `mkSurfaceHookErrors`

These are the Phase-4 (NZHookShape) consumer properties:

* `mkSurfaceHookErrors_weight_le` — every hook has weight ≤ `hookWeightBound = 4`.
* `mkSurfaceHookErrors_X_no_Z`    — hooks from X-stabs have no Z-component.
* `mkSurfaceHookErrors_Z_no_X`    — hooks from Z-stabs have no X-component.
* `mkSurfaceStabilizers_mem_hookErrors` — the full stabilizer is always a hook.
* `mkSurfaceHookErrors_X_rowRestricted` — X-stab hooks' X-components live in
  the X-stab's row-set.
* `mkSurfaceHookErrors_Z_colRestricted` — Z-stab hooks' Z-components live in
  the Z-stab's col-set.

We also expose the convenience predicates `isXStab d s`, `isZStab d s`,
and `supportSize d s` used by Phase 4.

Note: since `SurfaceParametric.lean` keeps many helper lemmas `private`,
we re-inline the small pieces (`decode_eq_I_or_stabType` body,
`classify_type_X`/`Z` body, `classifyStab_bulk{X,Z}_bounds` body, etc.) as
needed. The inlines are self-contained `simp [...]` / `split_ifs` patterns;
no axiom is added, no helper is duplicated as a real definition. -/

/-! ### Re-derived `decode_eq_I_or_stabType` (file-local copy)

`decode_eq_I_or_stabType` is `private` to `SurfaceParametric.lean`, so we
restate it here. Proof is identical (4-line `split_ifs <;> first | left | right`). -/

/-- Every value `decodeStabPauliAt d i row col` returns is either `I` or
    equals `stabType d i`. (Re-derivation of the `private` lemma in
    `SurfaceParametric.lean`.) -/
lemma decode_eq_I_or_stabType' (d i row col : Nat) :
    decodeStabPauliAt d i row col = Pauli.I ∨
    decodeStabPauliAt d i row col = stabType d i := by
  simp only [decodeStabPauliAt, stabType]
  split_ifs <;> first | (left; rfl) | (right; rfl)

/-- The Pauli kind of stabilizer `s`: `X` (top/bottom-X boundary or bulk-X)
    or `Z` (right/left-Z boundary or bulk-Z). Definitionally `stabType d s.val`. -/
def isXStab (d : Nat) (s : Fin (numStabFormula d)) : Prop :=
  stabType d s.val = Pauli.X

/-- See `isXStab`. -/
def isZStab (d : Nat) (s : Fin (numStabFormula d)) : Prop :=
  stabType d s.val = Pauli.Z

instance (d : Nat) (s : Fin (numStabFormula d)) : Decidable (isXStab d s) := by
  unfold isXStab; infer_instance

instance (d : Nat) (s : Fin (numStabFormula d)) : Decidable (isZStab d s) := by
  unfold isZStab; infer_instance

/-- The support size of stabilizer `s` at distance `d`: the length of its gate
    schedule `kindOrderRC d (classifyStab d s.val)`. By case analysis, this is
    either `2` (boundary kinds) or `4` (bulk kinds). -/
def supportSize (d : Nat) (s : Fin (numStabFormula d)) : Nat :=
  (kindOrderRC d (classifyStab d s.val)).length

/-! ### Length bound on `kindOrderRC` -/

/-- Every `kindOrderRC` list has length at most `hookWeightBound = 4`. -/
lemma kindOrderRC_length_le_four (d : Nat) (k : StabKind) :
    (kindOrderRC d k).length ≤ 4 := by
  cases k <;> simp [kindOrderRC]

/-- `supportSize d s ≤ hookWeightBound`. -/
lemma supportSize_le_hookWeightBound (d : Nat) (s : Fin (numStabFormula d)) :
    supportSize d s ≤ hookWeightBound := by
  unfold supportSize hookWeightBound
  exact kindOrderRC_length_le_four _ _

/-! ### Auxiliary: every entry of `suffixHook` is either `I` or `kindPauli k`

Because `suffixPairs d k j` is `((kindOrderRC d k).drop j).map (fun rc => (_, kindPauli k))`,
every Pauli value placed by `ofList` is `kindPauli k`. The `getD Pauli.I` default
handles the "lookup misses" case. -/

/-- For a list of pairs whose second components are all `c`, `List.lookup` returns
    either `none` or `some c`. -/
lemma lookup_map_const_snd {α : Type _} (l : List α) (f : α → Nat) (c : Pauli)
    (n : Nat) :
    (l.map (fun a => (f a, c))).lookup n = none ∨
    (l.map (fun a => (f a, c))).lookup n = some c := by
  induction l with
  | nil => left; rfl
  | cons a as ih =>
      simp only [List.map_cons, List.lookup]
      by_cases hbeq : (n == f a) = true
      · right
        rw [hbeq]
      · rw [Bool.not_eq_true] at hbeq
        rw [hbeq]
        simp only [cond_false]
        exact ih

/-- Every entry of `suffixHook d k j` is either `Pauli.I` or `kindPauli k`. -/
lemma suffixHook_eq_I_or_kindPauli (d : Nat) (k : StabKind) (j : Nat)
    (q : Fin (d * d)) :
    suffixHook d k j q = Pauli.I ∨ suffixHook d k j q = kindPauli k := by
  unfold suffixHook ofList suffixPairs
  rcases lookup_map_const_snd ((kindOrderRC d k).drop j)
      (fun rc => gridIdx d rc.1 rc.2) (kindPauli k) q.val with hnone | hsome
  · left; rw [hnone]; rfl
  · right; rw [hsome]; rfl

/-! ### Weight bound on `suffixHook`

By a counting argument: the support of `suffixHook d k j` is contained in the
set of qubit indices `gridIdx d rc.1 rc.2` for `rc` in the drop-list. -/

/-- If `q.val` is not in the keys list, lookup returns `none`. -/
lemma lookup_eq_none_of_notMem {α : Type _} (l : List α) (f : α → Nat) (c : Pauli)
    (n : Nat) (hnm : ∀ a ∈ l, n ≠ f a) :
    (l.map (fun a => (f a, c))).lookup n = none := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      simp only [List.map_cons, List.lookup]
      have hne : (n == f a) = false := by
        have : n ≠ f a := hnm a (by simp)
        exact decide_eq_false (by simpa)
      rw [hne]
      simp only [cond_false]
      exact ih (fun b hb => hnm b (List.mem_cons_of_mem _ hb))

/-- If `q.val` does not appear as a key in `suffixPairs`, then `suffixHook` is `I`. -/
lemma suffixHook_eq_I_of_idx_not_key (d : Nat) (k : StabKind) (j : Nat)
    (q : Fin (d * d))
    (hnm : ∀ rc ∈ ((kindOrderRC d k).drop j), q.val ≠ gridIdx d rc.1 rc.2) :
    suffixHook d k j q = Pauli.I := by
  unfold suffixHook ofList suffixPairs
  rw [lookup_eq_none_of_notMem _ _ _ _ hnm]
  rfl

/-- The weight of `suffixHook d k j` is bounded by `(kindOrderRC d k).length`,
    which in turn is at most `4`. -/
lemma suffixHook_weight_le_four (d : Nat) (k : StabKind) (j : Nat) :
    ErrorVec.weight (suffixHook d k j) ≤ 4 := by
  unfold ErrorVec.weight
  set keys : List Nat :=
    ((kindOrderRC d k).drop j).map (fun rc => gridIdx d rc.1 rc.2) with hkeys
  -- Show the filter is a subset of {q : Fin (d*d) | q.val ∈ keys}.
  -- Contrapositive: if i.val ∉ keys, then suffixHook = I (so i is not in support).
  have h_keys_to_I :
      ∀ i : Fin (d * d), i.val ∉ keys → suffixHook d k j i = Pauli.I := by
    intro i hmem
    apply suffixHook_eq_I_of_idx_not_key d k j i
    intro rc hrc heq
    apply hmem
    rw [hkeys]
    exact List.mem_map.mpr ⟨rc, hrc, heq.symm⟩
  have h_subset :
      (Finset.univ.filter fun i : Fin (d * d) => suffixHook d k j i ≠ Pauli.I) ⊆
      (Finset.univ.filter fun i : Fin (d * d) => i.val ∈ keys) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    -- Argue by Decidable: either i.val ∈ keys, or not.
    rcases Decidable.em (i.val ∈ keys) with h | h
    · exact h
    · exact absurd (h_keys_to_I i h) hi
  have h_card_le :
      (Finset.univ.filter fun i : Fin (d * d) => suffixHook d k j i ≠ Pauli.I).card
        ≤ (Finset.univ.filter fun i : Fin (d * d) => i.val ∈ keys).card :=
    Finset.card_le_card h_subset
  -- Now bound the keys-filter card by keys.length.
  have h_keys_card :
      (Finset.univ.filter fun i : Fin (d * d) => i.val ∈ keys).card ≤ keys.length := by
    have h_le_toFinset :
        (Finset.univ.filter fun i : Fin (d * d) => i.val ∈ keys).card ≤ keys.toFinset.card := by
      apply Finset.card_le_card_of_injOn (fun i : Fin (d * d) => i.val)
      · intro i hi
        have hi' : i.val ∈ keys := by
          have := (Finset.mem_coe.mp hi)
          exact (Finset.mem_filter.mp this).2
        rw [Finset.mem_coe, List.mem_toFinset]; exact hi'
      · intro i _ j _ heq
        exact Fin.ext heq
    exact h_le_toFinset.trans (List.toFinset_card_le _)
  calc (Finset.univ.filter fun i : Fin (d * d) => suffixHook d k j i ≠ Pauli.I).card
      ≤ (Finset.univ.filter fun i : Fin (d * d) => i.val ∈ keys).card := h_card_le
    _ ≤ keys.length := h_keys_card
    _ = ((kindOrderRC d k).drop j).length := by rw [hkeys, List.length_map]
    _ ≤ (kindOrderRC d k).length := by rw [List.length_drop]; omega
    _ ≤ 4 := kindOrderRC_length_le_four d k

/-! ### Headline: weight bound -/

/-! ### Stabilizer support is contained in the gridIdx-image of `kindOrderRC`

This is the geometric content: every (row, col) where `decodeStabPauliAt` is
non-I lies in the support `kindOrderRC d (classifyStab d s.val)`. -/

/-- If `decodeStabPauliAt d i row col ≠ I`, then `(row, col) ∈ kindOrderRC d
    (classifyStab d i)`. Proof is structural by case-split on both the support
    conditions of `decodeStabPauliAt` and the matching classifier branch. -/
lemma decode_ne_I_implies_in_kindOrderRC (d i row col : Nat)
    (hne : decodeStabPauliAt d i row col ≠ Pauli.I) :
    (row, col) ∈ kindOrderRC d (classifyStab d i) := by
  -- Strategy: case-analyze each branch of `decodeStabPauliAt` and explicitly
  -- choose the matching branch of `classifyStab` to reduce kindOrderRC.
  unfold decodeStabPauliAt at hne
  unfold classifyStab kindOrderRC
  by_cases hbulk : i < (d - 1) * (d - 1)
  · -- Bulk region.
    rw [if_pos hbulk] at hne
    by_cases hsupp : (row = i / (d - 1) ∨ row = i / (d - 1) + 1) ∧
                     (col = i % (d - 1) ∨ col = i % (d - 1) + 1)
    · -- In support.
      rw [if_pos hsupp] at hne
      rw [if_pos hbulk]
      by_cases hkind : (i / (d - 1) + i % (d - 1)) % 2 = 0
      · rw [if_pos hkind]
        simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq]
        obtain ⟨hrow, hcol⟩ := hsupp
        rcases hrow with rfl | rfl <;> rcases hcol with rfl | rfl <;> tauto
      · rw [if_neg hkind]
        simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq]
        obtain ⟨hrow, hcol⟩ := hsupp
        rcases hrow with rfl | rfl <;> rcases hcol with rfl | rfl <;> tauto
    · rw [if_neg hsupp] at hne; exact absurd rfl hne
  · -- Boundary region.
    rw [if_neg hbulk] at hne
    rw [if_neg hbulk]
    by_cases hTop : i - (d - 1) * (d - 1) < (d - 1) / 2
    · rw [if_pos hTop] at hne; rw [if_pos hTop]
      -- Top-X: support condition is `row = 0 ∧ (col = 2 * b ∨ col = 2 * b + 1)`.
      by_cases hsupp : row = 0 ∧ (col = 2 * (i - (d - 1) * (d - 1)) ∨
                                  col = 2 * (i - (d - 1) * (d - 1)) + 1)
      · rw [if_pos hsupp] at hne
        simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq]
        obtain ⟨hrow, hcol⟩ := hsupp
        rcases hcol with rfl | rfl <;> tauto
      · rw [if_neg hsupp] at hne; exact absurd rfl hne
    · rw [if_neg hTop] at hne; rw [if_neg hTop]
      by_cases hRight : i - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)
      · rw [if_pos hRight] at hne; rw [if_pos hRight]
        -- Right-Z: col = d-1 ∧ (row = 2*bb ∨ row = 2*bb + 1)
        by_cases hsupp : col = d - 1 ∧
            (row = 2 * (i - (d - 1) * (d - 1) - (d - 1) / 2) ∨
             row = 2 * (i - (d - 1) * (d - 1) - (d - 1) / 2) + 1)
        · rw [if_pos hsupp] at hne
          simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq]
          obtain ⟨hcol, hrow⟩ := hsupp
          rcases hrow with rfl | rfl <;> tauto
        · rw [if_neg hsupp] at hne; exact absurd rfl hne
      · rw [if_neg hRight] at hne; rw [if_neg hRight]
        by_cases hLeft : i - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)
        · rw [if_pos hLeft] at hne; rw [if_pos hLeft]
          -- Left-Z: col = 0 ∧ (row = 2*bb+1 ∨ row = 2*bb+2)
          by_cases hsupp : col = 0 ∧
              (row = 2 * (i - (d - 1) * (d - 1) - 2 * ((d - 1) / 2)) + 1 ∨
               row = 2 * (i - (d - 1) * (d - 1) - 2 * ((d - 1) / 2)) + 2)
          · rw [if_pos hsupp] at hne
            simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq]
            obtain ⟨hcol, hrow⟩ := hsupp
            rcases hrow with rfl | rfl <;> tauto
          · rw [if_neg hsupp] at hne; exact absurd rfl hne
        · rw [if_neg hLeft] at hne; rw [if_neg hLeft]
          -- Bottom-X: row = d-1 ∧ (col = 2*bb+1 ∨ col = 2*bb+2)
          by_cases hsupp : row = d - 1 ∧
              (col = 2 * (i - (d - 1) * (d - 1) - 3 * ((d - 1) / 2)) + 1 ∨
               col = 2 * (i - (d - 1) * (d - 1) - 3 * ((d - 1) / 2)) + 2)
          · rw [if_pos hsupp] at hne
            simp only [List.mem_cons, List.mem_singleton, Prod.mk.injEq]
            obtain ⟨hrow, hcol⟩ := hsupp
            rcases hcol with rfl | rfl <;> tauto
          · rw [if_neg hsupp] at hne; exact absurd rfl hne

/-- Weight of `mkSurfaceStabilizers` is at most `4`. -/
private lemma mkSurfaceStabilizers_weight_le_four (d : Nat) (hd : 0 < d)
    (s : Fin (numStabFormula d)) :
    ErrorVec.weight (mkSurfaceStabilizers d hd s) ≤ 4 := by
  unfold ErrorVec.weight mkSurfaceStabilizers
  -- Map each q in the support to a pair in kindOrderRC, then count.
  set k : StabKind := classifyStab d s.val with hk_def
  set keys : List Nat := (kindOrderRC d k).map (fun rc => gridIdx d rc.1 rc.2) with hkeys
  have h_subset :
      (Finset.univ.filter fun q : Fin (d * d) =>
        decodeStabPauliAt d s.val (q.val / d) (q.val % d) ≠ Pauli.I) ⊆
      (Finset.univ.filter fun i : Fin (d * d) => i.val ∈ keys) := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    have hmem := decode_ne_I_implies_in_kindOrderRC d s.val (q.val / d) (q.val % d) hq
    -- We need q.val ∈ keys = gridIdx-image of kindOrderRC.
    -- We have (q.val/d, q.val%d) ∈ kindOrderRC, so gridIdx (q.val/d) (q.val%d) ∈ keys.
    -- And gridIdx (q.val/d) (q.val%d) = d * (q.val/d) + (q.val%d) = q.val.
    have h_recon : gridIdx d (q.val / d) (q.val % d) = q.val := by
      unfold gridIdx
      exact (Nat.div_add_mod q.val d)
    rw [hkeys]
    rw [← h_recon]
    exact List.mem_map.mpr ⟨(q.val / d, q.val % d), hmem, rfl⟩
  have h_card_le :
      (Finset.univ.filter fun q : Fin (d * d) =>
        decodeStabPauliAt d s.val (q.val / d) (q.val % d) ≠ Pauli.I).card
        ≤ (Finset.univ.filter fun i : Fin (d * d) => i.val ∈ keys).card :=
    Finset.card_le_card h_subset
  have h_keys_card :
      (Finset.univ.filter fun i : Fin (d * d) => i.val ∈ keys).card ≤ keys.length := by
    have h_le_toFinset :
        (Finset.univ.filter fun i : Fin (d * d) => i.val ∈ keys).card ≤ keys.toFinset.card := by
      apply Finset.card_le_card_of_injOn (fun i : Fin (d * d) => i.val)
      · intro i hi
        have hi' : i.val ∈ keys := by
          have := (Finset.mem_coe.mp hi)
          exact (Finset.mem_filter.mp this).2
        rw [Finset.mem_coe, List.mem_toFinset]; exact hi'
      · intro i _ j _ heq
        exact Fin.ext heq
    exact h_le_toFinset.trans (List.toFinset_card_le _)
  calc (Finset.univ.filter fun q : Fin (d * d) =>
            decodeStabPauliAt d s.val (q.val / d) (q.val % d) ≠ Pauli.I).card
      ≤ (Finset.univ.filter fun i : Fin (d * d) => i.val ∈ keys).card := h_card_le
    _ ≤ keys.length := h_keys_card
    _ = (kindOrderRC d k).length := by rw [hkeys, List.length_map]
    _ ≤ 4 := kindOrderRC_length_le_four d k

/-- **Property 1.** Every hook in `mkSurfaceHookErrors` has weight at most
    `hookWeightBound = 4`. -/
theorem mkSurfaceHookErrors_weight_le (d : Nat) (hd : 0 < d) (hodd : d % 2 = 1)
    (s : Fin (numStabFormula d)) (e : ErrorVec (d * d))
    (he : e ∈ mkSurfaceHookErrors d hd hodd s) :
    ErrorVec.weight e ≤ hookWeightBound := by
  unfold mkSurfaceHookErrors at he
  simp only [Finset.mem_union, Finset.mem_image, List.mem_toFinset,
             Finset.mem_singleton] at he
  unfold hookWeightBound
  rcases he with ⟨j, _, rfl⟩ | rfl
  · exact suffixHook_weight_le_four d _ j
  · exact mkSurfaceStabilizers_weight_le_four d hd s

/-! ### Pauli-type purity (X-stabs ⇒ no Z, Z-stabs ⇒ no X) -/

/-- For an X-stab, `kindPauli (classifyStab d s.val) = Pauli.X`. -/
private lemma kindPauli_of_isXStab (d : Nat) (s : Fin (numStabFormula d))
    (hxs : isXStab d s) : kindPauli (classifyStab d s.val) = Pauli.X := by
  have h := kindPauli_eq_stabType d s.val
  unfold isXStab at hxs
  rw [h, hxs]

/-- For a Z-stab, `kindPauli (classifyStab d s.val) = Pauli.Z`. -/
private lemma kindPauli_of_isZStab (d : Nat) (s : Fin (numStabFormula d))
    (hzs : isZStab d s) : kindPauli (classifyStab d s.val) = Pauli.Z := by
  have h := kindPauli_eq_stabType d s.val
  unfold isZStab at hzs
  rw [h, hzs]

/-- For an X-stab, every entry of the full stabilizer is `I` or `X`. -/
private lemma mkSurfaceStabilizers_X_eq_I_or_X (d : Nat) (hd : 0 < d)
    (s : Fin (numStabFormula d)) (hxs : isXStab d s) (q : Fin (d * d)) :
    mkSurfaceStabilizers d hd s q = Pauli.I ∨ mkSurfaceStabilizers d hd s q = Pauli.X := by
  unfold mkSurfaceStabilizers
  have hi := decode_eq_I_or_stabType' d s.val (q.val / d) (q.val % d)
  unfold isXStab at hxs
  rcases hi with h | h
  · left; exact h
  · right; rw [h, hxs]

/-- For a Z-stab, every entry of the full stabilizer is `I` or `Z`. -/
private lemma mkSurfaceStabilizers_Z_eq_I_or_Z (d : Nat) (hd : 0 < d)
    (s : Fin (numStabFormula d)) (hzs : isZStab d s) (q : Fin (d * d)) :
    mkSurfaceStabilizers d hd s q = Pauli.I ∨ mkSurfaceStabilizers d hd s q = Pauli.Z := by
  unfold mkSurfaceStabilizers
  have hi := decode_eq_I_or_stabType' d s.val (q.val / d) (q.val % d)
  unfold isZStab at hzs
  rcases hi with h | h
  · left; exact h
  · right; rw [h, hzs]

/-- **Property 2.** Hooks from X-stabilizers have no Z-component (every entry
    is in `{I, X}`). -/
theorem mkSurfaceHookErrors_X_no_Z (d : Nat) (hd : 0 < d) (hodd : d % 2 = 1)
    (s : Fin (numStabFormula d)) (hxs : isXStab d s) (e : ErrorVec (d * d))
    (he : e ∈ mkSurfaceHookErrors d hd hodd s) :
    ∀ q, Pauli.hasZComponent (e q) = false := by
  intro q
  unfold mkSurfaceHookErrors at he
  simp only [Finset.mem_union, Finset.mem_image, List.mem_toFinset,
             Finset.mem_singleton] at he
  have hpX := kindPauli_of_isXStab d s hxs
  rcases he with ⟨j, _, rfl⟩ | rfl
  · -- Suffix-hook: each entry is I or kindPauli = X. Neither has Z-component.
    rcases suffixHook_eq_I_or_kindPauli d (classifyStab d s.val) j q with h | h
    · rw [h]; rfl
    · rw [h, hpX]; rfl
  · -- Full stabilizer: each entry is I or X. Neither has Z-component.
    rcases mkSurfaceStabilizers_X_eq_I_or_X d hd s hxs q with h | h
    · rw [h]; rfl
    · rw [h]; rfl

/-- **Property 3.** Hooks from Z-stabilizers have no X-component (every entry
    is in `{I, Z}`). -/
theorem mkSurfaceHookErrors_Z_no_X (d : Nat) (hd : 0 < d) (hodd : d % 2 = 1)
    (s : Fin (numStabFormula d)) (hzs : isZStab d s) (e : ErrorVec (d * d))
    (he : e ∈ mkSurfaceHookErrors d hd hodd s) :
    ∀ q, Pauli.hasXComponent (e q) = false := by
  intro q
  unfold mkSurfaceHookErrors at he
  simp only [Finset.mem_union, Finset.mem_image, List.mem_toFinset,
             Finset.mem_singleton] at he
  have hpZ := kindPauli_of_isZStab d s hzs
  rcases he with ⟨j, _, rfl⟩ | rfl
  · rcases suffixHook_eq_I_or_kindPauli d (classifyStab d s.val) j q with h | h
    · rw [h]; rfl
    · rw [h, hpZ]; rfl
  · rcases mkSurfaceStabilizers_Z_eq_I_or_Z d hd s hzs q with h | h
    · rw [h]; rfl
    · rw [h]; rfl

/-! ### The full stabilizer is always a hook -/

/-- **Property 4.** The full stabilizer `mkSurfaceStabilizers d hd s` is always
    an element of the hook-error set (directly via the singleton-union branch). -/
theorem mkSurfaceStabilizers_mem_hookErrors (d : Nat) (hd : 0 < d) (hodd : d % 2 = 1)
    (s : Fin (numStabFormula d)) :
    mkSurfaceStabilizers d hd s ∈ mkSurfaceHookErrors d hd hodd s := by
  unfold mkSurfaceHookErrors
  exact Finset.mem_union_right _ (Finset.mem_singleton.mpr rfl)

/-! ### Row/col restriction of X-components and Z-components

Every entry of `kindOrderRC d k` has its row coordinate in `kindRowSet d k`
and its col coordinate in `kindColSet d k`. This is structural by `cases k`. -/

/-- Every `(r, c) ∈ kindOrderRC d k` has `r ∈ kindRowSet d k`. -/
private lemma row_mem_kindRowSet (d : Nat) (k : StabKind)
    (rc : Nat × Nat) (h : rc ∈ kindOrderRC d k) :
    rc.1 ∈ kindRowSet d k := by
  cases k
  · -- bulkZ r c: 4 positions, rowSet = {r, r+1}
    simp only [kindOrderRC, List.mem_cons, List.not_mem_nil, or_false] at h
    simp only [kindRowSet, Finset.mem_insert, Finset.mem_singleton]
    rcases h with rfl | rfl | rfl | rfl <;> simp
  · -- bulkX r c
    simp only [kindOrderRC, List.mem_cons, List.not_mem_nil, or_false] at h
    simp only [kindRowSet, Finset.mem_insert, Finset.mem_singleton]
    rcases h with rfl | rfl | rfl | rfl <;> simp
  · -- topX b: 2 positions, rowSet = {0}
    simp only [kindOrderRC, List.mem_cons, List.not_mem_nil, or_false] at h
    simp only [kindRowSet, Finset.mem_singleton]
    rcases h with rfl | rfl <;> simp
  · -- rightZ b
    simp only [kindOrderRC, List.mem_cons, List.not_mem_nil, or_false] at h
    simp only [kindRowSet, Finset.mem_insert, Finset.mem_singleton]
    rcases h with rfl | rfl <;> simp
  · -- leftZ b
    simp only [kindOrderRC, List.mem_cons, List.not_mem_nil, or_false] at h
    simp only [kindRowSet, Finset.mem_insert, Finset.mem_singleton]
    rcases h with rfl | rfl <;> simp
  · -- bottomX b: rowSet = {d-1}
    simp only [kindOrderRC, List.mem_cons, List.not_mem_nil, or_false] at h
    simp only [kindRowSet, Finset.mem_singleton]
    rcases h with rfl | rfl <;> simp

/-- Every `(r, c) ∈ kindOrderRC d k` has `c ∈ kindColSet d k`. -/
private lemma col_mem_kindColSet (d : Nat) (k : StabKind)
    (rc : Nat × Nat) (h : rc ∈ kindOrderRC d k) :
    rc.2 ∈ kindColSet d k := by
  cases k
  · -- bulkZ r c
    simp only [kindOrderRC, List.mem_cons, List.not_mem_nil, or_false] at h
    simp only [kindColSet, Finset.mem_insert, Finset.mem_singleton]
    rcases h with rfl | rfl | rfl | rfl <;> simp
  · -- bulkX r c
    simp only [kindOrderRC, List.mem_cons, List.not_mem_nil, or_false] at h
    simp only [kindColSet, Finset.mem_insert, Finset.mem_singleton]
    rcases h with rfl | rfl | rfl | rfl <;> simp
  · -- topX b
    simp only [kindOrderRC, List.mem_cons, List.not_mem_nil, or_false] at h
    simp only [kindColSet, Finset.mem_insert, Finset.mem_singleton]
    rcases h with rfl | rfl <;> simp
  · -- rightZ b: colSet = {d-1}
    simp only [kindOrderRC, List.mem_cons, List.not_mem_nil, or_false] at h
    simp only [kindColSet, Finset.mem_singleton]
    rcases h with rfl | rfl <;> simp
  · -- leftZ b: colSet = {0}
    simp only [kindOrderRC, List.mem_cons, List.not_mem_nil, or_false] at h
    simp only [kindColSet, Finset.mem_singleton]
    rcases h with rfl | rfl <;> simp
  · -- bottomX b
    simp only [kindOrderRC, List.mem_cons, List.not_mem_nil, or_false] at h
    simp only [kindColSet, Finset.mem_insert, Finset.mem_singleton]
    rcases h with rfl | rfl <;> simp

/-- Helper: if `lookup` on a `map` of pairs returned a non-I, then there's a
    matching key in the list. -/
private lemma lookup_ne_I_implies_mem {α : Type _} (l : List α) (f : α → Nat)
    (c : Pauli) (n : Nat)
    (hne : ((l.map (fun a => (f a, c))).lookup n).getD Pauli.I ≠ Pauli.I) :
    ∃ a, a ∈ l ∧ n = f a := by
  induction l with
  | nil => simp [List.lookup] at hne
  | cons a as ih =>
      simp only [List.map_cons, List.lookup] at hne
      by_cases hbeq : (n == f a) = true
      · refine ⟨a, by simp, ?_⟩
        simpa [beq_iff_eq] using hbeq
      · rw [Bool.not_eq_true] at hbeq
        rw [hbeq] at hne
        simp only [cond_false] at hne
        obtain ⟨b, hmem, heq⟩ := ih hne
        exact ⟨b, List.mem_cons_of_mem _ hmem, heq⟩

/-- If `suffixHook d k j q ≠ I`, then `(q.val/d, q.val%d)` corresponds to some
    element of `(kindOrderRC d k).drop j` via `gridIdx`. -/
lemma suffixHook_support_implies_kindOrderRC (d : Nat) (hd : 0 < d)
    (k : StabKind) (j : Nat) (q : Fin (d * d))
    (hsupp : suffixHook d k j q ≠ Pauli.I) :
    ∃ rc, rc ∈ (kindOrderRC d k).drop j ∧ q.val = gridIdx d rc.1 rc.2 := by
  unfold suffixHook ofList suffixPairs at hsupp
  exact lookup_ne_I_implies_mem _ _ _ _ hsupp

/-- If a position `q` is in the support of `suffixHook d k j` (i.e. non-`I`),
    then `q.val / d ∈ kindRowSet d k`. -/
private lemma suffixHook_support_row_in_kindRowSet (d : Nat) (hd : 0 < d)
    (k : StabKind) (j : Nat) (q : Fin (d * d))
    (hsupp : suffixHook d k j q ≠ Pauli.I)
    (hrow_bd : ∀ rc ∈ kindOrderRC d k, rc.1 < d ∧ rc.2 < d) :
    q.val / d ∈ kindRowSet d k := by
  obtain ⟨rc, hmem, hq_eq⟩ :=
    suffixHook_support_implies_kindOrderRC d hd k j q hsupp
  have hmem_full : rc ∈ kindOrderRC d k := List.mem_of_mem_drop hmem
  have ⟨hr_lt, hc_lt⟩ := hrow_bd rc hmem_full
  -- q.val = d * rc.1 + rc.2 = gridIdx d rc.1 rc.2
  unfold gridIdx at hq_eq
  have h_div : q.val / d = rc.1 := by
    rw [hq_eq, Nat.mul_add_div hd, Nat.div_eq_of_lt hc_lt, Nat.add_zero]
  rw [h_div]
  exact row_mem_kindRowSet d k rc hmem_full

/-- If a position `q` is in the support of `suffixHook d k j`, then
    `q.val % d ∈ kindColSet d k`. -/
private lemma suffixHook_support_col_in_kindColSet (d : Nat) (hd : 0 < d)
    (k : StabKind) (j : Nat) (q : Fin (d * d))
    (hsupp : suffixHook d k j q ≠ Pauli.I)
    (hrow_bd : ∀ rc ∈ kindOrderRC d k, rc.1 < d ∧ rc.2 < d) :
    q.val % d ∈ kindColSet d k := by
  obtain ⟨rc, hmem, hq_eq⟩ :=
    suffixHook_support_implies_kindOrderRC d hd k j q hsupp
  have hmem_full : rc ∈ kindOrderRC d k := List.mem_of_mem_drop hmem
  have ⟨hr_lt, hc_lt⟩ := hrow_bd rc hmem_full
  unfold gridIdx at hq_eq
  have h_mod : q.val % d = rc.2 := by
    rw [hq_eq, Nat.mul_add_mod, Nat.mod_eq_of_lt hc_lt]
  rw [h_mod]
  exact col_mem_kindColSet d k rc hmem_full

/-- Index bound discharger: every `(r, c)` in `kindOrderRC d k` has `r < d ∧ c < d`,
    provided the kind's classifying bounds hold (X-side dispatcher). -/
lemma kindOrderRC_in_bounds_X (d : Nat) (hodd : d % 2 = 1) (k : StabKind)
    (hX : (∃ r c, k = .bulkX r c ∧ r + 1 < d ∧ c + 1 < d ∧ (r + c) % 2 = 1) ∨
          (∃ b, k = .topX b ∧ b < (d - 1) / 2) ∨
          (∃ b, k = .bottomX b ∧ b < (d - 1) / 2)) :
    ∀ rc ∈ kindOrderRC d k, rc.1 < d ∧ rc.2 < d := by
  intro rc hmem
  rcases hX with ⟨r, c, rfl, hr, hc, _⟩ | ⟨b, rfl, hb⟩ | ⟨b, rfl, hb⟩ <;>
    simp [kindOrderRC, List.mem_cons, Prod.mk.injEq] at hmem
  · rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      refine ⟨by omega, by omega⟩
  · -- topX b: [(0, 2b), (0, 2b+1)]; 2b + 1 < d follows from b < (d-1)/2 and d > 0.
    have h2b : 2 * b + 1 < d := by
      have h2bd : 2 * b < 2 * ((d - 1) / 2) :=
        Nat.mul_lt_mul_left (by decide : 0 < 2) |>.mpr hb
      have hd_eq : 2 * ((d - 1) / 2) = d - 1 := by
        have := Nat.div_add_mod (d - 1) 2
        have hmod : (d - 1) % 2 = 0 := by omega
        omega
      omega
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      refine ⟨by omega, by omega⟩
  · -- bottomX b: [(d-1, 2b+1), (d-1, 2b+2)]
    have h2b : 2 * b + 2 ≤ d - 1 := by
      have h2bd : 2 * b < 2 * ((d - 1) / 2) :=
        Nat.mul_lt_mul_left (by decide : 0 < 2) |>.mpr hb
      have hd_eq : 2 * ((d - 1) / 2) = d - 1 := by
        have := Nat.div_add_mod (d - 1) 2
        have hmod : (d - 1) % 2 = 0 := by omega
        omega
      omega
    have hd_pos : 0 < d := by omega
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      refine ⟨by omega, by omega⟩

/-- Z-side index bound dispatcher. -/
private lemma kindOrderRC_in_bounds_Z (d : Nat) (hodd : d % 2 = 1) (k : StabKind)
    (hZ : (∃ r c, k = .bulkZ r c ∧ r + 1 < d ∧ c + 1 < d ∧ (r + c) % 2 = 0) ∨
          (∃ b, k = .rightZ b ∧ b < (d - 1) / 2) ∨
          (∃ b, k = .leftZ b ∧ b < (d - 1) / 2)) :
    ∀ rc ∈ kindOrderRC d k, rc.1 < d ∧ rc.2 < d := by
  intro rc hmem
  rcases hZ with ⟨r, c, rfl, hr, hc, _⟩ | ⟨b, rfl, hb⟩ | ⟨b, rfl, hb⟩ <;>
    simp [kindOrderRC, List.mem_cons, Prod.mk.injEq] at hmem
  · rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      refine ⟨by omega, by omega⟩
  · -- rightZ b: [(2b, d-1), (2b+1, d-1)]; need 2b+1 < d.
    have h2b : 2 * b + 1 < d := by
      have h2bd : 2 * b < 2 * ((d - 1) / 2) :=
        Nat.mul_lt_mul_left (by decide : 0 < 2) |>.mpr hb
      have hd_eq : 2 * ((d - 1) / 2) = d - 1 := by
        have := Nat.div_add_mod (d - 1) 2
        have hmod : (d - 1) % 2 = 0 := by omega
        omega
      omega
    have hd_pos : 0 < d := by omega
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      refine ⟨by omega, by omega⟩
  · -- leftZ b: [(2b+1, 0), (2b+2, 0)]; need 2b+2 < d.
    have h2b : 2 * b + 2 ≤ d - 1 := by
      have h2bd : 2 * b < 2 * ((d - 1) / 2) :=
        Nat.mul_lt_mul_left (by decide : 0 < 2) |>.mpr hb
      have hd_eq : 2 * ((d - 1) / 2) = d - 1 := by
        have := Nat.div_add_mod (d - 1) 2
        have hmod : (d - 1) % 2 = 0 := by omega
        omega
      omega
    have hd_pos : 0 < d := by omega
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      refine ⟨by omega, by omega⟩

/-! ### File-local re-derivations of the `private` `classify_type_X/Z` and
    `classifyStab_*_bounds` lemmas. -/

private lemma classify_type_X' (d i : Nat) :
    stabType d i = Pauli.X ↔
      (∃ r c, classifyStab d i = StabKind.bulkX r c) ∨
      (∃ b, classifyStab d i = StabKind.topX b) ∨
      (∃ b, classifyStab d i = StabKind.bottomX b) := by
  simp only [stabType, classifyStab]
  split_ifs with hbulk hkind hTop hRight hLeft <;> simp

private lemma classify_type_Z' (d i : Nat) :
    stabType d i = Pauli.Z ↔
      (∃ r c, classifyStab d i = StabKind.bulkZ r c) ∨
      (∃ b, classifyStab d i = StabKind.rightZ b) ∨
      (∃ b, classifyStab d i = StabKind.leftZ b) := by
  simp only [stabType, classifyStab]
  split_ifs with hbulk hkind hTop hRight hLeft <;> simp

private lemma classifyStab_bulkZ_bounds' (d i r c : Nat)
    (h : classifyStab d i = .bulkZ r c) :
    r + 1 < d ∧ c + 1 < d ∧ (r + c) % 2 = 0 := by
  simp only [classifyStab] at h
  split_ifs at h with hbulk hpar
  injection h with hr_eq hc_eq
  subst hr_eq; subst hc_eq
  have hdmone_pos : 0 < d - 1 := by
    rcases Nat.eq_zero_or_pos (d - 1) with hzero | hpos
    · exfalso; rw [hzero, Nat.mul_zero] at hbulk; omega
    · exact hpos
  have hr_lt : i / (d - 1) < d - 1 :=
    Nat.div_lt_iff_lt_mul hdmone_pos |>.mpr (by rw [Nat.mul_comm]; exact hbulk)
  have hc_lt : i % (d - 1) < d - 1 := Nat.mod_lt _ hdmone_pos
  exact ⟨by omega, by omega, hpar⟩

private lemma classifyStab_bulkX_bounds' (d i r c : Nat)
    (h : classifyStab d i = .bulkX r c) :
    r + 1 < d ∧ c + 1 < d ∧ (r + c) % 2 = 1 := by
  simp only [classifyStab] at h
  split_ifs at h with hbulk hpar
  injection h with hr_eq hc_eq
  subst hr_eq; subst hc_eq
  have hdmone_pos : 0 < d - 1 := by
    rcases Nat.eq_zero_or_pos (d - 1) with hzero | hpos
    · exfalso; rw [hzero, Nat.mul_zero] at hbulk; omega
    · exact hpos
  have hr_lt : i / (d - 1) < d - 1 :=
    Nat.div_lt_iff_lt_mul hdmone_pos |>.mpr (by rw [Nat.mul_comm]; exact hbulk)
  have hc_lt : i % (d - 1) < d - 1 := Nat.mod_lt _ hdmone_pos
  refine ⟨by omega, by omega, ?_⟩
  omega

private lemma classifyStab_topX_bounds' (d i b : Nat)
    (h : classifyStab d i = .topX b) :
    b < (d - 1) / 2 := by
  simp only [classifyStab] at h
  split_ifs at h with hbulk hpar hTop
  injection h with heq
  subst heq
  exact hTop

private lemma classifyStab_rightZ_bounds' (d i b : Nat)
    (h : classifyStab d i = .rightZ b) :
    b < (d - 1) / 2 := by
  simp only [classifyStab] at h
  split_ifs at h with hbulk hpar hTop hRight
  injection h with heq
  subst heq
  omega

private lemma classifyStab_leftZ_bounds' (d i b : Nat)
    (h : classifyStab d i = .leftZ b) :
    b < (d - 1) / 2 := by
  simp only [classifyStab] at h
  split_ifs at h with hbulk hpar hTop hRight hLeft
  injection h with heq
  subst heq
  omega

private lemma classifyStab_bottomX_bounds' (d i b : Nat) (hodd : d % 2 = 1)
    (hi : i < (d - 1) * (d - 1) + 2 * (d - 1))
    (h : classifyStab d i = .bottomX b) :
    b < (d - 1) / 2 := by
  simp only [classifyStab] at h
  split_ifs at h with hbulk hpar hTop hRight hLeft
  injection h with heq
  subst heq
  have hmod : (d - 1) % 2 = 0 := by omega
  have := Nat.div_add_mod (d - 1) 2
  omega

/-- Bridge: extract the X-side classification witnesses from an `isXStab`
    stabilizer at `d ≥ 3, odd d`. -/
lemma xStab_classify_witness (d : Nat) (hd : 3 ≤ d) (hodd : d % 2 = 1)
    (s : Fin (numStabFormula d)) (hxs : isXStab d s) :
    (∃ r c, classifyStab d s.val = .bulkX r c ∧
            r + 1 < d ∧ c + 1 < d ∧ (r + c) % 2 = 1) ∨
    (∃ b, classifyStab d s.val = .topX b ∧ b < (d - 1) / 2) ∨
    (∃ b, classifyStab d s.val = .bottomX b ∧ b < (d - 1) / 2) := by
  have hs_lt : s.val < (d - 1) * (d - 1) + 2 * (d - 1) := by
    have hs := s.isLt
    unfold numStabFormula at hs
    have h1 : (d - 1) * (d - 1) + 2 * (d - 1) ≥ 1 := by
      have hdm : d - 1 ≥ 2 := by omega
      have hmul : (d - 1) * (d - 1) ≥ 1 := by
        calc 1 ≤ (d - 1) := by omega
          _ ≤ (d - 1) * (d - 1) := Nat.le_mul_of_pos_left _ (by omega)
      omega
    omega
  unfold isXStab at hxs
  rcases (classify_type_X' d s.val).mp hxs with ⟨r, c, hcl⟩ | ⟨b, hcl⟩ | ⟨b, hcl⟩
  · obtain ⟨hr, hc, hpar⟩ := classifyStab_bulkX_bounds' d s.val r c hcl
    exact Or.inl ⟨r, c, hcl, hr, hc, hpar⟩
  · exact Or.inr (Or.inl ⟨b, hcl, classifyStab_topX_bounds' d s.val b hcl⟩)
  · exact Or.inr (Or.inr ⟨b, hcl,
      classifyStab_bottomX_bounds' d s.val b hodd hs_lt hcl⟩)

/-- Bridge for Z-side. -/
private lemma zStab_classify_witness (d : Nat) (hd : 3 ≤ d) (hodd : d % 2 = 1)
    (s : Fin (numStabFormula d)) (hzs : isZStab d s) :
    (∃ r c, classifyStab d s.val = .bulkZ r c ∧
            r + 1 < d ∧ c + 1 < d ∧ (r + c) % 2 = 0) ∨
    (∃ b, classifyStab d s.val = .rightZ b ∧ b < (d - 1) / 2) ∨
    (∃ b, classifyStab d s.val = .leftZ b ∧ b < (d - 1) / 2) := by
  unfold isZStab at hzs
  rcases (classify_type_Z' d s.val).mp hzs with ⟨r, c, hcl⟩ | ⟨b, hcl⟩ | ⟨b, hcl⟩
  · obtain ⟨hr, hc, hpar⟩ := classifyStab_bulkZ_bounds' d s.val r c hcl
    exact Or.inl ⟨r, c, hcl, hr, hc, hpar⟩
  · exact Or.inr (Or.inl ⟨b, hcl, classifyStab_rightZ_bounds' d s.val b hcl⟩)
  · exact Or.inr (Or.inr ⟨b, hcl, classifyStab_leftZ_bounds' d s.val b hcl⟩)

/-- For the full stabilizer at an X-stab, X-component at `q` implies
    `q.val / d ∈ kindRowSet`. -/
lemma mkSurfaceStabilizers_X_row (d : Nat) (hd : 0 < d) (hodd : d % 2 = 1)
    (s : Fin (numStabFormula d)) (hxs : isXStab d s)
    (q : Fin (d * d)) (h_supp : Pauli.hasXComponent (mkSurfaceStabilizers d hd s q) = true) :
    q.val / d ∈ kindRowSet d (classifyStab d s.val) := by
  -- Reduce hasXComponent = true to mkSurfaceStabilizers q ≠ I (since values
  -- are I or X for X-stabs).
  have h_ne_I : mkSurfaceStabilizers d hd s q ≠ Pauli.I := by
    intro h_I; rw [h_I] at h_supp; exact Bool.false_ne_true h_supp
  unfold mkSurfaceStabilizers at h_ne_I
  have hmem : (q.val / d, q.val % d) ∈ kindOrderRC d (classifyStab d s.val) :=
    decode_ne_I_implies_in_kindOrderRC d s.val (q.val / d) (q.val % d) h_ne_I
  exact row_mem_kindRowSet d (classifyStab d s.val) (q.val / d, q.val % d) hmem

/-- Mirror: Z-stab full stabilizer with Z-component implies col in colSet. -/
private lemma mkSurfaceStabilizers_Z_col (d : Nat) (hd : 0 < d) (hodd : d % 2 = 1)
    (s : Fin (numStabFormula d)) (hzs : isZStab d s)
    (q : Fin (d * d)) (h_supp : Pauli.hasZComponent (mkSurfaceStabilizers d hd s q) = true) :
    q.val % d ∈ kindColSet d (classifyStab d s.val) := by
  have h_ne_I : mkSurfaceStabilizers d hd s q ≠ Pauli.I := by
    intro h_I; rw [h_I] at h_supp; exact Bool.false_ne_true h_supp
  unfold mkSurfaceStabilizers at h_ne_I
  have hmem : (q.val / d, q.val % d) ∈ kindOrderRC d (classifyStab d s.val) :=
    decode_ne_I_implies_in_kindOrderRC d s.val (q.val / d) (q.val % d) h_ne_I
  exact col_mem_kindColSet d (classifyStab d s.val) (q.val / d, q.val % d) hmem

/-- **Property 5.** All X-stabilizer hooks are *row-restricted*: every position
    with non-zero X-component lies in a row from `kindRowSet d (classifyStab d s.val)`.

    Requires `d ≥ 3` (odd surface code regime) since the X-side bounds for
    `classifyStab` depend on `numStabFormula` being non-degenerate. -/
theorem mkSurfaceHookErrors_X_rowRestricted (d : Nat) (hd : 3 ≤ d) (hodd : d % 2 = 1)
    (s : Fin (numStabFormula d)) (hxs : isXStab d s) (e : ErrorVec (d * d))
    (he : e ∈ mkSurfaceHookErrors d (by omega) hodd s) :
    ∀ q, Pauli.hasXComponent (e q) = true →
         q.val / d ∈ kindRowSet d (classifyStab d s.val) := by
  intro q hq
  have hd_pos : 0 < d := by omega
  have hX_witness := xStab_classify_witness d hd hodd s hxs
  have hbd := kindOrderRC_in_bounds_X d hodd (classifyStab d s.val) hX_witness
  unfold mkSurfaceHookErrors at he
  simp only [Finset.mem_union, Finset.mem_image, List.mem_toFinset,
             Finset.mem_singleton] at he
  rcases he with ⟨j, _, rfl⟩ | rfl
  · -- Suffix hook: use suffixHook_support_row_in_kindRowSet.
    -- First show q is in the suffix's support (e q ≠ I).
    have hp_eq_X := kindPauli_of_isXStab d s hxs
    have h_ne_I : suffixHook d (classifyStab d s.val) j q ≠ Pauli.I := by
      intro h_I; rw [h_I] at hq; exact Bool.false_ne_true hq
    exact suffixHook_support_row_in_kindRowSet d hd_pos (classifyStab d s.val) j q
            h_ne_I hbd
  · -- Full stabilizer branch.
    exact mkSurfaceStabilizers_X_row d hd_pos hodd s hxs q hq

/-- **Property 6.** All Z-stabilizer hooks are *col-restricted*: every position
    with non-zero Z-component lies in a column from
    `kindColSet d (classifyStab d s.val)`. -/
theorem mkSurfaceHookErrors_Z_colRestricted (d : Nat) (hd : 3 ≤ d) (hodd : d % 2 = 1)
    (s : Fin (numStabFormula d)) (hzs : isZStab d s) (e : ErrorVec (d * d))
    (he : e ∈ mkSurfaceHookErrors d (by omega) hodd s) :
    ∀ q, Pauli.hasZComponent (e q) = true →
         q.val % d ∈ kindColSet d (classifyStab d s.val) := by
  intro q hq
  have hd_pos : 0 < d := by omega
  have hZ_witness := zStab_classify_witness d hd hodd s hzs
  have hbd := kindOrderRC_in_bounds_Z d hodd (classifyStab d s.val) hZ_witness
  unfold mkSurfaceHookErrors at he
  simp only [Finset.mem_union, Finset.mem_image, List.mem_toFinset,
             Finset.mem_singleton] at he
  rcases he with ⟨j, _, rfl⟩ | rfl
  · have hp_eq_Z := kindPauli_of_isZStab d s hzs
    have h_ne_I : suffixHook d (classifyStab d s.val) j q ≠ Pauli.I := by
      intro h_I; rw [h_I] at hq; exact Bool.false_ne_true hq
    exact suffixHook_support_col_in_kindColSet d hd_pos (classifyStab d s.val) j q
            h_ne_I hbd
  · exact mkSurfaceStabilizers_Z_col d hd_pos hodd s hzs q hq

/-! ## Axiom check (extended) -/

#print axioms mkSurfaceHookErrors_weight_le
#print axioms mkSurfaceHookErrors_X_no_Z
#print axioms mkSurfaceHookErrors_Z_no_X
#print axioms mkSurfaceStabilizers_mem_hookErrors
#print axioms mkSurfaceHookErrors_X_rowRestricted
#print axioms mkSurfaceHookErrors_Z_colRestricted

/-! ## d=3 sanity: parametric vs legacy

**Honest CRITICAL note on shape.**

The legacy `SurfaceD3.hookErrors : Fin 8 → List (ErrorVec 9)` enumerates
only the **proper suffix hooks** (the `j ∈ {1, …, |support|−1}` slice of
the gate schedule). It does **NOT** include the full stabilizer (the
`j = 0` slice). Per the d=3 table in `SurfaceVerification.lean:612-636`:

* `hookErrors s` has length 3 for the 4 bulk stabilizers (j = 1, 2, 3)
* `hookErrors s` has length 1 for the 4 boundary stabilizers (j = 1)

The parametric `mkSurfaceHookErrors d hd hodd s` *additionally* unions in
the stabilizer itself via `∪ {mkSurfaceStabilizers d hd s}`, matching the
`SurfaceD3PCC.backActionSet` convention (Phase E.2): the back-action set
contains every NZ-suffix hook *plus* the parent stabilizer (which is the
`j = 0` weight-`|support|` worst case). At d=3 the parametric per-stab
cardinalities are 4/4/4/4/2/2/2/2 = legacy 3/3/3/3/1/1/1/1 + 1 stab each.

Therefore the **literal** equality `mkSurfaceHookErrors = SurfaceD3.hookErrors`
is FALSE — the parametric set is a strict superset (by exactly the
stabilizer). This is intentional and documented; revising the parametric
definition to drop the stabilizer union would *break* `Phase E.2.b`'s
`PNZ_d3_nonSuccess` headline (which validated `|allHooks_PNZ| = 16`,
i.e. 8 stabs × (1 hook + 1 stab) for the 4 boundaries plus 8 stabs ×
(3 hooks + 1 stab) for the 4 bulks). The honest equality is therefore:

  `mkSurfaceHookErrors 3 hd hodd s
     = (SurfaceD3.hookErrors (mapD3StabIdx s)).toFinset
       ∪ {SurfaceD3.stabilizers (mapD3StabIdx s)}`

where `mapD3StabIdx : Fin (numStabFormula 3) → Fin 8` is the identity
(since `numStabFormula 3 = max 1 (2·2 + 2·2) = 8`). Proven below by
`fin_cases` + per-case `decide` (kernel reduction, NO `native_decide`).
-/

/-- At `d = 3`, `numStabFormula 3 = 8`, so the parametric stabilizer
    index type `Fin (numStabFormula 3)` coincides definitionally with the
    legacy `Fin 8`. The map is the identity. -/
def mapD3StabIdx (s : Fin (numStabFormula 3)) : Fin 8 :=
  ⟨s.val, by
    have : s.val < numStabFormula 3 := s.isLt
    simpa [numStabFormula] using this⟩

/-- Headline d=3 sanity: the parametric NZ hook-error set agrees with
    the legacy `SurfaceD3.hookErrors` (treated as a `Finset` via `toFinset`)
    augmented with the stabilizer itself, stabilizer-by-stabilizer. The
    augmentation reflects the `backActionSet := hookErrors ∪ {T_s}`
    convention used by `SurfaceD3PCC`. -/
theorem mkSurfaceHookErrors_d3_eq_legacy :
    ∀ s : Fin (numStabFormula 3),
      mkSurfaceHookErrors 3 (by decide) (by decide) s =
        ((SurfaceD3.hookErrors (mapD3StabIdx s)).toFinset ∪
         {SurfaceD3.stabilizers (mapD3StabIdx s)}) := by
  intro s
  fin_cases s <;> decide

#print axioms mkSurfaceHookErrors_d3_eq_legacy

/-! ## Parametric `QECParams` with the new `backActionSet`

The parametric rotated-surface-code `QECParams` at distance `d > 0` now wires
its `backActionSet` to the parametric NZ hook-error enumeration
`mkSurfaceHookErrors d hd hodd`, lifted to a `Set` via comprehension. The
weight bound `r := hookWeightBound = 4` is discharged by
`mkSurfaceHookErrors_weight_le`.

The constructor requires `hodd : d % 2 = 1` (matching `mkSurfaceHookErrors`
and `stab_commute_parametric`). It lives here rather than in
`SurfaceParametric.lean` because `mkSurfaceHookErrors` is defined in this
file; defining the constructor here keeps the import graph acyclic. -/

/-- Parametric rotated-surface-code `QECParams` at odd distance `d ≥ 1`.

* `stabilizers := mkSurfaceStabilizers d hd` — Phase-2 closed-form family.
* `backActionSet s` — Set comprehension over the Finset `mkSurfaceHookErrors d hd hodd s`.
* `r := hookWeightBound = 4` — every hook (proper suffix or full stabilizer) has weight ≤ 4.
* `backAction_weight_bound` — discharged by `mkSurfaceHookErrors_weight_le`. -/
def mkSurfaceQECParams (d : Nat) (hd : 0 < d) (hodd : d % 2 = 1) : QECParams where
  n        := d * d
  k        := 1
  d        := d
  R        := 1
  numStab  := numStabFormula d
  stabilizers := mkSurfaceStabilizers d hd
  backActionSet := fun s => { e | e ∈ mkSurfaceHookErrors d hd hodd s }
  r        := hookWeightBound
  backAction_weight_bound := by
    intro s e he
    exact mkSurfaceHookErrors_weight_le d hd hodd s e he
  C_budget := errorBudget d
  hn  := Nat.mul_pos hd hd
  hns := by
    show 0 < numStabFormula d
    unfold numStabFormula
    exact Nat.lt_of_lt_of_le (by decide : (0 : Nat) < 1) (le_max_left _ _)
  hR  := by decide

/-! ## Sanity #evals on arithmetic fields -/

example : (mkSurfaceQECParams 3 (by decide) (by decide)).n = 9 := rfl
example : (mkSurfaceQECParams 5 (by decide) (by decide)).n = 25 := rfl
example : (mkSurfaceQECParams 7 (by decide) (by decide)).n = 49 := rfl

#eval (mkSurfaceQECParams 3 (by decide) (by decide)).n        -- 9
#eval (mkSurfaceQECParams 5 (by decide) (by decide)).n        -- 25
#eval (mkSurfaceQECParams 7 (by decide) (by decide)).n        -- 49
#eval (mkSurfaceQECParams 3 (by decide) (by decide)).numStab  -- 8
#eval (mkSurfaceQECParams 5 (by decide) (by decide)).numStab  -- 24
#eval (mkSurfaceQECParams 7 (by decide) (by decide)).numStab  -- 48
#eval (mkSurfaceQECParams 3 (by decide) (by decide)).r        -- 4
#eval (mkSurfaceQECParams 5 (by decide) (by decide)).C_budget -- 2

#print axioms mkSurfaceQECParams

end QStab.Examples.SurfaceParametric
