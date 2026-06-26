import QStab.Examples.SurfaceParametric
import QStab.Examples.SurfaceGeneral
import QStab.Examples.SurfaceHookErrors
import QStab.Paper.SurfaceBarrier

/-! # Parametric row-step stabilizer witness for the rotated surface code

This file builds the **parametric row-step stabilizer witness** that the
`NZSurfaceSpec.rowCut_succ` field will eventually consume.  Concretely, for
each row index `i : Fin d` with `i.val + 1 < d` we exhibit a list of
parametric stabilizer indices whose `mkSurfaceStabilizers`-product equals the
Z-on-`{row i, row i+1}` operator.  In particular:

* `rowStepStabs d i` — the list of stabilizer-index `Fin (numStabFormula d)`
  values whose mkSurfaceStabilizers-product implements the row-step from
  row `i` to row `i + 1`.
* `rowStepWitness d hd i` — the `ErrorVec (d * d)` obtained by taking the
  list-product of `mkSurfaceStabilizers d hd` over `rowStepStabs d i`.
* `rowStepWitness_inStab` — `InStab (mkSurfaceQECParams d hd hodd)`
  membership, proved by structural induction on the list.

The structural breakdown (for **odd** `d ≥ 3`) is:

* Bulk-Z stabilizers at grid coord `(r = i, c)` for every `c ∈ {0, …, d-2}`
  with `(i + c) % 2 = 0`.  These together cover `(row i ∪ row i+1)` at every
  *middle* column, plus column `0` (if `i` even) or column `d-1` (if `i` odd).
* One boundary Z stabilizer to cap off the missing edge:
  * if `i` even: `rightZ` boundary at `b = i / 2` (covers col `d-1`, rows `{2b, 2b+1}`);
  * if `i` odd:  `leftZ`  boundary at `b = (i - 1) / 2` (covers col `0`, rows `{2b+1, 2b+2}`).

At `d = 3, i = 0` (even) this is `[bulkZ(0, 0), rightZ(0)] = [s1, s6]`,
matching the existing handwritten `D3Witness.rowCutFin_succ_0` exactly.
At `d = 3, i = 1` (odd) this is `[bulkZ(1, 1), leftZ(0)] = [s4, s7]`,
matching `D3Witness.rowCutFin_succ_1` exactly.

## Status

This file delivers the **first two of three** conjuncts of
`NZSurfaceSpec.rowCut_succ` for the canonical parametric surface code
`mkSurfaceQECParams d _ hodd`:

1. **`rowStepWitness_inStab_mkSurfaceQECParams`** — the witness `S` lies in
   `InStab (mkSurfaceQECParams d _ hodd)`.  Axiom-clean
   `[propext, Classical.choice, Quot.sound]`.
2. **`rowStepWitness_I_or_Z`** — `S q ∈ {I, Z}` for every qubit.  Axiom-clean
   `[propext, Quot.sound]`.

The **third conjunct** (`rowCut (i+1) = ErrorVec.mul S (rowCut i)`) is NOT
proved at parametric `d` — only verified concretely at `d = 3` and `d = 5`
via closed `decide` (see the `example`s at the end of this file).  The
parametric pointwise verification requires a per-qubit enumeration over the
bulk-Z parity structure and the {left, right}-Z boundary patches, estimated
at ~300+ LOC; it is deferred to a follow-up workflow.

## Discipline

* No `sorry`, `native_decide`, `Classical.choose`, `Exists.choose`, or
  `by_contra` is used.
* `decide` is used only on **finite, closed** equality checks at concrete
  `d = 3, 5` sanity tests (consistent with the rest of `SurfaceParametric`).
-/

namespace QStab.Examples.SurfaceParametric

open QStab QStab.Examples

/-! ## Encoding of stabilizer indices in `Fin (numStabFormula d)`

`mkSurfaceStabilizers` lays out generators in paper-order:

* indices `0 .. (d-1)² - 1` — bulk plaquettes at `(r, c)` with
  `r = i / (d-1)`, `c = i % (d-1)`.
* indices `(d-1)² + b` with `0 ≤ b < (d-1)/2`        — top-X boundaries.
* indices `(d-1)² + half + b` with `0 ≤ b < (d-1)/2` — right-Z boundaries.
* indices `(d-1)² + 2*half + b`                       — left-Z boundaries.
* indices `(d-1)² + 3*half + b`                       — bottom-X boundaries.

The helper `bulkIdx`, `rightZIdx`, `leftZIdx` produce raw `Nat` indices into
the appropriate slot, together with the `< numStabFormula d` bounds. -/

/-- The raw `Nat` index of the bulk plaquette stabilizer at grid coord
    `(r, c)` (with `r < d-1`, `c < d-1`).  Independent of the parity of
    `r + c`; the parity dictates whether the resulting stabilizer is
    `bulkZ` or `bulkX`. -/
def bulkIdx (d r c : Nat) : Nat := r * (d - 1) + c

/-- The raw `Nat` index of the `rightZ` boundary stabilizer with offset `b`
    (covering col `d-1`, rows `{2b, 2b+1}`). -/
def rightZIdx (d b : Nat) : Nat := (d - 1) * (d - 1) + (d - 1) / 2 + b

/-- The raw `Nat` index of the `leftZ` boundary stabilizer with offset `b`
    (covering col `0`, rows `{2b+1, 2b+2}`). -/
def leftZIdx (d b : Nat) : Nat := (d - 1) * (d - 1) + 2 * ((d - 1) / 2) + b

/-! ### `classifyStab` agreement (sanity)

These lemmas confirm that the constructed indices round-trip through
`classifyStab` to the expected `StabKind`.  They are not strictly needed
for the InStab proof, but they are useful for downstream pointwise
verification. -/

/-- For `r < d - 1`, `c < d - 1`, the raw `bulkIdx d r c` lies in the bulk
    slot `[0, (d-1)²)`. -/
theorem bulkIdx_lt_bulkCount (d r c : Nat) (hr : r < d - 1) (hc : c < d - 1) :
    bulkIdx d r c < (d - 1) * (d - 1) := by
  unfold bulkIdx
  have h3 : (r + 1) * (d - 1) ≤ (d - 1) * (d - 1) :=
    Nat.mul_le_mul_right _ hr
  have h2 : r * (d - 1) + (d - 1) = (r + 1) * (d - 1) := by
    rw [Nat.add_mul, Nat.one_mul]
  have h1 : r * (d - 1) + c < r * (d - 1) + (d - 1) := by omega
  omega

/-- `bulkIdx d r c` decodes back to `(r, c)` via `(·/(d-1), ·%(d-1))`. -/
theorem bulkIdx_div_mod (d r c : Nat) (_hd : 1 < d) (hc : c < d - 1) :
    bulkIdx d r c / (d - 1) = r ∧ bulkIdx d r c % (d - 1) = c := by
  unfold bulkIdx
  have hdm1 : 0 < d - 1 := by omega
  refine ⟨?_, ?_⟩
  · rw [Nat.mul_comm r (d - 1), Nat.mul_add_div hdm1,
        Nat.div_eq_of_lt hc, Nat.add_zero]
  · rw [Nat.mul_comm r (d - 1), Nat.mul_add_mod, Nat.mod_eq_of_lt hc]

/-- `classifyStab` of `bulkIdx d r c` with `(r + c) % 2 = 0` is `bulkZ r c`. -/
theorem classifyStab_bulkIdx_even (d r c : Nat) (hd : 1 < d)
    (hr : r < d - 1) (hc : c < d - 1) (hpar : (r + c) % 2 = 0) :
    classifyStab d (bulkIdx d r c) = StabKind.bulkZ r c := by
  unfold classifyStab
  have hlt := bulkIdx_lt_bulkCount d r c hr hc
  rw [if_pos hlt]
  obtain ⟨hdiv, hmod⟩ := bulkIdx_div_mod d r c hd hc
  rw [hdiv, hmod, if_pos hpar]

/-- `rightZIdx d b` with `b < (d-1)/2` is in `Fin (numStabFormula d)`.  -/
theorem rightZIdx_lt_numStab (d b : Nat) (_hd : 1 < d) (hb : b < (d - 1) / 2) :
    rightZIdx d b < numStabFormula d := by
  unfold rightZIdx numStabFormula
  have h2half_le_dm1 : 2 * ((d - 1) / 2) ≤ d - 1 := by
    have := Nat.div_mul_le_self (d - 1) 2
    omega
  have h_inner :
      (d - 1) * (d - 1) + (d - 1) / 2 + b
        < (d - 1) * (d - 1) + 2 * (d - 1) := by
    have hle : (d - 1) / 2 + b + b < (d - 1) + b := by
      have : 2 * ((d - 1) / 2) ≤ d - 1 := h2half_le_dm1
      omega
    -- 2 * (d-1) = (d-1) + (d-1) ≥ (d-1)/2 + (d-1)/2 + … but we just bound by direct arithmetic.
    have hb' : b < d - 1 := by
      calc b < (d - 1) / 2 := hb
        _ ≤ d - 1 := Nat.div_le_self _ _
    -- (d - 1) / 2 + b ≤ (d - 1) / 2 + (d - 1) - 1 < (d - 1) + (d - 1)
    have h_sum : (d - 1) / 2 + b < 2 * (d - 1) := by
      have : (d - 1) / 2 ≤ d - 1 := Nat.div_le_self _ _
      omega
    omega
  -- numStabFormula = max 1 (...)
  exact Nat.lt_of_lt_of_le h_inner (Nat.le_max_right _ _)

/-- `leftZIdx d b` with `b < (d-1)/2` is in `Fin (numStabFormula d)`. -/
theorem leftZIdx_lt_numStab (d b : Nat) (_hd : 1 < d) (hb : b < (d - 1) / 2) :
    leftZIdx d b < numStabFormula d := by
  unfold leftZIdx numStabFormula
  have h2half_le_dm1 : 2 * ((d - 1) / 2) ≤ d - 1 := by
    have := Nat.div_mul_le_self (d - 1) 2
    omega
  have h_inner :
      (d - 1) * (d - 1) + 2 * ((d - 1) / 2) + b
        < (d - 1) * (d - 1) + 2 * (d - 1) := by
    have hb' : b < d - 1 := by
      calc b < (d - 1) / 2 := hb
        _ ≤ d - 1 := Nat.div_le_self _ _
    -- 2 * ((d-1)/2) + b < 2 * (d - 1)
    have : 2 * ((d - 1) / 2) + b < 2 * (d - 1) := by omega
    omega
  exact Nat.lt_of_lt_of_le h_inner (Nat.le_max_right _ _)

/-- For odd `d` with `r < d - 1`, `c < d - 1`, the bulkIdx is in
    `Fin (numStabFormula d)`. -/
theorem bulkIdx_lt_numStab (d r c : Nat) (_hd : 1 < d)
    (hr : r < d - 1) (hc : c < d - 1) :
    bulkIdx d r c < numStabFormula d := by
  unfold numStabFormula
  have h := bulkIdx_lt_bulkCount d r c hr hc
  have h' : bulkIdx d r c < (d - 1) * (d - 1) + 2 * (d - 1) := by omega
  exact Nat.lt_of_lt_of_le h' (Nat.le_max_right _ _)

/-- `classifyStab` of `rightZIdx d b` (with `b < (d-1)/2`) is `rightZ b`. -/
theorem classifyStab_rightZIdx (d b : Nat) (_hd : 1 < d) (hb : b < (d - 1) / 2) :
    classifyStab d (rightZIdx d b) = StabKind.rightZ b := by
  unfold classifyStab rightZIdx
  -- Index = (d-1)² + (d-1)/2 + b, which is ≥ (d-1)² so the bulk branch is skipped.
  have hge : (d - 1) * (d - 1) ≤ (d - 1) * (d - 1) + (d - 1) / 2 + b := by omega
  rw [if_neg (Nat.not_lt_of_ge hge)]
  -- Inside the boundary slot we land in `rightZ` because `half ≤ b' < 2 * half`.
  set b' := (d - 1) * (d - 1) + (d - 1) / 2 + b - (d - 1) * (d - 1) with hb'def
  have hb'_eq : b' = (d - 1) / 2 + b := by
    rw [hb'def]; omega
  -- `b' < half` is false:
  have hnot_top : ¬ b' < (d - 1) / 2 := by
    rw [hb'_eq]; omega
  rw [if_neg hnot_top]
  -- `b' < 2 * half` is true:
  have h_mid : b' < 2 * ((d - 1) / 2) := by
    rw [hb'_eq]; omega
  rw [if_pos h_mid]
  -- `b' - half = b`
  have h_sub : b' - (d - 1) / 2 = b := by rw [hb'_eq]; omega
  rw [h_sub]

/-- `classifyStab` of `leftZIdx d b` (with `b < (d-1)/2`) is `leftZ b`. -/
theorem classifyStab_leftZIdx (d b : Nat) (_hd : 1 < d) (hb : b < (d - 1) / 2) :
    classifyStab d (leftZIdx d b) = StabKind.leftZ b := by
  unfold classifyStab leftZIdx
  have hge : (d - 1) * (d - 1) ≤ (d - 1) * (d - 1) + 2 * ((d - 1) / 2) + b := by omega
  rw [if_neg (Nat.not_lt_of_ge hge)]
  set b' := (d - 1) * (d - 1) + 2 * ((d - 1) / 2) + b - (d - 1) * (d - 1) with hb'def
  have hb'_eq : b' = 2 * ((d - 1) / 2) + b := by
    rw [hb'def]; omega
  have hnot_top : ¬ b' < (d - 1) / 2 := by
    rw [hb'_eq]; omega
  rw [if_neg hnot_top]
  have hnot_right : ¬ b' < 2 * ((d - 1) / 2) := by
    rw [hb'_eq]; omega
  rw [if_neg hnot_right]
  have h_left : b' < 3 * ((d - 1) / 2) := by
    rw [hb'_eq]; omega
  rw [if_pos h_left]
  have h_sub : b' - 2 * ((d - 1) / 2) = b := by rw [hb'_eq]; omega
  rw [h_sub]

/-! ## d=3 sanity checks for the index helpers

These confirm that `bulkIdx`, `rightZIdx`, `leftZIdx` at `d = 3` match the
expected paper-order indices (s1 = 0, s4 = 3, s6 = 5, s7 = 6). -/

example : bulkIdx 3 0 0 = 0 := by decide
example : bulkIdx 3 1 1 = 3 := by decide
example : rightZIdx 3 0 = 5 := by decide
example : leftZIdx 3 0 = 6 := by decide

-- d = 5, i = 0 (even) → bulk Z at (0, 0) and (0, 2); rightZ at b = 0.
example : bulkIdx 5 0 0 = 0 := by decide
example : bulkIdx 5 0 2 = 2 := by decide
example : rightZIdx 5 0 = 18 := by decide  -- (d-1)² + (d-1)/2 = 16 + 2 = 18

-- d = 5, i = 1 (odd) → bulk Z at (1, 1) and (1, 3); leftZ at b = 0.
example : bulkIdx 5 1 1 = 5 := by decide
example : bulkIdx 5 1 3 = 7 := by decide
example : leftZIdx 5 0 = 20 := by decide  -- 16 + 2 * 2 = 20

/-! ## Row-step stabilizer list

For an odd `d ≥ 3` and a row index `i` with `i + 1 < d`, the row-step
witness is the parametric stabilizer product over the list

* bulk Z indices `bulkIdx d i c` for `c ∈ {0, …, d-2}` with `(i + c) % 2 = 0`,
* plus the appropriate boundary index (rightZ for `i` even, leftZ for `i` odd).

We construct the list of bulk Z indices via `List.range` filter, and prefix
the boundary index.  This gives a canonical, normalised representation.

The list contents are **raw `Nat` indices**.  Casting into
`Fin (numStabFormula d)` requires the `< numStabFormula d` bound,
which we discharge via `bulkIdx_lt_numStab`, `rightZIdx_lt_numStab`,
`leftZIdx_lt_numStab`. -/

/-- The list of bulk Z stabilizer indices for the row-step at row `i`
    (raw `Nat` indices). -/
def rowStepBulkList (d i : Nat) : List Nat :=
  (List.range (d - 1)).filter (fun c => decide ((i + c) % 2 = 0))
    |>.map (fun c => bulkIdx d i c)

/-- The boundary stabilizer index for the row-step at row `i`. -/
def rowStepBoundaryIdx (d i : Nat) : Nat :=
  if i % 2 = 0 then rightZIdx d (i / 2)
               else leftZIdx d ((i - 1) / 2)

/-- The complete list of raw `Nat` stabilizer indices for the row-step at row `i`. -/
def rowStepStabsRaw (d i : Nat) : List Nat :=
  rowStepBoundaryIdx d i :: rowStepBulkList d i

/-! ### d=3 sanity: `rowStepStabsRaw 3` matches the existing handwritten witnesses

* `rowStepStabsRaw 3 0 = [rightZIdx 3 0, bulkIdx 3 0 0] = [5, 0]`, matching
  `D3Witness.rowCutFin_succ_0` which uses `[s6, s1]` (in any order — the
  product is commutative under XOR of `{I, Z}`-valued Pauli vectors).
* `rowStepStabsRaw 3 1 = [leftZIdx 3 0, bulkIdx 3 1 1] = [6, 3]`, matching
  `D3Witness.rowCutFin_succ_1` which uses `[s7, s4]`.
-/
example : rowStepStabsRaw 3 0 = [5, 0] := by decide
example : rowStepStabsRaw 3 1 = [6, 3] := by decide

-- d = 5 sanity.
-- i = 0 (even): rightZ at b=0, bulk Z at (0, c) for c ∈ {0, 2}.
example : rowStepStabsRaw 5 0 = [18, 0, 2] := by decide
-- i = 1 (odd): leftZ at b=0, bulk Z at (1, c) for c ∈ {1, 3}.
example : rowStepStabsRaw 5 1 = [20, 5, 7] := by decide
-- i = 2 (even): rightZ at b=1, bulk Z at (2, c) for c ∈ {0, 2}.
example : rowStepStabsRaw 5 2 = [19, 8, 10] := by decide
-- i = 3 (odd): leftZ at b=1, bulk Z at (3, c) for c ∈ {1, 3}.
example : rowStepStabsRaw 5 3 = [21, 13, 15] := by decide

/-! ## InStab membership of the row-step witness

We now lift `rowStepStabsRaw` to a list of `mkSurfaceStabilizers` values via
`mkSurfaceQECParams`-typed indices, and show that its `listProd` lies in
`InStab`.  The proof is structural: every list element is `mkSurfaceStabilizers d hd k`
for some `k : Fin (numStabFormula d)`, so its `InStab.gen` membership lifts to
a `listProd` membership by induction.

For brevity we use a direct fold rather than `Paper.LogicalCosets.listProd`. -/

/-- Pointwise-multiplication fold of a list of `ErrorVec`s. -/
def stabListProd {n : Nat} : List (ErrorVec n) → ErrorVec n
  | [] => ErrorVec.identity n
  | a :: l => ErrorVec.mul a (stabListProd l)

/-- Membership-by-list: if every element of `l : List (ErrorVec P.n)` is in
    `InStab P`, then the iterated product is too. -/
theorem InStab.stabListProd_of_all {P : QECParams} :
    ∀ (l : List (ErrorVec P.n)),
      (∀ E ∈ l, InStab P E) → InStab P (stabListProd l)
  | [], _ => by unfold stabListProd; exact InStab.identity
  | a :: l, h => by
    unfold stabListProd
    refine InStab.mul (h a (by simp)) ?_
    exact InStab.stabListProd_of_all l (fun E hE => h E (by simp [hE]))

/-- For odd `d ≥ 3` and a row index `i` with `i + 1 < d`, every raw index in
    `rowStepStabsRaw d i` is `< numStabFormula d`. -/
theorem rowStepStabsRaw_lt_numStab (d : Nat) (hd : 1 < d) (hodd : d % 2 = 1)
    (i : Nat) (hi : i + 1 < d) :
    ∀ k ∈ rowStepStabsRaw d i, k < numStabFormula d := by
  intro k hk
  have hi_lt : i < d - 1 := by omega
  -- For odd d > 1, d ≥ 3.
  have hd_ge : d ≥ 3 := by omega
  have hdm1_even : (d - 1) % 2 = 0 := by omega
  unfold rowStepStabsRaw at hk
  simp only [List.mem_cons] at hk
  rcases hk with hk | hk
  · -- k = boundary index
    subst hk
    unfold rowStepBoundaryIdx
    by_cases hpar : i % 2 = 0
    · rw [if_pos hpar]
      apply rightZIdx_lt_numStab d (i / 2) hd
      -- Need: i / 2 < (d - 1) / 2.
      omega
    · rw [if_neg hpar]
      apply leftZIdx_lt_numStab d ((i - 1) / 2) hd
      -- Need: (i - 1) / 2 < (d - 1) / 2.
      have hi_odd : i % 2 = 1 := by omega
      omega
  · -- k is a bulk element
    unfold rowStepBulkList at hk
    simp only [List.mem_map, List.mem_filter, List.mem_range] at hk
    obtain ⟨c, ⟨hc_range, _⟩, hbulk_eq⟩ := hk
    subst hbulk_eq
    exact bulkIdx_lt_numStab d i c hd hi_lt hc_range

/-- The row-step witness `ErrorVec` for the parametric `QECParams`
    `mkSurfaceQECParams d hd hodd`: the `stabListProd` of the parametric
    stabilizer family evaluated at every index in `rowStepStabsRaw d i`. -/
def rowStepWitness (d : Nat) (hd : 1 < d) (hodd : d % 2 = 1)
    (i : Nat) (hi : i + 1 < d) : ErrorVec (d * d) :=
  stabListProd ((rowStepStabsRaw d i).attach.map
    (fun ⟨k, hk⟩ =>
      mkSurfaceStabilizers d (by omega)
        ⟨k, rowStepStabsRaw_lt_numStab d hd hodd i hi k hk⟩))

/-- **Headline:** `rowStepWitness d hd hodd i hi` lies in `InStab` of the
    canonical parametric surface code `mkSurfaceQECParams d hd hodd`.

    The proof goes via `InStab.stabListProd_of_all`: every element of the
    underlying list is `mkSurfaceStabilizers d hd ⟨k, _⟩` for some `k`, which
    is exactly the `stabilizers` field of `mkSurfaceQECParams d hd hodd`,
    hence in `InStab.gen` form.

    All `n`/`numStab` field accesses on `mkSurfaceQECParams` are definitional
    (`rfl`-equal to the parametric ones), so no `▸`-casts appear in the
    headline. -/
theorem rowStepWitness_inStab_mkSurfaceQECParams
    (d : Nat) (hodd : d % 2 = 1)
    (hd1 : 1 < d) (i : Nat) (hi : i + 1 < d) :
    InStab (mkSurfaceQECParams d (by omega) hodd) (rowStepWitness d hd1 hodd i hi) := by
  unfold rowStepWitness
  apply InStab.stabListProd_of_all
  intro E hE
  obtain ⟨⟨k, hk⟩, _, hE_eq⟩ := List.mem_map.mp hE
  subst hE_eq
  have hk_lt : k < numStabFormula d := rowStepStabsRaw_lt_numStab d hd1 hodd i hi k hk
  show InStab (mkSurfaceQECParams d (by omega) hodd)
    (mkSurfaceStabilizers d (by omega) ⟨k, hk_lt⟩)
  -- `(mkSurfaceQECParams d _ hodd).stabilizers ⟨k, hk_lt⟩ = mkSurfaceStabilizers d _ ⟨k, hk_lt⟩`
  -- holds by definition of `mkSurfaceQECParams.stabilizers`.  The remaining gap is just the
  -- positivity-proof irrelevance (`hd1 : 1 < d` vs the `Nat.pos_of_lt_succ` derived `0 < d`).
  exact InStab.gen (P := mkSurfaceQECParams d (by omega) hodd) ⟨k, hk_lt⟩

/-! ## "All `I` or `Z`" structural property

The row-step witness — built from Z-bulk and {leftZ, rightZ} boundary
stabilizers — has only `I` and `Z` entries pointwise.  This is the second
conjunct of `NZSurfaceSpec.rowCut_succ`. -/

/-- Pointwise `{I, Z}` is closed under `Pauli.mul`. -/
private lemma I_or_Z_mul {a b : Pauli} (ha : a = Pauli.I ∨ a = Pauli.Z)
    (hb : b = Pauli.I ∨ b = Pauli.Z) :
    Pauli.mul a b = Pauli.I ∨ Pauli.mul a b = Pauli.Z := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> subst ha <;> subst hb
  · left; rfl
  · right; rfl
  · right; rfl
  · left; rfl

/-- Pointwise `{I, Z}` is preserved by `stabListProd`. -/
theorem stabListProd_all_I_or_Z {n : Nat} (l : List (ErrorVec n))
    (h : ∀ E ∈ l, ∀ q, E q = Pauli.I ∨ E q = Pauli.Z) :
    ∀ q : Fin n, stabListProd l q = Pauli.I ∨ stabListProd l q = Pauli.Z := by
  intro q
  induction l with
  | nil =>
    unfold stabListProd ErrorVec.identity
    left; rfl
  | cons a l ih =>
    unfold stabListProd
    show Pauli.mul (a q) (stabListProd l q) = Pauli.I ∨
         Pauli.mul (a q) (stabListProd l q) = Pauli.Z
    apply I_or_Z_mul
    · exact h a (by simp) q
    · exact ih (fun E hE => h E (by simp [hE]))

/-- The `stabType` of every index in `rowStepStabsRaw d i` is `Pauli.Z`.
    (Every such index is either a bulk-Z plaquette or a {left, right}-Z boundary;
    by construction the row-step witness uses no X-type stabilizers.) -/
theorem stabType_rowStepStabsRaw (d : Nat) (hd1 : 1 < d) (hodd : d % 2 = 1)
    (i : Nat) (hi : i + 1 < d) :
    ∀ k ∈ rowStepStabsRaw d i, stabType d k = Pauli.Z := by
  intro k hk
  have hd_ge : d ≥ 3 := by omega
  have hi_lt : i < d - 1 := by omega
  unfold rowStepStabsRaw at hk
  simp only [List.mem_cons] at hk
  rcases hk with hk | hk
  · -- boundary index
    subst hk
    unfold rowStepBoundaryIdx
    by_cases hpar : i % 2 = 0
    · -- rightZ branch: index = (d-1)² + half + (i/2)
      rw [if_pos hpar]
      unfold stabType rightZIdx
      have hge : (d - 1) * (d - 1) ≤ (d - 1) * (d - 1) + (d - 1) / 2 + i / 2 := by omega
      rw [if_neg (Nat.not_lt_of_ge hge)]
      -- After subtracting bulkCount, b = (d-1)/2 + i/2.
      set b := (d - 1) * (d - 1) + (d - 1) / 2 + i / 2 - (d - 1) * (d - 1) with hb_def
      have hb_eq : b = (d - 1) / 2 + i / 2 := by rw [hb_def]; omega
      -- b ≥ (d-1)/2 (not in topX branch)
      have hnot_top : ¬ b < (d - 1) / 2 := by rw [hb_eq]; omega
      rw [if_neg hnot_top]
      -- We have i/2 < (d-1)/2 hence b < 2*(d-1)/2 (in rightZ branch).
      have hpar_i : i % 2 = 0 := hpar
      have hb_lt : b < 2 * ((d - 1) / 2) := by
        rw [hb_eq]
        have : i / 2 < (d - 1) / 2 := by omega
        omega
      rw [if_pos hb_lt]
    · -- leftZ branch: index = (d-1)² + 2*half + ((i-1)/2)
      rw [if_neg hpar]
      unfold stabType leftZIdx
      have hge : (d - 1) * (d - 1) ≤ (d - 1) * (d - 1) + 2 * ((d - 1) / 2) + (i - 1) / 2 := by omega
      rw [if_neg (Nat.not_lt_of_ge hge)]
      set b := (d - 1) * (d - 1) + 2 * ((d - 1) / 2) + (i - 1) / 2 - (d - 1) * (d - 1) with hb_def
      have hb_eq : b = 2 * ((d - 1) / 2) + (i - 1) / 2 := by rw [hb_def]; omega
      have hnot_top : ¬ b < (d - 1) / 2 := by rw [hb_eq]; omega
      rw [if_neg hnot_top]
      have hnot_right : ¬ b < 2 * ((d - 1) / 2) := by rw [hb_eq]; omega
      rw [if_neg hnot_right]
      have hpar_i : i % 2 = 1 := by omega
      have hb_lt : b < 3 * ((d - 1) / 2) := by
        rw [hb_eq]
        have : (i - 1) / 2 < (d - 1) / 2 := by omega
        omega
      rw [if_pos hb_lt]
  · -- bulk
    unfold rowStepBulkList at hk
    simp only [List.mem_map, List.mem_filter, List.mem_range,
               decide_eq_true_eq] at hk
    obtain ⟨c, ⟨hc_range, hc_par⟩, hbulk_eq⟩ := hk
    subst hbulk_eq
    unfold stabType
    have hlt := bulkIdx_lt_bulkCount d i c hi_lt hc_range
    rw [if_pos hlt]
    obtain ⟨hdiv, hmod⟩ := bulkIdx_div_mod d i c hd1 hc_range
    rw [hdiv, hmod, if_pos hc_par]

/-- Re-proof of the private lemma `decode_eq_I_or_stabType` from `SurfaceParametric`.
    (The `private` modifier blocks direct access from this file, so we duplicate
    the trivial split-ifs proof.) -/
lemma decode_I_or_stabType_pub (d k row col : Nat) :
    decodeStabPauliAt d k row col = Pauli.I ∨
    decodeStabPauliAt d k row col = stabType d k := by
  simp only [decodeStabPauliAt, stabType]
  split_ifs <;> first | (left; rfl) | (right; rfl)

/-- Every value of `decodeStabPauliAt d k row col` for `k` in `rowStepStabsRaw d i`
    is either `I` or `Z`.  Composes `decode_I_or_stabType_pub` with
    `stabType_rowStepStabsRaw`. -/
theorem decodeStabPauliAt_rowStepStabsRaw_I_or_Z
    (d : Nat) (hd1 : 1 < d) (hodd : d % 2 = 1)
    (i : Nat) (hi : i + 1 < d) :
    ∀ k ∈ rowStepStabsRaw d i, ∀ row col : Nat,
      decodeStabPauliAt d k row col = Pauli.I ∨
      decodeStabPauliAt d k row col = Pauli.Z := by
  intro k hk row col
  have h_type := stabType_rowStepStabsRaw d hd1 hodd i hi k hk
  rcases decode_I_or_stabType_pub d k row col with h | h
  · left; exact h
  · right; rw [h, h_type]

/-- **Headline:** every coordinate of `rowStepWitness d hd1 hodd i hi` is in
    `{Pauli.I, Pauli.Z}`.  This is the second conjunct that
    `NZSurfaceSpec.rowCut_succ` demands. -/
theorem rowStepWitness_I_or_Z (d : Nat) (hd1 : 1 < d) (hodd : d % 2 = 1)
    (i : Nat) (hi : i + 1 < d) :
    ∀ q : Fin (d * d),
      rowStepWitness d hd1 hodd i hi q = Pauli.I ∨
      rowStepWitness d hd1 hodd i hi q = Pauli.Z := by
  unfold rowStepWitness
  apply stabListProd_all_I_or_Z
  intro E hE q
  obtain ⟨⟨k, hk⟩, _, hE_eq⟩ := List.mem_map.mp hE
  subst hE_eq
  -- E q = mkSurfaceStabilizers d _ ⟨k, _⟩ q = decodeStabPauliAt d k (q.val/d) (q.val%d).
  show decodeStabPauliAt d k (q.val / d) (q.val % d) = Pauli.I ∨
       decodeStabPauliAt d k (q.val / d) (q.val % d) = Pauli.Z
  exact decodeStabPauliAt_rowStepStabsRaw_I_or_Z d hd1 hodd i hi k hk _ _

/-! ## d=3 cross-validation against legacy `D3Witness.rowCutFin_succ_*`

At `d = 3`, the row-step witness should evaluate to exactly the same
`ErrorVec` as the handwritten product used in `D3Witness.rowCutFin_succ_0`
(i.e. `s6 * s1`, which is Z on qubits {0,1,2,3,4,5}, the union of row 0 and
row 1).

Recall:
* `SurfaceD3.s1 = Z₁Z₂Z₄Z₅` on qubits `{0, 1, 3, 4}` (bulk Z at (0, 0));
* `SurfaceD3.s6 = Z₃Z₆` on qubits `{2, 5}` (rightZ at b=0).

Their pointwise product is Z on `{0, 1, 2, 3, 4, 5}` and I on `{6, 7, 8}`,
which is exactly Z on rows 0 and 1.  We confirm this via `decide` on the
finite domain `Fin 9`. -/

-- The d=3, i=0 row-step witness is Z on rows {0, 1} and I on row 2.
example :
    ∀ q : Fin 9,
      rowStepWitness 3 (by decide) (by decide) 0 (by decide) q
        = (if q.val < 6 then Pauli.Z else Pauli.I) := by
  decide

-- The d=3, i=1 row-step witness is Z on rows {1, 2} and I on row 0.
example :
    ∀ q : Fin 9,
      rowStepWitness 3 (by decide) (by decide) 1 (by decide) q
        = (if q.val ≥ 3 then Pauli.Z else Pauli.I) := by
  decide

-- The d=5, i=0 row-step witness is Z on rows {0, 1} and I on rows {2, 3, 4}.
-- This is the parametric extrapolation to d = 5; verified by closed `decide`.
example :
    ∀ q : Fin 25,
      rowStepWitness 5 (by decide) (by decide) 0 (by decide) q
        = (if q.val < 10 then Pauli.Z else Pauli.I) := by
  decide

/-! ## Parametric row-cut family (`NZSurfaceSpec.rowCut`)

The row-direction analogue of `mkSurfaceCutOp` (which is column-based).
`mkSurfaceRowCut d i` places `Z` on every data qubit whose row index
(`q.val / d`) equals `i.val`, and `I` everywhere else.  This is the
canonical `NZSurfaceSpec.rowCut` family for the parametric rotated
surface code.

The two structural wrappers `mkSurfaceRowCut_zero` and `mkSurfaceRowCut_spec`
are `rfl` (definitionally true) and depend on **zero** axioms — stricter
than the standard `[propext, Classical.choice, Quot.sound]` baseline. -/

/-- The **parametric row-`i` cut operator** of the rotated surface code at
    distance `d`: `Z` on every data qubit in row `i` (`q.val / d = i.val`),
    `I` elsewhere.  The row-direction analogue of `mkSurfaceCutOp`. -/
def mkSurfaceRowCut (d : Nat) (i : Fin d) : ErrorVec (d * d) :=
  fun q => if q.val / d = i.val then Pauli.Z else Pauli.I

/-- `NZSurfaceSpec.rowCut_zero`: the row-0 cut operator equals the
    parametric logical-Z (Z on top row, I elsewhere). -/
theorem mkSurfaceRowCut_zero (d : Nat) (hd : 0 < d) :
    mkSurfaceRowCut d ⟨0, hd⟩ = mkSurfaceLogicalZ d := rfl

/-- `NZSurfaceSpec.rowCut_spec`: pointwise specification of
    `mkSurfaceRowCut`. -/
theorem mkSurfaceRowCut_spec (d : Nat) (i : Fin d) (q : Fin (d * d)) :
    mkSurfaceRowCut d i q = if q.val / d = i.val then Pauli.Z else Pauli.I := rfl

/-! ### d=3, d=5 sanity for `mkSurfaceRowCut`. -/

-- d=3 row 0 = Z on qubits {0,1,2}.
example :
    ∀ q : Fin 9,
      mkSurfaceRowCut 3 ⟨0, by decide⟩ q
        = (if q.val < 3 then Pauli.Z else Pauli.I) := by
  decide

-- d=3 row 1 = Z on qubits {3,4,5}.
example :
    ∀ q : Fin 9,
      mkSurfaceRowCut 3 ⟨1, by decide⟩ q
        = (if 3 ≤ q.val ∧ q.val < 6 then Pauli.Z else Pauli.I) := by
  decide

-- d=5 row 2 = Z on qubits {10,11,12,13,14}.
example :
    ∀ q : Fin 25,
      mkSurfaceRowCut 5 ⟨2, by decide⟩ q
        = (if 10 ≤ q.val ∧ q.val < 15 then Pauli.Z else Pauli.I) := by
  decide

/-! ## Z-side of `hook_spread_bound` (the easy half)

When a hook `e_B` has no X-component (Z-type stabilizer hook), multiplying
by it preserves the X-component pattern of `S_wit · E` pointwise.  Hence
the row-X-card is unchanged exactly; the `+1` slack in
`NZSurfaceSpec.hook_spread_bound` is unused.

The hard half (X-stab hooks, requiring stabilizer absorption) is deferred
to a follow-up tick. -/

/-- Pointwise X-component preservation: multiplying by a Z-only `e_B`
    does not change the X-component of any qubit in `S · E`. -/
private lemma hasX_mul_noX {n : Nat} (S e_B E : ErrorVec n)
    (h_noX : ∀ q, Pauli.hasXComponent (e_B q) = false) (q : Fin n) :
    Pauli.hasXComponent (ErrorVec.mul S (ErrorVec.mul e_B E) q)
      = Pauli.hasXComponent (ErrorVec.mul S E q) := by
  show Pauli.hasXComponent (Pauli.mul (S q) (Pauli.mul (e_B q) (E q)))
     = Pauli.hasXComponent (Pauli.mul (S q) (E q))
  rw [Pauli.hasXComponent_mul_eq_xor, Pauli.hasXComponent_mul_eq_xor,
      Pauli.hasXComponent_mul_eq_xor, h_noX q, Bool.false_xor]

/-- The **Z-side** of `NZSurfaceSpec.hook_spread_bound`: when the hook
    `e_B` has no X-component (Z-type stabilizer hook), choosing
    `S_wit' := S_wit` gives row-X-card equality (well within the +1
    budget).  Independent of the specific surface stabilizer index. -/
theorem hook_spread_bound_Z_side (d : Nat) (hd : 0 < d) (hodd : d % 2 = 1)
    (_s_idx : Fin (numStabFormula d))
    (e_B : ErrorVec (d * d))
    (h_noX : ∀ q, Pauli.hasXComponent (e_B q) = false)
    (E : ErrorVec (d * d)) (S_wit : ErrorVec (d * d))
    (hS : InStab (mkSurfaceQECParams d hd hodd) S_wit) :
    ∃ S_wit' : ErrorVec (d * d), InStab (mkSurfaceQECParams d hd hodd) S_wit' ∧
      (Finset.univ.filter fun row : Fin d =>
        ∃ q : Fin (d * d), q.val / d = row.val ∧
          Pauli.hasXComponent
            (ErrorVec.mul S_wit' (ErrorVec.mul e_B E) q) = true).card
      ≤ (Finset.univ.filter fun row : Fin d =>
        ∃ q : Fin (d * d), q.val / d = row.val ∧
          Pauli.hasXComponent (ErrorVec.mul S_wit E q) = true).card + 1 := by
  refine ⟨S_wit, hS, ?_⟩
  -- The two filter sets are equal (X-component pattern preserved).
  have hfilter_eq :
      (Finset.univ.filter fun row : Fin d =>
        ∃ q : Fin (d * d), q.val / d = row.val ∧
          Pauli.hasXComponent
            (ErrorVec.mul S_wit (ErrorVec.mul e_B E) q) = true)
      = (Finset.univ.filter fun row : Fin d =>
        ∃ q : Fin (d * d), q.val / d = row.val ∧
          Pauli.hasXComponent (ErrorVec.mul S_wit E q) = true) := by
    apply Finset.filter_congr
    intro row _
    constructor
    · rintro ⟨q, hq_row, hq_x⟩
      exact ⟨q, hq_row, (hasX_mul_noX S_wit e_B E h_noX q) ▸ hq_x⟩
    · rintro ⟨q, hq_row, hq_x⟩
      exact ⟨q, hq_row, (hasX_mul_noX S_wit e_B E h_noX q).symm ▸ hq_x⟩
  rw [hfilter_eq]
  exact Nat.le_succ _

/-! ## X-side, singleton row: `xInRow_singleton`

When the hook `e_B`'s X-components are confined to a single row `i`,
multiplying by `e_B` preserves X-component pointwise OUTSIDE row `i`.
So the row-X-card filter sets agree outside row `i`, and `filter_with`
is contained in `insert i filter_without`.  Cardinality bound is then
`card ≤ card + 1`. -/

/-- Pointwise X-component preservation OUTSIDE the restricted row.
    If `e_B` has X-components only in row `i`, then for any qubit `q`
    not in row `i`, multiplying by `e_B` does not change
    `hasXComponent`. -/
private lemma hasX_mul_outside_row {d : Nat} (S e_B E : ErrorVec (d * d))
    (i : Fin d)
    (h_row : ∀ q, Pauli.hasXComponent (e_B q) = true → q.val / d = i.val)
    (q : Fin (d * d)) (hq : q.val / d ≠ i.val) :
    Pauli.hasXComponent (ErrorVec.mul S (ErrorVec.mul e_B E) q)
      = Pauli.hasXComponent (ErrorVec.mul S E q) := by
  have hxB : Pauli.hasXComponent (e_B q) = false := by
    cases h : Pauli.hasXComponent (e_B q) with
    | true => exact absurd (h_row q h) hq
    | false => rfl
  show Pauli.hasXComponent (Pauli.mul (S q) (Pauli.mul (e_B q) (E q)))
     = Pauli.hasXComponent (Pauli.mul (S q) (E q))
  rw [Pauli.hasXComponent_mul_eq_xor, Pauli.hasXComponent_mul_eq_xor,
      Pauli.hasXComponent_mul_eq_xor, hxB, Bool.false_xor]

/-- **Helper**: the bare cardinality inequality (no existential) when
    `e_B`'s X-components are confined to a single row `i`.  The
    witness is fixed to `S_wit` (the input).  Used by both the
    `xInRow_singleton` case (e_B directly single-row) and the
    `xInRows_via_absorption` case (residual `T · e_B` single-row). -/
private lemma hook_spread_card_le_singleRow {d : Nat}
    (i : Fin d) (e_B E S_wit : ErrorVec (d * d))
    (h_row : ∀ q, Pauli.hasXComponent (e_B q) = true → q.val / d = i.val) :
    (Finset.univ.filter fun row : Fin d =>
        ∃ q : Fin (d * d), q.val / d = row.val ∧
          Pauli.hasXComponent
            (ErrorVec.mul S_wit (ErrorVec.mul e_B E) q) = true).card
      ≤ (Finset.univ.filter fun row : Fin d =>
        ∃ q : Fin (d * d), q.val / d = row.val ∧
          Pauli.hasXComponent (ErrorVec.mul S_wit E q) = true).card + 1 := by
  set F_with := Finset.univ.filter fun row : Fin d =>
    ∃ q : Fin (d * d), q.val / d = row.val ∧
      Pauli.hasXComponent
        (ErrorVec.mul S_wit (ErrorVec.mul e_B E) q) = true
    with hF_with
  set F_without := Finset.univ.filter fun row : Fin d =>
    ∃ q : Fin (d * d), q.val / d = row.val ∧
      Pauli.hasXComponent (ErrorVec.mul S_wit E q) = true
    with hF_without
  have hsubset : F_with ⊆ insert i F_without := by
    intro row hrow
    simp only [hF_with, Finset.mem_filter, Finset.mem_univ, true_and] at hrow
    obtain ⟨q, hq_row, hq_x⟩ := hrow
    by_cases hrow_eq : row = i
    · exact Finset.mem_insert.mpr (Or.inl hrow_eq)
    · have hq_notRow : q.val / d ≠ i.val := by
        rw [hq_row]; intro heq; exact hrow_eq (Fin.ext heq)
      have hpreserved := hasX_mul_outside_row S_wit e_B E i h_row q hq_notRow
      have hq_x' : Pauli.hasXComponent (ErrorVec.mul S_wit E q) = true := by
        rw [← hpreserved]; exact hq_x
      apply Finset.mem_insert.mpr; right
      simp only [hF_without, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨q, hq_row, hq_x'⟩
  calc F_with.card
      ≤ (insert i F_without).card := Finset.card_le_card hsubset
    _ ≤ F_without.card + 1 := Finset.card_insert_le _ _

/-- The **xInRow-singleton** case of `NZSurfaceSpec.hook_spread_bound`:
    when the hook's X-components are confined to a single row `i`,
    choosing `S_wit' := S_wit` gives row-X-card growth of at most +1
    (the row `i` itself).

    Covers the surface-code cases: topX boundary hooks (row 0),
    bottomX boundary hooks (row d-1), bulkX suffix-2/suffix-3 hooks
    (single bulk row).  Does NOT cover bulkX suffix-1 or full-stab
    hooks (those span two rows and need the absorption argument). -/
theorem hook_spread_bound_xInRow_singleton
    (d : Nat) (hd : 0 < d) (hodd : d % 2 = 1)
    (i : Fin d) (_s_idx : Fin (numStabFormula d))
    (e_B : ErrorVec (d * d))
    (h_row : ∀ q, Pauli.hasXComponent (e_B q) = true → q.val / d = i.val)
    (E S_wit : ErrorVec (d * d))
    (hS : InStab (mkSurfaceQECParams d hd hodd) S_wit) :
    ∃ S_wit' : ErrorVec (d * d), InStab (mkSurfaceQECParams d hd hodd) S_wit' ∧
      (Finset.univ.filter fun row : Fin d =>
        ∃ q : Fin (d * d), q.val / d = row.val ∧
          Pauli.hasXComponent
            (ErrorVec.mul S_wit' (ErrorVec.mul e_B E) q) = true).card
      ≤ (Finset.univ.filter fun row : Fin d =>
        ∃ q : Fin (d * d), q.val / d = row.val ∧
          Pauli.hasXComponent (ErrorVec.mul S_wit E q) = true).card + 1 := by
  exact ⟨S_wit, hS, hook_spread_card_le_singleRow i e_B E S_wit h_row⟩

/-! ## Full-stab absorption: when `e_B` is itself a stabilizer

The full-stab hook case: `e_B = mkSurfaceStabilizers d hd s_idx` (the
parent stabilizer included as a hook).  Choosing
`S_wit' := S_wit · e_B` gives row-X-card EQUALITY because
`(S_wit · e_B) · (e_B · E) = S_wit · E` by Pauli self-inverse.

The lemma is generic — `e_B ∈ InStab` is the only hypothesis. It would
apply uniformly to ANY scheme that includes parent stabilizers in the
back-action set. -/

/-- Pointwise identity exploiting Pauli self-inverse: for any `e_B`,
    `(S · e_B) · (e_B · E) = S · E`. -/
private lemma mul_absorb_self_left {n : Nat} (e_B S E : ErrorVec n) :
    ErrorVec.mul (ErrorVec.mul S e_B) (ErrorVec.mul e_B E)
      = ErrorVec.mul S E := by
  funext q
  show Pauli.mul (Pauli.mul (S q) (e_B q)) (Pauli.mul (e_B q) (E q))
     = Pauli.mul (S q) (E q)
  rw [Pauli.mul_assoc, ← Pauli.mul_assoc (e_B q), Pauli.mul_self,
      Pauli.I_mul]

/-- The **full-stab absorption** case of `NZSurfaceSpec.hook_spread_bound`:
    if the hook `e_B` is itself a stabilizer
    (`InStab (mkSurfaceQECParams ...) e_B`), choosing
    `S_wit' := S_wit · e_B` gives row-X-card EQUALITY — even tighter
    than the +1 budget.

    Covers the case `e_B = mkSurfaceStabilizers d hd s_idx` arising
    from `mkSurfaceStabilizers_mem_hookErrors`.  The argument is
    generic across schemes; only the `InStab` premise on `e_B` is
    needed. -/
theorem hook_spread_bound_full_stab_absorb
    (d : Nat) (hd : 0 < d) (hodd : d % 2 = 1)
    (_s_idx : Fin (numStabFormula d))
    (e_B : ErrorVec (d * d))
    (he_inStab : InStab (mkSurfaceQECParams d hd hodd) e_B)
    (E S_wit : ErrorVec (d * d))
    (hS : InStab (mkSurfaceQECParams d hd hodd) S_wit) :
    ∃ S_wit' : ErrorVec (d * d), InStab (mkSurfaceQECParams d hd hodd) S_wit' ∧
      (Finset.univ.filter fun row : Fin d =>
        ∃ q : Fin (d * d), q.val / d = row.val ∧
          Pauli.hasXComponent
            (ErrorVec.mul S_wit' (ErrorVec.mul e_B E) q) = true).card
      ≤ (Finset.univ.filter fun row : Fin d =>
        ∃ q : Fin (d * d), q.val / d = row.val ∧
          Pauli.hasXComponent (ErrorVec.mul S_wit E q) = true).card + 1 := by
  refine ⟨ErrorVec.mul S_wit e_B, InStab.mul hS he_inStab, ?_⟩
  rw [mul_absorb_self_left]
  exact Nat.le_succ _

/-! ## Absorption with a single-row residual

When the hook `e_B` itself spans two rows but multiplying by an absorber
`T ∈ InStab` produces a residual `T · e_B` whose X-components are
confined to a single row, the +1 bound follows by choosing
`S_wit' := S_wit · T` and applying the single-row helper to the
residual.  This is the structural pattern used by the bulkX suffix-1
case (where `T = mkSurfaceStabilizers d hd s_idx` is the parent X-stab
and the residual is the "dropped" single-qubit position). -/

/-- **Absorption with single-row residual**: choosing
    `S_wit' := S_wit · T` gives the +1 bound when `T · e_B` is
    X-component-restricted to row `i`.  Generic across schemes — could
    be used by any code family where a hook absorbed by a stabilizer
    yields a single-row residual. -/
theorem hook_spread_bound_xInRows_via_absorption
    (d : Nat) (hd : 0 < d) (hodd : d % 2 = 1)
    (_s_idx : Fin (numStabFormula d))
    (e_B T : ErrorVec (d * d))
    (hT_inStab : InStab (mkSurfaceQECParams d hd hodd) T)
    (i : Fin d)
    (h_residual_singleRow : ∀ q,
        Pauli.hasXComponent (ErrorVec.mul T e_B q) = true → q.val / d = i.val)
    (E S_wit : ErrorVec (d * d))
    (hS : InStab (mkSurfaceQECParams d hd hodd) S_wit) :
    ∃ S_wit' : ErrorVec (d * d), InStab (mkSurfaceQECParams d hd hodd) S_wit' ∧
      (Finset.univ.filter fun row : Fin d =>
        ∃ q : Fin (d * d), q.val / d = row.val ∧
          Pauli.hasXComponent
            (ErrorVec.mul S_wit' (ErrorVec.mul e_B E) q) = true).card
      ≤ (Finset.univ.filter fun row : Fin d =>
        ∃ q : Fin (d * d), q.val / d = row.val ∧
          Pauli.hasXComponent (ErrorVec.mul S_wit E q) = true).card + 1 := by
  refine ⟨ErrorVec.mul S_wit T, InStab.mul hS hT_inStab, ?_⟩
  -- Key pointwise rewrite: (S_wit · T) · (e_B · E) = S_wit · ((T · e_B) · E)
  -- via Pauli associativity.
  have habsorb : ∀ q,
      ErrorVec.mul (ErrorVec.mul S_wit T) (ErrorVec.mul e_B E) q
        = ErrorVec.mul S_wit (ErrorVec.mul (ErrorVec.mul T e_B) E) q := by
    intro q
    show Pauli.mul (Pauli.mul (S_wit q) (T q)) (Pauli.mul (e_B q) (E q))
       = Pauli.mul (S_wit q) (Pauli.mul (Pauli.mul (T q) (e_B q)) (E q))
    rw [Pauli.mul_assoc, ← Pauli.mul_assoc (T q)]
  -- Rewrite the LHS filter via habsorb (pointwise equality → filter equality).
  have hfilterEq :
      (Finset.univ.filter fun row : Fin d =>
        ∃ q : Fin (d * d), q.val / d = row.val ∧
          Pauli.hasXComponent
            (ErrorVec.mul (ErrorVec.mul S_wit T) (ErrorVec.mul e_B E) q) = true)
      = (Finset.univ.filter fun row : Fin d =>
        ∃ q : Fin (d * d), q.val / d = row.val ∧
          Pauli.hasXComponent
            (ErrorVec.mul S_wit (ErrorVec.mul (ErrorVec.mul T e_B) E) q) = true) := by
    apply Finset.filter_congr
    intro row _
    constructor
    · rintro ⟨q, hq, hx⟩; exact ⟨q, hq, (habsorb q) ▸ hx⟩
    · rintro ⟨q, hq, hx⟩; exact ⟨q, hq, (habsorb q).symm ▸ hx⟩
  rw [hfilterEq]
  -- Apply the single-row helper to the residual F := T · e_B
  exact hook_spread_card_le_singleRow i (ErrorVec.mul T e_B) E S_wit
          h_residual_singleRow

/-! ## bulkX suffix-1 scaffold

For a bulk-X stabilizer `s_idx` with grid coord `(r, c)`, the suffix-1
hook spans two rows `{r, r+1}` and is NOT directly covered by
`hook_spread_bound_xInRow_singleton`.  The fix: absorb by the parent
stabilizer `T_s = mkSurfaceStabilizers d hd s_idx`.  The residual
`T_s · suffix1` has X-component only at the single "dropped" position
`(r, c)` — single row `r`.  Applying
`hook_spread_bound_xInRows_via_absorption` with `T := T_s` and the
residual-single-row hypothesis discharges the +1 bound.

The scaffold below makes the composition visible.  The "residual is
single-row" hypothesis is the only remaining structural content —
when proven parametrically, the bulkX suffix-1 case closes
unconditionally.  Until then, callers can supply it per-d via
`decide` at concrete `d`. -/

/-- **bulkX suffix-1 absorption scaffold**: composes the absorption
    theorem with `InStab.gen` for the parent stabilizer.  Takes the
    residual single-row property as a caller-supplied hypothesis.

    Once `hres` is proven structurally for all bulkX kinds, this
    becomes the closed-form bulkX suffix-1 dispatcher (no caller
    hypothesis needed). -/
theorem hook_spread_bound_bulkX_suffix1_via_residual
    (d : Nat) (hd : 0 < d) (hodd : d % 2 = 1)
    (r : Fin d) (s_idx : Fin (numStabFormula d))
    (hres : ∀ q : Fin (d * d), Pauli.hasXComponent
              (ErrorVec.mul
                (mkSurfaceStabilizers d hd s_idx)
                (suffixHook d (classifyStab d s_idx.val) 1) q) = true
            → q.val / d = r.val)
    (E S_wit : ErrorVec (d * d))
    (hS : InStab (mkSurfaceQECParams d hd hodd) S_wit) :
    ∃ S_wit' : ErrorVec (d * d), InStab (mkSurfaceQECParams d hd hodd) S_wit' ∧
      (Finset.univ.filter fun row : Fin d =>
        ∃ q : Fin (d * d), q.val / d = row.val ∧
          Pauli.hasXComponent
            (ErrorVec.mul S_wit'
              (ErrorVec.mul (suffixHook d (classifyStab d s_idx.val) 1) E) q) = true).card
      ≤ (Finset.univ.filter fun row : Fin d =>
        ∃ q : Fin (d * d), q.val / d = row.val ∧
          Pauli.hasXComponent (ErrorVec.mul S_wit E q) = true).card + 1 := by
  apply hook_spread_bound_xInRows_via_absorption d hd hodd s_idx
    (suffixHook d (classifyStab d s_idx.val) 1)
    (mkSurfaceStabilizers d hd s_idx)
    (InStab.gen (P := mkSurfaceQECParams d hd hodd) s_idx)
    r hres E S_wit hS

/-! ## Unconditionally-closing dispatch wrappers

For two subcases of `NZSurfaceSpec.hook_spread_bound`, the closing
theorem is unconditional (no caller-supplied row hypothesis needed):

* **Z-side** (all bulkZ/leftZ/rightZ stabs): the X-component pattern
  is preserved exactly by Z-only hook multiplication, via
  `mkSurfaceHookErrors_Z_no_X`.

* **Full-stab** (parent stabilizer included in `mkSurfaceHookErrors`):
  `InStab.gen` + `hook_spread_bound_full_stab_absorb` close
  unconditionally via Pauli self-inverse.

These two dispatchers cover Z-stab hooks (all of them) + X-stab
full-stab hooks (one per X-stab). Remaining X-stab subcases (single-row
suffix hooks + bulkX suffix-1 absorption) need parametric row
identification — deferred to subsequent ticks. -/

/-- **Z-side dispatcher**: when the stabilizer at `s_idx` is Z-type,
    every hook in `mkSurfaceHookErrors d hd hodd s_idx` is
    X-component-free.  Closes uniformly over the three Z-stab kinds
    (bulkZ, rightZ, leftZ). -/
theorem hook_spread_bound_Z_dispatch
    (d : Nat) (hd : 0 < d) (hodd : d % 2 = 1)
    (s_idx : Fin (numStabFormula d))
    (hZ : isZStab d s_idx)
    (e_B : ErrorVec (d * d))
    (he : e_B ∈ mkSurfaceHookErrors d hd hodd s_idx)
    (E : ErrorVec (d * d)) (S_wit : ErrorVec (d * d))
    (hS : InStab (mkSurfaceQECParams d hd hodd) S_wit) :
    ∃ S_wit' : ErrorVec (d * d), InStab (mkSurfaceQECParams d hd hodd) S_wit' ∧
      (Finset.univ.filter fun row : Fin d =>
        ∃ q : Fin (d * d), q.val / d = row.val ∧
          Pauli.hasXComponent
            (ErrorVec.mul S_wit' (ErrorVec.mul e_B E) q) = true).card
      ≤ (Finset.univ.filter fun row : Fin d =>
        ∃ q : Fin (d * d), q.val / d = row.val ∧
          Pauli.hasXComponent (ErrorVec.mul S_wit E q) = true).card + 1 :=
  hook_spread_bound_Z_side d hd hodd s_idx e_B
    (mkSurfaceHookErrors_Z_no_X d hd hodd s_idx hZ e_B he)
    E S_wit hS

/-- **Full-stab dispatcher**: when `e_B` is the parent stabilizer
    `mkSurfaceStabilizers d hd s_idx`, `InStab.gen` discharges the
    `InStab` premise and the absorption theorem closes via Pauli
    self-inverse. -/
theorem hook_spread_bound_fullStab_dispatch
    (d : Nat) (hd : 0 < d) (hodd : d % 2 = 1)
    (s_idx : Fin (numStabFormula d))
    (E : ErrorVec (d * d)) (S_wit : ErrorVec (d * d))
    (hS : InStab (mkSurfaceQECParams d hd hodd) S_wit) :
    ∃ S_wit' : ErrorVec (d * d), InStab (mkSurfaceQECParams d hd hodd) S_wit' ∧
      (Finset.univ.filter fun row : Fin d =>
        ∃ q : Fin (d * d), q.val / d = row.val ∧
          Pauli.hasXComponent
            (ErrorVec.mul S_wit'
              (ErrorVec.mul (mkSurfaceStabilizers d hd s_idx) E) q) = true).card
      ≤ (Finset.univ.filter fun row : Fin d =>
        ∃ q : Fin (d * d), q.val / d = row.val ∧
          Pauli.hasXComponent (ErrorVec.mul S_wit E q) = true).card + 1 :=
  hook_spread_bound_full_stab_absorb d hd hodd s_idx
    (mkSurfaceStabilizers d hd s_idx)
    (InStab.gen (P := mkSurfaceQECParams d hd hodd) s_idx)
    E S_wit hS

/-! ## Boundary X-stab dispatchers (topX / bottomX)

For topX and bottomX, `kindRowSet` is a singleton, so the X-rowRestricted
property of `mkSurfaceHookErrors` from Path A directly yields the
single-row hypothesis required by `xInRow_singleton`.  No new structural
unfold of `suffixHook` is needed — the existing
`mkSurfaceHookErrors_X_rowRestricted` provides exactly the right
information.  Both dispatchers close at `[propext, Classical.choice,
Quot.sound]`. -/

/-- **topX X-stab dispatcher**: every X-component in a topX hook lies
    in row 0 (`kindRowSet d (.topX _) = {0}`).  Closes via
    `xInRow_singleton` with `i = ⟨0, hd⟩`. -/
theorem hook_spread_bound_topX_dispatch
    (d : Nat) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (s_idx : Fin (numStabFormula d))
    (hX : isXStab d s_idx)
    (b : Nat)
    (hkind : classifyStab d s_idx.val = .topX b)
    (e_B : ErrorVec (d * d))
    (he : e_B ∈ mkSurfaceHookErrors d (by omega) hodd s_idx)
    (E : ErrorVec (d * d)) (S_wit : ErrorVec (d * d))
    (hS : InStab (mkSurfaceQECParams d (by omega) hodd) S_wit) :
    ∃ S_wit' : ErrorVec (d * d), InStab (mkSurfaceQECParams d (by omega) hodd) S_wit' ∧
      (Finset.univ.filter fun row : Fin d =>
        ∃ q : Fin (d * d), q.val / d = row.val ∧
          Pauli.hasXComponent
            (ErrorVec.mul S_wit' (ErrorVec.mul e_B E) q) = true).card
      ≤ (Finset.univ.filter fun row : Fin d =>
        ∃ q : Fin (d * d), q.val / d = row.val ∧
          Pauli.hasXComponent (ErrorVec.mul S_wit E q) = true).card + 1 := by
  have hrow_set := mkSurfaceHookErrors_X_rowRestricted d hd3 hodd s_idx hX e_B he
  have h_row : ∀ q, Pauli.hasXComponent (e_B q) = true → q.val / d = 0 := by
    intro q hq
    have h := hrow_set q hq
    rw [hkind] at h
    simp only [kindRowSet, Finset.mem_singleton] at h
    exact h
  exact hook_spread_bound_xInRow_singleton d (by omega) hodd
    ⟨0, by omega⟩ s_idx e_B h_row E S_wit hS

/-- **bottomX X-stab dispatcher**: every X-component in a bottomX hook
    lies in row `d-1` (`kindRowSet d (.bottomX _) = {d-1}`).  Closes
    via `xInRow_singleton` with `i = ⟨d-1, by omega⟩`. -/
theorem hook_spread_bound_bottomX_dispatch
    (d : Nat) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (s_idx : Fin (numStabFormula d))
    (hX : isXStab d s_idx)
    (b : Nat)
    (hkind : classifyStab d s_idx.val = .bottomX b)
    (e_B : ErrorVec (d * d))
    (he : e_B ∈ mkSurfaceHookErrors d (by omega) hodd s_idx)
    (E : ErrorVec (d * d)) (S_wit : ErrorVec (d * d))
    (hS : InStab (mkSurfaceQECParams d (by omega) hodd) S_wit) :
    ∃ S_wit' : ErrorVec (d * d), InStab (mkSurfaceQECParams d (by omega) hodd) S_wit' ∧
      (Finset.univ.filter fun row : Fin d =>
        ∃ q : Fin (d * d), q.val / d = row.val ∧
          Pauli.hasXComponent
            (ErrorVec.mul S_wit' (ErrorVec.mul e_B E) q) = true).card
      ≤ (Finset.univ.filter fun row : Fin d =>
        ∃ q : Fin (d * d), q.val / d = row.val ∧
          Pauli.hasXComponent (ErrorVec.mul S_wit E q) = true).card + 1 := by
  have hrow_set := mkSurfaceHookErrors_X_rowRestricted d hd3 hodd s_idx hX e_B he
  have h_row : ∀ q, Pauli.hasXComponent (e_B q) = true → q.val / d = d - 1 := by
    intro q hq
    have h := hrow_set q hq
    rw [hkind] at h
    simp only [kindRowSet, Finset.mem_singleton] at h
    exact h
  exact hook_spread_bound_xInRow_singleton d (by omega) hodd
    ⟨d - 1, by omega⟩ s_idx e_B h_row E S_wit hS

/-! ## bulkX suffix structural helper (drop ≥ 2)

For bulkX (Z-order schedule [(r,c), (r,c+1), (r+1,c), (r+1,c+1)]),
the drop-`j` list for `j ∈ {2, 3}` contains only elements with row
`r+1`.  This is a structural fact about the schedule order; combined
with `suffixHook_support_implies_kindOrderRC` it gives the row
identification for suffix hooks at j ≥ 2. -/

/-- Every position in `kindOrderRC d (.bulkX r c)` has col `< d` when
    `c + 1 < d`.  Used by `bulkX_suffix_ge_two_dispatch` to derive
    `rc.2 < d` for the row-quotient computation. -/
lemma kindOrderRC_bulkX_col_lt_d (d r c : Nat) (hc : c + 1 < d)
    (rc : Nat × Nat) (h : rc ∈ kindOrderRC d (.bulkX r c)) : rc.2 < d := by
  simp only [kindOrderRC, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h <;> rw [h] <;> simp <;> omega

/-- Arithmetic helper: `(d * (r + 1) + c) / d = r + 1` when `c < d`. -/
private lemma div_quot_succ_lemma (d r c : Nat) (hd : 0 < d) (hc : c < d) :
    (d * (r + 1) + c) / d = r + 1 := by
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hc]; omega

/-- Drop ≥ 2 of the bulkX Z-order schedule has all positions in row
    `r+1`.  Only suffix indices `j = 2` and `j = 3` produce non-empty
    drop-lists for the length-4 bulkX schedule. -/
theorem kindOrderRC_bulkX_drop_ge_two_row (d r c j : Nat) (hj : 2 ≤ j)
    (rc : Nat × Nat) (h : rc ∈ (kindOrderRC d (.bulkX r c)).drop j) :
    rc.1 = r + 1 := by
  have hlen : (kindOrderRC d (.bulkX r c)).length = 4 := by simp [kindOrderRC]
  by_cases h2 : j = 2
  · subst h2
    simp only [kindOrderRC, List.drop, List.mem_cons, List.not_mem_nil,
               or_false] at h
    rcases h with h | h
    · rw [h]
    · rw [h]
  by_cases h3 : j = 3
  · subst h3
    simp only [kindOrderRC, List.drop, List.mem_cons, List.not_mem_nil,
               or_false] at h
    rw [h]
  have hj4 : 4 ≤ j := by omega
  have hempty : (kindOrderRC d (.bulkX r c)).drop j = [] := by
    apply List.drop_eq_nil_of_le; omega
  rw [hempty] at h
  simp at h

/-- **bulkX suffix (j ≥ 2) dispatcher**: when `e_B = suffixHook d (.bulkX r c) j`
    for `j ≥ 2`, all X-positions are in row `r + 1`.  Closes via
    `xInRow_singleton` with `i = ⟨r + 1, _⟩`. -/
theorem hook_spread_bound_bulkX_suffix_ge_two_dispatch
    (d : Nat) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (s_idx : Fin (numStabFormula d))
    (hX : isXStab d s_idx)
    (r c : Nat)
    (hkind : classifyStab d s_idx.val = .bulkX r c)
    (j : Nat) (hj : 2 ≤ j)
    (E S_wit : ErrorVec (d * d))
    (hS : InStab (mkSurfaceQECParams d (by omega) hodd) S_wit) :
    ∃ S_wit' : ErrorVec (d * d), InStab (mkSurfaceQECParams d (by omega) hodd) S_wit' ∧
      (Finset.univ.filter fun row : Fin d =>
        ∃ q : Fin (d * d), q.val / d = row.val ∧
          Pauli.hasXComponent
            (ErrorVec.mul S_wit'
              (ErrorVec.mul (suffixHook d (.bulkX r c) j) E) q) = true).card
      ≤ (Finset.univ.filter fun row : Fin d =>
        ∃ q : Fin (d * d), q.val / d = row.val ∧
          Pauli.hasXComponent (ErrorVec.mul S_wit E q) = true).card + 1 := by
  have hX_witness := xStab_classify_witness d hd3 hodd s_idx hX
  have hbounds : r + 1 < d ∧ c + 1 < d := by
    rcases hX_witness with ⟨r', c', hkind', hr, hc, _⟩ | ⟨b, hkind', _⟩ | ⟨b, hkind', _⟩
    · rw [hkind] at hkind'; injection hkind' with h1 h2
      subst h1; subst h2; exact ⟨hr, hc⟩
    · rw [hkind] at hkind'; cases hkind'
    · rw [hkind] at hkind'; cases hkind'
  obtain ⟨hr_succ_lt, hc_succ_lt⟩ := hbounds
  have h_row : ∀ q : Fin (d * d),
      Pauli.hasXComponent (suffixHook d (.bulkX r c) j q) = true →
        q.val / d = r + 1 := by
    intro q hq
    have hsupp : suffixHook d (.bulkX r c) j q ≠ Pauli.I := by
      intro h_I; rw [h_I] at hq; exact Bool.false_ne_true hq
    obtain ⟨rc, hrc_mem, hq_eq⟩ :=
      suffixHook_support_implies_kindOrderRC d (by omega) (.bulkX r c) j q hsupp
    have hrc_row : rc.1 = r + 1 :=
      kindOrderRC_bulkX_drop_ge_two_row d r c j hj rc hrc_mem
    have hrc_in : rc ∈ kindOrderRC d (.bulkX r c) := List.mem_of_mem_drop hrc_mem
    have hrc_col_lt_d : rc.2 < d :=
      kindOrderRC_bulkX_col_lt_d d r c hc_succ_lt rc hrc_in
    rw [hq_eq, hrc_row]
    exact div_quot_succ_lemma d r rc.2 (by omega) hrc_col_lt_d
  exact hook_spread_bound_xInRow_singleton d (by omega) hodd
    ⟨r + 1, hr_succ_lt⟩ s_idx _ h_row E S_wit hS

/-! ## Toward bulkX suffix-1 residual single-row

For bulkX `s_idx`, the residual `T_s · suffix1(T_s)` has X-component
only at the dropped position (r, c).  The full proof requires bridging
`mkSurfaceStabilizers` and `kindOrderRC` support; structural helpers
about `kindOrderRC` (row membership, row-r+1-in-drop-1) are landed
here, with the full residual proof deferred. -/

/-- Every position in bulkX `kindOrderRC` has row in `{r, r+1}`. -/
private lemma kindOrderRC_bulkX_row_in_two (d r c : Nat)
    (rc : Nat × Nat) (h : rc ∈ kindOrderRC d (.bulkX r c)) :
    rc.1 = r ∨ rc.1 = r + 1 := by
  simp only [kindOrderRC, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h <;> rw [h] <;> simp

/-- Row-`r+1` positions of bulkX `kindOrderRC` lie in `drop 1` of the
    schedule.  The full schedule is `[(r,c), (r,c+1), (r+1,c),
    (r+1,c+1)]`; drop 1 is `[(r,c+1), (r+1,c), (r+1,c+1)]`.  Both row-r+1
    positions ((r+1,c) and (r+1,c+1)) are present in drop 1.

    This is the key structural fact for the bulkX suffix-1 absorption:
    when the parent stab is multiplied by suffix-1, the row-r+1 positions
    cancel (both in suffix-1's support) leaving only the row-r position
    (r, c) where the parent has X but suffix-1 does not. -/
lemma kindOrderRC_bulkX_row_succ_in_drop_one (d r c : Nat)
    (rc : Nat × Nat) (hmem : rc ∈ kindOrderRC d (.bulkX r c))
    (hrow : rc.1 = r + 1) :
    rc ∈ (kindOrderRC d (.bulkX r c)).drop 1 := by
  simp only [kindOrderRC, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h
  · rw [h] at hrow; omega
  · rw [h] at hrow; omega
  · rw [h]; simp [kindOrderRC, List.drop]
  · rw [h]; simp [kindOrderRC, List.drop]

/-! ### d=3 sanity for the bulkX suffix-1 residual

These concrete `decide`-based examples validate that the residual
`T_s · suffix1(T_s)` is single-row at d=3 for both bulkX stabilizers
(stab 1 = bulkX(0,1), stab 2 = bulkX(1,0)).  Used as ground-truth
checks against the eventual parametric residual proof. -/

example :
    ∀ q : Fin 9,
      Pauli.hasXComponent
        (ErrorVec.mul (mkSurfaceStabilizers 3 (by decide) ⟨1, by decide⟩)
          (suffixHook 3 (.bulkX 0 1) 1) q) = true →
      q.val / 3 = 0 := by decide

example :
    ∀ q : Fin 9,
      Pauli.hasXComponent
        (ErrorVec.mul (mkSurfaceStabilizers 3 (by decide) ⟨2, by decide⟩)
          (suffixHook 3 (.bulkX 1 0) 1) q) = true →
      q.val / 3 = 1 := by decide

/-! ## Forward direction: suffixHook non-trivial at kindOrderRC-drop members

The reverse direction (`suffixHook_support_implies_kindOrderRC`) was
already provided by SurfaceHookErrors.lean: `suffixHook q ≠ I → q's
coord is in drop j`.  Here we prove the FORWARD direction: if q's coord
is in drop j, then `suffixHook q ≠ I` (specifically returns
`kindPauli k`).  Both compile at the very strict `[propext, Quot.sound]`
axiom set — no `Classical.choice`. -/

/-- Inductive helper: lookup of a key present in the list returns non-`none`. -/
private lemma lookup_ne_none_of_key_mem
    {α : Type _} (l : List α) (f : α → Nat) (c : Pauli) (n : Nat)
    (h : ∃ a ∈ l, n = f a) :
    (l.map (fun a => (f a, c))).lookup n ≠ none := by
  induction l with
  | nil =>
    obtain ⟨a, ha, _⟩ := h
    simp at ha
  | cons a as ih =>
    intro hnone
    simp only [List.map_cons, List.lookup] at hnone
    by_cases hbeq : (n == f a) = true
    · rw [hbeq] at hnone
      simp at hnone
    · rw [Bool.not_eq_true] at hbeq
      rw [hbeq] at hnone
      obtain ⟨b, hb, hb_eq⟩ := h
      rw [List.mem_cons] at hb
      rcases hb with hb_left | hb_right
      · subst hb_left
        have : (n == f b) = true := beq_iff_eq.mpr hb_eq
        rw [this] at hbeq
        exact Bool.noConfusion hbeq
      · exact ih ⟨b, hb_right, hb_eq⟩ hnone

/-- Forward direction: if q's coordinate is in `drop j` of `kindOrderRC d k`,
    then `suffixHook d k j q ≠ Pauli.I`.  The "ne I" form ensures the value
    is exactly `kindPauli k` (X for X-stab kinds, Z for Z-stab kinds). -/
lemma suffixHook_at_kindOrderRC_drop_ne_I (d : Nat) (k : StabKind) (j : Nat)
    (q : Fin (d * d))
    (hmem : ∃ rc, rc ∈ (kindOrderRC d k).drop j ∧ q.val = gridIdx d rc.1 rc.2) :
    suffixHook d k j q ≠ Pauli.I := by
  intro h_eq_I
  unfold suffixHook ofList suffixPairs at h_eq_I
  rcases lookup_map_const_snd ((kindOrderRC d k).drop j)
      (fun rc => gridIdx d rc.1 rc.2) (kindPauli k) q.val with hnone | hsome
  · exact lookup_ne_none_of_key_mem ((kindOrderRC d k).drop j)
      (fun rc => gridIdx d rc.1 rc.2) (kindPauli k) q.val
      (by obtain ⟨rc, h1, h2⟩ := hmem; exact ⟨rc, h1, h2⟩)
      hnone
  · rw [hsome] at h_eq_I
    simp at h_eq_I
    cases k <;> simp [kindPauli] at h_eq_I

/-! ## Bridge: mkSurfaceStabilizers ↔ kindOrderRC for bulkX

The forward direction `mkSurfaceStabilizers_bulkX_X_implies_in_kindOrderRC`
follows from the existing public `decode_ne_I_implies_in_kindOrderRC`.

The reverse direction `in_kindOrderRC_bulkX_implies_decode_ne_I` requires
the structural fact about `decodeStabPauliAt`'s bulk case: composes
`inStabSupport_iff_supportByKind` (also just unprivated) + a direct
case analysis on the 4 kindOrderRC elements via `supportByKind`. -/

/-- Forward bridge: `T_s q = X` (for bulkX X-stab) implies
    `(q.val/d, q.val%d) ∈ kindOrderRC d (.bulkX r c)`. -/
lemma mkSurfaceStabilizers_bulkX_X_implies_in_kindOrderRC
    (d : Nat) (hd : 0 < d)
    (s_idx : Fin (numStabFormula d))
    (q : Fin (d * d))
    (hx : Pauli.hasXComponent (mkSurfaceStabilizers d hd s_idx q) = true) :
    (q.val / d, q.val % d) ∈ kindOrderRC d (classifyStab d s_idx.val) := by
  have h_ne_I : mkSurfaceStabilizers d hd s_idx q ≠ Pauli.I := by
    intro h_I; rw [h_I] at hx; exact Bool.false_ne_true hx
  unfold mkSurfaceStabilizers at h_ne_I
  exact decode_ne_I_implies_in_kindOrderRC d s_idx.val (q.val / d) (q.val % d) h_ne_I

/-- For bulkX kind, every kindOrderRC element satisfies the abstract
    support predicate `supportByKind`. -/
lemma supportByKind_of_mem_kindOrderRC_bulkX (d r c : Nat) (rc : Nat × Nat)
    (h : rc ∈ kindOrderRC d (.bulkX r c)) :
    supportByKind d (.bulkX r c) rc.1 rc.2 = true := by
  simp only [kindOrderRC, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [supportByKind, decide_eq_true_eq]
  rcases h with h | h | h | h <;> rw [h] <;> simp

/-- Reverse bridge: if `(row, col) ∈ kindOrderRC d (.bulkX r c)` and
    `classifyStab d i = .bulkX r c`, then `decodeStabPauliAt d i row col`
    is not `Pauli.I`.  Composes `inStabSupport_iff_supportByKind` +
    `supportByKind_of_mem_kindOrderRC_bulkX`. -/
lemma in_kindOrderRC_bulkX_implies_decode_ne_I
    (d : Nat) (i r c : Nat)
    (hkind : classifyStab d i = .bulkX r c)
    (row col : Nat)
    (hmem : (row, col) ∈ kindOrderRC d (.bulkX r c)) :
    decodeStabPauliAt d i row col ≠ Pauli.I := by
  show inStabSupport d i row col
  rw [inStabSupport_iff_supportByKind, hkind]
  exact supportByKind_of_mem_kindOrderRC_bulkX d r c (row, col) hmem

/-! ## The bulkX suffix-1 residual single-row theorem

This composes all 8 helpers landed across ticks 7-16 to close the LAST
X-side subcase of `NZSurfaceSpec.hook_spread_bound`.  Combined with the
5 unconditional X-side dispatchers and the Z-side dispatcher, this
gives 6/6 subcases ready for the dispatch wrapper. -/

/-- **Parametric bulkX-suffix-1 residual single-row**: for an X-stab
    of bulkX kind, the residual `T_s · suffix1(T_s)` has X-component
    only at qubit `(r, c)` — single row `r`.

    Proof structure: XOR-decompose `hasX(T_s · suffix1 q) = true` into
    two subcases.
    Case A (T_s X, suffix1 I): row in {r, r+1} via X_row; if r+1, then
    in drop-1 via row_succ_in_drop_one; then suffix1 X by forward
    direction.  Contradicts suffix1 I.  So row = r.
    Case B (T_s I, suffix1 X): suffix1 X implies q in drop-1 ⊆
    kindOrderRC (backward direction); then T_s X by reverse bridge.
    Contradicts T_s I. -/
theorem bulkX_suffix1_residual_row_eq_r
    (d : Nat) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (s_idx : Fin (numStabFormula d))
    (hX : isXStab d s_idx)
    (r c : Nat)
    (hkind : classifyStab d s_idx.val = .bulkX r c)
    (q : Fin (d * d))
    (hx : Pauli.hasXComponent
          (ErrorVec.mul (mkSurfaceStabilizers d (by omega) s_idx)
            (suffixHook d (.bulkX r c) 1) q) = true) :
    q.val / d = r := by
  have hd_pos : 0 < d := by omega
  have hbounds : r + 1 < d ∧ c + 1 < d := by
    have hX_witness := xStab_classify_witness d hd3 hodd s_idx hX
    rcases hX_witness with ⟨r', c', hkind', hr, hc, _⟩ | ⟨b, hkind', _⟩ | ⟨b, hkind', _⟩
    · rw [hkind] at hkind'; injection hkind' with h1 h2
      subst h1; subst h2; exact ⟨hr, hc⟩
    · rw [hkind] at hkind'; cases hkind'
    · rw [hkind] at hkind'; cases hkind'
  obtain ⟨hr_succ_lt, hc_succ_lt⟩ := hbounds
  rw [show ErrorVec.mul (mkSurfaceStabilizers d hd_pos s_idx)
            (suffixHook d (.bulkX r c) 1) q
        = Pauli.mul (mkSurfaceStabilizers d hd_pos s_idx q)
                    (suffixHook d (.bulkX r c) 1 q) from rfl,
      Pauli.hasXComponent_mul_eq_xor] at hx
  by_cases hT : Pauli.hasXComponent (mkSurfaceStabilizers d hd_pos s_idx q) = true
  · -- Case A
    have hSf : Pauli.hasXComponent (suffixHook d (.bulkX r c) 1 q) = false := by
      cases hSf_val : Pauli.hasXComponent (suffixHook d (.bulkX r c) 1 q)
      · rfl
      · rw [hT, hSf_val] at hx; simp at hx
    have h_row_in : q.val / d ∈ kindRowSet d (classifyStab d s_idx.val) :=
      mkSurfaceStabilizers_X_row d hd_pos hodd s_idx hX q hT
    rw [hkind] at h_row_in
    simp only [kindRowSet, Finset.mem_insert, Finset.mem_singleton] at h_row_in
    rcases h_row_in with hrow_r | hrow_succ_r
    · exact hrow_r
    · exfalso
      have hin : (q.val / d, q.val % d) ∈ kindOrderRC d (classifyStab d s_idx.val) :=
        mkSurfaceStabilizers_bulkX_X_implies_in_kindOrderRC d hd_pos s_idx q hT
      rw [hkind] at hin
      have hin_drop : (q.val / d, q.val % d) ∈ (kindOrderRC d (.bulkX r c)).drop 1 :=
        kindOrderRC_bulkX_row_succ_in_drop_one d r c (q.val / d, q.val % d) hin
          hrow_succ_r
      have hSf_ne : suffixHook d (.bulkX r c) 1 q ≠ Pauli.I := by
        apply suffixHook_at_kindOrderRC_drop_ne_I
        refine ⟨(q.val / d, q.val % d), hin_drop, ?_⟩
        show q.val = d * (q.val / d) + q.val % d
        exact (Nat.div_add_mod q.val d).symm
      have hSf_eq_I : suffixHook d (.bulkX r c) 1 q = Pauli.I := by
        rcases suffixHook_eq_I_or_kindPauli d (.bulkX r c) 1 q with h | h
        · exact h
        · have : kindPauli (.bulkX r c) = Pauli.X := rfl
          rw [this] at h
          rw [h] at hSf
          simp [Pauli.hasXComponent] at hSf
      exact hSf_ne hSf_eq_I
  · -- Case B
    exfalso
    push_neg at hT
    have hT_false : Pauli.hasXComponent (mkSurfaceStabilizers d hd_pos s_idx q) = false := by
      cases hval : Pauli.hasXComponent (mkSurfaceStabilizers d hd_pos s_idx q)
      · rfl
      · exact absurd hval hT
    have hSf : Pauli.hasXComponent (suffixHook d (.bulkX r c) 1 q) = true := by
      cases hSf_val : Pauli.hasXComponent (suffixHook d (.bulkX r c) 1 q)
      · rw [hT_false, hSf_val] at hx; simp at hx
      · rfl
    have hSf_ne : suffixHook d (.bulkX r c) 1 q ≠ Pauli.I := by
      intro h_I; rw [h_I] at hSf; simp [Pauli.hasXComponent] at hSf
    obtain ⟨rc, hrc_mem, hq_eq⟩ :=
      suffixHook_support_implies_kindOrderRC d hd_pos (.bulkX r c) 1 q hSf_ne
    have hrc_in : rc ∈ kindOrderRC d (.bulkX r c) := List.mem_of_mem_drop hrc_mem
    have hrc_col_lt_d : rc.2 < d :=
      kindOrderRC_bulkX_col_lt_d d r c hc_succ_lt rc hrc_in
    have hq_div : q.val / d = rc.1 := by
      rw [hq_eq]; show (d * rc.1 + rc.2) / d = rc.1
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ hd_pos, Nat.div_eq_of_lt hrc_col_lt_d]
      omega
    have hq_mod : q.val % d = rc.2 := by
      rw [hq_eq]; show (d * rc.1 + rc.2) % d = rc.2
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrc_col_lt_d]
    have h_dec_ne_I : decodeStabPauliAt d s_idx.val rc.1 rc.2 ≠ Pauli.I :=
      in_kindOrderRC_bulkX_implies_decode_ne_I d s_idx.val r c hkind rc.1 rc.2 hrc_in
    have hT_ne_I : mkSurfaceStabilizers d hd_pos s_idx q ≠ Pauli.I := by
      show decodeStabPauliAt d s_idx.val (q.val / d) (q.val % d) ≠ Pauli.I
      rw [hq_div, hq_mod]
      exact h_dec_ne_I
    have hstabType : stabType d s_idx.val = Pauli.X := hX
    have hI_or_X : mkSurfaceStabilizers d hd_pos s_idx q = Pauli.I ∨
                   mkSurfaceStabilizers d hd_pos s_idx q = Pauli.X := by
      show decodeStabPauliAt d s_idx.val (q.val / d) (q.val % d) = Pauli.I ∨
           decodeStabPauliAt d s_idx.val (q.val / d) (q.val % d) = Pauli.X
      rcases decode_I_or_stabType_pub d s_idx.val (q.val / d) (q.val % d) with hI | hX'
      · left; exact hI
      · right; rw [hX', hstabType]
    rcases hI_or_X with hI | hXX
    · exact hT_ne_I hI
    · rw [hXX] at hT_false
      simp [Pauli.hasXComponent] at hT_false

/-! ## Dichotomy: every surface stabilizer is X- or Z-type

This is the key case-split used by the `hook_spread_bound_parametric`
dispatch wrapper to route between Z-side and X-side closing theorems. -/

/-- Every surface stab is either X-type or Z-type. -/
lemma isXStab_or_isZStab (d : Nat) (s : Fin (numStabFormula d)) :
    isXStab d s ∨ isZStab d s := by
  show stabType d s.val = Pauli.X ∨ stabType d s.val = Pauli.Z
  simp only [stabType]
  split_ifs <;> tauto

/-! ## Partial dispatch wrapper: Z-side closed; X-side as hypothesis

This intermediate wrapper handles the Z-stab branch unconditionally
via `hook_spread_bound_Z_dispatch`.  The X-stab branch is factored out
as a caller hypothesis (`X_dispatch`), to be filled in by an X-side
dispatch wrapper that case-splits on classifyStab kind. -/

/-- Dispatcher composing Z-side dispatch unconditionally; takes X-side
    dispatch as a parameter to be supplied by composition. -/
theorem hook_spread_bound_parametric_via_X_hypothesis
    (d : Nat) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (s_idx : Fin (numStabFormula d))
    (e_B : ErrorVec (d * d))
    (he : e_B ∈ mkSurfaceHookErrors d (by omega) hodd s_idx)
    (E S_wit : ErrorVec (d * d))
    (hS : InStab (mkSurfaceQECParams d (by omega) hodd) S_wit)
    (X_dispatch : isXStab d s_idx →
        ∃ S_wit' : ErrorVec (d * d), InStab (mkSurfaceQECParams d (by omega) hodd) S_wit' ∧
          (Finset.univ.filter fun row : Fin d =>
            ∃ q : Fin (d * d), q.val / d = row.val ∧
              Pauli.hasXComponent
                (ErrorVec.mul S_wit' (ErrorVec.mul e_B E) q) = true).card
          ≤ (Finset.univ.filter fun row : Fin d =>
            ∃ q : Fin (d * d), q.val / d = row.val ∧
              Pauli.hasXComponent (ErrorVec.mul S_wit E q) = true).card + 1) :
    ∃ S_wit' : ErrorVec (d * d), InStab (mkSurfaceQECParams d (by omega) hodd) S_wit' ∧
      (Finset.univ.filter fun row : Fin d =>
        ∃ q : Fin (d * d), q.val / d = row.val ∧
          Pauli.hasXComponent
            (ErrorVec.mul S_wit' (ErrorVec.mul e_B E) q) = true).card
      ≤ (Finset.univ.filter fun row : Fin d =>
        ∃ q : Fin (d * d), q.val / d = row.val ∧
          Pauli.hasXComponent (ErrorVec.mul S_wit E q) = true).card + 1 := by
  rcases isXStab_or_isZStab d s_idx with hX | hZ
  · exact X_dispatch hX
  · exact hook_spread_bound_Z_dispatch d (by omega) hodd s_idx hZ e_B he E S_wit hS

/-! ## Contradiction lemmas: Z-kind classification rules out isXStab

When `classifyStab` returns a Z-type kind (bulkZ / rightZ / leftZ),
the stabilizer cannot satisfy `isXStab`.  Used by the X-side
dispatcher to dismiss the Z-kind branches via `xStab_classify_witness`'s
3-way disjunction. -/

private lemma not_isXStab_of_classify_bulkZ (d : Nat) (s : Fin (numStabFormula d))
    (r c : Nat) (hk : classifyStab d s.val = .bulkZ r c) : ¬ isXStab d s := by
  unfold isXStab
  have h := kindPauli_eq_stabType d s.val
  rw [hk] at h
  show stabType d s.val ≠ Pauli.X
  rw [← h]; intro h_eq; simp [kindPauli] at h_eq

private lemma not_isXStab_of_classify_rightZ (d : Nat) (s : Fin (numStabFormula d))
    (b : Nat) (hk : classifyStab d s.val = .rightZ b) : ¬ isXStab d s := by
  unfold isXStab
  have h := kindPauli_eq_stabType d s.val
  rw [hk] at h
  show stabType d s.val ≠ Pauli.X
  rw [← h]; intro h_eq; simp [kindPauli] at h_eq

private lemma not_isXStab_of_classify_leftZ (d : Nat) (s : Fin (numStabFormula d))
    (b : Nat) (hk : classifyStab d s.val = .leftZ b) : ¬ isXStab d s := by
  unfold isXStab
  have h := kindPauli_eq_stabType d s.val
  rw [hk] at h
  show stabType d s.val ≠ Pauli.X
  rw [← h]; intro h_eq; simp [kindPauli] at h_eq

/-! ## bulkX suffix-1 specialized dispatcher

The `hook_spread_bound_bulkX_suffix1_via_residual` scaffold uses the
`classifyStab d s_idx.val` form of `suffixHook`.  After case-splitting
on `xStab_classify_witness`, the goal contains `.bulkX r c` instead.
This specialized dispatcher takes `r`, `c`, `hkind` explicitly and
calls `hook_spread_bound_xInRows_via_absorption` DIRECTLY (bypassing
the scaffold) to match the post-subst goal form. -/

theorem hook_spread_bound_bulkX_suffix1_dispatch
    (d : Nat) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (s_idx : Fin (numStabFormula d))
    (hX : isXStab d s_idx)
    (r c : Nat)
    (hkind : classifyStab d s_idx.val = .bulkX r c)
    (hr_lt : r < d)
    (E S_wit : ErrorVec (d * d))
    (hS : InStab (mkSurfaceQECParams d (by omega) hodd) S_wit) :
    ∃ S_wit' : ErrorVec (d * d), InStab (mkSurfaceQECParams d (by omega) hodd) S_wit' ∧
      (Finset.univ.filter fun row : Fin d =>
        ∃ q : Fin (d * d), q.val / d = row.val ∧
          Pauli.hasXComponent
            (ErrorVec.mul S_wit'
              (ErrorVec.mul (suffixHook d (.bulkX r c) 1) E) q) = true).card
      ≤ (Finset.univ.filter fun row : Fin d =>
        ∃ q : Fin (d * d), q.val / d = row.val ∧
          Pauli.hasXComponent (ErrorVec.mul S_wit E q) = true).card + 1 :=
  hook_spread_bound_xInRows_via_absorption d (by omega) hodd s_idx
    (suffixHook d (.bulkX r c) 1)
    (mkSurfaceStabilizers d (by omega) s_idx)
    (InStab.gen (P := mkSurfaceQECParams d (by omega) hodd) s_idx)
    ⟨r, hr_lt⟩
    (fun q hxq => bulkX_suffix1_residual_row_eq_r d hd3 hodd s_idx hX r c hkind q hxq)
    E S_wit hS

/-! ## X-side dispatcher: composes 4 X-stab subcases + parent-stab -/

/-- **X-side dispatcher**: case-splits on `xStab_classify_witness` (topX,
    bottomX, bulkX) + for bulkX, on `suffixIndices = [1,2,3]`.  Routes
    each case to the appropriate sub-dispatcher.  Parent-stab branch
    closes via `hook_spread_bound_fullStab_dispatch`. -/
theorem hook_spread_bound_X_dispatch_full
    (d : Nat) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (s_idx : Fin (numStabFormula d))
    (hX : isXStab d s_idx)
    (e_B : ErrorVec (d * d))
    (he : e_B ∈ mkSurfaceHookErrors d (by omega) hodd s_idx)
    (E S_wit : ErrorVec (d * d))
    (hS : InStab (mkSurfaceQECParams d (by omega) hodd) S_wit) :
    ∃ S_wit' : ErrorVec (d * d), InStab (mkSurfaceQECParams d (by omega) hodd) S_wit' ∧
      (Finset.univ.filter fun row : Fin d =>
        ∃ q : Fin (d * d), q.val / d = row.val ∧
          Pauli.hasXComponent
            (ErrorVec.mul S_wit' (ErrorVec.mul e_B E) q) = true).card
      ≤ (Finset.univ.filter fun row : Fin d =>
        ∃ q : Fin (d * d), q.val / d = row.val ∧
          Pauli.hasXComponent (ErrorVec.mul S_wit E q) = true).card + 1 := by
  unfold mkSurfaceHookErrors at he
  rw [Finset.mem_union] at he
  rcases he with he_suff | he_full
  · rw [Finset.mem_image] at he_suff
    obtain ⟨j, hj_mem, hj_eq⟩ := he_suff
    have hX_wit := xStab_classify_witness d hd3 hodd s_idx hX
    rcases hX_wit with ⟨r, c, hkind, hr_lt, _, _⟩ | ⟨b, hkind, _⟩ | ⟨b, hkind, _⟩
    · rw [hkind] at hj_eq hj_mem; subst hj_eq
      have hj_range : j = 1 ∨ j = 2 ∨ j = 3 := by
        have h_eq : suffixIndices d (.bulkX r c) = [1, 2, 3] := rfl
        rw [h_eq, List.mem_toFinset] at hj_mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj_mem; exact hj_mem
      rcases hj_range with h_j1 | h_j2 | h_j3
      · subst h_j1
        exact hook_spread_bound_bulkX_suffix1_dispatch d hd3 hodd s_idx hX r c hkind
          (by omega) E S_wit hS
      · subst h_j2
        exact hook_spread_bound_bulkX_suffix_ge_two_dispatch d hd3 hodd s_idx hX r c hkind
          2 (by omega) E S_wit hS
      · subst h_j3
        exact hook_spread_bound_bulkX_suffix_ge_two_dispatch d hd3 hodd s_idx hX r c hkind
          3 (by omega) E S_wit hS
    · rw [hkind] at hj_eq hj_mem; subst hj_eq
      exact hook_spread_bound_topX_dispatch d hd3 hodd s_idx hX b hkind _
        (by unfold mkSurfaceHookErrors; rw [Finset.mem_union]; left
            rw [Finset.mem_image]; exact ⟨j, by rw [hkind]; exact hj_mem, by rw [hkind]⟩)
        E S_wit hS
    · rw [hkind] at hj_eq hj_mem; subst hj_eq
      exact hook_spread_bound_bottomX_dispatch d hd3 hodd s_idx hX b hkind _
        (by unfold mkSurfaceHookErrors; rw [Finset.mem_union]; left
            rw [Finset.mem_image]; exact ⟨j, by rw [hkind]; exact hj_mem, by rw [hkind]⟩)
        E S_wit hS
  · rw [Finset.mem_singleton] at he_full; subst he_full
    exact hook_spread_bound_fullStab_dispatch d (by omega) hodd s_idx E S_wit hS

/-! ## ★ THE PARAMETRIC `NZSurfaceSpec.hook_spread_bound` HEADLINE ★

Composes `hook_spread_bound_X_dispatch_full` (X-side) +
`hook_spread_bound_Z_dispatch` (Z-side) via `isXStab_or_isZStab`
dichotomy.  This is the unconditional parametric `hook_spread_bound`
field for the rotated surface code at arbitrary odd `d ≥ 3`. -/

/-- **The parametric `NZSurfaceSpec.hook_spread_bound`**: for any back-action
    error `e_B` from `mkSurfaceHookErrors`, there exists a stabilizer
    witness `S_wit'` such that the row-X-card grows by at most 1.  Axiom-clean
    at `[propext, Classical.choice, Quot.sound]`. -/
theorem hook_spread_bound_parametric
    (d : Nat) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (s_idx : Fin (numStabFormula d))
    (e_B : ErrorVec (d * d))
    (he : e_B ∈ mkSurfaceHookErrors d (by omega) hodd s_idx)
    (E S_wit : ErrorVec (d * d))
    (hS : InStab (mkSurfaceQECParams d (by omega) hodd) S_wit) :
    ∃ S_wit' : ErrorVec (d * d), InStab (mkSurfaceQECParams d (by omega) hodd) S_wit' ∧
      (Finset.univ.filter fun row : Fin d =>
        ∃ q : Fin (d * d), q.val / d = row.val ∧
          Pauli.hasXComponent
            (ErrorVec.mul S_wit' (ErrorVec.mul e_B E) q) = true).card
      ≤ (Finset.univ.filter fun row : Fin d =>
        ∃ q : Fin (d * d), q.val / d = row.val ∧
          Pauli.hasXComponent (ErrorVec.mul S_wit E q) = true).card + 1 := by
  rcases isXStab_or_isZStab d s_idx with hX | hZ
  · exact hook_spread_bound_X_dispatch_full d hd3 hodd s_idx hX e_B he E S_wit hS
  · exact hook_spread_bound_Z_dispatch d (by omega) hodd s_idx hZ e_B he E S_wit hS

/-! ## `NZSurfaceSpec.rowCut_succ` conjunct (c) — pointwise reduction

The `NZSurfaceSpec.rowCut_succ` field demands `∃ S, InStab params S ∧
(∀ q, S q = I ∨ S q = Z) ∧ rowCut ⟨i+1, hi⟩ = ErrorVec.mul S (rowCut i)`.

For our parametric instantiation `S := rowStepWitness d hd1 hodd i hi`,
conjuncts (a) `InStab` and (b) `{I, Z}` are already discharged by
`rowStepWitness_inStab_mkSurfaceQECParams` and `rowStepWitness_I_or_Z`.

Conjunct (c) is the actual telescoping equation `mkSurfaceRowCut d ⟨i+1, hi⟩ =
ErrorVec.mul (rowStepWitness ...) (mkSurfaceRowCut d ⟨i, hi_pos⟩)`.

This section gives:

1. **`rowStepWitness_rowCut_eq`** — a pointwise reduction taking the
   "row support" hypothesis (`rowStepWitness q = Z` iff `q.val / d ∈ {i, i+1}`,
   else `I`).  Axiom-clean at `[propext, Quot.sound]` (stricter than baseline).

2. **`mkSurfaceRowCut_succ_conditional`** — the full `∃`-form matching the
   exact shape of `NZSurfaceSpec.rowCut_succ`, parameterised on the same
   row-support hypothesis.

The remaining obligation is the row-support hypothesis itself,
`rowStepWitness_row_support`, which is a per-qubit XOR-counting fact about
the bulk-Z stabilizer product.  Per-d sanity (`decide` at `d = 3, 5`) confirms
the statement; the parametric proof is deferred to a follow-up tick. -/

/-- **Conjunct (c) of `NZSurfaceSpec.rowCut_succ`** — pointwise reduction:
    given the "row support" hypothesis that `rowStepWitness q = Z` iff
    `q.val / d ∈ {i, i+1}`, the telescoping equation
    `mkSurfaceRowCut d ⟨i+1, hi⟩ = ErrorVec.mul (rowStepWitness ...)
    (mkSurfaceRowCut d ⟨i, hi_pos⟩)` follows by a 3-way case split on
    `q.val / d`.  Axiom-clean at `[propext, Quot.sound]`. -/
theorem rowStepWitness_rowCut_eq
    (d : Nat) (hd1 : 1 < d) (hodd : d % 2 = 1)
    (i : Nat) (hi : i + 1 < d) (hi_pos : i < d)
    (hpointwise : ∀ q : Fin (d * d),
       rowStepWitness d hd1 hodd i hi q =
         if q.val / d = i ∨ q.val / d = i + 1 then Pauli.Z else Pauli.I) :
    mkSurfaceRowCut d ⟨i + 1, hi⟩
      = ErrorVec.mul (rowStepWitness d hd1 hodd i hi)
                     (mkSurfaceRowCut d ⟨i, hi_pos⟩) := by
  funext q
  show mkSurfaceRowCut d ⟨i + 1, hi⟩ q
       = Pauli.mul (rowStepWitness d hd1 hodd i hi q)
                   (mkSurfaceRowCut d ⟨i, hi_pos⟩ q)
  rw [mkSurfaceRowCut_spec, mkSurfaceRowCut_spec, hpointwise q]
  by_cases h1 : q.val / d = i
  · -- q in row i: LHS = I (since i ≠ i+1), RHS = Pauli.mul Z Z = I
    have h2 : q.val / d ≠ i + 1 := by omega
    have h_or : q.val / d = i ∨ q.val / d = i + 1 := Or.inl h1
    rw [if_neg h2, if_pos h_or, if_pos h1]
    rfl
  · by_cases h2 : q.val / d = i + 1
    · -- q in row i+1: LHS = Z, RHS = Pauli.mul Z I = Z
      have h_or : q.val / d = i ∨ q.val / d = i + 1 := Or.inr h2
      rw [if_pos h2, if_pos h_or, if_neg h1]
      rfl
    · -- q in neither row: LHS = I, RHS = Pauli.mul I I = I
      have h_or : ¬ (q.val / d = i ∨ q.val / d = i + 1) :=
        fun hc => hc.elim h1 h2
      rw [if_neg h2, if_neg h_or, if_neg h1]
      rfl

/-- **The conditional `NZSurfaceSpec.rowCut_succ` for the parametric
    surface code** — the full `∃`-form parameterised on the row-support
    hypothesis.  Witness is `rowStepWitness d hd1 hodd i hi`.

    The three conjuncts:
    * (a) `InStab` — `rowStepWitness_inStab_mkSurfaceQECParams`
    * (b) `∀ q, S q = I ∨ S q = Z` — `rowStepWitness_I_or_Z`
    * (c) telescoping pointwise equation — `rowStepWitness_rowCut_eq`

    Axiom-clean at `[propext, Classical.choice, Quot.sound]`.  Plugged into
    `mkSurfaceNZSurfaceSpec` (to come), this discharges `rowCut_succ`
    modulo the deferred `rowStepWitness_row_support` pointwise lemma. -/
theorem mkSurfaceRowCut_succ_conditional
    (d : Nat) (hd1 : 1 < d) (hodd : d % 2 = 1)
    (i : Nat) (hi : i + 1 < d) (hi_pos : i < d)
    (hpointwise : ∀ q : Fin (d * d),
       rowStepWitness d hd1 hodd i hi q =
         if q.val / d = i ∨ q.val / d = i + 1 then Pauli.Z else Pauli.I) :
    ∃ S : ErrorVec (d * d),
      InStab (mkSurfaceQECParams d (by omega) hodd) S ∧
      (∀ q : Fin (d * d), S q = Pauli.I ∨ S q = Pauli.Z) ∧
      mkSurfaceRowCut d ⟨i + 1, hi⟩
        = ErrorVec.mul S (mkSurfaceRowCut d ⟨i, hi_pos⟩) :=
  ⟨ rowStepWitness d hd1 hodd i hi
  , rowStepWitness_inStab_mkSurfaceQECParams d hodd hd1 i hi
  , rowStepWitness_I_or_Z d hd1 hodd i hi
  , rowStepWitness_rowCut_eq d hd1 hodd i hi hi_pos hpointwise ⟩

/-! ### d=3, d=5 sanity for the row-support hypothesis.

These `decide`-based sanity checks confirm that the hypothesis
`hpointwise` in `mkSurfaceRowCut_succ_conditional` IS satisfied at the
small concrete distances we care about (d=3, d=5).  This validates
that the parametric design is mathematically correct, and that any
per-d instantiation will be able to discharge the hypothesis. -/

-- d=3, i=0: rowStepWitness is Z on rows {0, 1}, I on row 2.
example :
    ∀ q : Fin (3 * 3),
      rowStepWitness 3 (by decide) (by decide) 0 (by decide) q =
        (if q.val / 3 = 0 ∨ q.val / 3 = 0 + 1 then Pauli.Z else Pauli.I) := by
  decide

-- d=3, i=1: rowStepWitness is Z on rows {1, 2}, I on row 0.
example :
    ∀ q : Fin (3 * 3),
      rowStepWitness 3 (by decide) (by decide) 1 (by decide) q =
        (if q.val / 3 = 1 ∨ q.val / 3 = 1 + 1 then Pauli.Z else Pauli.I) := by
  decide

-- d=5, i=2: rowStepWitness is Z on rows {2, 3}, I on rows {0, 1, 4}.
example :
    ∀ q : Fin (5 * 5),
      rowStepWitness 5 (by decide) (by decide) 2 (by decide) q =
        (if q.val / 5 = 2 ∨ q.val / 5 = 2 + 1 then Pauli.Z else Pauli.I) := by
  decide

/-! ## Foundation: pointwise XOR semantics of `stabListProd`

The row-support residual obligation
`rowStepWitness q = Z ↔ q.val/d ∈ {i, i+1}` reduces, via these three
lemmas, to a per-qubit Z-count parity check over the underlying
stabilizer list.

* **`stabListProd_apply`** — pointwise definitional unfolding: at any
  qubit `q`, the product evaluates to `(l.map (·q)).foldr mul I`.
  Axiom-free.

* **`foldr_mul_I_or_Z_eq_Z_iff_count_odd`** — for a list whose every
  element is `{I, Z}`, the iterated `Pauli.mul` is `Z` iff the count of
  `Z`-entries is odd.  Axiom-clean at `[propext, Quot.sound]`.

* **`stabListProd_at_eq_Z_iff_count_odd`** — composed: for a list of
  `ErrorVec`s each in `{I, Z}` at qubit `q`, `stabListProd l q = Z` iff
  the count of stabs marked `Z` at `q` is odd.  Axiom-clean at
  `[propext, Quot.sound]`.

This is the foundation that the per-qubit row-support proof will
exploit: for each qubit `q`, the residual obligation becomes a Z-count
parity check over `rowStepStabsRaw d i`. -/

/-- **Pointwise semantics of `stabListProd`**: at any qubit `q`,
    `stabListProd l q` equals the iterated `Pauli.mul` over the list of
    values `l.map (·q)`, starting from `Pauli.I`.  Axiom-free. -/
theorem stabListProd_apply {n : Nat} (l : List (ErrorVec n)) (q : Fin n) :
    stabListProd l q = (l.map (fun E => E q)).foldr Pauli.mul Pauli.I := by
  induction l with
  | nil => unfold stabListProd ErrorVec.identity; rfl
  | cons a l ih =>
    show Pauli.mul (a q) (stabListProd l q) = _
    rw [ih]; rfl

/-- Auxiliary: foldr `Pauli.mul` over an I-or-Z list stays in `{I, Z}`. -/
private lemma foldr_mul_I_or_Z_is_I_or_Z (l : List Pauli)
    (h : ∀ p ∈ l, p = Pauli.I ∨ p = Pauli.Z) :
    l.foldr Pauli.mul Pauli.I = Pauli.I ∨ l.foldr Pauli.mul Pauli.I = Pauli.Z := by
  induction l with
  | nil => left; rfl
  | cons a l ih =>
    have ha := h a (by simp)
    have ih' := ih (fun p hp => h p (by simp [hp]))
    simp only [List.foldr]
    rcases ha with ha | ha <;> subst ha <;> rcases ih' with hl | hl <;> rw [hl] <;> decide

/-- **Parity-counting fact for I-or-Z products**: for a list whose every
    element is in `{I, Z}`, the iterated `Pauli.mul` (foldr from `I`) equals
    `Z` iff the count of `Z` entries is odd.  Axiom-clean at
    `[propext, Quot.sound]`. -/
theorem foldr_mul_I_or_Z_eq_Z_iff_count_odd
    (l : List Pauli) (h : ∀ p ∈ l, p = Pauli.I ∨ p = Pauli.Z) :
    (l.foldr Pauli.mul Pauli.I = Pauli.Z)
      ↔ ((l.filter (· = Pauli.Z)).length % 2 = 1) := by
  induction l with
  | nil => decide
  | cons a l ih =>
    have ih' := ih (fun p hp => h p (by simp [hp]))
    have ha := h a (by simp)
    have hIorZ := foldr_mul_I_or_Z_is_I_or_Z l (fun p hp => h p (by simp [hp]))
    rcases ha with ha | ha
    · subst ha
      have hfilter : ((Pauli.I :: l).filter (· = Pauli.Z)) = l.filter (· = Pauli.Z) := by
        simp [List.filter]
      have hfoldr : (Pauli.I :: l).foldr Pauli.mul Pauli.I = l.foldr Pauli.mul Pauli.I := by
        show Pauli.mul Pauli.I (l.foldr Pauli.mul Pauli.I) = _
        cases l.foldr Pauli.mul Pauli.I <;> rfl
      rw [hfilter, hfoldr]; exact ih'
    · subst ha
      have hfilter : ((Pauli.Z :: l).filter (· = Pauli.Z))
                   = Pauli.Z :: l.filter (· = Pauli.Z) := by
        simp [List.filter]
      have hfoldr : (Pauli.Z :: l).foldr Pauli.mul Pauli.I
                  = Pauli.mul Pauli.Z (l.foldr Pauli.mul Pauli.I) := rfl
      rw [hfilter, hfoldr, List.length_cons]
      rcases hIorZ with hI | hZ
      · rw [hI]
        refine ⟨fun _ => ?_, fun _ => by decide⟩
        have hcount_ne_one : ¬ ((l.filter (· = Pauli.Z)).length % 2 = 1) := by
          intro hodd
          have := ih'.mpr hodd; rw [hI] at this
          exact absurd this (by decide)
        have hcount_even : (l.filter (· = Pauli.Z)).length % 2 = 0 := by omega
        omega
      · rw [hZ]
        refine ⟨fun hc => absurd hc (by decide), fun hodd => ?_⟩
        have hcount_odd : (l.filter (· = Pauli.Z)).length % 2 = 1 := ih'.mp hZ
        omega

/-- Auxiliary length identity: filtering by `·q = Z` after mapping `·q`
    has the same length as filtering directly by `·q = Z`. -/
private lemma length_filter_map_at_q {n : Nat} (l : List (ErrorVec n)) (q : Fin n) :
    ((l.map (fun E => E q)).filter (· = Pauli.Z)).length
      = (l.filter (fun E => E q = Pauli.Z)).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show ((a q :: (l.map (fun E => E q))).filter (· = Pauli.Z)).length
       = ((a :: l).filter (fun E => E q = Pauli.Z)).length
    by_cases h : a q = Pauli.Z
    · simp [List.filter, h, ih]
    · simp [List.filter, h, ih]

/-- **Composed**: for an `ErrorVec` list whose every element is `{I, Z}` at a
    fixed qubit `q`, `stabListProd l q = Z` iff the count of stabs marked
    `Z` at `q` is odd.  Axiom-clean at `[propext, Quot.sound]`.

    This is the foundation for `rowStepWitness_row_support`: for each
    qubit `q`, the row-support obligation becomes a Z-count parity check
    over the rowStep stabilizer list. -/
theorem stabListProd_at_eq_Z_iff_count_odd {n : Nat}
    (l : List (ErrorVec n)) (q : Fin n)
    (h : ∀ E ∈ l, E q = Pauli.I ∨ E q = Pauli.Z) :
    stabListProd l q = Pauli.Z ↔
      ((l.filter (fun E => E q = Pauli.Z)).length % 2 = 1) := by
  rw [stabListProd_apply]
  have h_map : ∀ p ∈ l.map (fun E => E q), p = Pauli.I ∨ p = Pauli.Z := by
    intro p hp
    obtain ⟨E, hE, hp_eq⟩ := List.mem_map.mp hp
    subst hp_eq; exact h E hE
  rw [foldr_mul_I_or_Z_eq_Z_iff_count_odd _ h_map, length_filter_map_at_q]

/-- Generic helper: `stabListProd` of an all-`I` list at any `q` is `I`. -/
theorem stabListProd_all_I_at_q {n : Nat} (l : List (ErrorVec n)) (q : Fin n)
    (h : ∀ E ∈ l, E q = Pauli.I) :
    stabListProd l q = Pauli.I := by
  induction l with
  | nil => unfold stabListProd ErrorVec.identity; rfl
  | cons a l ih =>
    show Pauli.mul (a q) (stabListProd l q) = Pauli.I
    rw [h a (by simp), ih (fun E hE => h E (by simp [hE]))]
    rfl

/-! ## Outside-rows case of `rowStepWitness_row_support`

Every stabilizer in `rowStepStabsRaw d i` has its support contained in
rows `{i, i+1}`:

* Bulk Z at `(i, c)`: support = rows `{i, i+1}`, cols `{c, c+1}`.
* Boundary right-Z at `b = i/2` (i even): col `d-1`, rows `{i, i+1}`.
* Boundary left-Z at `b = (i-1)/2` (i odd): col `0`, rows `{i, i+1}`.

Hence at any qubit `q` with row `q.val/d ∉ {i, i+1}`, every stab
contributes `I`, so the iterated product is `I`. -/

/-- For every raw stabilizer index `k` in `rowStepStabsRaw d i`, the
    `decodeStabPauliAt` value at any row outside `{i, i+1}` is `Pauli.I`.

    Three cases:
    * `k = rightZIdx d (i/2)` (i even): support row ∈ `{i, i+1}`.
    * `k = leftZIdx d ((i-1)/2)` (i odd): support row ∈ `{i, i+1}`.
    * `k = bulkIdx d i c` (bulk Z): support row ∈ `{i, i+1}`.

    In all cases, row outside `{i, i+1}` forces the inner `if` to take
    the `Pauli.I` branch.  Axiom-clean at `[propext, Quot.sound]`. -/
theorem decodeStabPauliAt_rowStepStabsRaw_eq_I_outside
    (d : Nat) (hd1 : 1 < d) (hodd : d % 2 = 1)
    (i : Nat) (hi : i + 1 < d)
    (k : Nat) (hk : k ∈ rowStepStabsRaw d i)
    (row col : Nat) (h_outside : row ≠ i ∧ row ≠ i + 1) :
    decodeStabPauliAt d k row col = Pauli.I := by
  have hd_ge : d ≥ 3 := by omega
  have hi_lt : i < d - 1 := by omega
  unfold rowStepStabsRaw at hk
  simp only [List.mem_cons] at hk
  rcases hk with hk_bdy | hk_bulk
  · -- Boundary case
    subst hk_bdy
    unfold rowStepBoundaryIdx
    by_cases hpar : i % 2 = 0
    · -- rightZ at b = i/2
      rw [if_pos hpar]
      unfold decodeStabPauliAt rightZIdx
      have hge : (d - 1) * (d - 1) ≤ (d - 1) * (d - 1) + (d - 1) / 2 + i / 2 := by omega
      rw [if_neg (Nat.not_lt_of_ge hge)]
      set b_outer := (d - 1) * (d - 1) + (d - 1) / 2 + i / 2 - (d - 1) * (d - 1) with hb_outer_def
      have hb_outer_eq : b_outer = (d - 1) / 2 + i / 2 := by rw [hb_outer_def]; omega
      have hnot_top : ¬ b_outer < (d - 1) / 2 := by rw [hb_outer_eq]; omega
      rw [if_neg hnot_top]
      have h_mid : b_outer < 2 * ((d - 1) / 2) := by
        rw [hb_outer_eq]
        have h_ii : i / 2 < (d - 1) / 2 := by omega
        omega
      rw [if_pos h_mid]
      have h_bb : b_outer - (d - 1) / 2 = i / 2 := by rw [hb_outer_eq]; omega
      rw [h_bb]
      have h_even : 2 * (i / 2) = i := by omega
      have h_rows : ¬ (row = 2 * (i / 2) ∨ row = 2 * (i / 2) + 1) := by
        rw [h_even]
        intro h
        rcases h with h | h
        · exact h_outside.1 h
        · exact h_outside.2 h
      have h_conj : ¬ (col = d - 1 ∧ (row = 2 * (i / 2) ∨ row = 2 * (i / 2) + 1)) :=
        fun ⟨_, h2⟩ => h_rows h2
      rw [if_neg h_conj]
    · -- leftZ at b = (i-1)/2
      rw [if_neg hpar]
      have h_odd : i % 2 = 1 := by omega
      unfold decodeStabPauliAt leftZIdx
      have hge : (d - 1) * (d - 1) ≤ (d - 1) * (d - 1) + 2 * ((d - 1) / 2) + (i - 1) / 2 := by omega
      rw [if_neg (Nat.not_lt_of_ge hge)]
      set b_outer := (d - 1) * (d - 1) + 2 * ((d - 1) / 2) + (i - 1) / 2 - (d - 1) * (d - 1) with hb_outer_def
      have hb_outer_eq : b_outer = 2 * ((d - 1) / 2) + (i - 1) / 2 := by rw [hb_outer_def]; omega
      have hnot_top : ¬ b_outer < (d - 1) / 2 := by rw [hb_outer_eq]; omega
      rw [if_neg hnot_top]
      have hnot_right : ¬ b_outer < 2 * ((d - 1) / 2) := by rw [hb_outer_eq]; omega
      rw [if_neg hnot_right]
      have h_left : b_outer < 3 * ((d - 1) / 2) := by
        rw [hb_outer_eq]
        have : (i - 1) / 2 < (d - 1) / 2 := by omega
        omega
      rw [if_pos h_left]
      have h_bb : b_outer - 2 * ((d - 1) / 2) = (i - 1) / 2 := by rw [hb_outer_eq]; omega
      rw [h_bb]
      have h_eq1 : 2 * ((i - 1) / 2) + 1 = i := by omega
      have h_eq2 : 2 * ((i - 1) / 2) + 2 = i + 1 := by omega
      have h_rows : ¬ (row = 2 * ((i - 1) / 2) + 1 ∨ row = 2 * ((i - 1) / 2) + 2) := by
        rw [h_eq1, h_eq2]
        intro h
        rcases h with h | h
        · exact h_outside.1 h
        · exact h_outside.2 h
      have h_conj : ¬ (col = 0 ∧ (row = 2 * ((i - 1) / 2) + 1 ∨ row = 2 * ((i - 1) / 2) + 2)) :=
        fun ⟨_, h2⟩ => h_rows h2
      rw [if_neg h_conj]
  · -- Bulk case: k = bulkIdx d i c
    unfold rowStepBulkList at hk_bulk
    simp only [List.mem_map, List.mem_filter, List.mem_range] at hk_bulk
    obtain ⟨c, ⟨hc_range, _hc_par⟩, hk_eq⟩ := hk_bulk
    subst hk_eq
    unfold decodeStabPauliAt
    have hlt := bulkIdx_lt_bulkCount d i c hi_lt hc_range
    rw [if_pos hlt]
    obtain ⟨hdiv, hmod⟩ := bulkIdx_div_mod d i c hd1 hc_range
    rw [hdiv, hmod]
    have h_rows : ¬ (row = i ∨ row = i + 1) := by
      intro h
      rcases h with h | h
      · exact h_outside.1 h
      · exact h_outside.2 h
    have h_conj : ¬ ((row = i ∨ row = i + 1) ∧ (col = c ∨ col = c + 1)) :=
      fun ⟨h1, _⟩ => h_rows h1
    rw [if_neg h_conj]

/-- **Outside-rows case of `rowStepWitness_row_support`**: for any qubit
    `q` whose row index is NOT in `{i, i+1}`, the row-step witness
    evaluates to `Pauli.I`.

    Proof: every stab in `rowStepStabsRaw d i` contributes `I` at such a
    qubit (by `decodeStabPauliAt_rowStepStabsRaw_eq_I_outside`), so the
    iterated product is `I` (by `stabListProd_all_I_at_q`).

    Axiom-clean at `[propext, Quot.sound]`. -/
theorem rowStepWitness_eq_I_outside_rows
    (d : Nat) (hd1 : 1 < d) (hodd : d % 2 = 1)
    (i : Nat) (hi : i + 1 < d)
    (q : Fin (d * d)) (h_outside : q.val / d ≠ i ∧ q.val / d ≠ i + 1) :
    rowStepWitness d hd1 hodd i hi q = Pauli.I := by
  unfold rowStepWitness
  apply stabListProd_all_I_at_q
  intro E hE
  obtain ⟨⟨k, hk⟩, _, hE_eq⟩ := List.mem_map.mp hE
  subst hE_eq
  exact decodeStabPauliAt_rowStepStabsRaw_eq_I_outside d hd1 hodd i hi k hk _ _ h_outside

/-! ## Boundary-stab `Z`-values at the corner qubits of rows `{i, i+1}`

These four lemmas isolate the EXACT (row, col) coordinates at which the
boundary stab in `rowStepStabsRaw d i` returns `Pauli.Z`:

* **i even**, boundary = rightZ at b=i/2: returns `Z` at `(i, d-1)` and
  `(i+1, d-1)`.
* **i odd**, boundary = leftZ at b=(i-1)/2: returns `Z` at `(i, 0)` and
  `(i+1, 0)`.

The non-Z corners are covered by the outside-rows lemma; here we pin
down the IN-row, IN-support corners. -/

/-- For `i` even, the boundary stab `rightZ` returns `Z` at `(i, d-1)`. -/
theorem boundary_rightZ_at_row_i_col_dm1
    (d : Nat) (hd1 : 1 < d) (hodd : d % 2 = 1)
    (i : Nat) (hi : i + 1 < d) (hpar : i % 2 = 0) :
    decodeStabPauliAt d (rowStepBoundaryIdx d i) i (d - 1) = Pauli.Z := by
  unfold rowStepBoundaryIdx
  rw [if_pos hpar]
  unfold decodeStabPauliAt rightZIdx
  have hd_ge : d ≥ 3 := by omega
  have hge : (d - 1) * (d - 1) ≤ (d - 1) * (d - 1) + (d - 1) / 2 + i / 2 := by omega
  rw [if_neg (Nat.not_lt_of_ge hge)]
  set b_outer := (d - 1) * (d - 1) + (d - 1) / 2 + i / 2 - (d - 1) * (d - 1) with hb_def
  have hb_eq : b_outer = (d - 1) / 2 + i / 2 := by rw [hb_def]; omega
  have hnot_top : ¬ b_outer < (d - 1) / 2 := by rw [hb_eq]; omega
  rw [if_neg hnot_top]
  have h_mid : b_outer < 2 * ((d - 1) / 2) := by
    rw [hb_eq]
    have hii : i / 2 < (d - 1) / 2 := by omega
    omega
  rw [if_pos h_mid]
  have h_bb : b_outer - (d - 1) / 2 = i / 2 := by rw [hb_eq]; omega
  rw [h_bb]
  have h_cond : (d - 1) = d - 1 ∧ (i = 2 * (i / 2) ∨ i = 2 * (i / 2) + 1) := by
    refine ⟨rfl, Or.inl ?_⟩; omega
  rw [if_pos h_cond]

/-- For `i` even, the boundary stab `rightZ` returns `Z` at `(i+1, d-1)`. -/
theorem boundary_rightZ_at_row_ip1_col_dm1
    (d : Nat) (hd1 : 1 < d) (hodd : d % 2 = 1)
    (i : Nat) (hi : i + 1 < d) (hpar : i % 2 = 0) :
    decodeStabPauliAt d (rowStepBoundaryIdx d i) (i + 1) (d - 1) = Pauli.Z := by
  unfold rowStepBoundaryIdx
  rw [if_pos hpar]
  unfold decodeStabPauliAt rightZIdx
  have hd_ge : d ≥ 3 := by omega
  have hge : (d - 1) * (d - 1) ≤ (d - 1) * (d - 1) + (d - 1) / 2 + i / 2 := by omega
  rw [if_neg (Nat.not_lt_of_ge hge)]
  set b_outer := (d - 1) * (d - 1) + (d - 1) / 2 + i / 2 - (d - 1) * (d - 1) with hb_def
  have hb_eq : b_outer = (d - 1) / 2 + i / 2 := by rw [hb_def]; omega
  have hnot_top : ¬ b_outer < (d - 1) / 2 := by rw [hb_eq]; omega
  rw [if_neg hnot_top]
  have h_mid : b_outer < 2 * ((d - 1) / 2) := by
    rw [hb_eq]
    have hii : i / 2 < (d - 1) / 2 := by omega
    omega
  rw [if_pos h_mid]
  have h_bb : b_outer - (d - 1) / 2 = i / 2 := by rw [hb_eq]; omega
  rw [h_bb]
  have h_cond : (d - 1) = d - 1 ∧ ((i + 1) = 2 * (i / 2) ∨ (i + 1) = 2 * (i / 2) + 1) := by
    refine ⟨rfl, Or.inr ?_⟩; omega
  rw [if_pos h_cond]

/-- For `i` odd, the boundary stab `leftZ` returns `Z` at `(i, 0)`. -/
theorem boundary_leftZ_at_row_i_col_0
    (d : Nat) (hd1 : 1 < d) (hodd : d % 2 = 1)
    (i : Nat) (hi : i + 1 < d) (hpar : i % 2 = 1) :
    decodeStabPauliAt d (rowStepBoundaryIdx d i) i 0 = Pauli.Z := by
  unfold rowStepBoundaryIdx
  have hpar_neg : ¬ (i % 2 = 0) := by omega
  rw [if_neg hpar_neg]
  unfold decodeStabPauliAt leftZIdx
  have hd_ge : d ≥ 3 := by omega
  have hge : (d - 1) * (d - 1) ≤ (d - 1) * (d - 1) + 2 * ((d - 1) / 2) + (i - 1) / 2 := by omega
  rw [if_neg (Nat.not_lt_of_ge hge)]
  set b_outer := (d - 1) * (d - 1) + 2 * ((d - 1) / 2) + (i - 1) / 2 - (d - 1) * (d - 1) with hb_def
  have hb_eq : b_outer = 2 * ((d - 1) / 2) + (i - 1) / 2 := by rw [hb_def]; omega
  have hnot_top : ¬ b_outer < (d - 1) / 2 := by rw [hb_eq]; omega
  rw [if_neg hnot_top]
  have hnot_right : ¬ b_outer < 2 * ((d - 1) / 2) := by rw [hb_eq]; omega
  rw [if_neg hnot_right]
  have h_left : b_outer < 3 * ((d - 1) / 2) := by
    rw [hb_eq]
    have : (i - 1) / 2 < (d - 1) / 2 := by omega
    omega
  rw [if_pos h_left]
  have h_bb : b_outer - 2 * ((d - 1) / 2) = (i - 1) / 2 := by rw [hb_eq]; omega
  rw [h_bb]
  have h_cond : (0 : Nat) = 0 ∧ (i = 2 * ((i - 1) / 2) + 1 ∨ i = 2 * ((i - 1) / 2) + 2) := by
    refine ⟨rfl, Or.inl ?_⟩; omega
  rw [if_pos h_cond]

/-- For `i` odd, the boundary stab `leftZ` returns `Z` at `(i+1, 0)`. -/
theorem boundary_leftZ_at_row_ip1_col_0
    (d : Nat) (hd1 : 1 < d) (hodd : d % 2 = 1)
    (i : Nat) (hi : i + 1 < d) (hpar : i % 2 = 1) :
    decodeStabPauliAt d (rowStepBoundaryIdx d i) (i + 1) 0 = Pauli.Z := by
  unfold rowStepBoundaryIdx
  have hpar_neg : ¬ (i % 2 = 0) := by omega
  rw [if_neg hpar_neg]
  unfold decodeStabPauliAt leftZIdx
  have hd_ge : d ≥ 3 := by omega
  have hge : (d - 1) * (d - 1) ≤ (d - 1) * (d - 1) + 2 * ((d - 1) / 2) + (i - 1) / 2 := by omega
  rw [if_neg (Nat.not_lt_of_ge hge)]
  set b_outer := (d - 1) * (d - 1) + 2 * ((d - 1) / 2) + (i - 1) / 2 - (d - 1) * (d - 1) with hb_def
  have hb_eq : b_outer = 2 * ((d - 1) / 2) + (i - 1) / 2 := by rw [hb_def]; omega
  have hnot_top : ¬ b_outer < (d - 1) / 2 := by rw [hb_eq]; omega
  rw [if_neg hnot_top]
  have hnot_right : ¬ b_outer < 2 * ((d - 1) / 2) := by rw [hb_eq]; omega
  rw [if_neg hnot_right]
  have h_left : b_outer < 3 * ((d - 1) / 2) := by
    rw [hb_eq]
    have : (i - 1) / 2 < (d - 1) / 2 := by omega
    omega
  rw [if_pos h_left]
  have h_bb : b_outer - 2 * ((d - 1) / 2) = (i - 1) / 2 := by rw [hb_eq]; omega
  rw [h_bb]
  have h_cond : (0 : Nat) = 0 ∧ ((i + 1) = 2 * ((i - 1) / 2) + 1 ∨ (i + 1) = 2 * ((i - 1) / 2) + 2) := by
    refine ⟨rfl, Or.inr ?_⟩; omega
  rw [if_pos h_cond]

/-! ## Bulk-Z value lemmas (4 corners of the bulk plaquette)

For a bulk Z stab at `(i, c)` with `c < d - 1` and `(i + c) % 2 = 0`
(so it ends up classified as `bulkZ`), `decode` returns `Z` at the 4
corner qubits of the 2×2 plaquette covering rows `{i, i+1}` and cols
`{c, c+1}`, and `I` elsewhere. -/

/-- Bulk-Z corner: `(i, c)` (top-left). -/
theorem bulkZ_at_row_i_col_c
    (d : Nat) (hd1 : 1 < d) (hodd : d % 2 = 1)
    (i : Nat) (hi : i + 1 < d) (c : Nat) (hc : c < d - 1)
    (hpar : (i + c) % 2 = 0) :
    decodeStabPauliAt d (bulkIdx d i c) i c = Pauli.Z := by
  unfold decodeStabPauliAt
  have hi_lt : i < d - 1 := by omega
  have hlt := bulkIdx_lt_bulkCount d i c hi_lt hc
  rw [if_pos hlt]
  obtain ⟨hdiv, hmod⟩ := bulkIdx_div_mod d i c hd1 hc
  rw [hdiv, hmod]
  have h_cond : (i = i ∨ i = i + 1) ∧ (c = c ∨ c = c + 1) :=
    ⟨Or.inl rfl, Or.inl rfl⟩
  rw [if_pos h_cond, if_pos hpar]

/-- Bulk-Z corner: `(i, c+1)` (top-right). -/
theorem bulkZ_at_row_i_col_cp1
    (d : Nat) (hd1 : 1 < d) (hodd : d % 2 = 1)
    (i : Nat) (hi : i + 1 < d) (c : Nat) (hc : c < d - 1)
    (hpar : (i + c) % 2 = 0) :
    decodeStabPauliAt d (bulkIdx d i c) i (c + 1) = Pauli.Z := by
  unfold decodeStabPauliAt
  have hi_lt : i < d - 1 := by omega
  have hlt := bulkIdx_lt_bulkCount d i c hi_lt hc
  rw [if_pos hlt]
  obtain ⟨hdiv, hmod⟩ := bulkIdx_div_mod d i c hd1 hc
  rw [hdiv, hmod]
  have h_cond : (i = i ∨ i = i + 1) ∧ ((c + 1) = c ∨ (c + 1) = c + 1) :=
    ⟨Or.inl rfl, Or.inr rfl⟩
  rw [if_pos h_cond, if_pos hpar]

/-- Bulk-Z corner: `(i+1, c)` (bottom-left). -/
theorem bulkZ_at_row_ip1_col_c
    (d : Nat) (hd1 : 1 < d) (hodd : d % 2 = 1)
    (i : Nat) (hi : i + 1 < d) (c : Nat) (hc : c < d - 1)
    (hpar : (i + c) % 2 = 0) :
    decodeStabPauliAt d (bulkIdx d i c) (i + 1) c = Pauli.Z := by
  unfold decodeStabPauliAt
  have hi_lt : i < d - 1 := by omega
  have hlt := bulkIdx_lt_bulkCount d i c hi_lt hc
  rw [if_pos hlt]
  obtain ⟨hdiv, hmod⟩ := bulkIdx_div_mod d i c hd1 hc
  rw [hdiv, hmod]
  have h_cond : ((i + 1) = i ∨ (i + 1) = i + 1) ∧ (c = c ∨ c = c + 1) :=
    ⟨Or.inr rfl, Or.inl rfl⟩
  rw [if_pos h_cond, if_pos hpar]

/-- Bulk-Z corner: `(i+1, c+1)` (bottom-right). -/
theorem bulkZ_at_row_ip1_col_cp1
    (d : Nat) (hd1 : 1 < d) (hodd : d % 2 = 1)
    (i : Nat) (hi : i + 1 < d) (c : Nat) (hc : c < d - 1)
    (hpar : (i + c) % 2 = 0) :
    decodeStabPauliAt d (bulkIdx d i c) (i + 1) (c + 1) = Pauli.Z := by
  unfold decodeStabPauliAt
  have hi_lt : i < d - 1 := by omega
  have hlt := bulkIdx_lt_bulkCount d i c hi_lt hc
  rw [if_pos hlt]
  obtain ⟨hdiv, hmod⟩ := bulkIdx_div_mod d i c hd1 hc
  rw [hdiv, hmod]
  have h_cond : ((i + 1) = i ∨ (i + 1) = i + 1) ∧ ((c + 1) = c ∨ (c + 1) = c + 1) :=
    ⟨Or.inr rfl, Or.inr rfl⟩
  rw [if_pos h_cond, if_pos hpar]

/-- Bulk-Z off-corner: row ∈ `{i, i+1}` but col ∉ `{c, c+1}` → `I`. -/
theorem bulkZ_at_inside_row_outside_col
    (d : Nat) (hd1 : 1 < d) (hodd : d % 2 = 1)
    (i : Nat) (hi : i + 1 < d) (c : Nat) (hc : c < d - 1)
    (row col : Nat) (_h_row : row = i ∨ row = i + 1)
    (h_col_out : col ≠ c ∧ col ≠ c + 1) :
    decodeStabPauliAt d (bulkIdx d i c) row col = Pauli.I := by
  unfold decodeStabPauliAt
  have hi_lt : i < d - 1 := by omega
  have hlt := bulkIdx_lt_bulkCount d i c hi_lt hc
  rw [if_pos hlt]
  obtain ⟨hdiv, hmod⟩ := bulkIdx_div_mod d i c hd1 hc
  rw [hdiv, hmod]
  have h_cond_neg : ¬ ((row = i ∨ row = i + 1) ∧ (col = c ∨ col = c + 1)) := by
    intro ⟨_, hcol⟩
    rcases hcol with hcol | hcol
    · exact h_col_out.1 hcol
    · exact h_col_out.2 hcol
  rw [if_neg h_cond_neg]

/-- Boundary off-col (i even): rightZ at row ∈ `{i, i+1}`, col ≠ `d-1` → `I`. -/
theorem boundary_rightZ_off_col
    (d : Nat) (hd1 : 1 < d) (hodd : d % 2 = 1)
    (i : Nat) (hi : i + 1 < d) (hpar : i % 2 = 0)
    (row col : Nat) (_h_row : row = i ∨ row = i + 1) (h_col_ne : col ≠ d - 1) :
    decodeStabPauliAt d (rowStepBoundaryIdx d i) row col = Pauli.I := by
  unfold rowStepBoundaryIdx
  rw [if_pos hpar]
  unfold decodeStabPauliAt rightZIdx
  have hd_ge : d ≥ 3 := by omega
  have hge : (d - 1) * (d - 1) ≤ (d - 1) * (d - 1) + (d - 1) / 2 + i / 2 := by omega
  rw [if_neg (Nat.not_lt_of_ge hge)]
  set b_outer := (d - 1) * (d - 1) + (d - 1) / 2 + i / 2 - (d - 1) * (d - 1) with hb_def
  have hb_eq : b_outer = (d - 1) / 2 + i / 2 := by rw [hb_def]; omega
  have hnot_top : ¬ b_outer < (d - 1) / 2 := by rw [hb_eq]; omega
  rw [if_neg hnot_top]
  have h_mid : b_outer < 2 * ((d - 1) / 2) := by
    rw [hb_eq]
    have hii : i / 2 < (d - 1) / 2 := by omega
    omega
  rw [if_pos h_mid]
  have h_bb : b_outer - (d - 1) / 2 = i / 2 := by rw [hb_eq]; omega
  rw [h_bb]
  have h_cond_neg : ¬ (col = d - 1 ∧ (row = 2 * (i / 2) ∨ row = 2 * (i / 2) + 1)) :=
    fun ⟨hcol, _⟩ => h_col_ne hcol
  rw [if_neg h_cond_neg]

/-- Boundary off-col (i odd): leftZ at row ∈ `{i, i+1}`, col ≠ `0` → `I`. -/
theorem boundary_leftZ_off_col
    (d : Nat) (hd1 : 1 < d) (hodd : d % 2 = 1)
    (i : Nat) (hi : i + 1 < d) (hpar : i % 2 = 1)
    (row col : Nat) (_h_row : row = i ∨ row = i + 1) (h_col_ne : col ≠ 0) :
    decodeStabPauliAt d (rowStepBoundaryIdx d i) row col = Pauli.I := by
  unfold rowStepBoundaryIdx
  have hpar_neg : ¬ (i % 2 = 0) := by omega
  rw [if_neg hpar_neg]
  unfold decodeStabPauliAt leftZIdx
  have hd_ge : d ≥ 3 := by omega
  have hge : (d - 1) * (d - 1) ≤ (d - 1) * (d - 1) + 2 * ((d - 1) / 2) + (i - 1) / 2 := by omega
  rw [if_neg (Nat.not_lt_of_ge hge)]
  set b_outer := (d - 1) * (d - 1) + 2 * ((d - 1) / 2) + (i - 1) / 2 - (d - 1) * (d - 1) with hb_def
  have hb_eq : b_outer = 2 * ((d - 1) / 2) + (i - 1) / 2 := by rw [hb_def]; omega
  have hnot_top : ¬ b_outer < (d - 1) / 2 := by rw [hb_eq]; omega
  rw [if_neg hnot_top]
  have hnot_right : ¬ b_outer < 2 * ((d - 1) / 2) := by rw [hb_eq]; omega
  rw [if_neg hnot_right]
  have h_left : b_outer < 3 * ((d - 1) / 2) := by
    rw [hb_eq]
    have : (i - 1) / 2 < (d - 1) / 2 := by omega
    omega
  rw [if_pos h_left]
  have h_bb : b_outer - 2 * ((d - 1) / 2) = (i - 1) / 2 := by rw [hb_eq]; omega
  rw [h_bb]
  have h_cond_neg : ¬ (col = 0 ∧ (row = 2 * ((i - 1) / 2) + 1 ∨ row = 2 * ((i - 1) / 2) + 2)) :=
    fun ⟨hcol, _⟩ => h_col_ne hcol
  rw [if_neg h_cond_neg]

/-! ## Inside-row Z-value iff characterizations

These two lemmas crystallize the previous per-corner facts into clean
`↔` statements: at a qubit `(row, col)` with `row ∈ {i, i+1}`, when does
a given stab in `rowStepStabsRaw d i` contribute `Z`?

* Bulk Z at `(i, c)`: contributes `Z` iff `col ∈ {c, c+1}`.
* Boundary: contributes `Z` iff `(i even ∧ col = d-1) ∨ (i odd ∧ col = 0)`.

These give the COUNTING argument its clean shape: at fixed `(row, col)`
with row inside, count Z-contributions = (boundary indicator) + (bulk
indicator count over c). -/

/-- For row ∈ `{i, i+1}` and any bulk Z stab (parity-filtered), the
    decode equals `Z` iff `col ∈ {c, c+1}`. -/
theorem bulkIdx_decode_inside_row_eq_Z_iff
    (d : Nat) (hd1 : 1 < d) (hodd : d % 2 = 1)
    (i : Nat) (hi : i + 1 < d)
    (c : Nat) (hc : c < d - 1) (hpar : (i + c) % 2 = 0)
    (row col : Nat) (h_row : row = i ∨ row = i + 1) :
    decodeStabPauliAt d (bulkIdx d i c) row col = Pauli.Z ↔ col = c ∨ col = c + 1 := by
  by_cases hcol : col = c ∨ col = c + 1
  · refine ⟨fun _ => hcol, fun _ => ?_⟩
    rcases h_row with h_row | h_row
    · rcases hcol with hcol | hcol
      · rw [h_row, hcol]; exact bulkZ_at_row_i_col_c d hd1 hodd i hi c hc hpar
      · rw [h_row, hcol]; exact bulkZ_at_row_i_col_cp1 d hd1 hodd i hi c hc hpar
    · rcases hcol with hcol | hcol
      · rw [h_row, hcol]; exact bulkZ_at_row_ip1_col_c d hd1 hodd i hi c hc hpar
      · rw [h_row, hcol]; exact bulkZ_at_row_ip1_col_cp1 d hd1 hodd i hi c hc hpar
  · refine ⟨fun h_eq => ?_, fun hc' => absurd hc' hcol⟩
    have h_I : decodeStabPauliAt d (bulkIdx d i c) row col = Pauli.I := by
      apply bulkZ_at_inside_row_outside_col d hd1 hodd i hi c hc row col h_row
      refine ⟨fun h => hcol (Or.inl h), fun h => hcol (Or.inr h)⟩
    rw [h_I] at h_eq; exact absurd h_eq (by decide)

/-! ### Combinatorial helpers for the bulk Z-count

These lemmas enable the parity-counting argument on
`rowStepBulkList d i`:

* `mem_rowStepBulkList_iff` — structural unfolding of list membership.
* `parity_exactly_one_of_consecutive` — exactly one of `(i+col) % 2 = 0`
  and `(i+(col-1)) % 2 = 0` holds (for `col ≥ 1`).
* `rowStepBulkList_consecutive_unique` — applied to bulk indices:
  exactly one of `bulkIdx d i col` and `bulkIdx d i (col-1)` is in
  `rowStepBulkList d i` (when `1 ≤ col < d-1`).

These together pin down: for `col` in the middle range, the bulk
contribution at `(row inside, col)` is exactly one Z. -/

/-- Structural unfolding: `k ∈ rowStepBulkList d i` iff there exists a
    valid plaquette column `c` with the right parity, giving
    `k = bulkIdx d i c`. -/
theorem mem_rowStepBulkList_iff
    (d i k : Nat) :
    k ∈ rowStepBulkList d i ↔
      ∃ c, c < d - 1 ∧ (i + c) % 2 = 0 ∧ k = bulkIdx d i c := by
  unfold rowStepBulkList
  simp only [List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · intro ⟨c, ⟨hc_range, hc_par⟩, hk_eq⟩
    exact ⟨c, hc_range, hc_par, hk_eq.symm⟩
  · intro ⟨c, hc_range, hc_par, hk_eq⟩
    exact ⟨c, ⟨hc_range, hc_par⟩, hk_eq.symm⟩

/-- Parity-flip fact: for `col ≥ 1`, exactly one of `(i + col)` and
    `(i + (col - 1))` is even. -/
theorem parity_exactly_one_of_consecutive
    (i col : Nat) (hcol : col ≥ 1) :
    ((i + col) % 2 = 0 ∧ (i + (col - 1)) % 2 ≠ 0) ∨
    ((i + col) % 2 ≠ 0 ∧ (i + (col - 1)) % 2 = 0) := by
  by_cases h : (i + col) % 2 = 0
  · left; exact ⟨h, by omega⟩
  · right; exact ⟨h, by omega⟩

/-- For middle columns `1 ≤ col < d-1`, exactly one of the two adjacent
    bulk-column candidates `c = col` and `c = col - 1` is in
    `rowStepBulkList d i`.  This is the unique-bulk-Z-contributor fact
    for the middle case. -/
theorem rowStepBulkList_consecutive_unique
    (d i col : Nat) (hcol1 : col ≥ 1) (hcol2 : col < d - 1) :
    (bulkIdx d i col ∈ rowStepBulkList d i ∧
     bulkIdx d i (col - 1) ∉ rowStepBulkList d i) ∨
    (bulkIdx d i col ∉ rowStepBulkList d i ∧
     bulkIdx d i (col - 1) ∈ rowStepBulkList d i) := by
  rcases parity_exactly_one_of_consecutive i col hcol1
    with ⟨h_col, h_colm1⟩ | ⟨h_col, h_colm1⟩
  · left
    refine ⟨?_, ?_⟩
    · rw [mem_rowStepBulkList_iff]
      exact ⟨col, hcol2, h_col, rfl⟩
    · intro hmem
      rw [mem_rowStepBulkList_iff] at hmem
      obtain ⟨c, _hc_lt, hc_par, hc_eq⟩ := hmem
      have hc_val : c = col - 1 := by
        unfold bulkIdx at hc_eq; omega
      rw [hc_val] at hc_par
      exact h_colm1 hc_par
  · right
    refine ⟨?_, ?_⟩
    · intro hmem
      rw [mem_rowStepBulkList_iff] at hmem
      obtain ⟨c, _hc_lt, hc_par, hc_eq⟩ := hmem
      have hc_val : c = col := by
        unfold bulkIdx at hc_eq; omega
      rw [hc_val] at hc_par
      exact h_col hc_par
    · rw [mem_rowStepBulkList_iff]
      refine ⟨col - 1, ?_, h_colm1, rfl⟩; omega

/-! ### Bridge: `rowStepWitness` value in terms of raw-Nat-list filter count

The `rowStepWitness` definition goes through `(rowStepStabsRaw d i).attach.map`,
which is awkward to reason about directly.  This pair of lemmas converts
the `rowStepWitness q` value (an `ErrorVec`-list product) into a `List Nat`
filter-count parity check, which is much easier to manipulate. -/

/-- Auxiliary length identity used by `rowStepWitness_eq_Z_iff_count_odd`. -/
private theorem map_filter_length_decode
    (d : Nat) (q : Fin (d * d)) (l : List Nat) :
    ((l.map (fun k => decodeStabPauliAt d k (q.val / d) (q.val % d))).filter
      (· = Pauli.Z)).length =
    (l.filter (fun k => decodeStabPauliAt d k (q.val / d) (q.val % d) = Pauli.Z)).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : decodeStabPauliAt d a (q.val / d) (q.val % d) = Pauli.Z
    · simp [List.filter, h, ih]
    · simp [List.filter, h, ih]

/-- **Direct evaluation of `rowStepWitness` at a qubit `q`**: equals the
    `Pauli.mul` foldr over the list of decoded values, one per raw index in
    `rowStepStabsRaw d i`.

    Bridges the `attach.map (mkSurfaceStabilizers ⟨k, _⟩)` formulation with
    plain `map decodeStabPauliAt` over the Nat list, exploiting
    definitional equality `mkSurfaceStabilizers d hd ⟨k, hk⟩ q =
    decodeStabPauliAt d k (q.val/d) (q.val%d)`. -/
theorem rowStepWitness_apply
    (d : Nat) (hd1 : 1 < d) (hodd : d % 2 = 1)
    (i : Nat) (hi : i + 1 < d) (q : Fin (d * d)) :
    rowStepWitness d hd1 hodd i hi q =
      ((rowStepStabsRaw d i).map
        (fun k => decodeStabPauliAt d k (q.val / d) (q.val % d))).foldr Pauli.mul Pauli.I := by
  unfold rowStepWitness
  rw [stabListProd_apply]
  congr 1
  rw [List.map_map]
  show (rowStepStabsRaw d i).attach.map (fun x : { k // k ∈ rowStepStabsRaw d i } =>
    decodeStabPauliAt d x.val (q.val / d) (q.val % d)) = _
  induction (rowStepStabsRaw d i) <;> simp [*]

/-- **The pivotal count-parity theorem**: `rowStepWitness d hd1 hodd i hi q = Z`
    iff the number of raw stabilizer indices in `rowStepStabsRaw d i` whose
    decode at `(q.val / d, q.val % d)` is `Z` is odd.

    Combines `rowStepWitness_apply` with the parity-counting fact
    `foldr_mul_I_or_Z_eq_Z_iff_count_odd` (every decoded value is `{I, Z}`
    since every stab in `rowStepStabsRaw d i` has `stabType = Z` by
    `stabType_rowStepStabsRaw`). -/
theorem rowStepWitness_eq_Z_iff_count_odd
    (d : Nat) (hd1 : 1 < d) (hodd : d % 2 = 1)
    (i : Nat) (hi : i + 1 < d) (q : Fin (d * d)) :
    rowStepWitness d hd1 hodd i hi q = Pauli.Z ↔
      ((rowStepStabsRaw d i).filter
        (fun k => decodeStabPauliAt d k (q.val / d) (q.val % d) = Pauli.Z)).length % 2 = 1 := by
  rw [rowStepWitness_apply]
  have h_IZ : ∀ p ∈ (rowStepStabsRaw d i).map
                (fun k => decodeStabPauliAt d k (q.val / d) (q.val % d)),
              p = Pauli.I ∨ p = Pauli.Z := by
    intro p hp
    obtain ⟨k, hk, hp_eq⟩ := List.mem_map.mp hp
    subst hp_eq
    have h_kind := stabType_rowStepStabsRaw d hd1 hodd i hi k hk
    rcases decode_I_or_stabType_pub d k (q.val / d) (q.val % d) with h | h
    · left; exact h
    · right; rw [h, h_kind]
  rw [foldr_mul_I_or_Z_eq_Z_iff_count_odd _ h_IZ, map_filter_length_decode]

/-! ### Unique-candidate construction for the middle-col bulk count

For middle col (1 ≤ col < d-1) and any parity of `i`, exactly one of
`{col-1, col}` satisfies `(i+c) % 2 = 0` (by `parity_exactly_one_of_consecutive`).
That unique c is captured by `uniqueC i col`, which lies in
`[0, d-1)` and is the only c satisfying both predicates `(i+c)%2 = 0`
and `(col = c ∨ col = c+1)`.

This yields the middle-col bulk count = 1 cleanly. -/

/-- The unique column index satisfying `(i+c) % 2 = 0 ∧ (col = c ∨ col = c+1)`
    for middle col: if `(i+col) % 2 = 0`, it's `col`; else it's `col - 1`. -/
def uniqueC (i col : Nat) : Nat := if (i + col) % 2 = 0 then col else col - 1

/-- `uniqueC i col < d - 1` for middle col `1 ≤ col < d-1`. -/
theorem uniqueC_lt_dm1 (d i col : Nat) (hcol1 : col ≥ 1) (hcol2 : col < d - 1) :
    uniqueC i col < d - 1 := by
  unfold uniqueC; split_ifs <;> omega

/-- For middle col (col ≥ 1), the predicate `(i+c) % 2 = 0 ∧ (col = c ∨ col = c+1)`
    holds iff `c = uniqueC i col`.

    The two col-cond candidates are `c = col` (matches `col = c`) and
    `c = col - 1` (matches `col = c+1`).  Of these, exactly one passes
    parity; the choice is captured by `uniqueC`. -/
theorem pred_iff_eq_uniqueC
    (i col : Nat) (hcol : col ≥ 1) (c : Nat) :
    decide ((i + c) % 2 = 0 ∧ (col = c ∨ col = c + 1)) = decide (c = uniqueC i col) := by
  apply Bool.eq_iff_iff.mpr
  unfold uniqueC
  by_cases hpar : (i + col) % 2 = 0
  · simp only [if_pos hpar, decide_eq_true_eq]
    refine ⟨fun ⟨h_par_c, h_col⟩ => ?_, fun h_c => ?_⟩
    · rcases h_col with h_col | h_col
      · exact h_col.symm
      · exfalso
        have h_c_val : c = col - 1 := by omega
        rw [h_c_val] at h_par_c; omega
    · subst h_c; exact ⟨hpar, Or.inl rfl⟩
  · simp only [if_neg hpar, decide_eq_true_eq]
    have hpar1 : (i + col) % 2 = 1 := by omega
    refine ⟨fun ⟨h_par_c, h_col⟩ => ?_, fun h_c => ?_⟩
    · rcases h_col with h_col | h_col
      · exfalso; rw [← h_col] at h_par_c; omega
      · omega
    · subst h_c
      refine ⟨by omega, Or.inr ?_⟩; omega

/-- Range filter length = 1 for middle col: the count of `c ∈ [0, d-1)`
    satisfying `(i+c) % 2 = 0 ∧ (col = c ∨ col = c+1)` is exactly 1. -/
theorem range_filter_pred_length_eq_one_middle
    (d i col : Nat) (hcol1 : col ≥ 1) (hcol2 : col < d - 1) :
    ((List.range (d - 1)).filter
      (fun c => decide ((i + c) % 2 = 0 ∧ (col = c ∨ col = c + 1)))).length = 1 := by
  have h_filter_eq : (List.range (d - 1)).filter
      (fun c => decide ((i + c) % 2 = 0 ∧ (col = c ∨ col = c + 1))) =
    (List.range (d - 1)).filter (fun c => decide (c = uniqueC i col)) :=
    List.filter_congr (fun c _ => pred_iff_eq_uniqueC i col hcol1 c)
  rw [h_filter_eq]
  have h_uniqueC_lt : uniqueC i col < d - 1 := uniqueC_lt_dm1 d i col hcol1 hcol2
  rw [show ((List.range (d - 1)).filter (fun c => decide (c = uniqueC i col))).length =
        (List.range (d - 1)).count (uniqueC i col) from by
    simp [List.count, List.countP_eq_length_filter]; rfl,
      List.count_range, if_pos h_uniqueC_lt]

/-- Helper for the middle-col bulk count: the filter on the 2-element list
    `[col-1, col]` by parity has length exactly 1.

    Used as the terminal step of the middle-col counting argument after
    reducing `(List.range (d-1)).filter (col-cond ∧ parity)` to
    `[col-1, col].filter parity`.  (Not used by the current proof path,
    but kept as an alternative tactic.) -/
theorem two_elem_filter_parity_length_eq_one
    (i col : Nat) (hcol : col ≥ 1) :
    ([col - 1, col].filter (fun c => decide ((i + c) % 2 = 0))).length = 1 := by
  rcases parity_exactly_one_of_consecutive i col hcol with ⟨h_col, h_colm1⟩ | ⟨h_col, h_colm1⟩
  · have h1 : decide ((i + col) % 2 = 0) = true := decide_eq_true h_col
    have h2 : decide ((i + (col - 1)) % 2 = 0) = false := decide_eq_false h_colm1
    simp [List.filter, h1, h2]
  · have h1 : decide ((i + col) % 2 = 0) = false := decide_eq_false h_col
    have h2 : decide ((i + (col - 1)) % 2 = 0) = true := decide_eq_true h_colm1
    simp [List.filter, h1, h2]

/-- Bridge: the bulk filter on "decode at (row, col) = Z" reduces to a
    pure range-filter on `(i+c)%2 = 0 ∧ (col = c ∨ col = c+1)`.

    Eliminates `bulkIdx`/`decodeStabPauliAt` interlocks and turns the bulk
    counting into a clean range-counting argument. -/
theorem rowStepBulkList_filter_decode_Z_eq
    (d : Nat) (hd1 : 1 < d) (hodd : d % 2 = 1)
    (i : Nat) (hi : i + 1 < d)
    (row col : Nat) (h_row : row = i ∨ row = i + 1) :
    ((rowStepBulkList d i).filter
      (fun k => decodeStabPauliAt d k row col = Pauli.Z)).length =
    ((List.range (d - 1)).filter
      (fun c => decide ((i + c) % 2 = 0 ∧ (col = c ∨ col = c + 1)))).length := by
  unfold rowStepBulkList
  rw [List.filter_map, List.length_map, List.filter_filter]
  congr 1
  apply List.filter_congr
  intro c hc
  simp only [List.mem_range] at hc
  by_cases hpar : (i + c) % 2 = 0
  · have h_iff := bulkIdx_decode_inside_row_eq_Z_iff d hd1 hodd i hi c hc hpar row col h_row
    by_cases h_col : col = c ∨ col = c + 1
    · have h_decode : decodeStabPauliAt d (bulkIdx d i c) row col = Pauli.Z := h_iff.mpr h_col
      simp [hpar, h_decode, h_col]
    · have h_decode : decodeStabPauliAt d (bulkIdx d i c) row col ≠ Pauli.Z :=
        fun h => h_col (h_iff.mp h)
      simp [hpar, h_decode, h_col]
  · simp [hpar]

/-- Edge col = 0: the range filter for `(i+c)%2 = 0 ∧ (0 = c ∨ 0 = c+1)` has length 1 if `i` is even, 0 otherwise.

    Only candidate is c = 0 (since `0 = c+1` is impossible in `Nat`); c = 0 in range
    requires `(i+0)%2 = 0`, i.e., `i` even. -/
theorem range_filter_col_0_length
    (d i : Nat) (hd1 : 1 < d) :
    ((List.range (d - 1)).filter
      (fun c => decide ((i + c) % 2 = 0 ∧ ((0 : Nat) = c ∨ (0 : Nat) = c + 1)))).length =
      if i % 2 = 0 then 1 else 0 := by
  by_cases hpar : i % 2 = 0
  · rw [if_pos hpar]
    have h_pred_iff : ∀ c, decide ((i + c) % 2 = 0 ∧ ((0 : Nat) = c ∨ (0 : Nat) = c + 1)) =
                          decide (c = 0) := by
      intro c
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      refine ⟨fun ⟨_, h⟩ => ?_, fun h => ?_⟩
      · rcases h with h | h
        · exact h.symm
        · omega
      · subst h; refine ⟨by omega, Or.inl rfl⟩
    rw [show (List.range (d - 1)).filter
          (fun c => decide ((i + c) % 2 = 0 ∧ ((0 : Nat) = c ∨ (0 : Nat) = c + 1))) =
        (List.range (d - 1)).filter (fun c => decide (c = 0)) from
      List.filter_congr (fun c _ => h_pred_iff c)]
    rw [show ((List.range (d - 1)).filter (fun c => decide (c = 0))).length =
        (List.range (d - 1)).count 0 from by
      simp [List.count, List.countP_eq_length_filter]; rfl,
      List.count_range, if_pos (by omega : (0 : Nat) < d - 1)]
  · rw [if_neg hpar]
    have h_pred_false : ∀ c, decide ((i + c) % 2 = 0 ∧ ((0 : Nat) = c ∨ (0 : Nat) = c + 1)) = false := by
      intro c
      apply decide_eq_false
      intro ⟨h_par, h_col⟩
      rcases h_col with h | h
      · subst h; omega
      · omega
    rw [show (List.range (d - 1)).filter
          (fun c => decide ((i + c) % 2 = 0 ∧ ((0 : Nat) = c ∨ (0 : Nat) = c + 1))) = [] from by
        rw [List.filter_eq_nil_iff]
        intro c _ h
        exact absurd h (by rw [h_pred_false]; decide)]
    rfl

/-- **Middle-col bulk count = 1**: for row ∈ `{i, i+1}` and `1 ≤ col < d-1`,
    the bulk filter on "decode = Z" has length exactly 1.

    Composes `rowStepBulkList_filter_decode_Z_eq` +
    `range_filter_pred_length_eq_one_middle`. -/
theorem rowStepBulkList_filter_decode_Z_length_middle
    (d : Nat) (hd1 : 1 < d) (hodd : d % 2 = 1)
    (i : Nat) (hi : i + 1 < d)
    (row col : Nat) (h_row : row = i ∨ row = i + 1)
    (hcol1 : col ≥ 1) (hcol2 : col < d - 1) :
    ((rowStepBulkList d i).filter
      (fun k => decodeStabPauliAt d k row col = Pauli.Z)).length = 1 := by
  rw [rowStepBulkList_filter_decode_Z_eq d hd1 hodd i hi row col h_row]
  exact range_filter_pred_length_eq_one_middle d i col hcol1 hcol2

/-- Edge col = d-1: range filter length = 1 if `i` is odd, 0 otherwise.
    Uses `c ∈ List.range (d-1) → c < d-1` to exclude `c = d-1`. -/
theorem range_filter_col_dm1_length
    (d i : Nat) (hd1 : 1 < d) (hodd : d % 2 = 1) :
    ((List.range (d - 1)).filter
      (fun c => decide ((i + c) % 2 = 0 ∧ ((d - 1) = c ∨ (d - 1) = c + 1)))).length =
      if i % 2 = 1 then 1 else 0 := by
  by_cases hpar : i % 2 = 1
  · rw [if_pos hpar]
    have h_filter_eq : (List.range (d - 1)).filter
        (fun c => decide ((i + c) % 2 = 0 ∧ ((d - 1) = c ∨ (d - 1) = c + 1))) =
      (List.range (d - 1)).filter (fun c => decide (c = d - 2)) := by
      apply List.filter_congr
      intro c hc
      rw [List.mem_range] at hc
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      refine ⟨fun ⟨_, h_col⟩ => ?_, fun h => ?_⟩
      · rcases h_col with h | h
        · omega
        · omega
      · subst h; refine ⟨?_, Or.inr ?_⟩ <;> omega
    rw [h_filter_eq]
    rw [show ((List.range (d - 1)).filter (fun c => decide (c = d - 2))).length =
        (List.range (d - 1)).count (d - 2) from by
      simp [List.count, List.countP_eq_length_filter]; rfl,
      List.count_range, if_pos (by omega : d - 2 < d - 1)]
  · rw [if_neg hpar]
    have h_pred_false : ∀ c, c < d - 1 →
        decide ((i + c) % 2 = 0 ∧ ((d - 1) = c ∨ (d - 1) = c + 1)) = false := by
      intro c hc
      apply decide_eq_false
      intro ⟨h_par, h_col⟩
      rcases h_col with h | h
      · omega
      · omega
    rw [show (List.range (d - 1)).filter
          (fun c => decide ((i + c) % 2 = 0 ∧ ((d - 1) = c ∨ (d - 1) = c + 1))) = [] from by
        rw [List.filter_eq_nil_iff]
        intro c hc hp
        rw [List.mem_range] at hc
        exact absurd hp (by rw [h_pred_false c hc]; decide)]
    rfl

/-- **Edge col=0 bulk count**: at col=0, the bulk Z-filter has length 1 if `i` is even, 0 otherwise. -/
theorem rowStepBulkList_filter_decode_Z_length_col_0
    (d : Nat) (hd1 : 1 < d) (hodd : d % 2 = 1)
    (i : Nat) (hi : i + 1 < d)
    (row : Nat) (h_row : row = i ∨ row = i + 1) :
    ((rowStepBulkList d i).filter
      (fun k => decodeStabPauliAt d k row 0 = Pauli.Z)).length =
      if i % 2 = 0 then 1 else 0 := by
  rw [rowStepBulkList_filter_decode_Z_eq d hd1 hodd i hi row 0 h_row]
  exact range_filter_col_0_length d i hd1

/-- **Edge col=d-1 bulk count**: at col=d-1, the bulk Z-filter has length 1 if `i` is odd, 0 otherwise. -/
theorem rowStepBulkList_filter_decode_Z_length_col_dm1
    (d : Nat) (hd1 : 1 < d) (hodd : d % 2 = 1)
    (i : Nat) (hi : i + 1 < d)
    (row : Nat) (h_row : row = i ∨ row = i + 1) :
    ((rowStepBulkList d i).filter
      (fun k => decodeStabPauliAt d k row (d - 1) = Pauli.Z)).length =
      if i % 2 = 1 then 1 else 0 := by
  rw [rowStepBulkList_filter_decode_Z_eq d hd1 hodd i hi row (d - 1) h_row]
  exact range_filter_col_dm1_length d i hd1 hodd

/-- Structural decomposition of `rowStepStabsRaw d i` filter count:
    splits into boundary contribution (1 or 0) + bulk count.

    Used as the entry point for case analysis on (boundary contributes?,
    bulk count?) in the inside-rows counting argument. -/
theorem rowStepStabsRaw_filter_length_split
    (d i : Nat) (pred : Nat → Bool) :
    ((rowStepStabsRaw d i).filter pred).length =
      (if pred (rowStepBoundaryIdx d i) then 1 else 0)
        + ((rowStepBulkList d i).filter pred).length := by
  unfold rowStepStabsRaw
  simp only [List.filter_cons]
  by_cases h : pred (rowStepBoundaryIdx d i) = true
  · rw [if_pos h]
    simp [h]; omega
  · rw [if_neg h]
    have h' : pred (rowStepBoundaryIdx d i) = false := by
      cases hp : pred (rowStepBoundaryIdx d i) <;> [rfl; exact absurd hp h]
    simp [h']

/-- Edge col case (col = 0): the bulk index `bulkIdx d i 0` is in
    `rowStepBulkList d i` iff `i` is even.  Used in the col=0 counting
    sub-case of `rowStepWitness_eq_Z_inside_rows`. -/
theorem rowStepBulkList_col_0_membership
    (d i : Nat) (hd : 1 < d) :
    bulkIdx d i 0 ∈ rowStepBulkList d i ↔ i % 2 = 0 := by
  rw [mem_rowStepBulkList_iff]
  constructor
  · intro ⟨c, _hc_lt, hc_par, hc_eq⟩
    have hc_val : c = 0 := by unfold bulkIdx at hc_eq; omega
    rw [hc_val] at hc_par; omega
  · intro hpar
    exact ⟨0, by omega, by omega, rfl⟩

/-- Edge col case (col = d-1): the bulk index `bulkIdx d i (d-2)` is in
    `rowStepBulkList d i` iff `i` is odd.  (For `d` odd, `d-2` is also
    odd, so `(i + (d-2)) % 2 = 0` iff `i` is odd.)  Used in the
    col=d-1 counting sub-case. -/
theorem rowStepBulkList_col_dm2_membership
    (d : Nat) (hd : 1 < d) (hodd : d % 2 = 1) (i : Nat) :
    bulkIdx d i (d - 2) ∈ rowStepBulkList d i ↔ i % 2 = 1 := by
  rw [mem_rowStepBulkList_iff]
  constructor
  · intro ⟨c, _hc_lt, hc_par, hc_eq⟩
    have hc_val : c = d - 2 := by unfold bulkIdx at hc_eq; omega
    rw [hc_val] at hc_par; omega
  · intro hpar
    refine ⟨d - 2, by omega, ?_, rfl⟩; omega

/-- For row ∈ `{i, i+1}` and the boundary stab, the decode equals `Z`
    iff `(i even ∧ col = d-1) ∨ (i odd ∧ col = 0)`. -/
theorem boundary_decode_inside_row_eq_Z_iff
    (d : Nat) (hd1 : 1 < d) (hodd : d % 2 = 1)
    (i : Nat) (hi : i + 1 < d)
    (row col : Nat) (h_row : row = i ∨ row = i + 1) :
    decodeStabPauliAt d (rowStepBoundaryIdx d i) row col = Pauli.Z ↔
      (i % 2 = 0 ∧ col = d - 1) ∨ (i % 2 = 1 ∧ col = 0) := by
  by_cases hpar : i % 2 = 0
  · refine ⟨fun h_eq => ?_, fun h => ?_⟩
    · by_cases hcol : col = d - 1
      · exact Or.inl ⟨hpar, hcol⟩
      · have h_I := boundary_rightZ_off_col d hd1 hodd i hi hpar row col h_row hcol
        rw [h_I] at h_eq; exact absurd h_eq (by decide)
    · rcases h with ⟨_, hcol⟩ | ⟨hpar', _⟩
      · rw [hcol]
        rcases h_row with h_row | h_row
        · rw [h_row]; exact boundary_rightZ_at_row_i_col_dm1 d hd1 hodd i hi hpar
        · rw [h_row]; exact boundary_rightZ_at_row_ip1_col_dm1 d hd1 hodd i hi hpar
      · omega
  · have hpar1 : i % 2 = 1 := by omega
    refine ⟨fun h_eq => ?_, fun h => ?_⟩
    · by_cases hcol : col = 0
      · exact Or.inr ⟨hpar1, hcol⟩
      · have h_I := boundary_leftZ_off_col d hd1 hodd i hi hpar1 row col h_row hcol
        rw [h_I] at h_eq; exact absurd h_eq (by decide)
    · rcases h with ⟨hpar', _⟩ | ⟨_, hcol⟩
      · omega
      · rw [hcol]
        rcases h_row with h_row | h_row
        · rw [h_row]; exact boundary_leftZ_at_row_i_col_0 d hd1 hodd i hi hpar1
        · rw [h_row]; exact boundary_leftZ_at_row_ip1_col_0 d hd1 hodd i hi hpar1

/-- ★ **THE INSIDE-ROWS HEADLINE** ★ : for `q : Fin (d*d)` with row index
    `q.val / d ∈ {i, i+1}`, the row-step witness evaluates to `Pauli.Z`.

    Composes the tick-31 count-odd bridge + the tick-32 boundary-bulk split
    with the per-case bulk counts (middle / col=0 / col=d-1) and boundary
    values.  Six sub-cases (3 col positions × 2 i-parities), each yielding
    boundary + bulk = 1 (odd).

    Axiom-clean at `[propext, Classical.choice, Quot.sound]`. -/
theorem rowStepWitness_eq_Z_inside_rows
    (d : Nat) (hd1 : 1 < d) (hodd : d % 2 = 1)
    (i : Nat) (hi : i + 1 < d)
    (q : Fin (d * d)) (h_row : q.val / d = i ∨ q.val / d = i + 1) :
    rowStepWitness d hd1 hodd i hi q = Pauli.Z := by
  rw [rowStepWitness_eq_Z_iff_count_odd, rowStepStabsRaw_filter_length_split]
  have h_col_lt : q.val % d < d := Nat.mod_lt _ (by omega)
  by_cases h_col_0 : q.val % d = 0
  · rw [h_col_0]
    by_cases hpar : i % 2 = 0
    · have h_bdy_I : decodeStabPauliAt d (rowStepBoundaryIdx d i) (q.val / d) 0 = Pauli.I :=
        boundary_rightZ_off_col d hd1 hodd i hi hpar (q.val / d) 0 h_row (by omega)
      have h_bdy_dec : (decide (decodeStabPauliAt d (rowStepBoundaryIdx d i) (q.val / d) 0 = Pauli.Z)) = false := by
        rw [h_bdy_I]; decide
      rw [h_bdy_dec]; simp
      have h_bulk := rowStepBulkList_filter_decode_Z_length_col_0 d hd1 hodd i hi (q.val / d) h_row
      rw [if_pos hpar] at h_bulk; rw [h_bulk]
    · have hpar1 : i % 2 = 1 := by omega
      have h_bdy_Z : decodeStabPauliAt d (rowStepBoundaryIdx d i) (q.val / d) 0 = Pauli.Z := by
        rcases h_row with h | h
        · rw [h]; exact boundary_leftZ_at_row_i_col_0 d hd1 hodd i hi hpar1
        · rw [h]; exact boundary_leftZ_at_row_ip1_col_0 d hd1 hodd i hi hpar1
      have h_bdy_dec : (decide (decodeStabPauliAt d (rowStepBoundaryIdx d i) (q.val / d) 0 = Pauli.Z)) = true := by
        rw [h_bdy_Z]; decide
      rw [h_bdy_dec]; simp
      have h_bulk := rowStepBulkList_filter_decode_Z_length_col_0 d hd1 hodd i hi (q.val / d) h_row
      rw [if_neg (by omega : ¬ i % 2 = 0)] at h_bulk; rw [h_bulk]
  · by_cases h_col_dm1 : q.val % d = d - 1
    · rw [h_col_dm1]
      by_cases hpar : i % 2 = 0
      · have h_bdy_Z : decodeStabPauliAt d (rowStepBoundaryIdx d i) (q.val / d) (d - 1) = Pauli.Z := by
          rcases h_row with h | h
          · rw [h]; exact boundary_rightZ_at_row_i_col_dm1 d hd1 hodd i hi hpar
          · rw [h]; exact boundary_rightZ_at_row_ip1_col_dm1 d hd1 hodd i hi hpar
        have h_bdy_dec : (decide (decodeStabPauliAt d (rowStepBoundaryIdx d i) (q.val / d) (d - 1) = Pauli.Z)) = true := by
          rw [h_bdy_Z]; decide
        rw [h_bdy_dec]; simp
        have h_bulk := rowStepBulkList_filter_decode_Z_length_col_dm1 d hd1 hodd i hi (q.val / d) h_row
        rw [if_neg (by omega : ¬ i % 2 = 1)] at h_bulk; rw [h_bulk]
      · have hpar1 : i % 2 = 1 := by omega
        have h_bdy_I : decodeStabPauliAt d (rowStepBoundaryIdx d i) (q.val / d) (d - 1) = Pauli.I :=
          boundary_leftZ_off_col d hd1 hodd i hi hpar1 (q.val / d) (d - 1) h_row (by omega)
        have h_bdy_dec : (decide (decodeStabPauliAt d (rowStepBoundaryIdx d i) (q.val / d) (d - 1) = Pauli.Z)) = false := by
          rw [h_bdy_I]; decide
        rw [h_bdy_dec]; simp
        have h_bulk := rowStepBulkList_filter_decode_Z_length_col_dm1 d hd1 hodd i hi (q.val / d) h_row
        rw [if_pos hpar1] at h_bulk; rw [h_bulk]
    · have hcol_ge_1 : q.val % d ≥ 1 := by omega
      have hcol_lt_dm1 : q.val % d < d - 1 := by omega
      have h_bdy_I : decodeStabPauliAt d (rowStepBoundaryIdx d i) (q.val / d) (q.val % d) = Pauli.I := by
        by_cases hpar : i % 2 = 0
        · exact boundary_rightZ_off_col d hd1 hodd i hi hpar (q.val / d) (q.val % d) h_row (by omega)
        · have hpar1 : i % 2 = 1 := by omega
          exact boundary_leftZ_off_col d hd1 hodd i hi hpar1 (q.val / d) (q.val % d) h_row (by omega)
      have h_bdy_dec : (decide (decodeStabPauliAt d (rowStepBoundaryIdx d i) (q.val / d) (q.val % d) = Pauli.Z)) = false := by
        rw [h_bdy_I]; decide
      rw [h_bdy_dec]; simp
      have h_bulk := rowStepBulkList_filter_decode_Z_length_middle d hd1 hodd i hi (q.val / d) (q.val % d) h_row hcol_ge_1 hcol_lt_dm1
      rw [h_bulk]

/-- ★★★ **THE FULL `rowStepWitness_row_support` LEMMA** ★★★

    Combines `rowStepWitness_eq_Z_inside_rows` (tick 38) and
    `rowStepWitness_eq_I_outside_rows` (tick 25) into a single pointwise
    characterization of `rowStepWitness d hd1 hodd i hi` at every qubit:
    `Z` if the qubit's row index is in `{i, i+1}`, `I` otherwise.

    This is the EXACT hypothesis `hpointwise` consumed by
    `mkSurfaceRowCut_succ_conditional` (tick 23).  Axiom-clean at
    `[propext, Classical.choice, Quot.sound]`. -/
theorem rowStepWitness_row_support
    (d : Nat) (hd1 : 1 < d) (hodd : d % 2 = 1)
    (i : Nat) (hi : i + 1 < d) :
    ∀ q : Fin (d * d),
      rowStepWitness d hd1 hodd i hi q =
        if q.val / d = i ∨ q.val / d = i + 1 then Pauli.Z else Pauli.I := by
  intro q
  by_cases h_in : q.val / d = i ∨ q.val / d = i + 1
  · rw [if_pos h_in]
    exact rowStepWitness_eq_Z_inside_rows d hd1 hodd i hi q h_in
  · rw [if_neg h_in]
    have h_out : q.val / d ≠ i ∧ q.val / d ≠ i + 1 :=
      ⟨fun h => h_in (Or.inl h), fun h => h_in (Or.inr h)⟩
    exact rowStepWitness_eq_I_outside_rows d hd1 hodd i hi q h_out

/-- ★★★ **THE UNCONDITIONAL `mkSurfaceRowCut_succ`** ★★★

    The complete `NZSurfaceSpec.rowCut_succ` field for the parametric
    surface code, **no hypothesis required**.  Discharges the
    `hpointwise` parameter of `mkSurfaceRowCut_succ_conditional` (tick 23)
    using `rowStepWitness_row_support`.

    All 3 conjuncts (a) `InStab`, (b) `{I, Z}` pointwise, (c) telescoping
    equation are now mechanically proven for any odd `d ≥ 3` and any
    row index `i` with `i + 1 < d`.  Axiom-clean at
    `[propext, Classical.choice, Quot.sound]`.

    This closes the rowCut_succ field of `NZSurfaceSpec` — the last
    hypothesis-laden field for the parametric assembly. -/
theorem mkSurfaceRowCut_succ_unconditional
    (d : Nat) (hd1 : 1 < d) (hodd : d % 2 = 1)
    (i : Nat) (hi : i + 1 < d) (hi_pos : i < d) :
    ∃ S : ErrorVec (d * d),
      InStab (mkSurfaceQECParams d (by omega) hodd) S ∧
      (∀ q : Fin (d * d), S q = Pauli.I ∨ S q = Pauli.Z) ∧
      mkSurfaceRowCut d ⟨i + 1, hi⟩
        = ErrorVec.mul S (mkSurfaceRowCut d ⟨i, hi_pos⟩) :=
  mkSurfaceRowCut_succ_conditional d hd1 hodd i hi hi_pos
    (rowStepWitness_row_support d hd1 hodd i hi)

end QStab.Examples.SurfaceParametric

/-! ## ★★★★ THE GRAND ASSEMBLY: parametric `NZSurfaceSpec d` ★★★★

For arbitrary odd `d ≥ 3`, composes all 11 fields of `NZSurfaceSpec`
into `mkSurfaceNZSurfaceSpec d hd3 hodd : NZSurfaceSpec d`, mechanically
proven and axiom-clean.

Each field's discharge (in order):
1. `params` — `mkSurfaceQECParams d _ hodd`
2. `hn` — `rfl` (params.n = d * d definitionally)
3. `hd_pos` — `omega` (from hd3 : 3 ≤ d)
4. `logicalZ` — `mkSurfaceLogicalZ d`
5. `rowCut` — `mkSurfaceRowCut d`
6. `rowCut_zero` — `mkSurfaceRowCut_zero` (tick 23, rfl-true)
7. `rowCut_succ` — `mkSurfaceRowCut_succ_unconditional` (tick 39)
8. `logicalZ_normalizer` — `logicalZ_normalizer_parametric` (Phase 2)
9. `rowCut_spec` — `mkSurfaceRowCut_spec` (tick 23, rfl-true)
10. `stab_commute` — `stab_commute_parametric` (Phase 2)
11. `hook_spread_bound` — `hook_spread_bound_parametric` (tick 22 HEADLINE)

This is the parametric BarrierWitness substrate for the surface code —
the paper's "130-line parametric file" mechanized in Lean. -/

open QStab QStab.Examples.SurfaceParametric QStab.Examples.SurfaceGeneral in
/-- ★★★★★ **THE PARAMETRIC `NZSurfaceSpec d` FOR THE ROTATED SURFACE CODE** ★★★★★

    For arbitrary odd `d ≥ 3`, this instance bundles all 11 fields of
    `NZSurfaceSpec` (params, geometry, algebraic + telescoping +
    commutativity properties, and the deepest hook_spread_bound).

    Closes Phase A.  Axiom-clean at `[propext, Classical.choice, Quot.sound]`. -/
def QStab.Examples.SurfaceParametric.mkSurfaceNZSurfaceSpec
    (d : Nat) (hd3 : 3 ≤ d) (hodd : d % 2 = 1) : NZSurfaceSpec d where
  params := mkSurfaceQECParams d (by omega) hodd
  hn := rfl
  hd_pos := by omega
  logicalZ := mkSurfaceLogicalZ d
  rowCut := fun i => mkSurfaceRowCut d i
  rowCut_zero := mkSurfaceRowCut_zero d (by omega)
  rowCut_succ := fun i hi =>
    mkSurfaceRowCut_succ_unconditional d (by omega) hodd i.val hi i.isLt
  logicalZ_normalizer := fun i =>
    logicalZ_normalizer_parametric d (by omega) i
  rowCut_spec := fun i q => mkSurfaceRowCut_spec d i q
  stab_commute := fun i j =>
    stab_commute_parametric d (by omega) hodd i j
  hook_spread_bound := fun s_idx e_B he E S_wit hS =>
    hook_spread_bound_parametric d hd3 hodd s_idx e_B he E S_wit hS

/-! ### d=3, d=5, d=7 #check smoke tests for `mkSurfaceNZSurfaceSpec` -/

#check (QStab.Examples.SurfaceParametric.mkSurfaceNZSurfaceSpec 3 (by decide) (by decide) :
          QStab.Examples.SurfaceGeneral.NZSurfaceSpec 3)
#check (QStab.Examples.SurfaceParametric.mkSurfaceNZSurfaceSpec 5 (by decide) (by decide) :
          QStab.Examples.SurfaceGeneral.NZSurfaceSpec 5)
#check (QStab.Examples.SurfaceParametric.mkSurfaceNZSurfaceSpec 7 (by decide) (by decide) :
          QStab.Examples.SurfaceGeneral.NZSurfaceSpec 7)

/-! ## ★★★★★★ Parametric `d_circ ≥ d` HEADLINE THEOREMS ★★★★★★

These three definitions compose `mkSurfaceNZSurfaceSpec` (tick 40) with
the existing `QStab.Paper.SurfaceBarrier` framework (`surfaceBarrier`,
`surface_isLAligned`, `surface_distance_preservation`) to produce
parametric versions for arbitrary odd `d ≥ 3`.

This is the paper's headline theorem: the rotated surface code achieves
circuit-level code distance `d_circ ≥ d` parametrically in `d` and `R`,
under NZ scheduling. -/

open QStab.Paper.BarrierFramework QStab.Paper.SurfaceBarrier in
/-- **The parametric surface-code BarrierFunction** for arbitrary odd `d ≥ 3`. -/
noncomputable def QStab.Examples.SurfaceParametric.parametricSurfaceBarrier
    (d : Nat) (hd3 : 3 ≤ d) (hodd : d % 2 = 1) :
    BarrierFunction
      (QStab.Examples.SurfaceParametric.mkSurfaceNZSurfaceSpec d hd3 hodd).params
      (barZClass (QStab.Examples.SurfaceParametric.mkSurfaceNZSurfaceSpec d hd3 hodd)) :=
  surfaceBarrier (QStab.Examples.SurfaceParametric.mkSurfaceNZSurfaceSpec d hd3 hodd)

open QStab.Paper.BarrierFramework QStab.Paper.SurfaceBarrier in
/-- **L-aligned property** for the parametric surface barrier. -/
theorem QStab.Examples.SurfaceParametric.parametricSurface_isLAligned
    (d : Nat) (hd3 : 3 ≤ d) (hodd : d % 2 = 1) :
    IsLAligned (QStab.Examples.SurfaceParametric.parametricSurfaceBarrier d hd3 hodd) :=
  surface_isLAligned (QStab.Examples.SurfaceParametric.mkSurfaceNZSurfaceSpec d hd3 hodd)

open QStab.Paper.BarrierFramework QStab.Paper.SurfaceBarrier in
/-- ★★★★★★ **THE PARAMETRIC `d_circ ≥ d` HEADLINE FOR THE ROTATED SURFACE CODE** ★★★★★★

    For any odd `d ≥ 3`, any state `s` at the end of any QClifford run
    that contains an undetected bar-Z (or bar-Y) logical error has
    fault budget `C_budget - s.C ≥ d`, i.e., at least `d` faults must
    have been applied.  This is the paper's main parametric headline.

    Axiom-clean at `[propext, Classical.choice, Quot.sound]`. -/
theorem QStab.Examples.SurfaceParametric.parametricSurface_distance_preservation
    (d : Nat) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (s : State (QStab.Examples.SurfaceParametric.mkSurfaceNZSurfaceSpec d hd3 hodd).params)
    (hrun : Run (QStab.Examples.SurfaceParametric.mkSurfaceNZSurfaceSpec d hd3 hodd).params
              (.done s))
    (h_in : LogicalClass.contains
              (barZClass (QStab.Examples.SurfaceParametric.mkSurfaceNZSurfaceSpec d hd3 hodd))
              s.E_tilde) :
    (QStab.Examples.SurfaceParametric.mkSurfaceNZSurfaceSpec d hd3 hodd).params.C_budget
      - s.C ≥ d :=
  surface_distance_preservation
    (QStab.Examples.SurfaceParametric.mkSurfaceNZSurfaceSpec d hd3 hodd) s hrun h_in
