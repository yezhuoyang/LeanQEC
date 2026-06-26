import QStab.Defs
import QStab.Examples.SurfaceCode
import QStab.Examples.SurfaceGeometry

/-! # Parametric rotated-surface-code `QECParams` (Phase 2: stabilizer family)

This file extends Phase 1 (`mkSurfaceQECParams`) with a **closed-form
parametric stabilizer family** `mkSurfaceStabilizers (d : Nat) (hd : 0 < d) :
Fin (numStabFormula d) → ErrorVec (d * d)` for the rotated surface code at
arbitrary distance `d`.

## Encoding

For each stabilizer index `i : Fin (numStabFormula d)` we determine an
abstract *region* (Z-bulk, X-bulk, top-X, right-Z, left-Z, bottom-X) and a
2-D grid coordinate, then return a Pauli at each data qubit `q` of the
`d × d` data grid.

The layout follows the **paper-order** convention of `SurfaceD3.stabilizers`
(invariant.tex §3.2):
* `0 .. (d-1)² - 1`           — bulks in row-major order; type alternates
                                  `Z` on `(r + c)` even, `X` on `(r + c)` odd.
* `(d-1)² .. + (d-1)/2 - 1`   — top-X boundaries on row `0`, cols `(2b, 2b+1)`.
* next `(d-1)/2` indices       — right-Z boundaries on col `d-1`, rows
                                  `(2b, 2b+1)`.
* next `(d-1)/2` indices       — left-Z boundaries on col `0`, rows
                                  `(2b+1, 2b+2)`.
* last `(d-1)/2` indices       — bottom-X boundaries on row `d-1`, cols
                                  `(2b+1, 2b+2)`.

For **odd** `d` (the case targeted by this workflow: `d = 3, 5, 7`) the
sum `4 · (d-1)/2 = 2(d-1)` matches `numStabFormula d`, so the encoding is
exact.  At **even** `d` the boundary block sizes differ; the function
returns sensible "no-op" placeholders (all-`I`) at the orphan indices and
is **not claimed to match** the hand-written `SurfaceD4.stabilizers`.

## d=3 sanity

The headline `mkSurfaceStabilizers_d3_matches_SurfaceD3` shows that
`mkSurfaceStabilizers 3 _ i = SurfaceD3.stabilizers i` for every
`i : Fin 8`, **with the identity permutation** — i.e. paper-order is
respected exactly.

## Discipline

* No `sorry`, `native_decide`, `Classical.choose`, `Exists.choose`,
  or `by_contra` is used.
* The decode function is a pure structural pattern of `Nat` comparisons;
  every `#eval` reduces to a closed `Pauli`/`ErrorVec` literal.
* `decide` IS used (allowed) on the `d=3` cross-check, where the
  goal is decidable equality of two functions of finite domain.
-/

namespace QStab.Examples.SurfaceParametric

open QStab QStab.Examples

/-! ## Phase-1 arithmetic carried forward (re-exported) -/

/-- Number of stabilizer generators of the rotated `d × d` surface code,
    formula `(d-1)² + 2 (d-1) = d² − 1`. We clamp at `1` so that the
    structural `hns : 0 < numStab` proof works from `0 < d` alone — at the
    degenerate `d = 1` case this is just a placeholder of size 1. -/
def numStabFormula (d : Nat) : Nat :=
  max 1 ((d - 1) * (d - 1) + 2 * (d - 1))

/-- The maximum hook back-action weight, parametric in `d`. The rotated
    surface code with a NZ schedule satisfies `r ≤ 4` for every distance. -/
def hookWeightBound : Nat := 4

/-- Canonical surface-code error budget at distance `d`. -/
def errorBudget (d : Nat) : Nat := (d - 1) / 2

/-! ## Region tagging

A `StabRegion` is the abstract category of a stabilizer position.
We do not actually need this as a Lean inductive — it is conceptual.
The decode function below collapses it into a Pauli at each data qubit. -/

/-! ## Decoding a stabilizer index into a per-qubit Pauli

Given the distance `d`, the stabilizer index `i : Nat` (with `i < numStabFormula d`),
and a data-qubit position `(row, col)` (each `< d`), produce the Pauli
that stabilizer `i` assigns to that qubit.

The function is deliberately *total over `Nat`* — out-of-range indices
yield `Pauli.I`, since the surrounding `mkSurfaceStabilizers` always
calls it with in-range indices. -/
def decodeStabPauliAt (d i row col : Nat) : Pauli :=
  let dm1 := d - 1
  let bulkCount := dm1 * dm1
  if i < bulkCount then
    -- Bulk plaquette at (r, c).
    let r := i / dm1
    let c := i % dm1
    let kind : Pauli := if (r + c) % 2 = 0 then Pauli.Z else Pauli.X
    if (row = r ∨ row = r + 1) ∧ (col = c ∨ col = c + 1) then kind else Pauli.I
  else
    let b := i - bulkCount
    let half := dm1 / 2
    if b < half then
      -- Top-X boundary on row 0, cols (2b, 2b+1).
      if row = 0 ∧ (col = 2 * b ∨ col = 2 * b + 1) then Pauli.X else Pauli.I
    else if b < 2 * half then
      let bb := b - half
      -- Right-Z boundary on col d-1, rows (2bb, 2bb+1).
      if col = dm1 ∧ (row = 2 * bb ∨ row = 2 * bb + 1) then Pauli.Z else Pauli.I
    else if b < 3 * half then
      let bb := b - 2 * half
      -- Left-Z boundary on col 0, rows (2bb+1, 2bb+2).
      if col = 0 ∧ (row = 2 * bb + 1 ∨ row = 2 * bb + 2) then Pauli.Z else Pauli.I
    else
      let bb := b - 3 * half
      -- Bottom-X boundary on row d-1, cols (2bb+1, 2bb+2).
      if row = dm1 ∧ (col = 2 * bb + 1 ∨ col = 2 * bb + 2) then Pauli.X else Pauli.I

/-! ## The parametric stabilizer family

For each `i : Fin (numStabFormula d)`, the stabilizer is the function
`q : Fin (d * d) ↦ decodeStabPauliAt d i.val (q.val / d) (q.val % d)`. -/
def mkSurfaceStabilizers (d : Nat) (_hd : 0 < d)
    (i : Fin (numStabFormula d)) : ErrorVec (d * d) :=
  fun q => decodeStabPauliAt d i.val (q.val / d) (q.val % d)

/-! ## Sanity: `d = 3` reproduces `SurfaceD3.stabilizers` exactly

We check all `8 × 9 = 72` Pauli entries by `decide`, which is fast on a
closed problem of this size and stays within the discipline (no
`native_decide`, no `Classical.choose`, no `by_contra`). -/

/-- At `d = 3`, the parametric stabilizer family equals
    `SurfaceD3.stabilizers` pointwise (identity permutation). -/
theorem mkSurfaceStabilizers_d3_matches_SurfaceD3 :
    ∀ (i : Fin 8) (q : Fin 9),
      mkSurfaceStabilizers 3 (by decide) i q = SurfaceD3.stabilizers i q := by
  decide

/-- Function-level form of the `d = 3` sanity check (uses `funext` to
    bridge from pointwise equality). -/
theorem mkSurfaceStabilizers_d3_eq_SurfaceD3 :
    ∀ (i : Fin 8),
      mkSurfaceStabilizers 3 (by decide) i = SurfaceD3.stabilizers i := by
  intro i
  funext q
  exact mkSurfaceStabilizers_d3_matches_SurfaceD3 i q

/-! ## Phase-1 `QECParams` carried forward

The parametric `QECParams` constructor `mkSurfaceQECParams` lives in the
downstream module `QStab/Examples/SurfaceHookErrors.lean` because its
`backActionSet` field now consumes the parametric hook-error enumeration
`mkSurfaceHookErrors`, which depends on `classifyStab`/`StabKind` defined
here. Keeping the constructor co-located with its `backActionSet`
witness avoids a circular import. -/

/-! ## Inspection — these reduce to closed `Pauli` literals -/

-- Stabilizer 0 at d=3, qubit 0 → Pauli.Z   (matches s1 = Z₁Z₂Z₄Z₅).
#eval mkSurfaceStabilizers 3 (by decide) ⟨0, by decide⟩ ⟨0, by decide⟩

-- Stabilizer 1 at d=3, qubit 2 → Pauli.X   (matches s2 = X₂X₃X₅X₆, qubit 2 = q₃).
#eval mkSurfaceStabilizers 3 (by decide) ⟨1, by decide⟩ ⟨2, by decide⟩

-- Stabilizer 4 at d=3, qubit 8 → Pauli.I   (s5 = X₁X₂ has no support on q₉).
#eval mkSurfaceStabilizers 3 (by decide) ⟨4, by decide⟩ ⟨8, by decide⟩

-- d=5, stabilizer 0 at qubit 6 → Pauli.Z   (bulk Z at (r=0,c=0) covers q at (1,1)=6).
#eval mkSurfaceStabilizers 5 (by decide) ⟨0, by decide⟩ ⟨6, by decide⟩

-- d=7, stabilizer 0 at qubit 8 → Pauli.Z   (bulk Z at (r=0,c=0) covers q at (1,1)=8).
#eval mkSurfaceStabilizers 7 (by decide) ⟨0, by decide⟩ ⟨8, by decide⟩

/-! ## Parametric logical-Z and column-cut operators

These are the two parametric ingredients needed by the topological row/column
cut argument (invariant.tex §3.2).

The chosen conventions match the existing `SurfaceD3` instance:

* The **logical Z** operator is the product of `Z` over the **top row** of
  data qubits, i.e. those `q : Fin (d * d)` with `q.val / d = 0` (equivalently
  `q.val < d`). At `d = 3` this is `Z` on `{0, 1, 2}`.

* The **column-`i` cut operator** is the product of `Z` over the entire
  column `i.val`, i.e. those `q : Fin (d * d)` with `q.val % d = i.val`.
  At `d = 3`, `mkSurfaceCutOp 3 0` is `Z` on `{0, 3, 6}` (the left column).

Both definitions are pointwise functions of `Fin (d * d) → Pauli`; the
parametric closed form means every `#eval` reduces to a closed `Pauli`
literal, and the `d = 3` sanity lemmas below typecheck by `decide` on the
finite domain. -/

/-- The **parametric logical-Z** operator of the rotated surface code at
    distance `d`: `Z` on every data qubit in the **top row**
    (`q.val / d = 0`, equivalently `q.val < d`), `I` elsewhere. -/
def mkSurfaceLogicalZ (d : Nat) : ErrorVec (d * d) :=
  fun q => if q.val / d = 0 then Pauli.Z else Pauli.I

/-- The **parametric column-`i` cut operator** of the rotated surface code at
    distance `d`: `Z` on every data qubit in column `i` (`q.val % d = i.val`),
    `I` elsewhere. Used in the topological lower-bound argument
    (`invariant.tex:1719`, generalised from `SurfaceD3.colCut` /
    `SurfaceD3.rowCut`). -/
def mkSurfaceCutOp (d : Nat) (i : Fin d) : ErrorVec (d * d) :=
  fun q => if q.val % d = i.val then Pauli.Z else Pauli.I

/-! ## `d = 3` sanity checks against `SurfaceD3`

`mkSurfaceLogicalZ 3 = SurfaceD3.logicalZ` exactly (both are `Z` on the
top-row qubits `{0, 1, 2}`).

`mkSurfaceCutOp 3 ⟨0, _⟩` is the **left-column** `Z` operator, i.e. `Z` on
qubits `{0, 3, 6}`. (This is a Z-typed analogue of `SurfaceD3.colCut 1`,
which the paper writes for the X cut; the row/column-cut argument in
§3.2 is symmetric.) -/

/-- Pointwise: at `d = 3`, the parametric logical-Z agrees with the hand-
    written `SurfaceD3.logicalZ`. -/
theorem mkSurfaceLogicalZ_d3_matches_SurfaceD3 :
    ∀ (q : Fin 9), mkSurfaceLogicalZ 3 q = SurfaceD3.logicalZ q := by
  decide

/-- Function-level: at `d = 3`, the parametric logical-Z equals the hand-
    written `SurfaceD3.logicalZ`. -/
theorem mkSurfaceLogicalZ_d3_eq_SurfaceD3 :
    mkSurfaceLogicalZ 3 = SurfaceD3.logicalZ := by
  funext q
  exact mkSurfaceLogicalZ_d3_matches_SurfaceD3 q

/-- Pointwise: at `d = 3`, `mkSurfaceCutOp 3 ⟨0, _⟩` is `Z` exactly on
    qubits `{0, 3, 6}` (left column), `I` elsewhere. -/
theorem mkSurfaceCutOp_d3_zero_left_column :
    ∀ (q : Fin 9),
      mkSurfaceCutOp 3 ⟨0, by decide⟩ q
        = (if q.val = 0 ∨ q.val = 3 ∨ q.val = 6 then Pauli.Z else Pauli.I) := by
  decide

/-- Pointwise: at `d = 3`, `mkSurfaceCutOp 3 ⟨1, _⟩` is `Z` exactly on the
    middle column qubits `{1, 4, 7}`. -/
theorem mkSurfaceCutOp_d3_one_middle_column :
    ∀ (q : Fin 9),
      mkSurfaceCutOp 3 ⟨1, by decide⟩ q
        = (if q.val = 1 ∨ q.val = 4 ∨ q.val = 7 then Pauli.Z else Pauli.I) := by
  decide

/-- Pointwise: at `d = 3`, `mkSurfaceCutOp 3 ⟨2, _⟩` is `Z` exactly on the
    right column qubits `{2, 5, 8}`. -/
theorem mkSurfaceCutOp_d3_two_right_column :
    ∀ (q : Fin 9),
      mkSurfaceCutOp 3 ⟨2, by decide⟩ q
        = (if q.val = 2 ∨ q.val = 5 ∨ q.val = 8 then Pauli.Z else Pauli.I) := by
  decide

/-! ## Inspection `#eval`s — reduce to closed `Pauli` literals -/

-- d = 3, logical Z: top row.
#eval mkSurfaceLogicalZ 3 ⟨0, by decide⟩   -- Pauli.Z
#eval mkSurfaceLogicalZ 3 ⟨1, by decide⟩   -- Pauli.Z
#eval mkSurfaceLogicalZ 3 ⟨2, by decide⟩   -- Pauli.Z
#eval mkSurfaceLogicalZ 3 ⟨3, by decide⟩   -- Pauli.I
#eval mkSurfaceLogicalZ 3 ⟨8, by decide⟩   -- Pauli.I

-- d = 3, column-0 cut: qubits {0, 3, 6}.
#eval mkSurfaceCutOp 3 ⟨0, by decide⟩ ⟨0, by decide⟩   -- Pauli.Z
#eval mkSurfaceCutOp 3 ⟨0, by decide⟩ ⟨3, by decide⟩   -- Pauli.Z
#eval mkSurfaceCutOp 3 ⟨0, by decide⟩ ⟨6, by decide⟩   -- Pauli.Z
#eval mkSurfaceCutOp 3 ⟨0, by decide⟩ ⟨1, by decide⟩   -- Pauli.I

-- d = 5, logical Z: top row qubits {0..4}.
#eval mkSurfaceLogicalZ 5 ⟨0, by decide⟩   -- Pauli.Z
#eval mkSurfaceLogicalZ 5 ⟨4, by decide⟩   -- Pauli.Z
#eval mkSurfaceLogicalZ 5 ⟨5, by decide⟩   -- Pauli.I

-- d = 5, column-2 cut: qubits {2, 7, 12, 17, 22}.
#eval mkSurfaceCutOp 5 ⟨2, by decide⟩ ⟨2, by decide⟩   -- Pauli.Z
#eval mkSurfaceCutOp 5 ⟨2, by decide⟩ ⟨7, by decide⟩   -- Pauli.Z
#eval mkSurfaceCutOp 5 ⟨2, by decide⟩ ⟨22, by decide⟩  -- Pauli.Z
#eval mkSurfaceCutOp 5 ⟨2, by decide⟩ ⟨3, by decide⟩   -- Pauli.I

-- d = 7, logical Z and column-3 cut spot-checks.
#eval mkSurfaceLogicalZ 7 ⟨6, by decide⟩            -- Pauli.Z
#eval mkSurfaceLogicalZ 7 ⟨7, by decide⟩            -- Pauli.I
#eval mkSurfaceCutOp 7 ⟨3, by decide⟩ ⟨3, by decide⟩  -- Pauli.Z
#eval mkSurfaceCutOp 7 ⟨3, by decide⟩ ⟨10, by decide⟩ -- Pauli.Z
#eval mkSurfaceCutOp 7 ⟨3, by decide⟩ ⟨45, by decide⟩ -- Pauli.Z (q=45: 45 % 7 = 3)
#eval mkSurfaceCutOp 7 ⟨3, by decide⟩ ⟨44, by decide⟩ -- Pauli.I (q=44: 44 % 7 = 2)

/-! ## Parametric column assignment (`mkSurfaceCol`) and its `cutOp_spec`

The rotated surface code has **no Sector-2 ancillas** at the data layer
(every data qubit participates in exactly one column).  Accordingly the
parametric column assignment

```
mkSurfaceCol (d : Nat) (q : Fin (d * d)) : Option (Fin d)
```

is `some ⟨q.val % d, _⟩` for every `q`, and `none` only in the degenerate
`d = 0` case (which is uninhabited, since `Fin (0 * 0) = Fin 0` has no
inhabitants — the `none` branch exists purely to make the function total).

The headline lemma `cutOp_spec_parametric` then says that
`mkSurfaceCutOp d i q = if mkSurfaceCol d q = some i then .Z else .I`,
which is **definitional**: both sides unfold to the same `if`-expression
on `q.val % d = i.val`.  No counting, no induction. -/

/-- Parametric column assignment for the rotated surface code at distance `d`.
    Returns `some ⟨q.val % d, _⟩` whenever `0 < d`, and `none` otherwise
    (the `d = 0` branch is unreachable because `Fin (0 * 0)` is empty,
    but we make the function total to avoid threading a positivity proof
    through every callsite). -/
def mkSurfaceCol (d : Nat) (q : Fin (d * d)) : Option (Fin d) :=
  if h : 0 < d then
    some ⟨q.val % d, Nat.mod_lt _ h⟩
  else
    none

/-- Parametric `cutOp_spec`: at distance `d > 0`, the column-`i` cut operator
    is `Z` exactly on the qubits whose column assignment is `some i`, and
    `I` elsewhere.  This is the definitional analogue of `hgp13_cutOp_spec`
    for the rotated surface code. -/
theorem cutOp_spec_parametric (d : Nat) (hd : 0 < d) (i : Fin d)
    (q : Fin (d * d)) :
    mkSurfaceCutOp d i q
      = if mkSurfaceCol d q = some i then Pauli.Z else Pauli.I := by
  unfold mkSurfaceCutOp mkSurfaceCol
  -- Reduce the `dite` on `0 < d` using the hypothesis `hd`.
  rw [dif_pos hd]
  -- Both sides are now `if (q.val % d = i.val) … else …`
  -- vs. `if some ⟨q.val % d, _⟩ = some i.val … else …`.
  -- Rewrite the `some = some` to the underlying `Fin` equality, then to
  -- the underlying `Nat` equality via `Fin.mk_eq_mk`.
  by_cases hmod : q.val % d = i.val
  · -- modulus matches `i.val` → both branches return `Pauli.Z`.
    have h_some : (some ⟨q.val % d, Nat.mod_lt _ hd⟩ : Option (Fin d))
                    = some i := by
      apply congrArg some
      apply Fin.ext
      exact hmod
    rw [if_pos hmod, if_pos h_some]
  · -- modulus does not match `i.val` → both branches return `Pauli.I`.
    have h_some : ¬ (some ⟨q.val % d, Nat.mod_lt _ hd⟩ : Option (Fin d))
                    = some i := by
      intro h
      apply hmod
      have := Option.some_injective _ h
      exact congrArg Fin.val this
    rw [if_neg hmod, if_neg h_some]

/-! ## Sanity `#eval`s and pointwise checks at `d = 3, 5, 7`

The `#eval` calls below reduce `mkSurfaceCol d q` to a closed
`Option (Fin d)` literal (`some ⟨_, _⟩`), confirming the function is
fully computable. -/

-- d = 3, columns: col 0 = {0,3,6}, col 1 = {1,4,7}, col 2 = {2,5,8}.
#eval mkSurfaceCol 3 ⟨0, by decide⟩   -- some 0
#eval mkSurfaceCol 3 ⟨1, by decide⟩   -- some 1
#eval mkSurfaceCol 3 ⟨2, by decide⟩   -- some 2
#eval mkSurfaceCol 3 ⟨3, by decide⟩   -- some 0
#eval mkSurfaceCol 3 ⟨4, by decide⟩   -- some 1
#eval mkSurfaceCol 3 ⟨7, by decide⟩   -- some 1
#eval mkSurfaceCol 3 ⟨8, by decide⟩   -- some 2

-- d = 5, columns are q.val % 5.
#eval mkSurfaceCol 5 ⟨0, by decide⟩    -- some 0
#eval mkSurfaceCol 5 ⟨7, by decide⟩    -- some 2
#eval mkSurfaceCol 5 ⟨12, by decide⟩   -- some 2
#eval mkSurfaceCol 5 ⟨24, by decide⟩   -- some 4

-- d = 7, columns are q.val % 7.
#eval mkSurfaceCol 7 ⟨0, by decide⟩    -- some 0
#eval mkSurfaceCol 7 ⟨10, by decide⟩   -- some 3
#eval mkSurfaceCol 7 ⟨45, by decide⟩   -- some 3
#eval mkSurfaceCol 7 ⟨48, by decide⟩   -- some 6

/-- Pointwise sanity at `d = 3`: `mkSurfaceCol 3 q` is `some (q.val % 3)`
    for every `q : Fin 9`. -/
example : ∀ (q : Fin 9), mkSurfaceCol 3 q = some ⟨q.val % 3, by omega⟩ := by
  decide

/-- Cross-check: at `d = 3`, the parametric `cutOp_spec` agrees with the
    closed-form `mkSurfaceCutOp` definition (both sides reduce to the
    same `if`-expression on `q.val % 3`). -/
example : ∀ (i : Fin 3) (q : Fin 9),
    mkSurfaceCutOp 3 i q
      = if mkSurfaceCol 3 q = some i then Pauli.Z else Pauli.I := by
  decide

/-- Cross-check: at `d = 5`. -/
example : ∀ (i : Fin 5) (q : Fin 25),
    mkSurfaceCutOp 5 i q
      = if mkSurfaceCol 5 q = some i then Pauli.Z else Pauli.I := by
  decide

/-- Cross-check: at `d = 7`. -/
example : ∀ (i : Fin 7) (q : Fin 49),
    mkSurfaceCutOp 7 i q
      = if mkSurfaceCol 7 q = some i then Pauli.Z else Pauli.I := by
  decide

/-! ## Parametric `logicalZ_normalizer`: every stabilizer commutes with logical Z

The headline `logicalZ_normalizer_parametric` proves that the parametric stabilizer
family `mkSurfaceStabilizers d hd` is contained in the normaliser of
`mkSurfaceLogicalZ d`, i.e. every generator has parity `false` against logical Z.

This is the parametric version of `D3Witness.logicalZ_norm`
(which proved the same fact at `d = 3` by `decide`).

### Proof strategy

1.  `mkSurfaceLogicalZ d q = Z` when `q.val / d = 0` (top row), else `I`.
2.  Therefore `anticommutes (stab q) (logicalZ q)` is true only when `q` is in the
    top row AND the stabilizer has X-component at `q`.
3.  By a bijection between `{q : Fin (d * d) | q.val / d = 0}` and `Fin d`
    (via `q ↦ ⟨q.val, _⟩`), the parity equals the parity of the set
    `{c : Fin d | hasXComponent (decodeStabPauliAt d i.val 0 c.val) = true}`.
4.  Case analysis on the stabilizer kind (bulk Z, bulk X with r = 0, top-X
    boundary, right/left-Z boundaries, bottom-X boundary) shows this set is
    either **empty** or a **pair `{c, c+1}`** with `c + 1 < d`.  In both cases
    the cardinality is even, so the parity bit is `false`.

No `sorry`, no `native_decide`, no `Classical.choose`, no `Exists.choose`,
no `by_contra`. -/

/-- Cardinality of a `Finset.filter` over `Fin d` is even, given that the
    predicate is either empty everywhere or matches exactly a pair
    `{a, a + 1}` with `a + 1 < d`. -/
private lemma card_filter_pair_or_empty_even (d : Nat) (P : Fin d → Prop)
    [DecidablePred P]
    (h : (∀ q, ¬ P q) ∨ ∃ a, a + 1 < d ∧ ∀ q : Fin d,
            P q ↔ (q.val = a ∨ q.val = a + 1)) :
    (Finset.univ.filter P).card % 2 = 0 := by
  rcases h with hempty | ⟨a, had, hPair⟩
  · have : (Finset.univ.filter P).card = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.filter_eq_empty_iff.mpr
      intro q _
      exact hempty q
    rw [this]
  · have : (Finset.univ.filter P).card = 2 := by
      have h_eq : Finset.univ.filter P =
                  Finset.univ.filter fun q : Fin d => q.val = a ∨ q.val = a + 1 := by
        apply Finset.ext; intro q
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hPair q
      rw [h_eq, Finset.card_eq_two]
      refine ⟨⟨a, by omega⟩, ⟨a + 1, had⟩, ?_, ?_⟩
      · intro h
        have := (Fin.mk.injEq _ _ _ _).mp h
        omega
      · ext q
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
                   Finset.mem_singleton]
        constructor
        · rintro (h | h)
          · left; apply Fin.ext; exact h
          · right; apply Fin.ext; exact h
        · rintro (rfl | rfl) <;> simp
    rw [this]

/-- Structural condition: the bulk-X case on row 0.  `decodeStabPauliAt d i 0 col`
    returns `X` (and only then has an X-component) under this condition. -/
private abbrev hasXCol_bulk (d i col : Nat) : Prop :=
  i < (d - 1) * (d - 1) ∧
  (0 = i / (d - 1) ∨ 0 = i / (d - 1) + 1) ∧
  (col = i % (d - 1) ∨ col = i % (d - 1) + 1) ∧
  ¬ (i / (d - 1) + i % (d - 1)) % 2 = 0

/-- Structural condition: the top-X boundary case. -/
private abbrev hasXCol_top (d i col : Nat) : Prop :=
  ¬ i < (d - 1) * (d - 1) ∧
  i - (d - 1) * (d - 1) < (d - 1) / 2 ∧
  (col = 2 * (i - (d - 1) * (d - 1)) ∨ col = 2 * (i - (d - 1) * (d - 1)) + 1)

/-- Structural condition: the degenerate bottom-X corner case (only fires for
    `d = 1`, where it is empty over `Fin 1`). -/
private abbrev hasXCol_botCorner (d i col : Nat) : Prop :=
  ¬ i < (d - 1) * (d - 1) ∧
  ¬ i - (d - 1) * (d - 1) < (d - 1) / 2 ∧
  ¬ i - (d - 1) * (d - 1) < 2 * ((d - 1) / 2) ∧
  ¬ i - (d - 1) * (d - 1) < 3 * ((d - 1) / 2) ∧
  0 = d - 1 ∧
  (col = 2 * (i - (d - 1) * (d - 1) - 3 * ((d - 1) / 2)) + 1 ∨
   col = 2 * (i - (d - 1) * (d - 1) - 3 * ((d - 1) / 2)) + 2)

/-- The X-component of `decodeStabPauliAt d i 0 col` is `true` iff one of the
    three structural conditions above holds.  All other branches of
    `decodeStabPauliAt` return `Z` or `I`, neither of which has an X-component. -/
private lemma decode_row0_X_iff (d i col : Nat) :
    Pauli.hasXComponent (decodeStabPauliAt d i 0 col) = true ↔
    hasXCol_bulk d i col ∨ hasXCol_top d i col ∨ hasXCol_botCorner d i col := by
  unfold decodeStabPauliAt
  simp only
  constructor
  · intro h
    split_ifs at h with hbulk hbsupp hkind hTop hbtsupp hRight hRsupp hLeft hLsupp hBbcond
    all_goals first
      | (left; tauto)
      | (right; left; tauto)
      | (right; right; tauto)
  · intro h
    rcases h with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4, h5, h6⟩
    · rw [if_pos h1, if_pos ⟨h2, h3⟩, if_neg h4]; rfl
    · rw [if_neg h1, if_pos h2, if_pos (⟨trivial, h3⟩ : True ∧ _)]; rfl
    · rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos (⟨h5, h6⟩ : _ ∧ _)]; rfl

/-- The structural conditions on `Fin d` form an empty set or a pair
    `{a, a + 1}` with `a + 1 < d`. -/
private lemma decode_row0_X_pair_or_empty (d : Nat) (hd : 0 < d) (i : Nat) :
    (∀ q : Fin d, ¬ (hasXCol_bulk d i q.val ∨ hasXCol_top d i q.val ∨
                     hasXCol_botCorner d i q.val)) ∨
    ∃ a, a + 1 < d ∧ ∀ q : Fin d,
      (hasXCol_bulk d i q.val ∨ hasXCol_top d i q.val ∨
       hasXCol_botCorner d i q.val) ↔
      (q.val = a ∨ q.val = a + 1) := by
  by_cases hbulk : i < (d - 1) * (d - 1)
  · have hdmone_pos : 0 < d - 1 := by
      rcases Nat.eq_zero_or_pos (d - 1) with h | h
      · exfalso; rw [h, Nat.mul_zero] at hbulk; omega
      · exact h
    by_cases hr0 : (0 : Nat) = i / (d - 1) ∨ 0 = i / (d - 1) + 1
    · by_cases hX : ¬ (i / (d - 1) + i % (d - 1)) % 2 = 0
      · -- bulk X at row 0: pair {c, c+1}
        right
        have hcl : i % (d - 1) < d - 1 := Nat.mod_lt _ hdmone_pos
        refine ⟨i % (d - 1), by omega, ?_⟩
        intro q
        constructor
        · rintro (⟨_, _, hc, _⟩ | ⟨h1, _, _⟩ | ⟨h1, _, _, _, _, _⟩)
          · exact hc
          · exact absurd hbulk h1
          · exact absurd hbulk h1
        · intro hc
          left
          exact ⟨hbulk, hr0, hc, hX⟩
      · -- bulk Z at row 0: no X-component
        push_neg at hX
        left
        intro q
        rintro (⟨_, _, _, h⟩ | ⟨h, _, _⟩ | ⟨h, _, _, _, _, _⟩)
        · exact h hX
        · exact h hbulk
        · exact h hbulk
    · -- bulk with r ≠ 0: support disjoint from row 0
      left
      intro q
      rintro (⟨_, h, _, _⟩ | ⟨h, _, _⟩ | ⟨h, _, _, _, _, _⟩)
      · exact hr0 h
      · exact h hbulk
      · exact h hbulk
  · by_cases hTop : i - (d - 1) * (d - 1) < (d - 1) / 2
    · -- top-X boundary: pair {2b, 2b+1}
      right
      have h2half_le_dm1 : 2 * ((d - 1) / 2) ≤ d - 1 := by
        have := Nat.div_mul_le_self (d - 1) 2
        omega
      have h_bound : 2 * (i - (d - 1) * (d - 1)) + 1 < d := by
        have h2b : 2 * (i - (d - 1) * (d - 1)) < 2 * ((d - 1) / 2) :=
          Nat.mul_lt_mul_left (by decide : 0 < 2) |>.mpr hTop
        omega
      refine ⟨2 * (i - (d - 1) * (d - 1)), h_bound, ?_⟩
      intro q
      constructor
      · rintro (⟨h, _, _, _⟩ | ⟨_, _, hc⟩ | ⟨_, h, _, _, _, _⟩)
        · exact absurd h hbulk
        · exact hc
        · exact absurd hTop h
      · intro hc
        right; left
        exact ⟨hbulk, hTop, hc⟩
    · by_cases hRight : i - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)
      · -- right-Z boundary: no X
        left
        intro q
        rintro (⟨h, _, _, _⟩ | ⟨_, h, _⟩ | ⟨_, _, h, _, _, _⟩)
        · exact absurd h hbulk
        · exact hTop h
        · exact h hRight
      · by_cases hLeft : i - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)
        · -- left-Z boundary: no X
          left
          intro q
          rintro (⟨h, _, _, _⟩ | ⟨_, h, _⟩ | ⟨_, _, _, h, _, _⟩)
          · exact absurd h hbulk
          · exact hTop h
          · exact h hLeft
        · -- bottom-X boundary
          by_cases hd1 : (0 : Nat) = d - 1
          · -- d = 1, support {2k+1, 2k+2} excludes col 0
            left
            intro q
            rintro (⟨h, _, _, _⟩ | ⟨_, h, _⟩ | ⟨_, _, _, _, _, h6⟩)
            · exact absurd h hbulk
            · exact hTop h
            · rcases h6 with h | h <;> omega
          · -- d ≠ 1: corner-only case can't fire
            left
            intro q
            rintro (⟨h, _, _, _⟩ | ⟨_, h, _⟩ | ⟨_, _, _, _, h, _⟩)
            · exact absurd h hbulk
            · exact hTop h
            · exact hd1 h

/-- The row-0 X-component cardinality of `decodeStabPauliAt d i 0 ·` is even. -/
private lemma decode_row0_X_card_even (d : Nat) (hd : 0 < d) (i : Nat) :
    (Finset.univ.filter fun c : Fin d =>
      Pauli.hasXComponent (decodeStabPauliAt d i 0 c.val) = true).card % 2 = 0 := by
  have h_eq : (Finset.univ.filter fun c : Fin d =>
      Pauli.hasXComponent (decodeStabPauliAt d i 0 c.val) = true) =
              Finset.univ.filter fun c : Fin d =>
                hasXCol_bulk d i c.val ∨ hasXCol_top d i c.val ∨
                hasXCol_botCorner d i c.val := by
    apply Finset.ext
    intro q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact decode_row0_X_iff d i q.val
  rw [h_eq]
  exact card_filter_pair_or_empty_even d _ (decode_row0_X_pair_or_empty d hd i)

/-- Bijection between row-0 qubits in `Fin (d * d)` and `Fin d`: the row-0
    X-component cardinality lifts unchanged. -/
private lemma row0_filter_card_eq (d : Nat) (hd : 0 < d) (i : Nat) :
    (Finset.univ.filter fun q : Fin (d * d) =>
      q.val / d = 0 ∧
      Pauli.hasXComponent (decodeStabPauliAt d i 0 q.val) = true).card =
    (Finset.univ.filter fun c : Fin d =>
      Pauli.hasXComponent (decodeStabPauliAt d i 0 c.val) = true).card := by
  apply Finset.card_bij
    (fun (q : Fin (d * d)) (hq : q ∈ _) =>
      (⟨q.val, Nat.lt_of_div_eq_zero hd (Finset.mem_filter.mp hq).2.1⟩ : Fin d))
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    exact hq.2
  · intro q1 _ q2 _ heq
    apply Fin.ext
    exact (Fin.mk.injEq _ _ _ _).mp heq
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    refine ⟨⟨c.val, ?_⟩, ?_, ?_⟩
    · calc c.val < d := c.isLt
        _ ≤ d * d := Nat.le_mul_of_pos_left d hd
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨Nat.div_eq_of_lt c.isLt, hc⟩
    · apply Fin.ext; rfl

/-- **Headline:** the parametric rotated-surface-code stabiliser family at
    distance `d > 0` lies in the normaliser of the parametric logical Z, i.e.
    every generator commutes with `mkSurfaceLogicalZ d`.

    This is the arbitrary-`d` version of `D3Witness.logicalZ_norm`
    (which proved the same fact at `d = 3` by `decide`).

    Proof: reduce parity to counting top-row X-components, then exhibit the
    support (empty or a pair `{c, c + 1}`) by case analysis on the stabiliser
    kind (bulk Z, bulk X, top-X, right-Z, left-Z, bottom-X).
-/
theorem logicalZ_normalizer_parametric (d : Nat) (hd : 0 < d)
    (i : Fin (numStabFormula d)) :
    ErrorVec.parity (mkSurfaceStabilizers d hd i) (mkSurfaceLogicalZ d) = false := by
  -- Step 1: rewrite the parity filter to a row-0-only filter using the
  -- structure of `mkSurfaceLogicalZ`.
  unfold ErrorVec.parity mkSurfaceStabilizers mkSurfaceLogicalZ
  -- Goal: ((Finset.univ.filter ...).card % 2 == 1) = false
  have h_filter_eq :
      (Finset.univ.filter fun q : Fin (d * d) =>
        ErrorVec.Pauli.anticommutes
            (decodeStabPauliAt d i.val (q.val / d) (q.val % d))
            (if q.val / d = 0 then Pauli.Z else Pauli.I) = true) =
      Finset.univ.filter fun q : Fin (d * d) =>
        q.val / d = 0 ∧
        Pauli.hasXComponent (decodeStabPauliAt d i.val 0 q.val) = true := by
    apply Finset.ext
    intro q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hrow : q.val / d = 0
    · -- top-row qubit: q.val < d, anticomm = hasXComponent
      rw [hrow, if_pos rfl]
      rw [Pauli.anticommutes_symm, Pauli.anticommutes_Z_eq_hasXComponent]
      have hqlt : q.val < d := Nat.lt_of_div_eq_zero hd hrow
      have hqv : q.val % d = q.val := Nat.mod_eq_of_lt hqlt
      rw [hqv]
      constructor
      · intro h; exact ⟨rfl, h⟩
      · intro ⟨_, h⟩; exact h
    · -- off-row qubit: logical-Z component is I, anticomm always false
      rw [if_neg hrow]
      have h_anti :
          ErrorVec.Pauli.anticommutes
              (decodeStabPauliAt d i.val (q.val / d) (q.val % d)) Pauli.I = false := by
        cases (decodeStabPauliAt d i.val (q.val / d) (q.val % d)) <;> rfl
      rw [h_anti]
      constructor
      · intro h; exact absurd h (by decide)
      · intro ⟨h, _⟩; exact absurd h hrow
  rw [h_filter_eq, row0_filter_card_eq d hd i.val]
  -- Goal: ((row-0-X-card) % 2 == 1) = false
  have h_even := decode_row0_X_card_even d hd i.val
  rw [h_even]
  decide

/-! ## Parametric `stab_commute`: infrastructure for proving commutation

The headline goal `stab_commute_parametric` is to prove that any two generators
of the parametric stabilizer family `mkSurfaceStabilizers d hd` commute, i.e.
the parity of their pointwise anticommutation pattern is `false`.

The intended signature (to be discharged in a subsequent PerPair phase) is:
```
theorem stab_commute_parametric (d : Nat) (hd : 0 < d) (hodd : d % 2 = 1)
    (i j : Fin (numStabFormula d)) :
    ErrorVec.parity (mkSurfaceStabilizers d hd i) (mkSurfaceStabilizers d hd j) = false
```

The **`hodd : d % 2 = 1`** hypothesis is *essential* and matches the canonical
rotated surface code (odd `d ≥ 3`; standard instances `d = 3, 5, 7`).  At
even `d` the unconstrained statement is *false*: a concrete counterexample
exists at `d = 4`, stabilizers `i = 5` and `j = 10` overlap on exactly one
data cell so their pointwise anticommutation parity is `true`.

This is the parametric version of `D3Witness.stab_commute_d3` (which proved
the same fact at `d = 3` by `decide` over 64 cases) and `D4Witness.stab_commute_d4`
(576 cases by `decide`).  Note that `D4Witness.stab_commute_d4` is honest only
because it operates on the hand-written `SurfaceD4.stabilizers`, *not* on
`mkSurfaceStabilizers 4`; the parametric family at `d = 4` does not have
the commutation property, which is exactly why the parametric headline
requires `hodd`.

### Proof strategy

`decodeStabPauliAt d i row col` always returns a Pauli in `{I, X, Z}`
(never `Y`). Moreover, each stabilizer index `i` has a fixed *type*
`stabType d i ∈ {X, Z}` such that `decode d i row col ∈ {I, stabType d i}`.

* If `stabType d i = stabType d j`, then `anticommutes (decode i q)(decode j q) = false`
  pointwise (X-X, Z-Z, X-I, Z-I, I-anything all commute).  Parity = 0.

* If `stabType d i ≠ stabType d j` (one X, one Z), then anticommutes is true iff
  both Paulis are non-identity, i.e. iff `q ∈ support(i) ∩ support(j)`.
  We then show this intersection has *even* cardinality (always 0 or 2) by
  case-splitting on the kind-pair (Z-bulk × X-bulk, Z-bulk × top-X, etc.). -/

/-- The Pauli **type** of stabilizer `i` at distance `d`: `Z` for Z-bulks
    and side-Z boundaries, `X` for X-bulks and top/bottom-X boundaries.
    Out-of-range indices return `Pauli.I` (never reached in `Fin (numStabFormula d)`). -/
def stabType (d i : Nat) : Pauli :=
  let dm1 := d - 1
  let bulkCount := dm1 * dm1
  if i < bulkCount then
    let r := i / dm1
    let c := i % dm1
    if (r + c) % 2 = 0 then Pauli.Z else Pauli.X
  else
    let b := i - bulkCount
    let half := dm1 / 2
    if b < half then Pauli.X
    else if b < 2 * half then Pauli.Z
    else if b < 3 * half then Pauli.Z
    else Pauli.X

/-- Every value `decodeStabPauliAt d i row col` returns is either `I` or
    equals `stabType d i`. -/
private lemma decode_eq_I_or_stabType (d i row col : Nat) :
    decodeStabPauliAt d i row col = Pauli.I ∨
    decodeStabPauliAt d i row col = stabType d i := by
  simp only [decodeStabPauliAt, stabType]
  split_ifs with hbulk hbsupp hkind hTop hbtsupp hRight hRsupp hLeft hLsupp hBot
  all_goals first | (left; rfl) | (right; rfl)

/-- Convenience: `anticommutes` of two `{I, X, Z}` values whose `stabType`s are
    *equal* is always `false`.  Concretely, all four combinations
    (I-I, I-X, X-I, X-X) and (I-I, I-Z, Z-I, Z-Z) commute. -/
private lemma anticommutes_same_type (a b : Pauli) (t : Pauli) (ht : t = Pauli.X ∨ t = Pauli.Z)
    (ha : a = Pauli.I ∨ a = t) (hb : b = Pauli.I ∨ b = t) :
    ErrorVec.Pauli.anticommutes a b = false := by
  rcases ht with ht | ht <;>
    rcases ha with ha | ha <;>
    rcases hb with hb | hb <;>
    subst ha <;> subst hb <;> subst ht <;> rfl

/-- Convenience: `anticommutes` of `{I, X}` value vs `{I, Z}` value is `true`
    iff both are non-identity. -/
private lemma anticommutes_diff_type_X_Z (a b : Pauli)
    (ha : a = Pauli.I ∨ a = Pauli.X) (hb : b = Pauli.I ∨ b = Pauli.Z) :
    ErrorVec.Pauli.anticommutes a b = true ↔ a = Pauli.X ∧ b = Pauli.Z := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> subst ha <;> subst hb <;>
    simp [ErrorVec.Pauli.anticommutes]

/-- Symmetric version: `{I, Z}` value vs `{I, X}` value. -/
private lemma anticommutes_diff_type_Z_X (a b : Pauli)
    (ha : a = Pauli.I ∨ a = Pauli.Z) (hb : b = Pauli.I ∨ b = Pauli.X) :
    ErrorVec.Pauli.anticommutes a b = true ↔ a = Pauli.Z ∧ b = Pauli.X := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> subst ha <;> subst hb <;>
    simp [ErrorVec.Pauli.anticommutes]

/-- For two stabilizer indices `i, j` whose `stabType d i = stabType d j`,
    the parity of their anticommutation count is `false`. -/
private lemma parity_same_type (d : Nat) (hd : 0 < d)
    (i j : Fin (numStabFormula d))
    (hsame : stabType d i.val = stabType d j.val) :
    ErrorVec.parity (mkSurfaceStabilizers d hd i) (mkSurfaceStabilizers d hd j) = false := by
  unfold ErrorVec.parity mkSurfaceStabilizers
  -- Show the filter is empty.
  have h_empty :
      (Finset.univ.filter fun q : Fin (d * d) =>
        ErrorVec.Pauli.anticommutes
          (decodeStabPauliAt d i.val (q.val / d) (q.val % d))
          (decodeStabPauliAt d j.val (q.val / d) (q.val % d)) = true) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro q _
    intro h
    -- Both decodes are in {I, stabType d i = stabType d j}.
    have hi := decode_eq_I_or_stabType d i.val (q.val / d) (q.val % d)
    have hj := decode_eq_I_or_stabType d j.val (q.val / d) (q.val % d)
    -- Need: stabType d i.val = X ∨ stabType d i.val = Z.
    have ht : stabType d i.val = Pauli.X ∨ stabType d i.val = Pauli.Z := by
      simp only [stabType]
      split_ifs <;> simp
    -- For j, rewrite hj's RHS using hsame.
    have hj' : decodeStabPauliAt d j.val (q.val / d) (q.val % d) = Pauli.I ∨
              decodeStabPauliAt d j.val (q.val / d) (q.val % d) = stabType d i.val := by
      rw [hsame]; exact hj
    have h_false := anticommutes_same_type _ _ (stabType d i.val) ht hi hj'
    rw [h] at h_false
    exact Bool.false_ne_true h_false.symm
  rw [h_empty]
  rfl

/-! ### Support sets and overlap counting for mixed-type pairs

When `stabType d i ≠ stabType d j`, one of `{i, j}` has type `X` and the
other has type `Z`.  The anticommutation count then equals the cardinality of
`support(i) ∩ support(j)`, where `support(k) = {q : decode d k _ _ ≠ I}`.

We define the support as an *abstract grid-coordinate set* by case-analysis on
the stabilizer kind, then prove the overlap count is always 0 or 2. -/

/-- Predicate: position `(row, col)` is in the support of stabilizer `i` at
    distance `d`, i.e. `decodeStabPauliAt d i row col ≠ I`. -/
def inStabSupport (d i row col : Nat) : Prop :=
  decodeStabPauliAt d i row col ≠ Pauli.I

instance (d i row col : Nat) : Decidable (inStabSupport d i row col) := by
  unfold inStabSupport
  infer_instance

/-- Both decodes non-identity iff anticommutes is `true`, when types differ. -/
private lemma anticommutes_iff_both_in_support (d i j row col : Nat)
    (hdiff : stabType d i ≠ stabType d j) :
    ErrorVec.Pauli.anticommutes
        (decodeStabPauliAt d i row col)
        (decodeStabPauliAt d j row col) = true ↔
    inStabSupport d i row col ∧ inStabSupport d j row col := by
  have hi := decode_eq_I_or_stabType d i row col
  have hj := decode_eq_I_or_stabType d j row col
  have hti : stabType d i = Pauli.X ∨ stabType d i = Pauli.Z := by
    simp only [stabType]; split_ifs <;> simp
  have htj : stabType d j = Pauli.X ∨ stabType d j = Pauli.Z := by
    simp only [stabType]; split_ifs <;> simp
  -- The four sub-cases on (stabType d i, stabType d j); two are excluded by hdiff.
  rcases hti with hti | hti <;> rcases htj with htj | htj
  · exact absurd (hti.trans htj.symm) hdiff
  · -- stabType d i = X, stabType d j = Z
    have hi' : decodeStabPauliAt d i row col = Pauli.I ∨
              decodeStabPauliAt d i row col = Pauli.X := by
      rw [hti] at hi; exact hi
    have hj' : decodeStabPauliAt d j row col = Pauli.I ∨
              decodeStabPauliAt d j row col = Pauli.Z := by
      rw [htj] at hj; exact hj
    rw [anticommutes_diff_type_X_Z _ _ hi' hj']
    unfold inStabSupport
    rcases hi' with hi' | hi' <;> rcases hj' with hj' | hj' <;>
      rw [hi', hj'] <;> simp
  · -- stabType d i = Z, stabType d j = X
    have hi' : decodeStabPauliAt d i row col = Pauli.I ∨
              decodeStabPauliAt d i row col = Pauli.Z := by
      rw [hti] at hi; exact hi
    have hj' : decodeStabPauliAt d j row col = Pauli.I ∨
              decodeStabPauliAt d j row col = Pauli.X := by
      rw [htj] at hj; exact hj
    rw [anticommutes_diff_type_Z_X _ _ hi' hj']
    unfold inStabSupport
    rcases hi' with hi' | hi' <;> rcases hj' with hj' | hj' <;>
      rw [hi', hj'] <;> simp
  · exact absurd (hti.trans htj.symm) hdiff

/-! ### Classifying stabilizer kinds

We classify each stabilizer index `i` into one of six abstract "kinds":
* `.bulkZ r c` — bulk Z plaquette at grid coord `(r, c)` (with `r + c` even).
* `.bulkX r c` — bulk X plaquette at grid coord `(r, c)` (with `r + c` odd).
* `.topX b`    — top-X boundary on row 0, cols `(2b, 2b+1)`.
* `.rightZ b`  — right-Z boundary on col `d-1`, rows `(2b, 2b+1)`.
* `.leftZ b`   — left-Z boundary on col `0`, rows `(2b+1, 2b+2)`.
* `.bottomX b` — bottom-X boundary on row `d-1`, cols `(2b+1, 2b+2)`.

The classifier `classifyStab d i : StabKind` reads off the kind from the
index decomposition used inside `decodeStabPauliAt`. -/

inductive StabKind where
  | bulkZ (r c : Nat)
  | bulkX (r c : Nat)
  | topX (b : Nat)
  | rightZ (b : Nat)
  | leftZ (b : Nat)
  | bottomX (b : Nat)

/-- Classify stabilizer index `i` at distance `d`. -/
def classifyStab (d i : Nat) : StabKind :=
  let dm1 := d - 1
  let bulkCount := dm1 * dm1
  if i < bulkCount then
    let r := i / dm1
    let c := i % dm1
    if (r + c) % 2 = 0 then StabKind.bulkZ r c else StabKind.bulkX r c
  else
    let b := i - bulkCount
    let half := dm1 / 2
    if b < half then StabKind.topX b
    else if b < 2 * half then StabKind.rightZ (b - half)
    else if b < 3 * half then StabKind.leftZ (b - 2 * half)
    else StabKind.bottomX (b - 3 * half)

/-- The decode at row, col only depends on `classifyStab d i`: this is the
    *abstract* support predicate `supportByKind`. -/
def supportByKind (d : Nat) (k : StabKind) (row col : Nat) : Bool :=
  match k with
  | .bulkZ r c => decide ((row = r ∨ row = r + 1) ∧ (col = c ∨ col = c + 1))
  | .bulkX r c => decide ((row = r ∨ row = r + 1) ∧ (col = c ∨ col = c + 1))
  | .topX b    => decide (row = 0 ∧ (col = 2 * b ∨ col = 2 * b + 1))
  | .rightZ b  => decide (col = d - 1 ∧ (row = 2 * b ∨ row = 2 * b + 1))
  | .leftZ b   => decide (col = 0 ∧ (row = 2 * b + 1 ∨ row = 2 * b + 2))
  | .bottomX b => decide (row = d - 1 ∧ (col = 2 * b + 1 ∨ col = 2 * b + 2))

/-- The support predicate `inStabSupport d i` agrees with `supportByKind d
    (classifyStab d i)`. -/
lemma inStabSupport_iff_supportByKind (d i row col : Nat) :
    inStabSupport d i row col ↔ supportByKind d (classifyStab d i) row col = true := by
  simp only [inStabSupport, decodeStabPauliAt, classifyStab, supportByKind]
  split_ifs with hbulk hbsupp hkind <;>
    first
    | (simp [hbsupp])
    | (simp; tauto)
    | (simp)
    | tauto

/-- Filter cardinality is even, given that the filter set is either empty
    or a pair of distinct grid coordinates `q1, q2 ∈ Fin (d * d)`. -/
private lemma card_filter_pair_or_empty_even_grid (d : Nat) (P : Fin (d * d) → Prop)
    [DecidablePred P]
    (h : (∀ q, ¬ P q) ∨
         ∃ q1 q2 : Fin (d * d), q1 ≠ q2 ∧
           (∀ q, P q ↔ q = q1 ∨ q = q2)) :
    (Finset.univ.filter P).card % 2 = 0 := by
  rcases h with hempty | ⟨q1, q2, hne, hPair⟩
  · have : (Finset.univ.filter P).card = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.filter_eq_empty_iff.mpr
      intro q _
      exact hempty q
    rw [this]
  · have : (Finset.univ.filter P).card = 2 := by
      have h_eq : Finset.univ.filter P =
                  Finset.univ.filter fun q : Fin (d * d) => q = q1 ∨ q = q2 := by
        apply Finset.ext; intro q
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hPair q
      rw [h_eq, Finset.card_eq_two]
      refine ⟨q1, q2, hne, ?_⟩
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
                 Finset.mem_singleton]
    rw [this]

/-! ### Mixed-type overlap counting

For mixed-type pairs (one stab is X-type, the other Z-type), the parity equals
`|supp(i) ∩ supp(j)| mod 2`.  We show this is always even, in fact `0` or `2`,
by case analysis on the 9 mixed-type kind-pairs.

To keep the proof manageable we work with the **abstract `supportByKind`**
predicate on `(row, col) ∈ Nat × Nat`, then transfer to `Fin (d * d)` qubit
indices via the bijection `(row, col) ↔ d * row + col`. -/

/-- `classifyStab d i` has type X iff `stabType d i = .X`. -/
private lemma classify_type_X (d i : Nat) :
    stabType d i = Pauli.X ↔
      (∃ r c, classifyStab d i = StabKind.bulkX r c) ∨
      (∃ b, classifyStab d i = StabKind.topX b) ∨
      (∃ b, classifyStab d i = StabKind.bottomX b) := by
  simp only [stabType, classifyStab]
  split_ifs with hbulk hkind hTop hRight hLeft <;> simp

/-- `classifyStab d i` has type Z iff `stabType d i = .Z`. -/
private lemma classify_type_Z (d i : Nat) :
    stabType d i = Pauli.Z ↔
      (∃ r c, classifyStab d i = StabKind.bulkZ r c) ∨
      (∃ b, classifyStab d i = StabKind.rightZ b) ∨
      (∃ b, classifyStab d i = StabKind.leftZ b) := by
  simp only [stabType, classifyStab]
  split_ifs with hbulk hkind hTop hRight hLeft <;> simp

/-! ### Factored mixed-type overlap counting (row/col split)

The support `supportByKind d k row col` of every kind is the Cartesian product of
a *row-set* and a *col-set*, each of cardinality `1` or `2`.  The intersection
of two kinds' supports therefore factorises as `(rowOverlap) × (colOverlap)`.

For a *mixed-type* pair, parity (for bulk×bulk) and stagger (for bulk×boundary
and boundary×boundary) preclude the `(rowOverlap, colOverlap) = (1, 1)`
configuration, so the product is always `0`, `2`, or `4` — always even.

We package this as a single lemma `mixed_overlap_card_even`, then combine with
`parity_same_type` to obtain the headline `stab_commute_parametric`. -/

/-- The row-set of a stabilizer kind, as a `Finset Nat` of size `1` or `2`. -/
def kindRowSet (d : Nat) (k : StabKind) : Finset Nat :=
  match k with
  | .bulkZ r _ => {r, r + 1}
  | .bulkX r _ => {r, r + 1}
  | .topX _    => {0}
  | .rightZ b  => {2 * b, 2 * b + 1}
  | .leftZ b   => {2 * b + 1, 2 * b + 2}
  | .bottomX _ => {d - 1}

/-- The col-set of a stabilizer kind, as a `Finset Nat` of size `1` or `2`. -/
def kindColSet (d : Nat) (k : StabKind) : Finset Nat :=
  match k with
  | .bulkZ _ c => {c, c + 1}
  | .bulkX _ c => {c, c + 1}
  | .topX b    => {2 * b, 2 * b + 1}
  | .rightZ _  => {d - 1}
  | .leftZ _   => {0}
  | .bottomX b => {2 * b + 1, 2 * b + 2}

/-- `supportByKind` factorises as `rowSet × colSet`. -/
private lemma supportByKind_iff_rowCol (d : Nat) (k : StabKind) (row col : Nat) :
    supportByKind d k row col = true ↔
    row ∈ kindRowSet d k ∧ col ∈ kindColSet d k := by
  cases k <;>
    simp [supportByKind, kindRowSet, kindColSet, Finset.mem_insert,
          Finset.mem_singleton, And.comm]

/-- Bijection between `Fin (d * d)` and `Finset.range d ×ˢ Finset.range d`
    via `q ↦ (q.val / d, q.val % d)`, used to factor mixed overlap counting.

    Counts qubits whose `(row, col) = (q.val / d, q.val % d)` lies in
    `R ×ˢ C` (intersected with the index range). -/
private lemma card_filter_rowCol (d : Nat) (hd : 0 < d) (R C : Finset Nat) :
    (Finset.univ.filter fun q : Fin (d * d) =>
       q.val / d ∈ R ∧ q.val % d ∈ C).card =
    (R.filter (· < d)).card * (C.filter (· < d)).card := by
  -- Use the explicit bijection: `q ↔ (q.val / d, q.val % d)` for `q.val < d * d`.
  rw [show (R.filter (· < d)).card * (C.filter (· < d)).card =
        ((R.filter (· < d)) ×ˢ (C.filter (· < d))).card from
      (Finset.card_product _ _).symm]
  apply Finset.card_bij
    (fun (q : Fin (d * d)) (_ : q ∈ _) => ((q.val / d, q.val % d) : Nat × Nat))
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    simp only [Finset.mem_product, Finset.mem_filter]
    have hqlt : q.val < d * d := q.isLt
    refine ⟨⟨hq.1, ?_⟩, ⟨hq.2, ?_⟩⟩
    · -- q.val / d < d, given q.val < d * d
      have h1 : q.val / d * d ≤ q.val := Nat.div_mul_le_self q.val d
      rcases Nat.lt_or_ge (q.val / d) d with hlt | hge
      · exact hlt
      · exfalso
        have h2 : d * d ≤ q.val / d * d := Nat.mul_le_mul_right d hge
        omega
    · exact Nat.mod_lt _ hd
  · intro q1 _ q2 _ heq
    apply Fin.ext
    have h1 : q1.val = d * (q1.val / d) + q1.val % d := (Nat.div_add_mod _ _).symm
    have h2 : q2.val = d * (q2.val / d) + q2.val % d := (Nat.div_add_mod _ _).symm
    have hdiv : q1.val / d = q2.val / d := (Prod.mk.inj heq).1
    have hmod : q1.val % d = q2.val % d := (Prod.mk.inj heq).2
    rw [h1, h2, hdiv, hmod]
  · intro ⟨r, c⟩ hrc
    simp only [Finset.mem_product, Finset.mem_filter] at hrc
    obtain ⟨⟨hrR, hrd⟩, hcC, hcd⟩ := hrc
    have h_div : (d * r + c) / d = r := by
      rw [Nat.mul_add_div hd, Nat.div_eq_of_lt hcd, Nat.add_zero]
    have h_mod : (d * r + c) % d = c := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hcd]
    have hlt : d * r + c < d * d := by
      have h2 : d * r + d ≤ d * d := by
        have heq : d * r + d = d * (r + 1) := by
          rw [Nat.mul_add, Nat.mul_one]
        rw [heq]
        exact Nat.mul_le_mul_left d hrd
      omega
    refine ⟨⟨d * r + c, hlt⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_⟩
      · show (d * r + c) / d ∈ R
        rw [h_div]; exact hrR
      · show (d * r + c) % d ∈ C
        rw [h_mod]; exact hcC
    · simp only [Prod.mk.injEq]
      exact ⟨h_div, h_mod⟩

/-- Membership in `(kindRowSet d k).filter (· < d)` for a given `row : Nat`. -/
private lemma mem_rowSet_filter (d : Nat) (k : StabKind) (row : Nat) :
    row ∈ (kindRowSet d k).filter (· < d) ↔ row ∈ kindRowSet d k ∧ row < d := by
  simp [Finset.mem_filter]

/-- Membership in `(kindColSet d k).filter (· < d)` for a given `col : Nat`. -/
private lemma mem_colSet_filter (d : Nat) (k : StabKind) (col : Nat) :
    col ∈ (kindColSet d k).filter (· < d) ↔ col ∈ kindColSet d k ∧ col < d := by
  simp [Finset.mem_filter]

/-- The size of a row-intersection between two kinds is bounded by `2`.
    All `kindRowSet`s are subsets of a 2-element consecutive set. -/
private lemma kindRowSet_card_le_two (d : Nat) (k : StabKind) :
    (kindRowSet d k).card ≤ 2 := by
  cases k <;> simp [kindRowSet]

/-- The size of a col-intersection between two kinds is bounded by `2`. -/
private lemma kindColSet_card_le_two (d : Nat) (k : StabKind) :
    (kindColSet d k).card ≤ 2 := by
  cases k <;> simp [kindColSet]

/-- Bound on the row-intersection of two kinds. -/
private lemma row_inter_card_le_two (d : Nat) (ki kj : StabKind) :
    ((kindRowSet d ki ∩ kindRowSet d kj).filter (· < d)).card ≤ 2 := by
  have h1 : ((kindRowSet d ki ∩ kindRowSet d kj).filter (· < d)).card ≤
              (kindRowSet d ki ∩ kindRowSet d kj).card :=
    Finset.card_filter_le _ _
  have h2 : (kindRowSet d ki ∩ kindRowSet d kj).card ≤ (kindRowSet d ki).card :=
    Finset.card_le_card (Finset.inter_subset_left)
  exact h1.trans (h2.trans (kindRowSet_card_le_two d ki))

/-- Bound on the col-intersection of two kinds. -/
private lemma col_inter_card_le_two (d : Nat) (ki kj : StabKind) :
    ((kindColSet d ki ∩ kindColSet d kj).filter (· < d)).card ≤ 2 := by
  have h1 : ((kindColSet d ki ∩ kindColSet d kj).filter (· < d)).card ≤
              (kindColSet d ki ∩ kindColSet d kj).card :=
    Finset.card_filter_le _ _
  have h2 : (kindColSet d ki ∩ kindColSet d kj).card ≤ (kindColSet d ki).card :=
    Finset.card_le_card (Finset.inter_subset_left)
  exact h1.trans (h2.trans (kindColSet_card_le_two d ki))

/-- If `a, b ≤ 2` and we never have `a = 1 ∧ b = 1`, then `a * b` is even.
    This is the abstract combinatorial heart of the mixed-overlap lemma:
    a product of two size-≤-2 cardinalities is even unless both are exactly `1`. -/
private lemma mul_even_of_not_both_one (a b : Nat) (ha : a ≤ 2) (hb : b ≤ 2)
    (h : ¬ (a = 1 ∧ b = 1)) : (a * b) % 2 = 0 := by
  -- a ∈ {0, 1, 2} and b ∈ {0, 1, 2}; enumerate by `omega` after the
  -- hypothesis `¬ (a = 1 ∧ b = 1)` rules out the lone odd product (1 * 1 = 1).
  have ha0 : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  have hb0 : b = 0 ∨ b = 1 ∨ b = 2 := by omega
  rcases ha0 with ha | ha | ha <;> rcases hb0 with hb | hb | hb <;>
    subst ha <;> subst hb <;> simp_all

/-- The shared-support filter for two stabilizers `i, j` (parametric form),
    expressed as a product of row-intersection and col-intersection sizes.

    The bijection `Fin (d * d) ↔ {(row, col) | row < d ∧ col < d}` is used to
    factor the count along the row and col axes. -/
private lemma shared_support_card_factors (d : Nat) (hd : 0 < d)
    (i j : Nat) :
    (Finset.univ.filter fun q : Fin (d * d) =>
        inStabSupport d i (q.val / d) (q.val % d) ∧
        inStabSupport d j (q.val / d) (q.val % d)).card =
    ((kindRowSet d (classifyStab d i) ∩ kindRowSet d (classifyStab d j)).filter
        (· < d)).card *
    ((kindColSet d (classifyStab d i) ∩ kindColSet d (classifyStab d j)).filter
        (· < d)).card := by
  have h_iff : ∀ q : Fin (d * d),
      (inStabSupport d i (q.val / d) (q.val % d) ∧
       inStabSupport d j (q.val / d) (q.val % d)) ↔
      ((q.val / d ∈ kindRowSet d (classifyStab d i) ∧
        q.val / d ∈ kindRowSet d (classifyStab d j)) ∧
       (q.val % d ∈ kindColSet d (classifyStab d i) ∧
        q.val % d ∈ kindColSet d (classifyStab d j))) := by
    intro q
    rw [inStabSupport_iff_supportByKind, inStabSupport_iff_supportByKind,
        supportByKind_iff_rowCol, supportByKind_iff_rowCol]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨h1, h3⟩, h2, h4⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨h1, h3⟩, h2, h4⟩
  have h_filter_eq :
      (Finset.univ.filter fun q : Fin (d * d) =>
          inStabSupport d i (q.val / d) (q.val % d) ∧
          inStabSupport d j (q.val / d) (q.val % d)) =
      (Finset.univ.filter fun q : Fin (d * d) =>
          q.val / d ∈ (kindRowSet d (classifyStab d i) ∩ kindRowSet d (classifyStab d j)) ∧
          q.val % d ∈ (kindColSet d (classifyStab d i) ∩ kindColSet d (classifyStab d j))) := by
    apply Finset.ext; intro q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
    exact h_iff q
  rw [h_filter_eq, card_filter_rowCol d hd]

/-! ### Inspection `#eval`s and per-d sanity checks

The parametric `stabType` and `classifyStab` reduce to closed literals
at every fixed `d`.  -/

-- d = 3: stab 0 = bulk Z, stab 1 = bulk X, stab 4 = top-X boundary.
#eval stabType 3 0           -- Pauli.Z (bulk Z at (0,0))
#eval stabType 3 1           -- Pauli.X (bulk X at (0,1))
#eval stabType 3 4           -- Pauli.X (top-X boundary)
#eval stabType 3 5           -- Pauli.Z (right-Z boundary)
#eval stabType 3 6           -- Pauli.Z (left-Z boundary)
#eval stabType 3 7           -- Pauli.X (bottom-X boundary)

-- d = 5, 7: parametric classification fires correctly.
#eval classifyStab 5 16      -- topX 0   (bulkCount = 16, b = 0, half = 2)
#eval classifyStab 7 36      -- topX 0   (bulkCount = 36, b = 0, half = 3)

/-! ### Status of the parametric stab_commute proof

This file establishes the **infrastructure** needed for the parametric
`stab_commute` theorem:

* `stabType d i : Pauli` — the (X or Z) type of stabilizer `i` at distance `d`.
* `decode_eq_I_or_stabType` — every `decode i row col` is `I` or `stabType d i`.
* `parity_same_type` — pairs of same-type stabs commute (parity = false).
* `anticommutes_iff_both_in_support` — for mixed-type pairs, anticommutes
  reduces to "both qubits in support".
* `classifyStab d i : StabKind` — geometric kind: bulkZ/X, top/bottom/left/right.
* `supportByKind` and `inStabSupport_iff_supportByKind` — abstract support.
* `card_filter_pair_or_empty_even_grid` — 0-or-2 cardinality → even.

The remaining mathematical content for the full headline
`stab_commute_parametric : ∀ (d) (hd : 0 < d) (hodd : d % 2 = 1) i j,
    parity (mkStab i) (mkStab j) = false`
is the geometric **overlap-counting** for the **9 mixed-type kind-pairs**:

  bulkZ × bulkX, bulkZ × topX, bulkZ × bottomX,
  rightZ × bulkX, rightZ × topX, rightZ × bottomX,
  leftZ × bulkX, leftZ × topX, leftZ × bottomX.

For each pair, the support intersection must be shown to have cardinality
`0` or `2` (always even); the geometric proof uses the parities of `r + c`
(bulkZ has even, bulkX has odd) and the staggered placement
`b < (d-1)/2` of the boundary blocks.  The **`hodd : d % 2 = 1`** hypothesis
threads through the boundary case-splits: at odd `d` the half-block count
`(d - 1) / 2 = (d - 1) / 2` cleanly partitions the `2 · (d - 1)` boundary
indices, while at even `d` the bottom-X / top-X staggers can collide on a
single cell (the `d = 4`, `i = 5`, `j = 10` counterexample).  Each case
requires ~50 LOC of `omega` + `Finset.card_eq_zero`/`Finset.card_eq_two`
reasoning; the total ~500 LOC mixed-pair-counting development is outside
the scope of this infrastructure layer.

For d = 3 and d = 4 there are existing `decide`-based proofs
(`D3Witness.stab_commute_d3` at `SurfaceGeneral.lean:1096`,
`D4Witness.stab_commute_d4` at `SurfaceGeneral.lean:1189`).  Those proofs
operate on the *hand-written* `SurfaceD3.stabilizers` /
`SurfaceD4.stabilizers`, which are not bound by the parametric encoding;
that is why `D4Witness.stab_commute_d4` succeeds even though the
parametric `stab_commute_parametric` at `d = 4` is false.

The infrastructure above is what a future PerPair workflow will consume to
discharge `stab_commute_parametric` for arbitrary odd `d ≥ 3`. -/

/-! ## Per-pair overlap lemmas and the headline `stab_commute_parametric`

We now discharge the 9 mixed-type kind-pairs and assemble the headline.

### Strategy

Each per-pair lemma proves
```
¬ ((kindRowSet d ki ∩ kindRowSet d kj).card = 1 ∧
   (kindColSet d ki ∩ kindColSet d kj).card = 1)
```

(under the appropriate bounds on `r, c, b` and parity / oddness hypotheses).

Combined with `row_inter_card_le_two`, `col_inter_card_le_two`, and
`mul_even_of_not_both_one`, this shows the shared-support count is even,
hence the parity is `false`.

### Small helpers used by the per-pair proofs -/

/-- Intersection of two 2-element consecutive sets `{a, a+1}` and `{b, b+1}`
    has cardinality `1` iff the pairs are adjacent (sharing exactly one
    endpoint), i.e., `a + 1 = b` or `b + 1 = a`. -/
private lemma inter_consec_pair_card_one (a b : Nat)
    (h : ({a, a+1} ∩ ({b, b+1} : Finset Nat)).card = 1) :
    a + 1 = b ∨ b + 1 = a := by
  by_cases hA : a ∈ ({b, b+1} : Finset Nat) <;>
    by_cases hB : a + 1 ∈ ({b, b+1} : Finset Nat)
  · -- Both `a, a+1 ∈ {b, b+1}`: intersection equals `{a, a+1}`, card = 2.
    have heq : ({a, a+1} ∩ ({b, b+1} : Finset Nat)) = ({a, a+1} : Finset Nat) := by
      ext x
      refine ⟨fun hx => (Finset.mem_inter.mp hx).1, ?_⟩
      intro hx
      refine Finset.mem_inter.mpr ⟨hx, ?_⟩
      rcases Finset.mem_insert.mp hx with rfl | hx2
      · exact hA
      · rcases Finset.mem_singleton.mp hx2 with rfl
        exact hB
    rw [heq] at h
    have hne : a ≠ a + 1 := by omega
    rw [Finset.card_insert_of_notMem (by simp [hne])] at h
    simp at h
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hA hB; omega
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hA hB; omega
  · -- Neither in: intersection empty, card = 0.
    have hempty : ({a, a+1} ∩ ({b, b+1} : Finset Nat)) = (∅ : Finset Nat) := by
      ext x
      simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
      intro hx1 hx2
      rcases Finset.mem_insert.mp hx1 with rfl | hx1'
      · exact hA hx2
      · rcases Finset.mem_singleton.mp hx1' with rfl
        exact hB hx2
    rw [hempty] at h; simp at h

/-- Intersection of singleton `{x}` and pair `{a, a+1}` has cardinality `1` iff
    `x = a` or `x = a + 1`. -/
private lemma inter_singleton_pair_card_one (x a : Nat)
    (h : (({x} : Finset Nat) ∩ {a, a+1}).card = 1) : x = a ∨ x = a + 1 := by
  by_cases hxa : x = a
  · left; exact hxa
  · by_cases hxa1 : x = a + 1
    · right; exact hxa1
    · -- Empty intersection: contradiction with `card = 1`.
      have hempty : (({x} : Finset Nat) ∩ {a, a+1}) = (∅ : Finset Nat) := by
        ext y
        simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
        intro hy1 hy2
        rcases Finset.mem_singleton.mp hy1 with rfl
        rcases Finset.mem_insert.mp hy2 with rfl | hy2'
        · exact hxa rfl
        · rcases Finset.mem_singleton.mp hy2' with rfl
          exact hxa1 rfl
      rw [hempty] at h; simp at h

/-- Intersection of pair `{a, a+1}` and singleton `{x}` has cardinality `1` iff
    `x = a` or `x = a + 1`. (Symmetric form.) -/
private lemma inter_pair_singleton_card_one (a x : Nat)
    (h : (({a, a+1} : Finset Nat) ∩ {x}).card = 1) : x = a ∨ x = a + 1 := by
  rw [Finset.inter_comm] at h
  exact inter_singleton_pair_card_one x a h

/-! ### The 9 mixed-type kind-pair overlap lemmas

Each lemma proves that the geometric overlap of a Z-type kind and an X-type
kind cannot have row-overlap `= 1` AND col-overlap `= 1` simultaneously,
ruling out the lone odd-product case `1 * 1 = 1`.

The lemmas are stated in *kind-direct* form: they take the constructor
arguments and bounds directly, not the stabilizer index. The headline below
bridges from `classifyStab` to these inputs. -/

/-- **Pair 1: bulkZ × bulkX.** The bulkZ stabilizer at grid `(rz, cz)` with
    `rz + cz` even and the bulkX stabilizer at `(rx, cx)` with `rx + cx` odd
    cannot share a single-cell row-AND-col overlap.

    Geometry: row-overlap `= 1` forces `rz = rx ± 1`; col-overlap `= 1`
    forces `cz = cx ± 1`. Combined, `(rz + cz) − (rx + cx) ∈ {−2, 0, +2}` is
    even, contradicting the parity mismatch `even − odd = odd`. -/
private lemma mixed_overlap_bulkZ_bulkX (d : Nat)
    (rz cz rx cx : Nat)
    (hZ : (rz + cz) % 2 = 0) (hX : (rx + cx) % 2 = 1) :
    ¬ ((kindRowSet d (.bulkZ rz cz) ∩ kindRowSet d (.bulkX rx cx)).card = 1 ∧
       (kindColSet d (.bulkZ rz cz) ∩ kindColSet d (.bulkX rx cx)).card = 1) := by
  intro ⟨hrow, hcol⟩
  -- Unfold to consecutive pairs.
  have hrow' : ({rz, rz + 1} ∩ ({rx, rx + 1} : Finset Nat)).card = 1 := hrow
  have hcol' : ({cz, cz + 1} ∩ ({cx, cx + 1} : Finset Nat)).card = 1 := hcol
  have hr := inter_consec_pair_card_one _ _ hrow'
  have hc := inter_consec_pair_card_one _ _ hcol'
  rcases hr with hr | hr <;> rcases hc with hc | hc <;> omega

/-- **Pair 2: bulkZ × topX.** The bulkZ stabilizer at `(rz, cz)` and the
    top-X boundary at block `b` (row 0, cols `(2b, 2b+1)`) cannot share a
    single-cell row-AND-col overlap.

    Geometry: row-overlap `= 1` against the singleton `{0}` forces `rz = 0`
    (since `rz + 1 ≠ 0`). Col-overlap `= 1` between consecutive pairs gives
    `cz ∈ {2b, 2b + 2}`. Parity `rz + cz` even with `rz = 0` requires `cz`
    even; both options `2b, 2b+2` are even, so the parity check passes — but
    we then need an additional constraint. Specifically: col-overlap `= 1`
    actually classifies as `cz + 1 = 2b ∨ 2b + 1 = cz`, giving `cz ∈
    {2b − 1, 2b + 1}`, both odd. Contradiction with `cz` even. -/
private lemma mixed_overlap_bulkZ_topX (d : Nat)
    (rz cz b : Nat)
    (hZ : (rz + cz) % 2 = 0) :
    ¬ ((kindRowSet d (.bulkZ rz cz) ∩ kindRowSet d (.topX b)).card = 1 ∧
       (kindColSet d (.bulkZ rz cz) ∩ kindColSet d (.topX b)).card = 1) := by
  intro ⟨hrow, hcol⟩
  -- Row: {rz, rz+1} ∩ {0}.
  have hrow' : (({rz, rz + 1} : Finset Nat) ∩ {0}).card = 1 := hrow
  have hr := inter_pair_singleton_card_one rz 0 hrow'
  -- 0 = rz ∨ 0 = rz + 1; latter impossible.
  have hrz : rz = 0 := by omega
  subst hrz
  -- Col: {cz, cz+1} ∩ {2b, 2b+1}. Apply inter_consec_pair_card_one.
  have hcol' : (({cz, cz + 1} : Finset Nat) ∩ {2 * b, 2 * b + 1}).card = 1 := hcol
  have hc := inter_consec_pair_card_one _ _ hcol'
  -- Cases: cz + 1 = 2b ∨ 2b + 1 = cz.
  -- Both make cz odd (cz = 2b−1 or cz = 2b+1), contradicting the parity
  -- constraint `0 + cz` even.
  have hcz_even : cz % 2 = 0 := by simpa using hZ
  rcases hc with hc | hc <;> omega

/-- **Pair 3: bulkZ × bottomX.** The bulkZ stabilizer at `(rz, cz)` and the
    bottom-X boundary at block `b` (row `d−1`, cols `(2b+1, 2b+2)`) cannot
    share a single-cell row-AND-col overlap, given `hodd : d % 2 = 1` and
    the bulkZ bound `rz + 1 < d`.

    Geometry: row-overlap `= 1` against `{d − 1}` forces `rz = d − 1` (ruled
    out by the bound) or `rz + 1 = d − 1`, i.e., `rz = d − 2`. Col-overlap
    `= 1` gives `cz ∈ {2b, 2b + 2}`, both even. Parity `(d − 2) + cz` even
    with `d` odd requires `cz` odd. Contradiction. -/
private lemma mixed_overlap_bulkZ_bottomX (d : Nat) (hodd : d % 2 = 1)
    (rz cz b : Nat)
    (hrz : rz + 1 < d) (hZ : (rz + cz) % 2 = 0) :
    ¬ ((kindRowSet d (.bulkZ rz cz) ∩ kindRowSet d (.bottomX b)).card = 1 ∧
       (kindColSet d (.bulkZ rz cz) ∩ kindColSet d (.bottomX b)).card = 1) := by
  intro ⟨hrow, hcol⟩
  -- Row: {rz, rz+1} ∩ {d-1}.
  have hrow' : (({rz, rz + 1} : Finset Nat) ∩ {d - 1}).card = 1 := hrow
  have hr := inter_pair_singleton_card_one rz (d - 1) hrow'
  -- d - 1 = rz (ruled out by hrz) ∨ d - 1 = rz + 1.
  have hrz2 : rz + 1 = d - 1 := by omega
  -- Col: {cz, cz+1} ∩ {2b+1, 2b+2}.
  have hcol' : (({cz, cz + 1} : Finset Nat) ∩ {2 * b + 1, 2 * b + 1 + 1}).card = 1 := hcol
  have hc := inter_consec_pair_card_one _ _ hcol'
  -- cz + 1 = 2b + 1 (i.e., cz = 2b) ∨ 2b + 2 = cz (i.e., cz = 2b + 2). Both even.
  -- Parity: rz + cz = (d - 2) + cz even, with d odd → d - 2 odd → cz odd.
  -- Contradiction.
  rcases hc with hc | hc <;> omega

/-- **Pair 4: rightZ × bulkX.** The right-Z boundary at block `b` (col `d−1`,
    rows `(2b, 2b+1)`) and bulkX at `(rx, cx)` cannot share a single-cell
    row-AND-col overlap, given `hodd : d % 2 = 1` and the bulkX bound
    `cx + 1 < d`.

    Geometry: col-overlap `= 1` against `{d − 1}` forces `cx = d − 1` (ruled
    out by `cx + 1 < d`) or `cx + 1 = d − 1`, i.e., `cx = d − 2`. Row-overlap
    `= 1` gives `rx ∈ {2b − 1, 2b + 1}`, both odd. Parity `rx + cx` odd with
    `cx = d − 2` odd (since `d` odd) requires `rx` even. Contradiction. -/
private lemma mixed_overlap_rightZ_bulkX (d : Nat) (hodd : d % 2 = 1)
    (b rx cx : Nat)
    (hcx : cx + 1 < d) (hX : (rx + cx) % 2 = 1) :
    ¬ ((kindRowSet d (.rightZ b) ∩ kindRowSet d (.bulkX rx cx)).card = 1 ∧
       (kindColSet d (.rightZ b) ∩ kindColSet d (.bulkX rx cx)).card = 1) := by
  intro ⟨hrow, hcol⟩
  -- Col: {d-1} ∩ {cx, cx+1}.
  have hcol' : ((({d - 1} : Finset Nat)) ∩ {cx, cx + 1}).card = 1 := hcol
  have hc := inter_singleton_pair_card_one (d - 1) cx hcol'
  -- d - 1 = cx (ruled out by hcx) ∨ d - 1 = cx + 1.
  have hcx2 : cx + 1 = d - 1 := by omega
  -- Row: {2b, 2b+1} ∩ {rx, rx+1}.
  have hrow' : (({2 * b, 2 * b + 1} : Finset Nat) ∩ {rx, rx + 1}).card = 1 := hrow
  have hr := inter_consec_pair_card_one _ _ hrow'
  -- 2b + 1 = rx ∨ rx + 1 = 2b. So rx = 2b + 1 or rx = 2b - 1, both odd.
  -- Parity: rx + cx = rx + (d - 2). d odd → d - 2 odd → rx even.
  -- Contradiction: rx both odd (from hr) and even (from parity).
  rcases hr with hr | hr <;> omega

/-- **Pair 5: rightZ × topX.** The right-Z boundary at block `bz` and the
    top-X boundary at block `bx` cannot share a single-cell row-AND-col
    overlap, given `hodd : d % 2 = 1` and the topX bound `bx < (d−1)/2`.

    Geometry: row-overlap `= 1` against `{0}` (topX's rowSet) forces
    `2*bz + 1 = 0` (impossible) or `2*bz = 0`, i.e., `bz = 0`. Col-overlap
    `= 1` against `{d − 1}` (rightZ's colSet) forces `d − 1 = 2*bx` or
    `d − 1 = 2*bx + 1`. `d` odd → `d − 1` even → second case impossible. So
    `d − 1 = 2*bx`, i.e., `bx = (d−1)/2`. But `bx < (d−1)/2`. Contradiction. -/
private lemma mixed_overlap_rightZ_topX (d : Nat) (hodd : d % 2 = 1)
    (bz bx : Nat)
    (hbx : bx < (d - 1) / 2) :
    ¬ ((kindRowSet d (.rightZ bz) ∩ kindRowSet d (.topX bx)).card = 1 ∧
       (kindColSet d (.rightZ bz) ∩ kindColSet d (.topX bx)).card = 1) := by
  intro ⟨hrow, hcol⟩
  -- Row: {2bz, 2bz+1} ∩ {0}.
  have hrow' : (({2 * bz, 2 * bz + 1} : Finset Nat) ∩ {0}).card = 1 := hrow
  have hr := inter_pair_singleton_card_one (2 * bz) 0 hrow'
  -- Col: {d-1} ∩ {2bx, 2bx+1}.
  have hcol' : ((({d - 1} : Finset Nat)) ∩ {2 * bx, 2 * bx + 1}).card = 1 := hcol
  have hc := inter_singleton_pair_card_one (d - 1) (2 * bx) hcol'
  -- d - 1 = 2bx or d - 1 = 2bx + 1. Latter: d-1 odd → d even → contradicts hodd.
  -- Former: d - 1 = 2bx, so bx = (d-1)/2; but bx < (d-1)/2. Contradiction.
  -- Both ruled out by omega using hodd, hbx.
  have hdpos : 0 < d := by omega
  rcases hc with hc | hc <;> omega

/-- **Pair 6: rightZ × bottomX.** The right-Z boundary at block `bz` and the
    bottom-X boundary at block `bx` cannot share a single-cell row-AND-col
    overlap, given `hodd : d % 2 = 1` and the rightZ bound `bz < (d−1)/2`.

    Geometry: row-overlap `= 1` against `{d − 1}` forces `d − 1 = 2*bz` or
    `d − 1 = 2*bz + 1`. `d` odd → `d − 1` even → second case impossible. So
    `d − 1 = 2*bz`, i.e., `bz = (d−1)/2`. But `bz < (d−1)/2`. Contradiction. -/
private lemma mixed_overlap_rightZ_bottomX (d : Nat) (hodd : d % 2 = 1)
    (bz bx : Nat)
    (hbz : bz < (d - 1) / 2) :
    ¬ ((kindRowSet d (.rightZ bz) ∩ kindRowSet d (.bottomX bx)).card = 1 ∧
       (kindColSet d (.rightZ bz) ∩ kindColSet d (.bottomX bx)).card = 1) := by
  intro ⟨hrow, hcol⟩
  -- Row: {2bz, 2bz+1} ∩ {d-1}.
  have hrow' : (({2 * bz, 2 * bz + 1} : Finset Nat) ∩ {d - 1}).card = 1 := hrow
  have hr := inter_pair_singleton_card_one (2 * bz) (d - 1) hrow'
  -- d - 1 = 2bz (so bz = (d-1)/2, contradicts hbz)
  -- or d - 1 = 2bz + 1 (d - 1 odd, contradicts hodd → d - 1 even).
  have hdpos : 0 < d := by omega
  rcases hr with hr | hr <;> omega

/-- **Pair 7: leftZ × bulkX.** The left-Z boundary at block `b` (col `0`,
    rows `(2b+1, 2b+2)`) and bulkX at `(rx, cx)` cannot share a single-cell
    row-AND-col overlap.

    Geometry: col-overlap `= 1` against `{0}` forces `cx = 0` (since
    `cx + 1 ≠ 0`). Row-overlap `= 1` gives `rx ∈ {2b, 2b + 2}` (from the
    helper: `2b + 2 = rx ∨ rx + 1 = 2b + 1`, i.e., `rx = 2b + 2 ∨ rx = 2b`).
    Both even. Parity `rx + cx = rx` odd. Contradiction. -/
private lemma mixed_overlap_leftZ_bulkX (d : Nat)
    (b rx cx : Nat)
    (hX : (rx + cx) % 2 = 1) :
    ¬ ((kindRowSet d (.leftZ b) ∩ kindRowSet d (.bulkX rx cx)).card = 1 ∧
       (kindColSet d (.leftZ b) ∩ kindColSet d (.bulkX rx cx)).card = 1) := by
  intro ⟨hrow, hcol⟩
  -- Col: {0} ∩ {cx, cx+1}.
  have hcol' : ((({0} : Finset Nat)) ∩ {cx, cx + 1}).card = 1 := hcol
  have hc := inter_singleton_pair_card_one 0 cx hcol'
  -- 0 = cx ∨ 0 = cx + 1. Latter impossible.
  have hcx : cx = 0 := by omega
  subst hcx
  -- Row: {2b+1, 2b+2} ∩ {rx, rx+1} = ({2b+1, (2b+1)+1} ∩ {rx, rx+1}).
  have hrow' : (({2 * b + 1, 2 * b + 1 + 1} : Finset Nat) ∩ {rx, rx + 1}).card = 1 := hrow
  have hr := inter_consec_pair_card_one _ _ hrow'
  -- 2b + 2 = rx ∨ rx + 1 = 2b + 1. So rx = 2b + 2 or rx = 2b. Both even.
  -- Parity: rx + 0 = rx odd. Contradiction.
  rcases hr with hr | hr <;> omega

/-- **Pair 8: leftZ × topX.** The left-Z boundary at block `bz` and the
    top-X boundary at block `bx` cannot share a single-cell row-AND-col
    overlap (no parity needed).

    Geometry: row-overlap `= 1` against `{0}` (topX's rowSet) is impossible
    because leftZ's rowSet `{2*bz + 1, 2*bz + 2}` never contains `0`
    (both elements are ≥ 1). The intersection is empty, contradicting
    `card = 1`. -/
private lemma mixed_overlap_leftZ_topX (d : Nat)
    (bz bx : Nat) :
    ¬ ((kindRowSet d (.leftZ bz) ∩ kindRowSet d (.topX bx)).card = 1 ∧
       (kindColSet d (.leftZ bz) ∩ kindColSet d (.topX bx)).card = 1) := by
  intro ⟨hrow, _hcol⟩
  -- Row: {2bz+1, 2bz+2} ∩ {0}.
  have hrow' : (({2 * bz + 1, 2 * bz + 1 + 1} : Finset Nat) ∩ {0}).card = 1 := hrow
  have hr := inter_pair_singleton_card_one (2 * bz + 1) 0 hrow'
  -- 0 = 2bz + 1 ∨ 0 = 2bz + 2; both impossible over `Nat`.
  omega

/-- **Pair 9: leftZ × bottomX.** The left-Z boundary at block `bz` and the
    bottom-X boundary at block `bx` cannot share a single-cell row-AND-col
    overlap.

    Geometry: col-overlap `= 1` against `{0}` (leftZ's colSet) is impossible
    because bottomX's colSet `{2*bx + 1, 2*bx + 2}` never contains `0`
    (both elements are ≥ 1). The intersection is empty, contradicting
    `card = 1`. -/
private lemma mixed_overlap_leftZ_bottomX (d : Nat)
    (bz bx : Nat) :
    ¬ ((kindRowSet d (.leftZ bz) ∩ kindRowSet d (.bottomX bx)).card = 1 ∧
       (kindColSet d (.leftZ bz) ∩ kindColSet d (.bottomX bx)).card = 1) := by
  intro ⟨_hrow, hcol⟩
  -- Col: {0} ∩ {2bx+1, 2bx+2}.
  have hcol' : ((({0} : Finset Nat)) ∩ {2 * bx + 1, 2 * bx + 1 + 1}).card = 1 := hcol
  have hc := inter_singleton_pair_card_one 0 (2 * bx + 1) hcol'
  -- 0 = 2bx + 1 ∨ 0 = 2bx + 2; both impossible.
  omega

/-! ### Kind-bounds extracted from `classifyStab` matches

For each Z-kind / X-kind branch, the classifier guarantees specific
constraints on the constructor arguments (boundedness, parity). The bounds
flow directly from the definition of `classifyStab`. -/

/-- If `classifyStab d i = bulkZ r c`, then `r + 1 < d`, `c + 1 < d`, and
    `(r + c) % 2 = 0`. -/
private lemma classifyStab_bulkZ_bounds (d i r c : Nat)
    (h : classifyStab d i = .bulkZ r c) :
    r + 1 < d ∧ c + 1 < d ∧ (r + c) % 2 = 0 := by
  simp only [classifyStab] at h
  split_ifs at h with hbulk hpar
  -- Only one surviving case: bulk + parity-even = bulkZ.
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

/-- If `classifyStab d i = bulkX r c`, then `r + 1 < d`, `c + 1 < d`, and
    `(r + c) % 2 = 1`. -/
private lemma classifyStab_bulkX_bounds (d i r c : Nat)
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

/-- If `classifyStab d i = topX b`, then `b < (d - 1) / 2`. -/
private lemma classifyStab_topX_bounds (d i b : Nat)
    (h : classifyStab d i = .topX b) :
    b < (d - 1) / 2 := by
  simp only [classifyStab] at h
  split_ifs at h with hbulk hpar hTop
  injection h with heq
  subst heq
  exact hTop

/-- If `classifyStab d i = rightZ b`, then `b < (d - 1) / 2`. -/
private lemma classifyStab_rightZ_bounds (d i b : Nat)
    (h : classifyStab d i = .rightZ b) :
    b < (d - 1) / 2 := by
  simp only [classifyStab] at h
  split_ifs at h with hbulk hpar hTop hRight
  injection h with heq
  subst heq
  omega

/-- If `classifyStab d i = leftZ b`, then `b < (d - 1) / 2`. -/
private lemma classifyStab_leftZ_bounds (d i b : Nat)
    (h : classifyStab d i = .leftZ b) :
    b < (d - 1) / 2 := by
  simp only [classifyStab] at h
  split_ifs at h with hbulk hpar hTop hRight hLeft
  injection h with heq
  subst heq
  omega

/-- If `classifyStab d i = bottomX b` for an `i < numStabFormula d` at *odd*
    `d ≥ 3`, then `b < (d - 1) / 2`.

    At `d = 1` this is vacuously false (the single stab classifies as
    `bottomX 0` but `(1 - 1)/2 = 0`); however at `d = 1` the headline trivially
    reduces to the same-type case (only one stab) and never enters this
    branch.  We therefore additionally take `2 ≤ d` to rule out the d=1 case. -/
private lemma classifyStab_bottomX_bounds (d i b : Nat) (hodd : d % 2 = 1)
    (hi : i < (d - 1) * (d - 1) + 2 * (d - 1))
    (h : classifyStab d i = .bottomX b) :
    b < (d - 1) / 2 := by
  simp only [classifyStab] at h
  split_ifs at h with hbulk hpar hTop hRight hLeft
  injection h with heq
  subst heq
  -- At odd `d`, `(d - 1) % 2 = 0`, so `2 * ((d - 1) / 2) = d - 1` and
  -- `4 * ((d - 1) / 2) = 2 * (d - 1)`. With i < bulkCount + 2*(d-1)
  -- and ¬ (i - bulkCount < 3 * half), we get i - bulkCount - 3*half < half.
  have hmod : (d - 1) % 2 = 0 := by omega
  have := Nat.div_add_mod (d - 1) 2
  omega

/-! ### Mixed-type overlap aggregator

A single helper that dispatches to the appropriate per-pair lemma based on the
*classified kinds* `ki`, `kj`, assuming `ki` is a Z-type kind and `kj` is an
X-type kind (along with the constructor bounds and parity flowing from
`classifyStab_*_bounds`). -/

/-- Aggregator: for the 9 mixed-type kind-pairs (Z-kind × X-kind), with the
    appropriate constructor bounds, the row-overlap and col-overlap cannot
    both equal `1`. -/
private lemma mixed_overlap_Z_X (d : Nat) (hodd : d % 2 = 1)
    (ki kj : StabKind)
    (hZ : (∃ r c, ki = .bulkZ r c ∧ r + 1 < d ∧ c + 1 < d ∧ (r + c) % 2 = 0) ∨
          (∃ b, ki = .rightZ b ∧ b < (d - 1) / 2) ∨
          (∃ b, ki = .leftZ b ∧ b < (d - 1) / 2))
    (hX : (∃ r c, kj = .bulkX r c ∧ r + 1 < d ∧ c + 1 < d ∧ (r + c) % 2 = 1) ∨
          (∃ b, kj = .topX b ∧ b < (d - 1) / 2) ∨
          (∃ b, kj = .bottomX b ∧ b < (d - 1) / 2)) :
    ¬ ((kindRowSet d ki ∩ kindRowSet d kj).card = 1 ∧
       (kindColSet d ki ∩ kindColSet d kj).card = 1) := by
  rcases hZ with ⟨rz, cz, hkz, hrz, hcz, hpz⟩ | ⟨bz, hkz, hbz⟩ | ⟨bz, hkz, _hbz⟩ <;>
    rcases hX with ⟨rx, cx, hkx, hrx, hcx, hpx⟩ | ⟨bx, hkx, hbx⟩ | ⟨bx, hkx, _hbx⟩ <;>
    subst hkz <;> subst hkx
  · exact mixed_overlap_bulkZ_bulkX d rz cz rx cx hpz hpx
  · exact mixed_overlap_bulkZ_topX d rz cz bx hpz
  · exact mixed_overlap_bulkZ_bottomX d hodd rz cz bx hrz hpz
  · exact mixed_overlap_rightZ_bulkX d hodd bz rx cx hcx hpx
  · exact mixed_overlap_rightZ_topX d hodd bz bx hbx
  · exact mixed_overlap_rightZ_bottomX d hodd bz bx hbz
  · exact mixed_overlap_leftZ_bulkX d bz rx cx hpx
  · exact mixed_overlap_leftZ_topX d bz bx
  · exact mixed_overlap_leftZ_bottomX d bz bx

/-- Every element of `kindRowSet d k` is `< d` once the appropriate kind-side
    bound is in place. We package this as: for the Z-kinds and X-kinds we
    use in the headline, the filter `(· < d)` on the row-set is a no-op. -/
private lemma kindRowSet_subset_lt_Z (d : Nat) (hd : 0 < d) (hodd : d % 2 = 1) (k : StabKind)
    (hZ : (∃ r c, k = .bulkZ r c ∧ r + 1 < d ∧ c + 1 < d ∧ (r + c) % 2 = 0) ∨
          (∃ b, k = .rightZ b ∧ b < (d - 1) / 2) ∨
          (∃ b, k = .leftZ b ∧ b < (d - 1) / 2)) :
    ∀ row ∈ kindRowSet d k, row < d := by
  intro row hrow
  rcases hZ with ⟨r, c, hk, hr, _, _⟩ | ⟨b, hk, hb⟩ | ⟨b, hk, hb⟩ <;> subst hk <;>
    simp only [kindRowSet, Finset.mem_insert, Finset.mem_singleton] at hrow
  · rcases hrow with rfl | rfl <;> omega
  · rcases hrow with rfl | rfl <;> omega
  · -- leftZ: row ∈ {2b+1, 2b+2}, need < d. b < (d-1)/2 and d odd → 2b+2 ≤ d-1.
    have h2b : 2 * b + 2 ≤ d - 1 := by
      have h2 : 2 * b < 2 * ((d - 1) / 2) := by
        exact Nat.mul_lt_mul_left (by decide : 0 < 2) |>.mpr hb
      have hd_eq : 2 * ((d - 1) / 2) = d - 1 := by
        have := Nat.div_add_mod (d - 1) 2
        have hmod : (d - 1) % 2 = 0 := by omega
        omega
      omega
    rcases hrow with rfl | rfl <;> omega

private lemma kindColSet_subset_lt_Z (d : Nat) (hd : 0 < d) (k : StabKind)
    (hZ : (∃ r c, k = .bulkZ r c ∧ r + 1 < d ∧ c + 1 < d ∧ (r + c) % 2 = 0) ∨
          (∃ b, k = .rightZ b ∧ b < (d - 1) / 2) ∨
          (∃ b, k = .leftZ b ∧ b < (d - 1) / 2)) :
    ∀ col ∈ kindColSet d k, col < d := by
  intro col hcol
  rcases hZ with ⟨r, c, hk, _, hc, _⟩ | ⟨b, hk, _⟩ | ⟨b, hk, _⟩ <;> subst hk <;>
    simp only [kindColSet, Finset.mem_insert, Finset.mem_singleton] at hcol
  · rcases hcol with rfl | rfl <;> omega
  · rcases hcol with rfl <;> omega
  · rcases hcol with rfl <;> omega

private lemma kindRowSet_subset_lt_X (d : Nat) (hd : 0 < d) (k : StabKind)
    (hX : (∃ r c, k = .bulkX r c ∧ r + 1 < d ∧ c + 1 < d ∧ (r + c) % 2 = 1) ∨
          (∃ b, k = .topX b ∧ b < (d - 1) / 2) ∨
          (∃ b, k = .bottomX b ∧ b < (d - 1) / 2)) :
    ∀ row ∈ kindRowSet d k, row < d := by
  intro row hrow
  rcases hX with ⟨r, c, hk, hr, _, _⟩ | ⟨b, hk, _⟩ | ⟨b, hk, _⟩ <;> subst hk <;>
    simp only [kindRowSet, Finset.mem_insert, Finset.mem_singleton] at hrow
  · rcases hrow with rfl | rfl <;> omega
  · rcases hrow with rfl <;> omega
  · rcases hrow with rfl <;> omega

private lemma kindColSet_subset_lt_X (d : Nat) (hd : 0 < d) (hodd : d % 2 = 1)
    (k : StabKind)
    (hX : (∃ r c, k = .bulkX r c ∧ r + 1 < d ∧ c + 1 < d ∧ (r + c) % 2 = 1) ∨
          (∃ b, k = .topX b ∧ b < (d - 1) / 2) ∨
          (∃ b, k = .bottomX b ∧ b < (d - 1) / 2)) :
    ∀ col ∈ kindColSet d k, col < d := by
  intro col hcol
  rcases hX with ⟨r, c, hk, _, hc, _⟩ | ⟨b, hk, hb⟩ | ⟨b, hk, hb⟩ <;> subst hk <;>
    simp only [kindColSet, Finset.mem_insert, Finset.mem_singleton] at hcol
  · rcases hcol with rfl | rfl <;> omega
  · rcases hcol with rfl | rfl <;> omega
  · -- bottomX: col ∈ {2b+1, 2b+2}, need < d. Same as leftZ row case.
    have h2b : 2 * b + 2 ≤ d - 1 := by
      have h2 : 2 * b < 2 * ((d - 1) / 2) := by
        exact Nat.mul_lt_mul_left (by decide : 0 < 2) |>.mpr hb
      have hd_eq : 2 * ((d - 1) / 2) = d - 1 := by
        have := Nat.div_add_mod (d - 1) 2
        have hmod : (d - 1) % 2 = 0 := by omega
        omega
      omega
    rcases hcol with rfl | rfl <;> omega

/-- Rewrite of `mixed_overlap_Z_X` after applying `Finset.filter (· < d)` on
    both intersections.  When the row/col-set elements are automatically
    `< d` (which the kind-bounds ensure), the filter is the identity and the
    filtered version follows from the raw version. -/
private lemma mixed_overlap_Z_X_filtered (d : Nat) (hd : 0 < d) (hodd : d % 2 = 1)
    (ki kj : StabKind)
    (hZ : (∃ r c, ki = .bulkZ r c ∧ r + 1 < d ∧ c + 1 < d ∧ (r + c) % 2 = 0) ∨
          (∃ b, ki = .rightZ b ∧ b < (d - 1) / 2) ∨
          (∃ b, ki = .leftZ b ∧ b < (d - 1) / 2))
    (hX : (∃ r c, kj = .bulkX r c ∧ r + 1 < d ∧ c + 1 < d ∧ (r + c) % 2 = 1) ∨
          (∃ b, kj = .topX b ∧ b < (d - 1) / 2) ∨
          (∃ b, kj = .bottomX b ∧ b < (d - 1) / 2)) :
    ¬ (((kindRowSet d ki ∩ kindRowSet d kj).filter (· < d)).card = 1 ∧
       ((kindColSet d ki ∩ kindColSet d kj).filter (· < d)).card = 1) := by
  -- The filter `(· < d)` is the identity on every row-set and col-set arising
  -- from a Z-kind or X-kind, so filtered card = raw card and we reduce
  -- directly to `mixed_overlap_Z_X`.
  have h_row_lt : ∀ row ∈ kindRowSet d ki ∩ kindRowSet d kj, row < d := by
    intro row hrow
    exact kindRowSet_subset_lt_Z d hd hodd ki hZ row (Finset.mem_inter.mp hrow).1
  have h_col_lt : ∀ col ∈ kindColSet d ki ∩ kindColSet d kj, col < d := by
    intro col hcol
    exact kindColSet_subset_lt_Z d hd ki hZ col (Finset.mem_inter.mp hcol).1
  have h_row_eq : (kindRowSet d ki ∩ kindRowSet d kj).filter (· < d) =
                  kindRowSet d ki ∩ kindRowSet d kj := by
    apply Finset.filter_eq_self.mpr h_row_lt
  have h_col_eq : (kindColSet d ki ∩ kindColSet d kj).filter (· < d) =
                  kindColSet d ki ∩ kindColSet d kj := by
    apply Finset.filter_eq_self.mpr h_col_lt
  rw [h_row_eq, h_col_eq]
  exact mixed_overlap_Z_X d hodd ki kj hZ hX

/-! ### The headline `stab_commute_parametric` -/

/-- **Headline.** At odd distance `d > 0`, every two generators of the
    parametric rotated-surface-code stabilizer family commute, i.e. the
    parity of their pointwise anticommutation pattern is `false`.

    Proof strategy:
    1. If `stabType d i = stabType d j`, apply `parity_same_type`.
    2. Otherwise, exactly one of `{i, j}` has type `Z` and the other `X`.
       Use `anticommutes_iff_both_in_support` to rewrite the parity filter
       as a shared-support filter, then `shared_support_card_factors` to
       factor the card as `(row-overlap) * (col-overlap)`. Bound each
       factor by `2` (via `kind{Row,Col}Set_card_le_two`), and rule out
       the `(1, 1)` configuration via the 9 mixed-pair lemmas, dispatched
       through the `mixed_overlap_Z_X` aggregator.

    The `hodd : d % 2 = 1` hypothesis is **essential**: at even `d` the
    parametric family admits collisions (counterexample: `d = 4, i = 5,
    j = 10` share one cell).  Existing handwritten `SurfaceD4.stabilizers`
    avoids this; the parametric encoding does not. -/
theorem stab_commute_parametric (d : Nat) (hd : 0 < d) (hodd : d % 2 = 1)
    (i j : Fin (numStabFormula d)) :
    ErrorVec.parity (mkSurfaceStabilizers d hd i) (mkSurfaceStabilizers d hd j)
      = false := by
  by_cases hsame : stabType d i.val = stabType d j.val
  · exact parity_same_type d hd i j hsame
  · -- Mixed-type case: reduce parity to shared-support cardinality.
    -- Step 1: rewrite the parity filter via `anticommutes_iff_both_in_support`.
    have h_filter_eq :
        (Finset.univ.filter fun q : Fin (d * d) =>
            ErrorVec.Pauli.anticommutes
              (decodeStabPauliAt d i.val (q.val / d) (q.val % d))
              (decodeStabPauliAt d j.val (q.val / d) (q.val % d)) = true) =
        (Finset.univ.filter fun q : Fin (d * d) =>
            inStabSupport d i.val (q.val / d) (q.val % d) ∧
            inStabSupport d j.val (q.val / d) (q.val % d)) := by
      apply Finset.ext; intro q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact anticommutes_iff_both_in_support d i.val j.val (q.val / d) (q.val % d) hsame
    -- Step 2: unfold parity and rewrite.
    unfold ErrorVec.parity mkSurfaceStabilizers
    rw [h_filter_eq, shared_support_card_factors d hd i.val j.val]
    -- Step 3: bound each factor by 2, rule out (1, 1) via the aggregator.
    -- One of (stabType i, stabType j) is X, the other Z.
    have hti : stabType d i.val = Pauli.X ∨ stabType d i.val = Pauli.Z := by
      simp only [stabType]; split_ifs <;> simp
    have htj : stabType d j.val = Pauli.X ∨ stabType d j.val = Pauli.Z := by
      simp only [stabType]; split_ifs <;> simp
    -- The two `Z`-then-`X` or `X`-then-`Z` cases.
    -- Define a generic dispatcher: pick the Z-kind on the left.
    have h_card_even :
        ((kindRowSet d (classifyStab d i.val) ∩
           kindRowSet d (classifyStab d j.val)).filter (· < d)).card *
        ((kindColSet d (classifyStab d i.val) ∩
           kindColSet d (classifyStab d j.val)).filter (· < d)).card % 2 = 0 := by
      -- The `i, j : Fin (numStabFormula d)` are bounded by numStabFormula.
      -- For odd `d ≥ 1`, numStabFormula = max 1 ((d-1)^2 + 2*(d-1)) and we
      -- get `i.val < (d-1)^2 + 2*(d-1)` when `d ≥ 2`. We carry both i and j
      -- through the same lemma.
      -- At odd d, numStab = max 1 ((d-1)^2 + 2(d-1)) and the value of i is
      -- bounded by the (d-1)^2 + 2(d-1) side once d ≥ 3. We handle d = 1
      -- separately: at d = 1, both i and j are 0 by Fin.fin_one_eq, so
      -- hsame holds and we are not in the mixed branch.
      have hd_ge_3 : 3 ≤ d := by
        -- hd says d ≥ 1, hodd rules out d ∈ {0, 2}. So d = 1 or d ≥ 3.
        -- d = 1 contradicts hsame: numStabFormula 1 = 1, so i = j = 0 and
        -- stabType d i.val = stabType d j.val trivially.
        rcases Nat.lt_or_ge d 3 with hlt | hge
        · exfalso
          have hd1 : d = 1 := by omega
          subst hd1
          have hi0 : i.val = 0 := by
            have := i.isLt
            simp only [numStabFormula] at this
            omega
          have hj0 : j.val = 0 := by
            have := j.isLt
            simp only [numStabFormula] at this
            omega
          exact hsame (by rw [hi0, hj0])
        · exact hge
      have hi_lt : i.val < (d - 1) * (d - 1) + 2 * (d - 1) := by
        have hi := i.isLt
        unfold numStabFormula at hi
        have h1 : (d - 1) * (d - 1) + 2 * (d - 1) ≥ 1 := by
          have hdm : d - 1 ≥ 2 := by omega
          have hmul : (d - 1) * (d - 1) ≥ 1 := by
            calc 1 ≤ (d - 1) := by omega
              _ ≤ (d - 1) * (d - 1) := Nat.le_mul_of_pos_left _ (by omega)
          omega
        omega
      have hj_lt : j.val < (d - 1) * (d - 1) + 2 * (d - 1) := by
        have hj := j.isLt
        unfold numStabFormula at hj
        have h1 : (d - 1) * (d - 1) + 2 * (d - 1) ≥ 1 := by
          have hdm : d - 1 ≥ 2 := by omega
          have hmul : (d - 1) * (d - 1) ≥ 1 := by
            calc 1 ≤ (d - 1) := by omega
              _ ≤ (d - 1) * (d - 1) := Nat.le_mul_of_pos_left _ (by omega)
          omega
        omega
      -- Extract Z-side classification with bounds.
      have hZ_from : ∀ k : Nat, k < (d - 1) * (d - 1) + 2 * (d - 1) →
          stabType d k = Pauli.Z →
          (∃ r c, classifyStab d k = .bulkZ r c ∧
                  r + 1 < d ∧ c + 1 < d ∧ (r + c) % 2 = 0) ∨
          (∃ b, classifyStab d k = .rightZ b ∧ b < (d - 1) / 2) ∨
          (∃ b, classifyStab d k = .leftZ b ∧ b < (d - 1) / 2) := by
        intro k _ hk
        rcases (classify_type_Z d k).mp hk with ⟨r, c, hcl⟩ | ⟨b, hcl⟩ | ⟨b, hcl⟩
        · obtain ⟨hr, hc, hpar⟩ := classifyStab_bulkZ_bounds d k r c hcl
          exact Or.inl ⟨r, c, hcl, hr, hc, hpar⟩
        · exact Or.inr (Or.inl ⟨b, hcl, classifyStab_rightZ_bounds d k b hcl⟩)
        · exact Or.inr (Or.inr ⟨b, hcl, classifyStab_leftZ_bounds d k b hcl⟩)
      have hX_from : ∀ k : Nat, k < (d - 1) * (d - 1) + 2 * (d - 1) →
          stabType d k = Pauli.X →
          (∃ r c, classifyStab d k = .bulkX r c ∧
                  r + 1 < d ∧ c + 1 < d ∧ (r + c) % 2 = 1) ∨
          (∃ b, classifyStab d k = .topX b ∧ b < (d - 1) / 2) ∨
          (∃ b, classifyStab d k = .bottomX b ∧ b < (d - 1) / 2) := by
        intro k hkbd hk
        rcases (classify_type_X d k).mp hk with ⟨r, c, hcl⟩ | ⟨b, hcl⟩ | ⟨b, hcl⟩
        · obtain ⟨hr, hc, hpar⟩ := classifyStab_bulkX_bounds d k r c hcl
          exact Or.inl ⟨r, c, hcl, hr, hc, hpar⟩
        · exact Or.inr (Or.inl ⟨b, hcl, classifyStab_topX_bounds d k b hcl⟩)
        · exact Or.inr (Or.inr ⟨b, hcl,
            classifyStab_bottomX_bounds d k b hodd hkbd hcl⟩)
      -- Case-split on (stabType i, stabType j); only the mixed cases survive `hsame`.
      rcases hti with hti | hti <;> rcases htj with htj | htj
      · exact absurd (hti.trans htj.symm) hsame
      · -- i is X, j is Z: swap.
        have hXi := hX_from i.val hi_lt hti
        have hZj := hZ_from j.val hj_lt htj
        have hno := mixed_overlap_Z_X_filtered d hd hodd
            (classifyStab d j.val) (classifyStab d i.val) hZj hXi
        -- Swap inter via Finset.inter_comm.
        rw [Finset.inter_comm, show
            (kindColSet d (classifyStab d i.val) ∩
             kindColSet d (classifyStab d j.val)) =
            (kindColSet d (classifyStab d j.val) ∩
             kindColSet d (classifyStab d i.val)) from Finset.inter_comm _ _]
        exact mul_even_of_not_both_one _ _
          (row_inter_card_le_two d _ _) (col_inter_card_le_two d _ _) hno
      · -- i is Z, j is X: direct.
        have hZi := hZ_from i.val hi_lt hti
        have hXj := hX_from j.val hj_lt htj
        have hno := mixed_overlap_Z_X_filtered d hd hodd
            (classifyStab d i.val) (classifyStab d j.val) hZi hXj
        exact mul_even_of_not_both_one _ _
          (row_inter_card_le_two d _ _) (col_inter_card_le_two d _ _) hno
      · exact absurd (hti.trans htj.symm) hsame
    -- Step 4: conclude `(card % 2 == 1) = false`.
    rw [h_card_even]; rfl

end QStab.Examples.SurfaceParametric
