import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Basic
import QStab.Examples.SurfaceGeometry
import QStab.Paper.Predicates
import QStab.Paper.PredicateBridge

/-!
# Parametric hook-shape datatype

This file introduces a small, *parametric* description of the qualitative
"shape" of a residual back-action operator `e_B` after a fault has been
propagated through a stabilizer-code FT gadget.

The design is deliberately Finset-based rather than enum-per-cardinality:
at code distances `d = 5, 7` the bulk stabilizers have weight 4 or 6, so
the supports of admissible hooks span multiple cardinalities. A single
`HookPattern` constructor plus a pair of `Finset (Fin d)` fields scales
uniformly to any distance.

We provide a `HookPattern` enumeration of the four qualitative cases
identified in the audit and wrap it with the geometric support data
required to evaluate any hook-classification predicate downstream.

## Discipline notes

* No `sorry`, no `native_decide`, no `Classical.choose`, no
  `Exists.choose`, no `by_contra`.
* `decide` (kernel-only) is allowed but not used here; the witnesses that
  follow simply construct concrete `HookShape` values.
-/

namespace QStab.Paper

open QStab.Examples

/-- Qualitative classification of a residual back-action Pauli `e_B`.

The four cases are mutually exclusive in the typing-rule design of the
paper:

* `identity`   – `e_B = I` (the fault has been absorbed entirely).
* `xInRows`    – every non-identity tensor factor of `e_B` is an `X` and
                 its support is contained in `rowSet : Finset (Fin d)`;
                 no `Z`-components are present.
* `zInCols`    – dually: every non-identity tensor factor of `e_B` is a
                 `Z` and its support is contained in `colSet`; no
                 `X`-components are present.
* `fullStab`   – `e_B` is stabilizer-equivalent to a *non-trivial*
                 product of code stabilizers, i.e. it lies in the
                 stabilizer group modulo the identity.

Carrying this as a small enum keeps proofs by-cases very cheap. -/
inductive HookPattern
  | identity
  | xInRows
  | zInCols
  | fullStab
  deriving DecidableEq, Repr

/-- The full *hook shape* attached to a residual `e_B` after fault
propagation through a depth-`d` stabilizer gadget.

* `pattern` – the qualitative case (see `HookPattern`).
* `rowSet`  – the geometric row support used by the `xInRows`
              (and, vacuously, `identity`) cases. It is a `Finset (Fin d)`
              so its cardinality is unconstrained.
* `colSet`  – the geometric column support used by the `zInCols`
              (and, vacuously, `identity`) cases.

Because both supports are stored regardless of `pattern`, the structure
is uniform across patterns: callers that do not need the rows simply
ignore `rowSet`, and similarly for `colSet`. This avoids dependent-type
gymnastics across pattern cases while still keeping the geometric data
attached. -/
structure HookShape (d : Nat) where
  pattern : HookPattern
  rowSet  : Finset (Fin d)
  colSet  : Finset (Fin d)
  deriving DecidableEq

/-- A lightweight `Repr` for `HookShape`. Mathlib's `Repr (Finset α)`
instance is marked `unsafe` (it sorts the underlying multiset), so we
cannot derive `Repr` automatically. Instead we print only the
`pattern` together with the *cardinalities* of `rowSet` and `colSet`,
which keeps the output deterministic and computable while still being
human-readable for diagnostics. -/
instance instReprHookShape {d : Nat} : Repr (HookShape d) where
  reprPrec h _ :=
    "HookShape.mk " ++ reprStr h.pattern
      ++ " (rows=" ++ reprStr h.rowSet.card ++ ")"
      ++ " (cols=" ++ reprStr h.colSet.card ++ ")"

namespace HookShape

/-- The "trivial" hook shape at any distance: identity pattern with
empty geometric support on both sides. Useful as a default and for
representing the `e_B = I` case after a fault is absorbed. -/
def trivial (d : Nat) : HookShape d :=
  { pattern := HookPattern.identity
    rowSet  := (∅ : Finset (Fin d))
    colSet  := (∅ : Finset (Fin d)) }

/-- An `xInRows` hook on a given row support, with no column data. -/
def ofRows {d : Nat} (rows : Finset (Fin d)) : HookShape d :=
  { pattern := HookPattern.xInRows
    rowSet  := rows
    colSet  := (∅ : Finset (Fin d)) }

/-- A `zInCols` hook on a given column support, with no row data. -/
def ofCols {d : Nat} (cols : Finset (Fin d)) : HookShape d :=
  { pattern := HookPattern.zInCols
    rowSet  := (∅ : Finset (Fin d))
    colSet  := cols }

/-- A `fullStab` hook may still record geometric witnesses (e.g. the
support of the stabilizer it is equivalent to). Both supports default
to empty when no witnessing data is available. -/
def ofStab {d : Nat}
    (rows : Finset (Fin d) := (∅ : Finset (Fin d)))
    (cols : Finset (Fin d) := (∅ : Finset (Fin d))) : HookShape d :=
  { pattern := HookPattern.fullStab
    rowSet  := rows
    colSet  := cols }

end HookShape

/-! ## `HookShapeOf` — the relating predicate

Given a residual back-action vector `e_B : ErrorVec (d * d)` and an abstract
`shape : HookShape d`, `HookShapeOf e_B shape` says that `e_B` *fits* the
shape. Each `HookPattern` case dictates the geometric/Pauli constraints:

* `.identity`  — every position is `Pauli.I`.
* `.xInRows`   — no position carries a `Z`-component, and every position
                 carrying an `X`-component lies in a row whose index belongs
                 to `shape.rowSet`.
* `.zInCols`   — symmetric to `xInRows`: no `X`-components, all `Z`-bearing
                 positions are in columns from `shape.colSet`.
* `.fullStab`  — a placeholder `True` for the prototype; the d=5,7 designs
                 will refine this to "stabilizer-equivalent to a non-trivial
                 product of stabilizers" using `QStab.ErrorVec.stabEquiv`.

### Decidability

Both `Pauli.hasXComponent` and `Pauli.hasZComponent` are `Bool`-valued, hence
the `∀ q : Fin (d*d), …` conjuncts reduce to Π-fintype decidability. The
row/column membership conjuncts are checked against `Finset.image Fin.val`
(a `Finset Nat`), which is decidable since `Nat` has `DecidableEq`. We expose
the resulting instance explicitly so that `decide` works on concrete
`(e_B, shape)` pairs.

The row index of qubit `q` on a `d × d` grid is `q.val / d` (the inverse of
`toIdx`'s `d * i + j` packing); the column index is `q.val % d`. We deliberately
*do not* unpack to `Fin d` here so as to keep the predicate independent of any
`d > 0` side-condition. -/

/-- The relating predicate: `e_B` fits the hook shape `shape`. -/
def HookShapeOf {d : Nat}
    (e_B : ErrorVec (d * d)) (shape : HookShape d) : Prop :=
  match shape.pattern with
  | HookPattern.identity =>
      ∀ q : Fin (d * d), e_B q = Pauli.I
  | HookPattern.xInRows =>
      (∀ q : Fin (d * d), Pauli.hasZComponent (e_B q) = false) ∧
      (∀ q : Fin (d * d),
        Pauli.hasXComponent (e_B q) = true →
          (q.val / d) ∈ shape.rowSet.image Fin.val)
  | HookPattern.zInCols =>
      (∀ q : Fin (d * d), Pauli.hasXComponent (e_B q) = false) ∧
      (∀ q : Fin (d * d),
        Pauli.hasZComponent (e_B q) = true →
          (q.val % d) ∈ shape.colSet.image Fin.val)
  | HookPattern.fullStab =>
      True

/-- `HookShapeOf` is decidable: every case is a conjunction/implication of
Bool equalities and `Finset Nat` memberships, all over the finite type
`Fin (d * d)`. We dispatch on `shape.pattern` so each branch picks up the
appropriate Π-fintype/Finset.decidableMem instance. -/
instance instDecidableHookShapeOf {d : Nat}
    (e_B : ErrorVec (d * d)) (shape : HookShape d) :
    Decidable (HookShapeOf e_B shape) := by
  unfold HookShapeOf
  -- Dispatch on the four pattern cases; each falls out to standard
  -- Π-fintype / Bool / Finset.decidableMem instances.
  cases shape.pattern with
  | identity => exact inferInstance
  | xInRows  => exact inferInstance
  | zInCols  => exact inferInstance
  | fullStab => exact inferInstance

/-! ### Sanity checks (kernel `decide`/`#eval`-able) -/

/-- `HookShapeOf (identity 9) (trivial 3)` reduces to `True` via `decide`. -/
example :
    HookShapeOf (d := 3) (ErrorVec.identity 9) (HookShape.trivial 3) := by
  decide

/-- A non-identity Pauli vector is not `identity`-shaped. -/
example :
    ¬ HookShapeOf (d := 3)
        (fun q : Fin 9 => if q.val = 0 then Pauli.X else Pauli.I)
        (HookShape.trivial 3) := by
  decide

/-- An all-`X`-on-row-0 vector fits an `xInRows` shape with `rowSet = {0}`. -/
example :
    HookShapeOf (d := 3)
      (fun q : Fin 9 => if q.val / 3 = 0 then Pauli.X else Pauli.I)
      (HookShape.ofRows ({⟨0, by decide⟩} : Finset (Fin 3))) := by
  decide

/-- Any vector fits a `fullStab` shape (placeholder; will be refined). -/
example
    (e_B : ErrorVec 9) :
    HookShapeOf (d := 3) e_B (HookShape.ofStab) := by
  -- `fullStab` case is `True` in the prototype; reduces by definition.
  show True
  trivial

/-! ## d=3 Surface code: `HookShape` assignment for all 16 NZ hooks

This section discharges the d=3 design validation goal: for the **family-side
mechanical hook set** `allHooks_PNZ` from
`QStab/QHL/Compile/Examples/SurfaceD3NZ.lean` (which has exactly 16 distinct
residual `ErrorVec 9` values with weight distribution `{2:8, 3:4, 4:4}`),
we assign a `HookShape 3` to each element and prove `HookShapeOf` on every
member of the list.

The 16 hooks were cross-validated against Stim-style fault propagation in
`notes/validate_PNZ_d3.py`. Their structural breakdown matches the
qualitative `HookPattern` taxonomy:

* **8 weight-2 elements** — 4 all-`X` (single-row), 4 all-`Z` (single-col).
* **4 weight-3 elements** — 2 all-`X` (two-row), 2 all-`Z` (two-col).
* **4 weight-4 elements** — the four bulk stabilizers themselves; classified
  as `fullStab` (the stabilizer-equivalent case).

The classifier `surfaceD3HookShape` is a transparent if-`=`-then chain
(16 hook-specific branches + `trivial 3` default), and the headline
theorem `surfaceD3_nz_hook_has_shape` discharges via kernel `decide` —
no `native_decide`, no `sorry`, no axiom-of-choice usage.

### Row/column geometry recap

Qubits `Fin 9` are laid out as a 3×3 grid via the packing `q = 3 * i + j`,
so `row(q) = q.val / 3` and `col(q) = q.val % 3`. Stabilizer indices and
qubit memberships match `QStab/Examples/SurfaceCode.lean`:

```
   q₀ q₁ q₂   row 0
   q₃ q₄ q₅   row 1
   q₆ q₇ q₈   row 2
```
-/

/-- Convenience: a `Fin 3` literal from a `Nat`. -/
private def fr3 (n : Nat) (h : n < 3 := by decide) : Fin 3 := ⟨n, h⟩

/-- Hook-shape assignment for the d=3 surface code's family-side NZ hooks.

Each of the 16 distinct residual `ErrorVec 9` values in `allHooks_PNZ`
gets classified into a `HookShape 3`:

* the 8 weight-2 entries map to `xInRows`/`zInCols` with a singleton
  `rowSet`/`colSet`;
* the 4 weight-3 entries map to `xInRows`/`zInCols` with a two-element
  `rowSet`/`colSet`;
* the 4 weight-4 entries (the bulk stabilizers themselves) map to
  `fullStab`;
* every other input defaults to `HookShape.trivial 3` (vacuously
  identity-shaped).

This is the explicit per-element table; the headline
`surfaceD3_nz_hook_has_shape` confirms it agrees with `HookShapeOf` on
every actual hook. -/
def surfaceD3HookShape (e : ErrorVec 9) : HookShape 3 :=
  -- Weight-2 X (4 elements): single-row supports
  if e = (ofList [(7, .X), (8, .X)] : ErrorVec 9) then
    HookShape.ofRows ({fr3 2} : Finset (Fin 3))
  else if e = (ofList [(6, .X), (7, .X)] : ErrorVec 9) then
    HookShape.ofRows ({fr3 2} : Finset (Fin 3))
  else if e = (ofList [(4, .X), (5, .X)] : ErrorVec 9) then
    HookShape.ofRows ({fr3 1} : Finset (Fin 3))
  else if e = (ofList [(0, .X), (1, .X)] : ErrorVec 9) then
    HookShape.ofRows ({fr3 0} : Finset (Fin 3))
  -- Weight-2 Z (4 elements): single-column supports
  else if e = (ofList [(5, .Z), (8, .Z)] : ErrorVec 9) then
    HookShape.ofCols ({fr3 2} : Finset (Fin 3))
  else if e = (ofList [(3, .Z), (6, .Z)] : ErrorVec 9) then
    HookShape.ofCols ({fr3 0} : Finset (Fin 3))
  else if e = (ofList [(2, .Z), (5, .Z)] : ErrorVec 9) then
    HookShape.ofCols ({fr3 2} : Finset (Fin 3))
  else if e = (ofList [(1, .Z), (4, .Z)] : ErrorVec 9) then
    HookShape.ofCols ({fr3 1} : Finset (Fin 3))
  -- Weight-3 (4 elements): two-row / two-column supports
  else if e = (ofList [(5, .Z), (7, .Z), (8, .Z)] : ErrorVec 9) then
    HookShape.ofCols ({fr3 1, fr3 2} : Finset (Fin 3))
  else if e = (ofList [(4, .X), (6, .X), (7, .X)] : ErrorVec 9) then
    HookShape.ofRows ({fr3 1, fr3 2} : Finset (Fin 3))
  else if e = (ofList [(2, .X), (4, .X), (5, .X)] : ErrorVec 9) then
    HookShape.ofRows ({fr3 0, fr3 1} : Finset (Fin 3))
  else if e = (ofList [(1, .Z), (3, .Z), (4, .Z)] : ErrorVec 9) then
    HookShape.ofCols ({fr3 0, fr3 1} : Finset (Fin 3))
  -- Weight-4 (4 elements = the bulk stabilizers themselves)
  else if e = (ofList [(4, .Z), (5, .Z), (7, .Z), (8, .Z)] : ErrorVec 9) then
    HookShape.ofStab
  else if e = (ofList [(3, .X), (4, .X), (6, .X), (7, .X)] : ErrorVec 9) then
    HookShape.ofStab
  else if e = (ofList [(1, .X), (2, .X), (4, .X), (5, .X)] : ErrorVec 9) then
    HookShape.ofStab
  else if e = (ofList [(0, .Z), (1, .Z), (3, .Z), (4, .Z)] : ErrorVec 9) then
    HookShape.ofStab
  -- Default: identity shape (used for every input not in the 16-element set).
  else
    HookShape.trivial 3

/-- The 16-element family-side NZ hook list for the d=3 surface code.

This is the literal Lean copy of `allHooks_PNZ` from
`QStab/QHL/Compile/Examples/SurfaceD3NZ.lean`; both lists are
cross-validated against Stim-style propagation in
`notes/validate_PNZ_d3.py`. We keep a local copy to avoid pulling the
heavyweight compile-rule infrastructure into `Paper/`. -/
def surfaceD3Hooks16 : List (ErrorVec 9) :=
  [ -- Weight 2 (8 elements)
    ofList [(7, .X), (8, .X)]
  , ofList [(6, .X), (7, .X)]
  , ofList [(5, .Z), (8, .Z)]
  , ofList [(4, .X), (5, .X)]
  , ofList [(3, .Z), (6, .Z)]
  , ofList [(2, .Z), (5, .Z)]
  , ofList [(1, .Z), (4, .Z)]
  , ofList [(0, .X), (1, .X)]
    -- Weight 3 (4 elements)
  , ofList [(5, .Z), (7, .Z), (8, .Z)]
  , ofList [(4, .X), (6, .X), (7, .X)]
  , ofList [(2, .X), (4, .X), (5, .X)]
  , ofList [(1, .Z), (3, .Z), (4, .Z)]
    -- Weight 4 (4 elements = the bulk stabilizers)
  , ofList [(4, .Z), (5, .Z), (7, .Z), (8, .Z)]
  , ofList [(3, .X), (4, .X), (6, .X), (7, .X)]
  , ofList [(1, .X), (2, .X), (4, .X), (5, .X)]
  , ofList [(0, .Z), (1, .Z), (3, .Z), (4, .Z)] ]

/-- Length sanity check: exactly 16 entries. -/
example : surfaceD3Hooks16.length = 16 := rfl

/-- **Headline d=3 design-validation theorem.** Every member of the
family-side NZ hook list `surfaceD3Hooks16` fits the `HookShape 3`
assigned by `surfaceD3HookShape`. Proved by kernel `decide` over the
16-element list — no `native_decide`, no `sorry`, no axiom-of-choice
usage.

This validates the parametric `Finset`-based `HookShape` design at
the smallest non-trivial code distance: the classifier reduces
purely by kernel computation, the `HookShapeOf` predicate is fully
decidable, and the per-row/per-column geometry survives concrete
membership checks against `Finset.image Fin.val`. -/
theorem surfaceD3_nz_hook_has_shape :
    ∀ e ∈ surfaceD3Hooks16,
      HookShapeOf (d := 3) e (surfaceD3HookShape e) := by
  intro e he
  fin_cases he <;> decide

/-! ### `#eval` smoke checks (reduce to literals) -/

/-- The classifier on the first weight-4 hook reports `fullStab`. -/
example :
    (surfaceD3HookShape (ofList [(4, .Z), (5, .Z), (7, .Z), (8, .Z)])).pattern
      = HookPattern.fullStab := by decide

/-- The classifier on the first weight-2 X hook reports `xInRows` with
    a singleton row support. -/
example :
    (surfaceD3HookShape (ofList [(7, .X), (8, .X)])).pattern
      = HookPattern.xInRows := by decide

example :
    (surfaceD3HookShape (ofList [(7, .X), (8, .X)])).rowSet.card = 1 := by
  decide

/-- The classifier on the first weight-3 Z hook reports `zInCols`
    with a two-element column support. -/
example :
    (surfaceD3HookShape (ofList [(5, .Z), (7, .Z), (8, .Z)])).pattern
      = HookPattern.zInCols := by decide

example :
    (surfaceD3HookShape (ofList [(5, .Z), (7, .Z), (8, .Z)])).colSet.card = 2 := by
  decide

/-! ## Parametric NZ hook recognition tooling (for Phase 4 and Phase 6)

This section adds the abstract tooling that Phase 4 (`SurfaceBarrierWitness`)
and Phase 6 (concrete `d = 3, 5, 7` spec instances) will consume. The d=3
classifier above already exhibits the pattern; here we expose:

* `HookShape.identityShape d` — a name-stable alias for the identity-pattern
  hook shape (`HookShape.trivial d`), giving the spec-instance code a stable
  hook for the "fault absorbed" case.
* `HookShapeOf.identityShape_iff` — the identity shape recognises exactly the
  identity `ErrorVec` (every position is `Pauli.I`).
* `HookShapeOf.xInRows_from_RowRestricted` — lifts an abstract semantic
  predicate (`RowRestrictedX` + no-Z assumption) into a concrete
  `HookShapeOf … (xInRows, {i}, ∅)` fact. This is the bridge Phase 4 uses
  when it discharges hook recognition via the predicate calculus from
  `Paper/Predicates.lean`.
* `HookShapeOf.zInCols_from_ColRestricted` — column/Z mirror.
* `SpecHasNZHookShape` — the Phase 6 per-spec obligation signature: given
  a `QECParams P` and a classifier `assignShape`, the obligation is that
  every back-action element is recognised by `HookShapeOf`. The d=3
  instance above (`surfaceD3_nz_hook_has_shape`) is one concrete witness;
  d=5 and d=7 specs in Phase 6 will provide their own.

**Per architecture audit (R1):** `nz_hook_has_shape` for arbitrary `d` is
NOT a free corollary — it depends on the spec instance's `backActionSet`
structure (e.g. whether the bulk stabilizers themselves appear at weight
`d-1` or weight `d+1`). We therefore expose only the *signature* here;
the concrete proof for each spec instance lives in Phase 6.

Discipline: no `sorry`, no `native_decide`, no `Classical.choose`,
no `Exists.choose`, no `by_contra` in any of the additions below. -/

namespace HookShape

/-- The identity-pattern hook shape at any code distance `d`. This is
defeq-equal to `HookShape.trivial d` but carries the more descriptive
name `identityShape`, matching the architectural narrative ("a fault
that has been absorbed produces the identity shape").

The two names are interchangeable; we keep both for documentation
clarity at the call sites in Phase 4 / Phase 6. -/
def identityShape (d : Nat) : HookShape d :=
  { pattern := HookPattern.identity
    rowSet  := (∅ : Finset (Fin d))
    colSet  := (∅ : Finset (Fin d)) }

/-- `identityShape = trivial` as `HookShape` values. -/
theorem identityShape_eq_trivial (d : Nat) :
    identityShape d = trivial d := rfl

end HookShape

/-! ### `HookShapeOf` recognisers from abstract semantic predicates -/

/-- The identity hook shape `HookShape.identityShape d` recognises exactly
the identity `ErrorVec`: `HookShapeOf e_B (identityShape d)` is
definitionally `∀ q, e_B q = Pauli.I`. This is the Phase 4 / Phase 6
entry point for the "fault absorbed" case. -/
theorem HookShapeOf_identityShape_iff (d : Nat) (e_B : ErrorVec (d * d)) :
    HookShapeOf e_B (HookShape.identityShape d) ↔ ∀ q, e_B q = Pauli.I :=
  Iff.rfl

/-- **Phase 4 bridge (X-row case).** Given the abstract semantic predicate
`RowRestrictedX e_B i` (every non-row-`i` cell has zero X-component) plus a
global "no Z-component" assumption `hZ`, the residual `e_B` fits the
concrete `HookShape` with pattern `xInRows` and singleton row support
`{i}`.

This is the lifting that `SurfaceBarrierWitness` (Phase 4) uses to
translate from the predicate calculus of `Paper/Predicates.lean` to the
classifier-style `HookShapeOf` consumed by Phase 6 spec instances.

Proof strategy:
* The `hasZComponent = false` conjunct is supplied directly by `hZ`.
* For the row-membership conjunct, we use `RowRestrictedX_iff_pointwise`
  (from `Paper/PredicateBridge.lean`) to convert `hRow` into the
  pointwise statement `∀ q, hasXComponent (e_B q) = true →
  q.val / d = i.val`, then conclude `q.val / d ∈ {i.val}` via
  `Finset.image_singleton` + `Finset.mem_singleton`. -/
theorem HookShapeOf_xInRows_from_RowRestricted {d : Nat}
    (e_B : ErrorVec (d * d)) (i : Fin d)
    (hZ : ∀ q, Pauli.hasZComponent (e_B q) = false)
    (hRow : QStab.Paper.Predicates.RowRestrictedX e_B i) :
    HookShapeOf e_B
      { pattern := HookPattern.xInRows
        rowSet  := ({i} : Finset (Fin d))
        colSet  := (∅ : Finset (Fin d)) } := by
  -- Derive `0 < d` from the witness `i : Fin d`.
  have hd : 0 < d := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  -- Convert `hRow` to its pointwise form.
  have hPt : ∀ q : Fin (d * d),
      Pauli.hasXComponent (e_B q) = true → q.val / d = i.val :=
    (QStab.Paper.PredicateBridge.RowRestrictedX_iff_pointwise e_B i hd).mp hRow
  -- Discharge the two `HookShapeOf` conjuncts.
  refine ⟨hZ, ?_⟩
  intro q hx
  -- From hPt q hx, q.val / d = i.val; conclude i.val ∈ ({i} : Finset (Fin d)).image Fin.val.
  have hqi : q.val / d = i.val := hPt q hx
  rw [hqi]
  -- ({i} : Finset (Fin d)).image Fin.val = {i.val}.
  rw [Finset.image_singleton]
  exact Finset.mem_singleton.mpr rfl

/-- **Phase 4 bridge (Z-column case).** Symmetric to
`HookShapeOf_xInRows_from_RowRestricted`. Given `ColRestrictedZ e_B j`
plus a "no X-component" assumption, `e_B` fits the `zInCols` shape with
singleton column support `{j}`. -/
theorem HookShapeOf_zInCols_from_ColRestricted {d : Nat}
    (e_B : ErrorVec (d * d)) (j : Fin d)
    (hX : ∀ q, Pauli.hasXComponent (e_B q) = false)
    (hCol : QStab.Paper.Predicates.ColRestrictedZ e_B j) :
    HookShapeOf e_B
      { pattern := HookPattern.zInCols
        rowSet  := (∅ : Finset (Fin d))
        colSet  := ({j} : Finset (Fin d)) } := by
  have hd : 0 < d := Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt
  have hPt : ∀ q : Fin (d * d),
      Pauli.hasZComponent (e_B q) = true → q.val % d = j.val :=
    (QStab.Paper.PredicateBridge.ColRestrictedZ_iff_pointwise e_B j hd).mp hCol
  refine ⟨hX, ?_⟩
  intro q hz
  have hqj : q.val % d = j.val := hPt q hz
  rw [hqj, Finset.image_singleton]
  exact Finset.mem_singleton.mpr rfl

/-! ### `SpecHasNZHookShape` — the Phase 6 per-spec obligation signature

For a `QECParams P` whose physical-qubit count factors as `n = d * d`
(the rotated-surface case), a `SpecHasNZHookShape` witness consists of a
classifier `assignShape : ErrorVec (d * d) → HookShape d` such that
**every** back-action element across **every** stabilizer is recognised
by `HookShapeOf`.

This is the abstract form of the goal discharged by
`surfaceD3_nz_hook_has_shape` for `d = 3` (above). Phase 6 will provide
analogous witnesses for `d = 5` and `d = 7`; per the architecture audit
(R1), each is a separate proof depending on that spec's
`backActionSet` structure, not a corollary of a general theorem.

We package it as a `Prop`-valued obligation so that downstream
machinery can quantify uniformly over "specs admitting NZ hook
recognition" without needing the abstract `HookShape`/classifier
plumbing at every call site. -/

/-- Phase 6 obligation: every back-action element of a spec is
recognised by the classifier `assignShape`.

Parameters:
* `P : QECParams` — the spec, with `P.n = d * d` for the rotated-surface case.
* `d : Nat` — the code distance (matched to `P.n` via `hn : P.n = d * d`).
* `assignShape : ErrorVec P.n → HookShape d` — the per-element classifier.

The obligation: for every stabilizer index `s : Fin P.numStab` and every
`e_B ∈ P.backActionSet s`, the value `assignShape e_B` recognises `e_B`
under `HookShapeOf`.

The `hn : P.n = d * d` hypothesis converts `ErrorVec P.n` to
`ErrorVec (d * d)` via `hn ▸ e_B`, so that `HookShapeOf` (which is
indexed by `d * d`) can consume the back-action element.

**Why this is a *signature* and not a proven theorem.** Per the
architecture audit (R1), the proof at arbitrary `d` depends on
*spec-specific* facts about `backActionSet` (e.g. whether the bulk
stabilizers themselves are members, what their weights are, whether
they admit a row/column-localised representative modulo stabilizers).
The d=3 instance `surfaceD3_nz_hook_has_shape` (above) is one such
witness; Phase 6 supplies d=5 and d=7. We expose the *type* of the
obligation here so Phase 4 / Phase 6 can name and consume it. -/
def SpecHasNZHookShape (P : QECParams) (d : Nat) (hn : P.n = d * d)
    (assignShape : ErrorVec P.n → HookShape d) : Prop :=
  ∀ (s : Fin P.numStab) (e_B : ErrorVec P.n),
    e_B ∈ P.backActionSet s → HookShapeOf (hn ▸ e_B) (assignShape e_B)

/-- Unfolding lemma for `SpecHasNZHookShape`. -/
theorem SpecHasNZHookShape_iff (P : QECParams) (d : Nat) (hn : P.n = d * d)
    (assignShape : ErrorVec P.n → HookShape d) :
    SpecHasNZHookShape P d hn assignShape ↔
      ∀ (s : Fin P.numStab) (e_B : ErrorVec P.n),
        e_B ∈ P.backActionSet s → HookShapeOf (hn ▸ e_B) (assignShape e_B) :=
  Iff.rfl

end QStab.Paper
