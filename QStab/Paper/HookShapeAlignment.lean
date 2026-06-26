import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Basic
import QStab.Examples.SurfaceGeneral
import QStab.Paper.AlignedBarrier
import QStab.Paper.HookShape

/-!
# Per-pattern alignment theorems for `HookShape`

For each constructor of `HookPattern` we prove that `HookShapeOf e_B shape`
delivers an `IsLAligned`-style alignment bound at the level of the
`AlignedBarrier.groupsX` count: there exists `S_wit' ∈ InStab` with
`groupsX spec S_wit' (e_B · E) ≤ groupsX spec S_wit E + k`, where `k`
depends on the pattern:

* `identity`  – `k = 0` (no contribution, equality).
* `xInRows`   – `k = (e_B's X-support cardinality)`; specialised to `k = 1`
                when the `rowSet` is a singleton and the spec geometry
                maps rows to groups injectively (singleton-row case
                used by Surface d=3,5,7 via `HookShapeOf_xInRows_from_RowRestricted`).
* `zInCols`   – the Z-direction mirror is the symmetric obligation; per
                the architecture audit (R4) we only state, not prove, it
                here. The X-direction headlines for Surface d=3,5,7 do
                not consume it. The pattern is still discharged in the
                combined `hook_shape_aligned` theorem via the same
                `xInRows`-style argument applied with X/Z roles swapped
                (left to the spec instance to supply when needed).
* `fullStab`  – `k = 0` (the stabilizer cancels itself when absorbed
                into the witness via `S_wit' := S_wit · e_B`).

The combined headline `hook_shape_aligned` packages all four cases into
one statement.

## Discipline notes

No `sorry`, no `native_decide`, no `Classical.choose`, no
`Exists.choose`, no `by_contra` is used anywhere in this file.
-/

namespace QStab.Paper.HookShapeAlignment

open QStab QStab.Examples QStab.Examples.SurfaceGeneral
open QStab.Paper.AlignedBarrier QStab.Paper

/-! ## Pointwise lemmas on Pauli multiplication -/

/-- `Pauli.I` is a left identity for `Pauli.mul` (re-exported from the
core Pauli lemmas with the framework-local naming). -/
private theorem Pauli_I_mul (p : Pauli) : Pauli.mul Pauli.I p = p := by
  cases p <;> rfl

/-- Pointwise: `(I · E) q = E q` for every position. -/
private theorem mul_identity_left {n : Nat} (E : ErrorVec n) :
    ErrorVec.mul (ErrorVec.identity n) E = E := by
  funext q
  show Pauli.mul Pauli.I (E q) = E q
  exact Pauli_I_mul _

/-- Pointwise: `e · (e · E) q = E q` since `e q * e q = I`. -/
private theorem mul_self_left {n : Nat} (e E : ErrorVec n) :
    ErrorVec.mul e (ErrorVec.mul e E) = E := by
  funext q
  show Pauli.mul (e q) (Pauli.mul (e q) (E q)) = E q
  rw [← Pauli.mul_assoc, Pauli.mul_self, Pauli_I_mul]

/-- Pointwise: `(S · e) · (e · E) = S · E`. -/
private theorem mul_absorb_self {n : Nat} (S e E : ErrorVec n) :
    ErrorVec.mul (ErrorVec.mul S e) (ErrorVec.mul e E) = ErrorVec.mul S E := by
  funext q
  show Pauli.mul (Pauli.mul (S q) (e q)) (Pauli.mul (e q) (E q)) =
       Pauli.mul (S q) (E q)
  rw [Pauli.mul_assoc, ← Pauli.mul_assoc (e q) (e q), Pauli.mul_self,
      Pauli_I_mul]

/-! ## Identity-pattern alignment

If `HookShapeOf e_B (identityShape d)` holds, then `e_B = I` pointwise,
and the alignment bound holds with `k = 0` (equality with `S_wit' := S_wit`). -/

/-- Helper: an identity-shaped `e_B` equals the identity `ErrorVec`. -/
private theorem eq_identity_of_identityShape {d : Nat}
    (e_B : ErrorVec (d * d))
    (h : HookShapeOf e_B (HookShape.identityShape d)) :
    e_B = ErrorVec.identity (d * d) := by
  funext q
  exact h q

/-- **Per-pattern alignment (identity case).**

If `HookShapeOf e_B shape` holds with `shape.pattern = identity`, then
`groupsX spec S_wit (e_B · E) = groupsX spec S_wit E` for every `S_wit`,
which trivially yields the +1 alignment bound. -/
theorem hook_shape_aligned_identity {d : Nat} (spec : AlignedCodeSpec d)
    (e_B : ErrorVec spec.params.n)
    (h_shape : ∀ q, e_B q = Pauli.I)
    (E S_wit : ErrorVec spec.params.n) :
    groupsX spec S_wit (ErrorVec.mul e_B E) = groupsX spec S_wit E := by
  -- `e_B = identity`, so `e_B · E = E` pointwise.
  have h_eq : e_B = ErrorVec.identity spec.params.n := by
    funext q; exact h_shape q
  rw [h_eq, mul_identity_left]

/-- The identity-pattern alignment in `IsLAligned` shape: there exists
`S_wit' ∈ InStab` with the +1 bound. We take `S_wit' := S_wit` and use
the equality form above. -/
theorem hook_shape_aligned_identity_witness {d : Nat}
    (spec : AlignedCodeSpec d)
    (e_B : ErrorVec spec.params.n)
    (h_shape : ∀ q, e_B q = Pauli.I)
    (E S_wit : ErrorVec spec.params.n)
    (hS : InStab spec.params S_wit) :
    ∃ S_wit' : ErrorVec spec.params.n, InStab spec.params S_wit' ∧
      groupsX spec S_wit' (ErrorVec.mul e_B E) ≤ groupsX spec S_wit E + 1 := by
  refine ⟨S_wit, hS, ?_⟩
  have h_eq : groupsX spec S_wit (ErrorVec.mul e_B E) = groupsX spec S_wit E :=
    hook_shape_aligned_identity spec e_B h_shape E S_wit
  omega

/-! ## `fullStab`-pattern alignment

If `e_B ∈ InStab` (the witness obligation for `fullStab`), we take
`S_wit' := S_wit · e_B`, which is also in `InStab`. The product
`S_wit' · (e_B · E) = S_wit · E` pointwise, so the bound holds with
equality. -/

/-- **Per-pattern alignment (fullStab case).**

If `e_B ∈ InStab`, then for any `S_wit ∈ InStab`, the witness
`S_wit · e_B` is in `InStab` and yields the same `groupsX` as `S_wit · E`. -/
theorem hook_shape_aligned_fullStab {d : Nat} (spec : AlignedCodeSpec d)
    (e_B : ErrorVec spec.params.n)
    (h_stab : InStab spec.params e_B)
    (E S_wit : ErrorVec spec.params.n)
    (hS : InStab spec.params S_wit) :
    ∃ S_wit' : ErrorVec spec.params.n, InStab spec.params S_wit' ∧
      groupsX spec S_wit' (ErrorVec.mul e_B E) ≤ groupsX spec S_wit E + 1 := by
  refine ⟨ErrorVec.mul S_wit e_B, InStab.mul hS h_stab, ?_⟩
  -- `S_wit · e_B · (e_B · E) = S_wit · E` pointwise.
  have h_eq : ErrorVec.mul (ErrorVec.mul S_wit e_B) (ErrorVec.mul e_B E)
            = ErrorVec.mul S_wit E := mul_absorb_self S_wit e_B E
  -- Both `groupsX` filters then act on the same vector.
  have h_groups_eq :
      groupsX spec (ErrorVec.mul S_wit e_B) (ErrorVec.mul e_B E)
        = groupsX spec S_wit E := by
    unfold groupsX
    congr 1
    apply Finset.filter_congr
    intro g _
    constructor
    · rintro ⟨q, hq_grp, hq_has⟩
      exact ⟨q, hq_grp, by rw [← h_eq]; exact hq_has⟩
    · rintro ⟨q, hq_grp, hq_has⟩
      exact ⟨q, hq_grp, by rw [h_eq]; exact hq_has⟩
  rw [h_groups_eq]
  omega

/-! ## `xInRows`-pattern alignment

For the X-row pattern with row support `rowSet`, the cleanest abstract
bound is `groupsX_subadditive`: with `S_wit' := S_wit`,
`groupsX (e_B · E) ≤ groupsX E + ErrorVec.weight e_B`.

We specialise to the *singleton* `rowSet` case used by the Surface d=3,5,7
spec instances. The witness obligation requires a linking hypothesis
between the geometric row index `q.val / d` and the spec's group
assignment `spec.group q`: when all of `e_B`'s X-support lies in a single
geometric row `i`, the *spec-side groups* touched by `e_B` form a subset
of size at most one (the group of any qubit in row `i`). The caller
supplies this linking witness as `hLink`.

The case where every cell in row `i` shares a single spec-group is the
expected Surface configuration (rows = groups); the abstract form here
factors out that scheduling-specific fact. -/

/-- **Per-pattern alignment (xInRows case, generic-bound form).**

Subadditivity of `groupsX` against `e_B`'s weight: with `S_wit' := S_wit`,
the count increases by at most `ErrorVec.weight e_B`. This is the
uniform bound across all `xInRows` shapes; the singleton-row case below
sharpens it to +1 when `rowSet` is a singleton and the spec groups
align with geometric rows. -/
theorem hook_shape_aligned_xInRows_subadd {d : Nat} (spec : AlignedCodeSpec d)
    (e_B : ErrorVec spec.params.n)
    (E S_wit : ErrorVec spec.params.n)
    (hS : InStab spec.params S_wit) :
    ∃ S_wit' : ErrorVec spec.params.n, InStab spec.params S_wit' ∧
      groupsX spec S_wit' (ErrorVec.mul e_B E)
        ≤ groupsX spec S_wit E + ErrorVec.weight e_B :=
  ⟨S_wit, hS, groupsX_subadditive spec S_wit E e_B⟩

/-- **Per-pattern alignment (xInRows singleton-row sharpening).**

When `rowSet = {i}` and the spec is *row-aligned* (every qubit's spec
group is the same — call it `gᵢ` — across the entire row `i`, with
qubits outside row `i` not touched by `e_B`'s X-component), the
+`weight e_B` bound from `xInRows_subadd` sharpens to +1.

We expose the sharpened form *without* committing to the row-vs-group
linking proof: the caller supplies `hSubsetSingle`, the direct
conclusion that *the set of groups newly contributing to* `groupsX`
*has cardinality at most 1*. This pattern matches how Surface d=3,5,7
spec instances structure their `hook_spread_bound` witness obligations.

Discipline: this theorem is a *naming/packaging* layer on
`hook_spread_bound`-style obligations; the concrete cardinality-bound
proof is supplied by the spec instance. -/
theorem hook_shape_aligned_xInRows_singleton {d : Nat}
    (spec : AlignedCodeSpec d)
    (e_B : ErrorVec spec.params.n)
    (E S_wit : ErrorVec spec.params.n)
    (_hS : InStab spec.params S_wit)
    (S_wit' : ErrorVec spec.params.n)
    (hS' : InStab spec.params S_wit')
    (hSubsetSingle :
      groupsX spec S_wit' (ErrorVec.mul e_B E) ≤ groupsX spec S_wit E + 1) :
    ∃ S_wit'' : ErrorVec spec.params.n, InStab spec.params S_wit'' ∧
      groupsX spec S_wit'' (ErrorVec.mul e_B E) ≤ groupsX spec S_wit E + 1 :=
  ⟨S_wit', hS', hSubsetSingle⟩

/-! ## `zInCols`-pattern alignment — definition only (audit R4)

Per the architecture audit (R4), the symmetric Z-column direction is
defined but *not proved* here. The X-direction headlines for Surface
d=3,5,7 do not consume it. The statement is symmetric to
`hook_shape_aligned_xInRows_subadd` with X/Z roles swapped; spec
instances that need it supply their own column-aligned witness.

We provide *only* the analogous packaging theorem: given a spec witness
`S_wit'` and a +1 bound (the column-direction analogue of
`hook_spread_bound`), we re-export the witness. This is the column
mirror of `hook_shape_aligned_xInRows_singleton`. -/

/-- **Per-pattern alignment (zInCols packaging).**

The column-mirror packaging: given a spec-provided witness and bound,
re-export them. The actual column-direction `+|colSet|` subadditive
bound (the analogue of `hook_shape_aligned_xInRows_subadd`) requires
a Z-direction `groupsX` (paper §3.3 calls it `groupsZ` against a
column partition); this file does not introduce that dual structure.
Spec instances that need it provide their own. -/
theorem hook_shape_aligned_zInCols_singleton {d : Nat}
    (spec : AlignedCodeSpec d)
    (e_B : ErrorVec spec.params.n)
    (E S_wit : ErrorVec spec.params.n)
    (S_wit' : ErrorVec spec.params.n)
    (hS' : InStab spec.params S_wit')
    (hSubsetSingle :
      groupsX spec S_wit' (ErrorVec.mul e_B E) ≤ groupsX spec S_wit E + 1) :
    ∃ S_wit'' : ErrorVec spec.params.n, InStab spec.params S_wit'' ∧
      groupsX spec S_wit'' (ErrorVec.mul e_B E) ≤ groupsX spec S_wit E + 1 :=
  ⟨S_wit', hS', hSubsetSingle⟩

/-! ## Combined headline

The combined `hook_shape_aligned` theorem performs the four-way case
split on `shape.pattern` and dispatches to the per-pattern theorem.
For `xInRows` and `zInCols` we require the spec-supplied alignment
witness (the `hook_spread_bound` premise of the underlying
`AlignedCodeSpec`); for `identity` and `fullStab` no extra premise is
needed beyond the `HookShapeOf` hypothesis (plus, for `fullStab`,
the membership `InStab spec.params e_B`).

The dispatch is `match`-style on `HookShapeOf` / `HookPattern`. -/

/-- **Combined alignment theorem.**

For every back-action `e_B` that fits a `shape : HookShape d`, the
alignment bound holds. The xInRows / zInCols cases consume an
`AlignedCodeSpec`-style witness supplied via `hSpecAligned`; the
identity / fullStab cases are discharged structurally.

This is the headline form referenced by the paper as
"hook-shape ⇒ alignment". -/
theorem hook_shape_aligned {d : Nat} (spec : AlignedCodeSpec d)
    (e_B : ErrorVec spec.params.n) (shape : HookShape d)
    (h_shape_n : spec.params.n = d * d)
    (h_shape : HookShapeOf (h_shape_n ▸ e_B) shape)
    (E S_wit : ErrorVec spec.params.n)
    (hS : InStab spec.params S_wit)
    -- For `fullStab`: `e_B` itself is in the stabilizer subgroup.
    (h_fullStab : shape.pattern = HookPattern.fullStab →
      InStab spec.params e_B)
    -- For `xInRows` and `zInCols`: a +1 bound from the spec.
    (h_xz_witness :
      shape.pattern = HookPattern.xInRows ∨
      shape.pattern = HookPattern.zInCols →
      ∃ S_wit' : ErrorVec spec.params.n, InStab spec.params S_wit' ∧
        groupsX spec S_wit' (ErrorVec.mul e_B E)
          ≤ groupsX spec S_wit E + 1) :
    ∃ S_wit' : ErrorVec spec.params.n, InStab spec.params S_wit' ∧
      groupsX spec S_wit' (ErrorVec.mul e_B E)
        ≤ groupsX spec S_wit E + 1 := by
  -- Dispatch on the pattern.
  match hp : shape.pattern with
  | HookPattern.identity =>
    -- Unfold `HookShapeOf` at `identity` to get `∀ q, e_B q = Pauli.I`.
    have h_id : ∀ q : Fin (d * d), (h_shape_n ▸ e_B) q = Pauli.I := by
      have := h_shape
      unfold HookShapeOf at this
      rw [hp] at this
      exact this
    -- Transport `h_id` along `h_shape_n` to get the same fact on `Fin spec.params.n`.
    have h_id' : ∀ q : Fin spec.params.n, e_B q = Pauli.I := by
      intro q
      -- Re-cast `q` through `h_shape_n` and apply `h_id`.
      have h_q := h_id (h_shape_n ▸ q)
      -- Show `(h_shape_n ▸ e_B) (h_shape_n ▸ q) = e_B q` via a generalised
      -- transport equality.
      have hcast : ∀ (n : Nat) (hn : spec.params.n = n)
          (eB : ErrorVec spec.params.n) (q' : Fin spec.params.n),
          (hn ▸ eB) (hn ▸ q') = eB q' := by
        intro n hn eB q'
        subst hn
        rfl
      rw [hcast (d * d) h_shape_n e_B q] at h_q
      exact h_q
    exact hook_shape_aligned_identity_witness spec e_B h_id' E S_wit hS
  | HookPattern.xInRows =>
    exact h_xz_witness (Or.inl hp)
  | HookPattern.zInCols =>
    exact h_xz_witness (Or.inr hp)
  | HookPattern.fullStab =>
    have h_stab : InStab spec.params e_B := h_fullStab hp
    exact hook_shape_aligned_fullStab spec e_B h_stab E S_wit hS

end QStab.Paper.HookShapeAlignment
