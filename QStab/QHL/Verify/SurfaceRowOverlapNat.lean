import QStab.QHL.Verify.SurfaceRowCharacterizationKeystone
import QStab.PauliOps

/-!
# Nat-arithmetic core of the surface-code row-overlap geometry

Pure `Nat`-arithmetic theorems about the flat classifier
`surfaceCellPauli d k q` (from `SurfaceRowCharacterizationKeystone`), where
`d`, `k`, `q : Nat`, grid linearization `q = d*row + col`, bulk plaquette
`(r,c) = (k/(d-1), k%(d-1))`, `numStab d = d²-1`, `nQubits d = d²`.

These are *ordinary* `Nat` theorems (no object logic), proved with the full power
of `omega`/`simp`/`decide`/`Nat`-lemmas — the same approach that cracked the
self-similarity bridge in `SurfaceSelfSimNat.lean`.  They establish:

* **Type uniformity** (`rowEntry_X_type` / `rowEntry_Z_type`): every entry of an
  X-type (resp. Z-type) row is in `{I, X}` (resp. `{I, Z}`).
* **Support membership** (`nonI_iff_suppMem`): a closed Boolean `(row,col)`
  characterization of where a stabilizer acts non-trivially.
* **Anti characterization** (`anticommutes_iff`): two different-type rows
  anticommute at `q` iff both are non-`I` there.
* **Overlap = stencil intersection** (the per-class `overlap_*` theorems): the
  shared non-`I` qubits of two different-type rows are exactly the explicit
  2-element set `{q0, q1}` (the stencil intersection), with `q0 ≠ q1`,
  `q0,q1 < d²`, and the *pin*: any shared non-`I` slot is `q0` or `q1`.

All overlap cases involve at least one bulk plaquette (verified `d = 3,5,7`):
bulk–bulk (edge-adjacent), bulk–top, bulk–right, bulk–left, bulk–bottom.
There are no boundary–boundary overlaps and same-type rows never overlap.
-/

namespace QHL.CodeLang.Surface.Verify

open QHL.CodeLang
open QHL.CodeLang.Surface

/-! ## The flat type predicate `rowIsXType` (k-only)

`rowIsXType d k` returns `true` when stabilizer `k` is an `X`-type row and `false`
when it is a `Z`-type row.  Bulk plaquettes have kind `X` iff `(r+c)` is odd
(matching `bulkKind`); boundary rows are `X` (top, bottom) or `Z` (right, left). -/

/-- Whether stabilizer `k` at distance `d` generates an `X`-type row. -/
def rowIsXType (d k : Nat) : Bool :=
  let dm1 := d - 1
  let bulkCount := dm1 * dm1
  let b := k - bulkCount
  let half := dm1 / 2
  if k < bulkCount then decide ((cellR d k + cellC d k) % 2 = 1)
  else if b < half then true        -- top-X
  else if b < 2 * half then false   -- right-Z
  else if b < 3 * half then false   -- left-Z
  else true                         -- bottom-X

/-! ## Type uniformity (Theorem 1)

Each row is purely one Pauli type: an `X`-type row has every entry in `{I, X}`,
and a `Z`-type row has every entry in `{I, Z}`.  Direct case analysis on the
branches of `surfaceCellPauli` and `bulkKind`. -/

/-- An `X`-type row's entry is always `I` or `X`. -/
theorem rowEntry_X_type (d k q : Nat) (hX : rowIsXType d k = true) :
    surfaceCellPauli d k q = Pauli.I ∨ surfaceCellPauli d k q = Pauli.X := by
  unfold surfaceCellPauli rowIsXType bulkKind at *
  -- split on the same branch structure
  by_cases hbulk : k < (d - 1) * (d - 1)
  · simp only [hbulk, if_true] at hX ⊢
    by_cases hband : inBulkBand d k q = true
    · simp only [hband, if_true]
      -- kind = X because (r+c) odd (from hX)
      have : (cellR d k + cellC d k) % 2 ≠ 0 := by
        simp only [decide_eq_true_eq] at hX; omega
      simp only [this]
      exact Or.inr rfl
    · simp only [Bool.not_eq_true] at hband
      simp only [hband]
      exact Or.inl rfl
  · simp only [hbulk, if_false] at hX ⊢
    by_cases hb1 : k - (d - 1) * (d - 1) < (d - 1) / 2
    · -- top-X
      simp only [hb1, if_true] at hX ⊢
      split <;> [exact Or.inr rfl; exact Or.inl rfl]
    · simp only [hb1, if_false] at hX ⊢
      by_cases hb2 : k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)
      · -- right-Z: hX is false, contradiction
        simp only [hb2, if_true] at hX
        exact absurd hX (by simp)
      · simp only [hb2, if_false] at hX ⊢
        by_cases hb3 : k - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)
        · -- left-Z: hX false, contradiction
          simp only [hb3, if_true] at hX
          exact absurd hX (by simp)
        · -- bottom-X
          simp only [hb3, if_false] at hX ⊢
          split <;> [exact Or.inr rfl; exact Or.inl rfl]

/-- A `Z`-type row's entry is always `I` or `Z`. -/
theorem rowEntry_Z_type (d k q : Nat) (hZ : rowIsXType d k = false) :
    surfaceCellPauli d k q = Pauli.I ∨ surfaceCellPauli d k q = Pauli.Z := by
  unfold surfaceCellPauli rowIsXType bulkKind at *
  by_cases hbulk : k < (d - 1) * (d - 1)
  · simp only [hbulk, if_true] at hZ ⊢
    by_cases hband : inBulkBand d k q = true
    · simp only [hband, if_true]
      have : (cellR d k + cellC d k) % 2 = 0 := by
        simp only [decide_eq_false_iff_not] at hZ; omega
      simp only [this]
      exact Or.inr rfl
    · simp only [Bool.not_eq_true] at hband
      simp only [hband]
      exact Or.inl rfl
  · simp only [hbulk, if_false] at hZ ⊢
    by_cases hb1 : k - (d - 1) * (d - 1) < (d - 1) / 2
    · -- top-X: hZ is true=false, contradiction
      simp only [hb1, if_true] at hZ
      exact absurd hZ (by simp)
    · simp only [hb1, if_false] at hZ ⊢
      by_cases hb2 : k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)
      · -- right-Z
        simp only [hb2, if_true] at hZ ⊢
        split <;> [exact Or.inr rfl; exact Or.inl rfl]
      · simp only [hb2, if_false] at hZ ⊢
        by_cases hb3 : k - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)
        · -- left-Z
          simp only [hb3, if_true] at hZ ⊢
          split <;> [exact Or.inr rfl; exact Or.inl rfl]
        · -- bottom-X: hZ true=false, contradiction
          simp only [hb3, if_false] at hZ
          exact absurd hZ (by simp)

/-! ## Anti characterization (Theorem 2)

For *different*-type rows `k1`, `k2`, the single-qubit Paulis anticommute at `q`
exactly when both rows act non-trivially there (one `X`, one `Z`).  This is a
direct consequence of type uniformity: each side is in `{I,X}` (resp. `{I,Z}`),
and `ErrorVec.Pauli.anticommutes` of two such is `true` iff one is `X` and the
other `Z`, i.e. iff both are non-`I`. -/

/-- Single-qubit anticommutation of two different-type rows at `q` holds iff both
act non-trivially at `q`. -/
theorem anticommutes_iff (d k1 k2 q : Nat)
    (hne : rowIsXType d k1 ≠ rowIsXType d k2) :
    ErrorVec.Pauli.anticommutes (surfaceCellPauli d k1 q) (surfaceCellPauli d k2 q) = true
      ↔ (surfaceCellPauli d k1 q ≠ Pauli.I ∧ surfaceCellPauli d k2 q ≠ Pauli.I) := by
  -- WLOG name the two types; one is X-type, the other Z-type.
  rcases Bool.eq_false_or_eq_true (rowIsXType d k1) with h1 | h1
  · -- `h1 : rowIsXType d k1 = true` ⇒ k1 is X-type, so k2 is Z-type
    have h2 : rowIsXType d k2 = false := by
      rcases Bool.eq_false_or_eq_true (rowIsXType d k2) with h | h
      · exact absurd (h1.trans h.symm) hne
      · exact h
    rcases rowEntry_X_type d k1 q h1 with e1 | e1 <;>
      rcases rowEntry_Z_type d k2 q h2 with e2 | e2 <;>
      simp [e1, e2, ErrorVec.Pauli.anticommutes]
  · -- `h1 : rowIsXType d k1 = false` ⇒ k1 is Z-type, so k2 is X-type
    have h2 : rowIsXType d k2 = true := by
      rcases Bool.eq_false_or_eq_true (rowIsXType d k2) with h | h
      · exact h
      · exact absurd (h1.trans h.symm) hne
    rcases rowEntry_Z_type d k1 q h1 with e1 | e1 <;>
      rcases rowEntry_X_type d k2 q h2 with e2 | e2 <;>
      simp [e1, e2, ErrorVec.Pauli.anticommutes]

/-! ## Support membership (the workhorse)

`suppMem d k q` is a closed Boolean over `(row, col) = (q/d, q%d)` and the
plaquette/boundary coordinates of `k` that holds exactly where stabilizer `k`
acts non-trivially.  `nonI_iff_suppMem` proves it equals `surfaceCellPauli ≠ I`.
This converts the geometric "both non-`I`" overlap condition into a conjunction
of decidable `(row,col)` constraints that `omega` can manipulate. -/

/-- Closed Boolean characterization of where stabilizer `k` acts non-trivially. -/
def suppMem (d k q : Nat) : Bool :=
  let row := q / d; let col := q % d
  let dm1 := d - 1
  let bulkCount := dm1 * dm1
  let b := k - bulkCount
  let half := dm1 / 2
  let r := cellR d k; let c := cellC d k
  if k < bulkCount then
    (decide (row = r) || decide (row = r + 1)) && (decide (col = c) || decide (col = c + 1))
      && decide (k < dm1 * dm1)
  else if b < half then
    decide (k < d * d - 1) && decide (row = 0) && (decide (col = 2 * b) || decide (col = 2 * b + 1))
  else if b < 2 * half then
    let bbR := b - half
    decide (col = dm1) && (decide (row = 2 * bbR) || decide (row = 2 * bbR + 1))
  else if b < 3 * half then
    let bbL := b - 2 * half
    decide (col = 0) && (decide (row = 2 * bbL + 1) || decide (row = 2 * bbL + 2))
  else
    let bbB := b - 3 * half
    decide (row = dm1) && (decide (col = 2 * bbB + 1) || decide (col = 2 * bbB + 2))

/-- For a non-`I` Pauli `p` and a `Prop`-decidable condition `cond`, the guarded
entry `ite cond p I` is non-`I` iff `cond` holds. -/
private theorem ite_pauli_nonI {cond : Prop} [Decidable cond] {p : Pauli}
    (hp : p ≠ Pauli.I) :
    (if cond then p else Pauli.I) ≠ Pauli.I ↔ decide cond = true := by
  by_cases h : cond <;> simp [h, hp]

/-- `surfaceCellPauli d k q` is non-`I` exactly when `suppMem d k q` holds. -/
theorem nonI_iff_suppMem (d k q : Nat) :
    surfaceCellPauli d k q ≠ Pauli.I ↔ suppMem d k q = true := by
  unfold surfaceCellPauli suppMem inBulkBand bulkKind cellRow cellCol
  -- Branch on the same five cases as `surfaceCellPauli` / `suppMem`.  In each
  -- branch both sides reduce to `ite <guard> kind I ≠ I ↔ <guard> = true` where
  -- `kind ∈ {X, Z}` (so `kind ≠ I`); the inner band guard is split by `by_cases`
  -- and each leaf is `decide`-able propositional reasoning.
  by_cases hbulk : k < (d - 1) * (d - 1)
  · -- bulk: result is `if band then (if parity then Z else X) else I`
    simp only [hbulk, if_true, decide_true, Bool.and_true]
    by_cases hband :
        ((decide (q / d = cellR d k) || decide (q / d = cellR d k + 1)) &&
          (decide (q % d = cellC d k) || decide (q % d = cellC d k + 1))) = true
    · -- band holds: kind ≠ I (true) and the band condition (RHS) is true
      rw [if_pos hband]
      have hkind : (if (cellR d k + cellC d k) % 2 = 0 then Pauli.Z else Pauli.X) ≠ Pauli.I := by
        split <;> simp
      exact iff_of_true hkind hband
    · rw [if_neg hband]
      exact iff_of_false (by simp) hband
  · simp only [hbulk, if_false]
    by_cases hb1 : k - (d - 1) * (d - 1) < (d - 1) / 2
    · simp only [hb1, if_true]
      by_cases hg :
          (decide (k < d * d - 1) && decide (q / d = 0) &&
            (decide (q % d = 2 * (k - (d - 1) * (d - 1))) ||
              decide (q % d = 2 * (k - (d - 1) * (d - 1)) + 1))) = true <;>
        simp only [hg, if_true, if_false, ne_eq, reduceCtorEq, not_false_eq_true,
          not_true_eq_false]
    · simp only [hb1, if_false]
      by_cases hb2 : k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)
      · simp only [hb2, if_true]
        by_cases hg :
            (decide (q % d = d - 1) &&
              (decide (q / d = 2 * (k - (d - 1) * (d - 1) - (d - 1) / 2)) ||
                decide (q / d = 2 * (k - (d - 1) * (d - 1) - (d - 1) / 2) + 1))) = true <;>
          simp only [hg, if_true, if_false, ne_eq, reduceCtorEq, not_false_eq_true,
            not_true_eq_false]
      · simp only [hb2, if_false]
        by_cases hb3 : k - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)
        · simp only [hb3, if_true]
          by_cases hg :
              (decide (q % d = 0) &&
                (decide (q / d = 2 * (k - (d - 1) * (d - 1) - 2 * ((d - 1) / 2)) + 1) ||
                  decide (q / d = 2 * (k - (d - 1) * (d - 1) - 2 * ((d - 1) / 2)) + 2))) = true <;>
            simp only [hg, if_true, if_false, ne_eq, reduceCtorEq, not_false_eq_true,
              not_true_eq_false]
        · simp only [hb3, if_false]
          by_cases hg :
              (decide (q / d = d - 1) &&
                (decide (q % d = 2 * (k - (d - 1) * (d - 1) - 3 * ((d - 1) / 2)) + 1) ||
                  decide (q % d = 2 * (k - (d - 1) * (d - 1) - 3 * ((d - 1) / 2)) + 2))) = true <;>
            simp only [hg, if_true, if_false, ne_eq, reduceCtorEq, not_false_eq_true,
              not_true_eq_false]

/-! ## `suppMem` in propositional `(row, col)` form, per class

Rewriting `suppMem` into a plain `Prop` over `row = q / d`, `col = q % d`, and the
plaquette/boundary coordinates of `k`.  These feed `omega` in the overlap proofs. -/

/-- Bulk `suppMem` as a `(row,col)` proposition. -/
theorem suppMem_bulk_prop (d k q : Nat) (hbulk : k < (d - 1) * (d - 1)) :
    suppMem d k q = true ↔
      (q / d = cellR d k ∨ q / d = cellR d k + 1) ∧
        (q % d = cellC d k ∨ q % d = cellC d k + 1) := by
  unfold suppMem
  simp only [hbulk, if_true, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, and_true]

/-- Top-X boundary `suppMem` as a `(row,col)` proposition. -/
theorem suppMem_top_prop (d k q : Nat) (hbulk : ¬ k < (d - 1) * (d - 1))
    (hb1 : k - (d - 1) * (d - 1) < (d - 1) / 2) :
    suppMem d k q = true ↔
      (k < d * d - 1 ∧ q / d = 0) ∧
        (q % d = 2 * (k - (d - 1) * (d - 1)) ∨ q % d = 2 * (k - (d - 1) * (d - 1)) + 1) := by
  unfold suppMem
  simp only [hbulk, if_false, hb1, if_true, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]

/-- Right-Z boundary `suppMem` as a `(row,col)` proposition. -/
theorem suppMem_right_prop (d k q : Nat) (hbulk : ¬ k < (d - 1) * (d - 1))
    (hb1 : ¬ k - (d - 1) * (d - 1) < (d - 1) / 2)
    (hb2 : k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) :
    suppMem d k q = true ↔
      q % d = d - 1 ∧
        (q / d = 2 * (k - (d - 1) * (d - 1) - (d - 1) / 2) ∨
          q / d = 2 * (k - (d - 1) * (d - 1) - (d - 1) / 2) + 1) := by
  unfold suppMem
  simp only [hbulk, if_false, hb1, hb2, if_true, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq]

/-- Left-Z boundary `suppMem` as a `(row,col)` proposition. -/
theorem suppMem_left_prop (d k q : Nat) (hbulk : ¬ k < (d - 1) * (d - 1))
    (hb1 : ¬ k - (d - 1) * (d - 1) < (d - 1) / 2)
    (hb2 : ¬ k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2))
    (hb3 : k - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)) :
    suppMem d k q = true ↔
      q % d = 0 ∧
        (q / d = 2 * (k - (d - 1) * (d - 1) - 2 * ((d - 1) / 2)) + 1 ∨
          q / d = 2 * (k - (d - 1) * (d - 1) - 2 * ((d - 1) / 2)) + 2) := by
  unfold suppMem
  simp only [hbulk, if_false, hb1, hb2, hb3, if_true, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq]

/-- Bottom-X boundary `suppMem` as a `(row,col)` proposition. -/
theorem suppMem_bottom_prop (d k q : Nat) (hbulk : ¬ k < (d - 1) * (d - 1))
    (hb1 : ¬ k - (d - 1) * (d - 1) < (d - 1) / 2)
    (hb2 : ¬ k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2))
    (hb3 : ¬ k - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)) :
    suppMem d k q = true ↔
      q / d = d - 1 ∧
        (q % d = 2 * (k - (d - 1) * (d - 1) - 3 * ((d - 1) / 2)) + 1 ∨
          q % d = 2 * (k - (d - 1) * (d - 1) - 3 * ((d - 1) / 2)) + 2) := by
  unfold suppMem
  simp only [hbulk, if_false, hb1, hb2, hb3, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]

/-! ## Coordinate decomposition

For `0 < d` and `q < d²`, the qubit `q` equals the grid point `d*R + C`
(with `C < d`) iff its row/col coordinates match `(R, C)`. -/

/-- `q = d * R + C` with `C < d` is equivalent to `q / d = R ∧ q % d = C`. -/
theorem grid_eq_iff (d q R C : Nat) (hd : 0 < d) (hC : C < d) :
    q = d * R + C ↔ (q / d = R ∧ q % d = C) := by
  constructor
  · intro h; subst h
    rw [Nat.mul_add_div hd, Nat.div_eq_of_lt hC, Nat.add_zero,
      Nat.mul_add_mod, Nat.mod_eq_of_lt hC]
    exact ⟨rfl, rfl⟩
  · rintro ⟨hR, hC'⟩
    have h := Nat.div_add_mod q d
    rw [hR, hC'] at h
    omega

/-! ## Overlap = stencil intersection (Theorems 3, 4, 5)

For two *different*-type rows the shared non-`I` qubits are exactly the explicit
2-element stencil intersection `{q0, q1}`.  Each theorem is decomposed by overlap
class-pair (every overlap involves at least one bulk plaquette).  We phrase the
shared-non-`I` condition through `nonI_iff_suppMem`/`suppMem_*_prop` and discharge
the `(row, col)` arithmetic by `omega` after `grid_eq_iff`.  Each statement also
records `q0 ≠ q1` and `q0, q1 < d²` (in-range + distinct), and the *pin* (any
shared non-`I` slot is `q0` or `q1`) is exactly the forward direction. -/

/-- **Bulk–Top overlap.**  A bulk plaquette `k1` (with `cellR d k1 = 0`,
`cellC d k1 = 2·b2`) and a top-X row `k2` (boundary index `b2`) share non-`I`
qubits exactly at `q0 = 2·b2`, `q1 = 2·b2 + 1` (both in row 0). -/
theorem overlap_bulk_top (d k1 k2 : Nat) (hd : 0 < d)
    (h1 : k1 < (d - 1) * (d - 1))
    (h2b : ¬ k2 < (d - 1) * (d - 1))
    (h2t : k2 - (d - 1) * (d - 1) < (d - 1) / 2)
    (h2lt : k2 < d * d - 1)
    (hr : cellR d k1 = 0) (hc : cellC d k1 = 2 * (k2 - (d - 1) * (d - 1)))
    (hb2 : 2 * (k2 - (d - 1) * (d - 1)) + 1 < d) :
    ∀ q, q < d * d →
      ((surfaceCellPauli d k1 q ≠ Pauli.I ∧ surfaceCellPauli d k2 q ≠ Pauli.I)
        ↔ (q = 2 * (k2 - (d - 1) * (d - 1)) ∨ q = 2 * (k2 - (d - 1) * (d - 1)) + 1)) := by
  intro q hq
  rw [nonI_iff_suppMem, nonI_iff_suppMem, suppMem_bulk_prop d k1 q h1,
    suppMem_top_prop d k2 q h2b h2t, hr, hc]
  have hqval : q = d * (q / d) + q % d := (Nat.div_add_mod q d).symm
  have hlt : q % d < d := Nat.mod_lt q hd
  -- both supports are in row 0, cols {2b2, 2b2+1}; q is determined by col.
  constructor
  · rintro ⟨_, ⟨_, hrow0⟩, hcol⟩
    rw [hrow0, Nat.mul_zero, Nat.zero_add] at hqval
    omega
  · -- both targets lie in row 0; pick row = 0 and the matching col.
    rintro (h0 | h0) <;> subst h0 <;>
      [(have hdiv : (2 * (k2 - (d - 1) * (d - 1))) / d = 0 := Nat.div_eq_of_lt (by omega)
        have hmod : (2 * (k2 - (d - 1) * (d - 1))) % d = 2 * (k2 - (d - 1) * (d - 1)) :=
          Nat.mod_eq_of_lt (by omega));
       (have hdiv : (2 * (k2 - (d - 1) * (d - 1)) + 1) / d = 0 := Nat.div_eq_of_lt hb2
        have hmod : (2 * (k2 - (d - 1) * (d - 1)) + 1) % d = 2 * (k2 - (d - 1) * (d - 1)) + 1 :=
          Nat.mod_eq_of_lt hb2)] <;>
      exact ⟨⟨Or.inl hdiv, by omega⟩, ⟨h2lt, hdiv⟩, by omega⟩

/-- **Bulk–Right overlap.**  A bulk plaquette `k1` (with `cellR d k1 = 2·bbR`,
`cellC d k1 = (d-1) - 1`) and a right-Z row `k2` (relative index `bbR`) share
non-`I` qubits exactly at `q0 = d·(2·bbR) + (d-1)`, `q1 = d·(2·bbR+1) + (d-1)`
(both in column `d-1`). -/
theorem overlap_bulk_right (d k1 k2 : Nat) (hd : 0 < d)
    (h1 : k1 < (d - 1) * (d - 1))
    (h2b : ¬ k2 < (d - 1) * (d - 1))
    (h2t : ¬ k2 - (d - 1) * (d - 1) < (d - 1) / 2)
    (h2r : k2 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2))
    (hr : cellR d k1 = 2 * (k2 - (d - 1) * (d - 1) - (d - 1) / 2))
    (hc : cellC d k1 = (d - 1) - 1)
    (hR1 : 2 * (k2 - (d - 1) * (d - 1) - (d - 1) / 2) + 1 < d) :
    ∀ q, q < d * d →
      ((surfaceCellPauli d k1 q ≠ Pauli.I ∧ surfaceCellPauli d k2 q ≠ Pauli.I)
        ↔ (q = d * (2 * (k2 - (d - 1) * (d - 1) - (d - 1) / 2)) + (d - 1) ∨
            q = d * (2 * (k2 - (d - 1) * (d - 1) - (d - 1) / 2) + 1) + (d - 1))) := by
  intro q hq
  rw [nonI_iff_suppMem, nonI_iff_suppMem, suppMem_bulk_prop d k1 q h1,
    suppMem_right_prop d k2 q h2b h2t h2r, hr, hc,
    grid_eq_iff d q (2 * (k2 - (d - 1) * (d - 1) - (d - 1) / 2)) (d - 1) hd (by omega),
    grid_eq_iff d q (2 * (k2 - (d - 1) * (d - 1) - (d - 1) / 2) + 1) (d - 1) hd (by omega)]
  have hlt : q % d < d := Nat.mod_lt q hd
  -- right forces col = d-1; bulk forces row ∈ {2bbR, 2bbR+1}.
  constructor
  · rintro ⟨⟨hrow, _⟩, hcol, _⟩
    rcases hrow with h | h <;> [left; right] <;> exact ⟨h, hcol⟩
  · rintro (⟨hrow, hcol⟩ | ⟨hrow, hcol⟩) <;>
      exact ⟨⟨by omega, by omega⟩, hcol, by omega⟩

/-- **Bulk–Left overlap.**  A bulk plaquette `k1` (with `cellR d k1 = 2·bbL+1`,
`cellC d k1 = 0`) and a left-Z row `k2` (relative index `bbL`) share non-`I`
qubits exactly at `q0 = d·(2·bbL+1)`, `q1 = d·(2·bbL+2)` (both in column `0`). -/
theorem overlap_bulk_left (d k1 k2 : Nat) (hd : 0 < d)
    (h1 : k1 < (d - 1) * (d - 1))
    (h2b : ¬ k2 < (d - 1) * (d - 1))
    (h2t : ¬ k2 - (d - 1) * (d - 1) < (d - 1) / 2)
    (h2r : ¬ k2 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2))
    (h2l : k2 - (d - 1) * (d - 1) < 3 * ((d - 1) / 2))
    (hr : cellR d k1 = 2 * (k2 - (d - 1) * (d - 1) - 2 * ((d - 1) / 2)) + 1)
    (hc : cellC d k1 = 0)
    (_hR1 : 2 * (k2 - (d - 1) * (d - 1) - 2 * ((d - 1) / 2)) + 2 < d) :
    ∀ q, q < d * d →
      ((surfaceCellPauli d k1 q ≠ Pauli.I ∧ surfaceCellPauli d k2 q ≠ Pauli.I)
        ↔ (q = d * (2 * (k2 - (d - 1) * (d - 1) - 2 * ((d - 1) / 2)) + 1) + 0 ∨
            q = d * (2 * (k2 - (d - 1) * (d - 1) - 2 * ((d - 1) / 2)) + 2) + 0)) := by
  intro q hq
  rw [nonI_iff_suppMem, nonI_iff_suppMem, suppMem_bulk_prop d k1 q h1,
    suppMem_left_prop d k2 q h2b h2t h2r h2l, hr, hc,
    grid_eq_iff d q (2 * (k2 - (d - 1) * (d - 1) - 2 * ((d - 1) / 2)) + 1) 0 hd hd,
    grid_eq_iff d q (2 * (k2 - (d - 1) * (d - 1) - 2 * ((d - 1) / 2)) + 2) 0 hd hd]
  have hlt : q % d < d := Nat.mod_lt q hd
  -- left forces col = 0; bulk forces row ∈ {2bbL+1, 2bbL+2}.
  constructor
  · rintro ⟨⟨hrow, _⟩, hcol, _⟩
    rcases hrow with h | h <;> [left; right] <;> exact ⟨h, hcol⟩
  · rintro (⟨hrow, hcol⟩ | ⟨hrow, hcol⟩) <;>
      exact ⟨⟨by omega, by omega⟩, hcol, by omega⟩

/-- **Bulk–Bottom overlap.**  A bulk plaquette `k1` (with `cellR d k1 = (d-1)-1`,
`cellC d k1 = 2·bbB+1`) and a bottom-X row `k2` (relative index `bbB`) share
non-`I` qubits exactly at `q0 = d·(d-1) + (2·bbB+1)`, `q1 = d·(d-1) + (2·bbB+2)`
(both in row `d-1`). -/
theorem overlap_bulk_bottom (d k1 k2 : Nat) (hd : 0 < d)
    (h1 : k1 < (d - 1) * (d - 1))
    (h2b : ¬ k2 < (d - 1) * (d - 1))
    (h2t : ¬ k2 - (d - 1) * (d - 1) < (d - 1) / 2)
    (h2r : ¬ k2 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2))
    (h2l : ¬ k2 - (d - 1) * (d - 1) < 3 * ((d - 1) / 2))
    (hr : cellR d k1 = (d - 1) - 1)
    (hc : cellC d k1 = 2 * (k2 - (d - 1) * (d - 1) - 3 * ((d - 1) / 2)) + 1)
    (hC1 : 2 * (k2 - (d - 1) * (d - 1) - 3 * ((d - 1) / 2)) + 2 < d) :
    ∀ q, q < d * d →
      ((surfaceCellPauli d k1 q ≠ Pauli.I ∧ surfaceCellPauli d k2 q ≠ Pauli.I)
        ↔ (q = d * (d - 1) + (2 * (k2 - (d - 1) * (d - 1) - 3 * ((d - 1) / 2)) + 1) ∨
            q = d * (d - 1) + (2 * (k2 - (d - 1) * (d - 1) - 3 * ((d - 1) / 2)) + 2))) := by
  intro q hq
  rw [nonI_iff_suppMem, nonI_iff_suppMem, suppMem_bulk_prop d k1 q h1,
    suppMem_bottom_prop d k2 q h2b h2t h2r h2l, hr, hc,
    grid_eq_iff d q (d - 1) (2 * (k2 - (d - 1) * (d - 1) - 3 * ((d - 1) / 2)) + 1) hd (by omega),
    grid_eq_iff d q (d - 1) (2 * (k2 - (d - 1) * (d - 1) - 3 * ((d - 1) / 2)) + 2) hd hC1]
  have hlt : q % d < d := Nat.mod_lt q hd
  -- bottom forces row = d-1; bulk forces col ∈ {2bbB+1, 2bbB+2}.
  constructor
  · rintro ⟨⟨_, hcol⟩, hrow, _⟩
    rcases hcol with h | h <;> [left; right] <;> exact ⟨hrow, h⟩
  · rintro (⟨hrow, hcol⟩ | ⟨hrow, hcol⟩) <;>
      exact ⟨⟨by omega, by omega⟩, hrow, by omega⟩

/-- **Bulk–Bulk overlap, horizontal edge-adjacency** (same rows, adjacent cols).
Two bulk plaquettes `k1`, `k2` with `cellR d k1 = cellR d k2` and
`cellC d k2 = cellC d k1 + 1` share non-`I` qubits exactly in the shared column
`cellC d k1 + 1`, at `q0 = d·r1 + (c1+1)`, `q1 = d·(r1+1) + (c1+1)`. -/
theorem overlap_bulk_bulk_horiz (d k1 k2 : Nat) (hd : 0 < d)
    (h1 : k1 < (d - 1) * (d - 1)) (h2 : k2 < (d - 1) * (d - 1))
    (hrEq : cellR d k1 = cellR d k2) (hcAdj : cellC d k2 = cellC d k1 + 1)
    (hcLt : cellC d k1 + 1 < d) :
    ∀ q, q < d * d →
      ((surfaceCellPauli d k1 q ≠ Pauli.I ∧ surfaceCellPauli d k2 q ≠ Pauli.I)
        ↔ (q = d * cellR d k1 + (cellC d k1 + 1) ∨
            q = d * (cellR d k1 + 1) + (cellC d k1 + 1))) := by
  intro q hq
  rw [nonI_iff_suppMem, nonI_iff_suppMem, suppMem_bulk_prop d k1 q h1,
    suppMem_bulk_prop d k2 q h2, hrEq, hcAdj,
    grid_eq_iff d q (cellR d k2) (cellC d k1 + 1) hd hcLt,
    grid_eq_iff d q (cellR d k2 + 1) (cellC d k1 + 1) hd hcLt]
  have hlt : q % d < d := Nat.mod_lt q hd
  -- shared col is c1+1; shared rows are {r2, r2+1}.
  constructor
  · rintro ⟨⟨hrow1, hcol1⟩, hrow2, hcol2⟩
    rcases hrow2 with h | h <;> [left; right] <;> exact ⟨h, by omega⟩
  · rintro (⟨hrow, hcol⟩ | ⟨hrow, hcol⟩) <;>
      exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩

/-- **Bulk–Bulk overlap, vertical edge-adjacency** (same cols, adjacent rows).
Two bulk plaquettes `k1`, `k2` with `cellC d k1 = cellC d k2` and
`cellR d k2 = cellR d k1 + 1` share non-`I` qubits exactly in the shared row
`cellR d k1 + 1`, at `q0 = d·(r1+1) + c1`, `q1 = d·(r1+1) + (c1+1)`. -/
theorem overlap_bulk_bulk_vert (d k1 k2 : Nat) (hd : 0 < d)
    (h1 : k1 < (d - 1) * (d - 1)) (h2 : k2 < (d - 1) * (d - 1))
    (hcEq : cellC d k1 = cellC d k2) (hrAdj : cellR d k2 = cellR d k1 + 1)
    (hcLt : cellC d k1 + 1 < d) :
    ∀ q, q < d * d →
      ((surfaceCellPauli d k1 q ≠ Pauli.I ∧ surfaceCellPauli d k2 q ≠ Pauli.I)
        ↔ (q = d * (cellR d k1 + 1) + cellC d k1 ∨
            q = d * (cellR d k1 + 1) + (cellC d k1 + 1))) := by
  intro q hq
  rw [nonI_iff_suppMem, nonI_iff_suppMem, suppMem_bulk_prop d k1 q h1,
    suppMem_bulk_prop d k2 q h2, hcEq, hrAdj,
    grid_eq_iff d q (cellR d k1 + 1) (cellC d k2) hd (by omega),
    grid_eq_iff d q (cellR d k1 + 1) (cellC d k2 + 1) hd (by omega)]
  have hlt : q % d < d := Nat.mod_lt q hd
  -- shared row is r1+1; shared cols are {c2, c2+1}.
  constructor
  · rintro ⟨⟨hrow1, hcol1⟩, hrow2, hcol2⟩
    rcases hcol2 with h | h <;> [left; right] <;> exact ⟨by omega, h⟩
  · rintro (⟨hrow, hcol⟩ | ⟨hrow, hcol⟩) <;>
      exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩

/-! ## In-range + distinct (Theorem 5)

For each overlap class the two overlap qubits `q0`, `q1` are distinct and lie in
range `q0, q1 < d²`.  These are pure arithmetic facts about the closed forms
(distinctness is immediate; range follows from the per-class edge bounds). -/

/-- Top-overlap `q0 = 2b`, `q1 = 2b+1` are distinct and `< d²`. -/
theorem overlap_top_range (d b : Nat) (hd : 0 < d) (hb : 2 * b + 1 < d) :
    2 * b ≠ 2 * b + 1 ∧ 2 * b < d * d ∧ 2 * b + 1 < d * d := by
  have : d ≤ d * d := Nat.le_mul_of_pos_left d hd
  omega

/-- Right-overlap `q0 = d·(2r)+(d-1)`, `q1 = d·(2r+1)+(d-1)` are distinct, `< d²`. -/
theorem overlap_right_range (d r : Nat) (hd : 0 < d) (hr : 2 * r + 1 < d) :
    d * (2 * r) + (d - 1) ≠ d * (2 * r + 1) + (d - 1) ∧
      d * (2 * r) + (d - 1) < d * d ∧ d * (2 * r + 1) + (d - 1) < d * d := by
  have e1 : d * (2 * r) + d = d * (2 * r + 1) := (Nat.mul_succ d (2 * r)).symm
  have e2 : d * (2 * r + 1) + d = d * (2 * r + 2) := (Nat.mul_succ d (2 * r + 1)).symm
  have b1 : d * (2 * r + 1) ≤ d * d := Nat.mul_le_mul_left d (by omega)
  have b2 : d * (2 * r + 2) ≤ d * d := Nat.mul_le_mul_left d (by omega)
  omega

/-- Left-overlap `q0 = d·(2l+1)`, `q1 = d·(2l+2)` are distinct and `< d²`. -/
theorem overlap_left_range (d l : Nat) (hd : 0 < d) (hl : 2 * l + 2 < d) :
    d * (2 * l + 1) + 0 ≠ d * (2 * l + 2) + 0 ∧
      d * (2 * l + 1) + 0 < d * d ∧ d * (2 * l + 2) + 0 < d * d := by
  have e1 : d * (2 * l + 1) + d = d * (2 * l + 2) := (Nat.mul_succ d (2 * l + 1)).symm
  have b2 : d * (2 * l + 2) < d * d := (Nat.mul_lt_mul_left hd).mpr (by omega)
  omega

/-- Bottom-overlap `q0 = d·(d-1)+(2b+1)`, `q1 = d·(d-1)+(2b+2)` are distinct, `< d²`. -/
theorem overlap_bottom_range (d b : Nat) (hd : 0 < d) (hb : 2 * b + 2 < d) :
    d * (d - 1) + (2 * b + 1) ≠ d * (d - 1) + (2 * b + 2) ∧
      d * (d - 1) + (2 * b + 1) < d * d ∧ d * (d - 1) + (2 * b + 2) < d * d := by
  -- d·(d-1) + d = d·d  (since d ≥ 1)
  have hkey : d * (d - 1) + d = d * d := by
    have : d - 1 + 1 = d := by omega
    rw [← Nat.mul_succ]; rw [Nat.succ_eq_add_one, this]
  omega

/-- Bulk–bulk horizontal-overlap `q0 = d·r+(c+1)`, `q1 = d·(r+1)+(c+1)` are
distinct and `< d²` (given `r+1 < d`, `c+1 < d`). -/
theorem overlap_bulk_bulk_horiz_range (d r c : Nat) (hd : 0 < d)
    (hr : r + 1 < d) (hc : c + 1 < d) :
    d * r + (c + 1) ≠ d * (r + 1) + (c + 1) ∧
      d * r + (c + 1) < d * d ∧ d * (r + 1) + (c + 1) < d * d := by
  have e1 : d * r + d = d * (r + 1) := (Nat.mul_succ d r).symm
  have e2 : d * (r + 1) + d = d * (r + 1 + 1) := (Nat.mul_succ d (r + 1)).symm
  have b1 : d * (r + 1) ≤ d * d := Nat.mul_le_mul_left d (by omega)
  have b2 : d * (r + 1 + 1) ≤ d * d := Nat.mul_le_mul_left d (by omega)
  omega

/-- Bulk–bulk vertical-overlap `q0 = d·(r+1)+c`, `q1 = d·(r+1)+(c+1)` are
distinct and `< d²` (given `r+1 < d`, `c+1 < d`). -/
theorem overlap_bulk_bulk_vert_range (d r c : Nat) (_hd : 0 < d)
    (hr : r + 1 < d) (hc : c + 1 < d) :
    d * (r + 1) + c ≠ d * (r + 1) + (c + 1) ∧
      d * (r + 1) + c < d * d ∧ d * (r + 1) + (c + 1) < d * d := by
  have e1 : d * (r + 1) + d = d * (r + 1 + 1) := (Nat.mul_succ d (r + 1)).symm
  have b1 : d * (r + 1 + 1) ≤ d * d := Nat.mul_le_mul_left d (by omega)
  omega

end QHL.CodeLang.Surface.Verify
