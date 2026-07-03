import QStab.QClifford.Compile.SurfaceXIdx
import QStab.QClifford.Compile.SurfaceHValid
import QStab.QClifford.Compile.CSSSplit
import QStab.QHL.Source.Examples.SurfaceParametricUpperBound

/-!
# The Z-side cleaning leg (the pivot-peel maximal-isotropic proof)

The four **crux lemmas** — one per no-pivot cell class, each saying "a `Z`-type vector that
commutes with the given X-check and is `I` on every row-major-earlier support cell is `I` on
the last (this) cell".  Extracted from `notes/validate_surface_maxiso.py`:

* **A** `(0, 2b+1)` — forced by `topX b`      (2-cell support);
* **B** `(r, c)` with `(r+c)` odd, `r,c ≥ 1` — forced by `bulkX (r-1) (c-1)` (4-cell);
* **C** `(d-1, 2bb+2)` — forced by `bottomX bb` (2-cell);
* **D** `(d-1, 0)` — forced by `X̄` itself (column-0 support).

Each is a `Finset.filter`-cardinality parity argument (template:
`mkSurfaceAttackerX_commutes_with_stabilizers`): the check's support concentrates the filter on
its cells, the `hprev` hypotheses kill the earlier ones, and even parity forces the last to `I`.
-/

namespace QStab.QClifford.Compile

open QStab QStab.QClifford.PCC.SurfaceNZ QStab.Examples.SurfaceParametric
open QHL.Source.Examples.SurfaceParametricUpperBound

/-- Decode of the `topX b` boundary X-check (mirror of `classifyStab_topXIdx`). -/
theorem decode_topXIdx (d b row col : Nat) (_hd : 1 < d) (hb : b < (d - 1) / 2) :
    decodeStabPauliAt d (topXIdx d b) row col
      = if row = 0 ∧ (col = 2 * b ∨ col = 2 * b + 1) then Pauli.X else Pauli.I := by
  unfold decodeStabPauliAt topXIdx
  have hge : (d - 1) * (d - 1) ≤ (d - 1) * (d - 1) + b := by omega
  rw [if_neg (Nat.not_lt_of_ge hge)]
  set b' := (d - 1) * (d - 1) + b - (d - 1) * (d - 1) with hb'def
  have hb'_eq : b' = b := by rw [hb'def]; omega
  rw [if_pos (by rw [hb'_eq]; exact hb), hb'_eq]

/-- Row-major division for last-row cells: `(d·(d−1)+c)/d = d−1` (`c < d`).  The one new
primitive over crux A — omega cannot divide by the variable `d`. -/
theorem lastRow_div (d c : Nat) (hd : 0 < d) (hc : c < d) :
    (d * (d - 1) + c) / d = d - 1 := by
  rw [Nat.mul_add_div hd, Nat.div_eq_of_lt hc, Nat.add_zero]

/-- Row-major remainder for last-row cells: `(d·(d−1)+c) % d = c` (`c < d`). -/
theorem lastRow_mod (d c : Nat) (hc : c < d) :
    (d * (d - 1) + c) % d = c := by
  rw [Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt hc

/-- **Crux A** (template-calibrator).  A `Z`-type vector commuting with `topX b` that is `I` on
the left support cell `(0, 2b)` is `I` on the right cell `(0, 2b+1)`. -/
theorem crux_topX (d : Nat) (hd0 : 0 < d) (hd : 1 < d) (b : Nat) (hb : b < (d - 1) / 2)
    (z : ErrorVec (d * d)) (hzt : ∀ q, z q = Pauli.Z ∨ z q = Pauli.I)
    (hpar : ErrorVec.parity
        (mkSurfaceStabilizers d hd0 ⟨topXIdx d b, topXIdx_lt_numStab d b hd hb⟩) z = false)
    (hprev : z (gridFin d hd0 (0, 2 * b)) = Pauli.I) :
    z (gridFin d hd0 (0, 2 * b + 1)) = Pauli.I := by
  -- support cells sit in-range (columns 2b, 2b+1 < d)
  have hb2 : 2 * b + 1 < d := by omega
  have hval0 : (gridFin d hd0 (0, 2 * b)).val = 2 * b := by
    rw [gridFin_val_of_lt d hd0 hd0 (by omega)]; omega
  have hval1 : (gridFin d hd0 (0, 2 * b + 1)).val = 2 * b + 1 := by
    rw [gridFin_val_of_lt d hd0 hd0 hb2]; omega
  -- the stabilizer value at any qubit
  have hstab : ∀ q : Fin (d * d),
      mkSurfaceStabilizers d hd0 ⟨topXIdx d b, topXIdx_lt_numStab d b hd hb⟩ q
        = if q.val / d = 0 ∧ (q.val % d = 2 * b ∨ q.val % d = 2 * b + 1)
          then Pauli.X else Pauli.I := by
    intro q; simp only [mkSurfaceStabilizers]; exact decode_topXIdx d b _ _ hd hb
  by_contra hne
  have hZ : z (gridFin d hd0 (0, 2 * b + 1)) = Pauli.Z := (hzt _).resolve_right hne
  -- the anticommuting-position filter is exactly {(0, 2b+1)}
  have hfilter : (Finset.univ.filter fun q =>
      ErrorVec.Pauli.anticommutes
        (mkSurfaceStabilizers d hd0 ⟨topXIdx d b, topXIdx_lt_numStab d b hd hb⟩ q) (z q) = true)
      = {gridFin d hd0 (0, 2 * b + 1)} := by
    apply Finset.ext; intro q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hq
      rw [hstab q] at hq
      -- stab q ≠ I, so the guard holds and q is one of the two support cells
      by_cases hg : q.val / d = 0 ∧ (q.val % d = 2 * b ∨ q.val % d = 2 * b + 1)
      · rw [if_pos hg] at hq
        have hqval : q.val = q.val % d := by
          conv_lhs => rw [← Nat.div_add_mod q.val d, hg.1]
          omega
        rcases hg.2 with h | h
        · -- q = (0, 2b); but z there is I, contradiction with anticommutes X (z q)
          exfalso
          have : q = gridFin d hd0 (0, 2 * b) := Fin.ext (by rw [hval0, hqval, h])
          rw [this, hprev] at hq; nomatch hq
        · exact Fin.ext (by rw [hval1, hqval, h])
      · rw [if_neg hg] at hq; simp [ErrorVec.Pauli.anticommutes] at hq
    · intro hq; subst hq
      rw [hstab _, if_pos ⟨by rw [hval1]; exact Nat.div_eq_of_lt hb2,
        Or.inr (by rw [hval1]; exact Nat.mod_eq_of_lt hb2)⟩, hZ]
      decide
  rw [ErrorVec.parity, hfilter, Finset.card_singleton] at hpar
  nomatch hpar

/-- Decode of the `bottomX b` boundary X-check (mirror of `classifyStab_bottomXIdx`). -/
theorem decode_bottomXIdx (d b row col : Nat) (_hd : 1 < d) (_hb : b < (d - 1) / 2) :
    decodeStabPauliAt d (bottomXIdx d b) row col
      = if row = d - 1 ∧ (col = 2 * b + 1 ∨ col = 2 * b + 2) then Pauli.X else Pauli.I := by
  unfold decodeStabPauliAt bottomXIdx
  have hge : (d - 1) * (d - 1) ≤ (d - 1) * (d - 1) + 3 * ((d - 1) / 2) + b := by omega
  rw [if_neg (Nat.not_lt_of_ge hge)]
  set b' := (d - 1) * (d - 1) + 3 * ((d - 1) / 2) + b - (d - 1) * (d - 1) with hb'def
  have hb'_eq : b' = 3 * ((d - 1) / 2) + b := by rw [hb'def]; omega
  rw [if_neg (by rw [hb'_eq]; omega), if_neg (by rw [hb'_eq]; omega),
    if_neg (by rw [hb'_eq]; omega)]
  have h_sub : b' - 3 * ((d - 1) / 2) = b := by rw [hb'_eq]; omega
  rw [h_sub]

/-- **Crux C** (bottomX).  A `Z`-type vector commuting with `bottomX b` that is `I` on the left
support cell `(d-1, 2b+1)` is `I` on the right cell `(d-1, 2b+2)`. -/
theorem crux_bottomX (d : Nat) (hd0 : 0 < d) (hd : 1 < d) (hodd : d % 2 = 1)
    (b : Nat) (hb : b < (d - 1) / 2) (z : ErrorVec (d * d)) (hzt : ∀ q, z q = Pauli.Z ∨ z q = Pauli.I)
    (hpar : ErrorVec.parity
        (mkSurfaceStabilizers d hd0 ⟨bottomXIdx d b, bottomXIdx_lt_numStab d b hd hodd hb⟩)
        z = false)
    (hprev : z (gridFin d hd0 (d - 1, 2 * b + 1)) = Pauli.I) :
    z (gridFin d hd0 (d - 1, 2 * b + 2)) = Pauli.I := by
  have hc1 : 2 * b + 1 < d := by omega
  have hc2 : 2 * b + 2 < d := by omega
  have hr : d - 1 < d := by omega
  have hval0 : (gridFin d hd0 (d - 1, 2 * b + 1)).val = d * (d - 1) + (2 * b + 1) :=
    gridFin_val_of_lt d hd0 hr hc1
  have hval1 : (gridFin d hd0 (d - 1, 2 * b + 2)).val = d * (d - 1) + (2 * b + 2) :=
    gridFin_val_of_lt d hd0 hr hc2
  have hstab : ∀ q : Fin (d * d),
      mkSurfaceStabilizers d hd0 ⟨bottomXIdx d b, bottomXIdx_lt_numStab d b hd hodd hb⟩ q
        = if q.val / d = d - 1 ∧ (q.val % d = 2 * b + 1 ∨ q.val % d = 2 * b + 2)
          then Pauli.X else Pauli.I := by
    intro q; simp only [mkSurfaceStabilizers]; exact decode_bottomXIdx d b _ _ hd hb
  by_contra hne
  have hZ : z (gridFin d hd0 (d - 1, 2 * b + 2)) = Pauli.Z := (hzt _).resolve_right hne
  have hfilter : (Finset.univ.filter fun q =>
      ErrorVec.Pauli.anticommutes
        (mkSurfaceStabilizers d hd0
          ⟨bottomXIdx d b, bottomXIdx_lt_numStab d b hd hodd hb⟩ q) (z q) = true)
      = {gridFin d hd0 (d - 1, 2 * b + 2)} := by
    apply Finset.ext; intro q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hq
      rw [hstab q] at hq
      by_cases hg : q.val / d = d - 1 ∧ (q.val % d = 2 * b + 1 ∨ q.val % d = 2 * b + 2)
      · rw [if_pos hg] at hq
        have hqval : q.val = d * (d - 1) + q.val % d := by
          have h := Nat.div_add_mod q.val d; rw [hg.1] at h; omega
        rcases hg.2 with h | h
        · exfalso
          have : q = gridFin d hd0 (d - 1, 2 * b + 1) := Fin.ext (by rw [hval0, hqval, h])
          rw [this, hprev] at hq; nomatch hq
        · exact Fin.ext (by rw [hval1, hqval, h])
      · rw [if_neg hg] at hq; simp [ErrorVec.Pauli.anticommutes] at hq
    · intro hq; subst hq
      rw [hstab _, if_pos ⟨by rw [hval1]; exact lastRow_div d (2 * b + 2) hd0 hc2,
        Or.inr (by rw [hval1]; exact lastRow_mod d (2 * b + 2) hc2)⟩, hZ]
      decide
  rw [ErrorVec.parity, hfilter, Finset.card_singleton] at hpar
  nomatch hpar

/-- **Crux D** (X̄).  A `Z`-type vector commuting with `X̄` (`mkSurfaceAttackerX`, the column-0
`X`-string) that is `I` on every column-0 cell of row `< d-1` is `I` on the corner `(d-1, 0)`. -/
theorem crux_Xbar (d : Nat) (hd0 : 0 < d) (hd : 1 < d)
    (z : ErrorVec (d * d)) (hzt : ∀ q, z q = Pauli.Z ∨ z q = Pauli.I)
    (hpar : ErrorVec.parity (mkSurfaceAttackerX d) z = false)
    (hprev : ∀ r, r < d - 1 → z (gridFin d hd0 (r, 0)) = Pauli.I) :
    z (gridFin d hd0 (d - 1, 0)) = Pauli.I := by
  have hstab : ∀ q : Fin (d * d),
      mkSurfaceAttackerX d q = if q.val % d = 0 then Pauli.X else Pauli.I := fun _ => rfl
  have hcorner : (gridFin d hd0 (d - 1, 0)).val = d * (d - 1) := by
    rw [gridFin_val_of_lt d hd0 (by omega) hd0]; omega
  by_contra hne
  have hZ : z (gridFin d hd0 (d - 1, 0)) = Pauli.Z := (hzt _).resolve_right hne
  have hfilter : (Finset.univ.filter fun q =>
      ErrorVec.Pauli.anticommutes (mkSurfaceAttackerX d q) (z q) = true)
      = {gridFin d hd0 (d - 1, 0)} := by
    apply Finset.ext; intro q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hq
      rw [hstab q] at hq
      by_cases hc0 : q.val % d = 0
      · rw [if_pos hc0] at hq
        have hrow : q.val / d < d := Nat.div_lt_of_lt_mul q.isLt
        have hqval : q.val = d * (q.val / d) := by
          have h := Nat.div_add_mod q.val d; rw [hc0, Nat.add_zero] at h; omega
        by_cases hrd : q.val / d = d - 1
        · exact Fin.ext (by rw [hcorner, hqval, hrd])
        · exfalso
          have : q = gridFin d hd0 (q.val / d, 0) :=
            Fin.ext (by rw [gridFin_val_of_lt d hd0 hrow hd0]; omega)
          rw [this, hprev _ (by omega)] at hq; nomatch hq
      · rw [if_neg hc0] at hq; simp [ErrorVec.Pauli.anticommutes] at hq
    · intro hq; subst hq
      rw [hstab _, if_pos (by rw [hcorner]; exact Nat.mul_mod_right d (d - 1)), hZ]
      decide
  rw [ErrorVec.parity, hfilter, Finset.card_singleton] at hpar
  nomatch hpar

/-- Decode of the odd-parity bulk X-check `bulkX r c` (mirror of `classifyStab_bulkIdx_odd`). -/
theorem decode_bulkXIdx (d r c row col : Nat) (hd : 1 < d) (hr : r < d - 1) (hc : c < d - 1)
    (hpar : (r + c) % 2 = 1) :
    decodeStabPauliAt d (bulkIdx d r c) row col
      = if (row = r ∨ row = r + 1) ∧ (col = c ∨ col = c + 1) then Pauli.X else Pauli.I := by
  unfold decodeStabPauliAt
  have hlt := bulkIdx_lt_bulkCount d r c hr hc
  rw [if_pos hlt]
  obtain ⟨hdiv, hmod⟩ := bulkIdx_div_mod d r c hd hc
  rw [hdiv, hmod]
  simp only [show (if (r + c) % 2 = 0 then Pauli.Z else Pauli.X) = Pauli.X from if_neg (by omega)]

/-- **Crux B** (bulkX, 4-cell).  A `Z`-type vector commuting with `bulkX r c` (parametrized by
its top-left `(r,c)`, `(r+c)` odd) that is `I` on the three row-major-earlier support cells
`(r,c)`, `(r,c+1)`, `(r+1,c)` is `I` on the bottom-right `(r+1,c+1)`. -/
theorem crux_bulkX (d : Nat) (hd0 : 0 < d) (hd : 1 < d) (r c : Nat)
    (hrd : r + 1 < d) (hcd : c + 1 < d) (hpar_rc : (r + c) % 2 = 1)
    (z : ErrorVec (d * d)) (hzt : ∀ q, z q = Pauli.Z ∨ z q = Pauli.I)
    (hpar : ErrorVec.parity
        (mkSurfaceStabilizers d hd0
          ⟨bulkIdx d r c, bulkIdx_lt_numStab d r c hd (by omega) (by omega)⟩) z = false)
    (hp1 : z (gridFin d hd0 (r, c)) = Pauli.I)
    (hp2 : z (gridFin d hd0 (r, c + 1)) = Pauli.I)
    (hp3 : z (gridFin d hd0 (r + 1, c)) = Pauli.I) :
    z (gridFin d hd0 (r + 1, c + 1)) = Pauli.I := by
  have hstab : ∀ q : Fin (d * d),
      mkSurfaceStabilizers d hd0
          ⟨bulkIdx d r c, bulkIdx_lt_numStab d r c hd (by omega) (by omega)⟩ q
        = if (q.val / d = r ∨ q.val / d = r + 1) ∧ (q.val % d = c ∨ q.val % d = c + 1)
          then Pauli.X else Pauli.I := by
    intro q; simp only [mkSurfaceStabilizers]
    exact decode_bulkXIdx d r c _ _ hd (by omega) (by omega) hpar_rc
  by_contra hne
  have hZ : z (gridFin d hd0 (r + 1, c + 1)) = Pauli.Z := (hzt _).resolve_right hne
  have hfilter : (Finset.univ.filter fun q =>
      ErrorVec.Pauli.anticommutes
        (mkSurfaceStabilizers d hd0
          ⟨bulkIdx d r c, bulkIdx_lt_numStab d r c hd (by omega) (by omega)⟩ q) (z q) = true)
      = {gridFin d hd0 (r + 1, c + 1)} := by
    apply Finset.ext; intro q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hq
      rw [hstab q] at hq
      by_cases hg : (q.val / d = r ∨ q.val / d = r + 1) ∧ (q.val % d = c ∨ q.val % d = c + 1)
      · rw [if_pos hg] at hq
        obtain ⟨hrow, hcol⟩ := hg
        have hqrc : ∀ (rr cc : Nat), q.val / d = rr → q.val % d = cc → q.val = d * rr + cc := by
          intro rr cc hrr hcc; have h := Nat.div_add_mod q.val d; rw [hrr, hcc] at h; omega
        rcases hrow with hrow | hrow <;> rcases hcol with hcol | hcol
        · exfalso
          have : q = gridFin d hd0 (r, c) :=
            Fin.ext (by rw [gridFin_val_of_lt d hd0 (by omega) (by omega)]; exact hqrc r c hrow hcol)
          rw [this, hp1] at hq; nomatch hq
        · exfalso
          have : q = gridFin d hd0 (r, c + 1) :=
            Fin.ext (by rw [gridFin_val_of_lt d hd0 (by omega) hcd]; exact hqrc r (c + 1) hrow hcol)
          rw [this, hp2] at hq; nomatch hq
        · exfalso
          have : q = gridFin d hd0 (r + 1, c) :=
            Fin.ext (by rw [gridFin_val_of_lt d hd0 hrd (by omega)]; exact hqrc (r + 1) c hrow hcol)
          rw [this, hp3] at hq; nomatch hq
        · exact Fin.ext (by rw [gridFin_val_of_lt d hd0 hrd hcd]; exact hqrc (r + 1) (c + 1) hrow hcol)
      · rw [if_neg hg] at hq; simp [ErrorVec.Pauli.anticommutes] at hq
    · intro hq; subst hq
      have hqd : (gridFin d hd0 (r + 1, c + 1)).val / d = r + 1 := by
        rw [gridFin_val_of_lt d hd0 hrd hcd, Nat.mul_add_div hd0, Nat.div_eq_of_lt hcd, Nat.add_zero]
      have hqm : (gridFin d hd0 (r + 1, c + 1)).val % d = c + 1 := by
        rw [gridFin_val_of_lt d hd0 hrd hcd, Nat.mul_add_mod, Nat.mod_eq_of_lt hcd]
      rw [hstab _, if_pos ⟨Or.inr hqd, Or.inr hqm⟩, hZ]
      decide
  rw [ErrorVec.parity, hfilter, Finset.card_singleton] at hpar
  nomatch hpar

/-! ## The abstract pivot-peel

Generic over an invariant `Inv` and a single dispatch hypothesis folding the pivot table and the
crux oracle: at a live cell either a pivot generator clears it (leaving the row-major prefix and
`Inv` intact) or the cell is dead.  Ascending `k` with `fuel = P.n - k` (the `reach_fold`
recipe); no Z-specific content, so the X-leg reuses it with the dual pivots. -/

/-- Multiplying by a `Z`-type generator is an involution. -/
theorem mul_ztype_involutive {n : Nat} (g z : ErrorVec n)
    (hg : ∀ i, g i = Pauli.Z ∨ g i = Pauli.I) :
    ErrorVec.mul g (ErrorVec.mul g z) = z := by
  funext i; simp only [ErrorVec.mul]; rcases hg i with h | h <;> rw [h] <;> cases z i <;> decide

/-- A `Z`-pivot clears its cell (`Z · Z = I`). -/
theorem mul_clears {n : Nat} (g z : ErrorVec n) (k : Fin n) (hgk : g k = Pauli.Z)
    (hzk : z k = Pauli.Z) : ErrorVec.mul g z k = Pauli.I := by
  simp only [ErrorVec.mul, hgk, hzk]; decide

/-- A generator that is `I` before its pivot leaves earlier cells fixed. -/
theorem mul_prefix {n : Nat} (g z : ErrorVec n) (q : Fin n) (hgq : g q = Pauli.I) :
    ErrorVec.mul g z q = z q := by
  simp only [ErrorVec.mul, hgq]; cases z q <;> decide

/-- **The abstract pivot-peel.**  Under `hdispatch` (a live cell either has a clearing pivot
generator or is dead), any `Inv`-vector cleared below `k` is a stabilizer product. -/
theorem abstract_peel {P : QECParams} (Inv : ErrorVec P.n → Prop)
    (hInvZ : ∀ z, Inv z → ∀ i, z i = Pauli.Z ∨ z i = Pauli.I)
    (hdispatch : ∀ (k : Fin P.n) (z : ErrorVec P.n), Inv z →
      (∀ q : Fin P.n, q.val < k.val → z q = Pauli.I) → z k ≠ Pauli.I →
      ∃ g, QStab.InStab P g ∧ (∀ i, g i = Pauli.Z ∨ g i = Pauli.I) ∧
        (∀ q : Fin P.n, q.val < k.val → g q = Pauli.I) ∧ g k = Pauli.Z
        ∧ Inv (ErrorVec.mul g z)) :
    ∀ (fuel k : Nat), P.n - k = fuel → k ≤ P.n → ∀ z : ErrorVec P.n, Inv z →
      (∀ q : Fin P.n, q.val < k → z q = Pauli.I) → QStab.InStab P z := by
  intro fuel
  induction fuel with
  | zero =>
      intro k _hfuel hk z _hInv hcleared
      have hkeq : k = P.n := by omega
      have hzid : z = ErrorVec.identity P.n :=
        funext fun q => hcleared q (by rw [hkeq]; exact q.isLt)
      rw [hzid]; exact QStab.InStab.identity
  | succ fuel ih =>
      intro k hfuel hk z hInv hcleared
      have hklt : k < P.n := by omega
      by_cases hzk : z ⟨k, hklt⟩ = Pauli.I
      · refine ih (k + 1) (by omega) (by omega) z hInv (fun q hq => ?_)
        rcases Nat.lt_succ_iff_lt_or_eq.mp hq with h | h
        · exact hcleared q h
        · rw [show q = ⟨k, hklt⟩ from Fin.ext h]; exact hzk
      · obtain ⟨g, hg_stab, hg_zt, hg_prefix, hg_k, hg_inv⟩ :=
          hdispatch ⟨k, hklt⟩ z hInv hcleared hzk
        have hz'cleared : ∀ q : Fin P.n, q.val < k + 1 → ErrorVec.mul g z q = Pauli.I := by
          intro q hq
          rcases Nat.lt_succ_iff_lt_or_eq.mp hq with h | h
          · rw [mul_prefix g z q (hg_prefix q h)]; exact hcleared q h
          · rw [show q = ⟨k, hklt⟩ from Fin.ext h,
              mul_clears g z ⟨k, hklt⟩ hg_k ((hInvZ z hInv ⟨k, hklt⟩).resolve_right hzk)]
        have hz' : QStab.InStab P (ErrorVec.mul g z) :=
          ih (k + 1) (by omega) (by omega) (ErrorVec.mul g z) hg_inv hz'cleared
        rw [← mul_ztype_involutive g z hg_zt]
        exact QStab.InStab.mul hg_stab hz'

/-! ## Z-check decode lemmas (the pivot generators) -/

/-- Decode of the even-parity bulk Z-check `bulkZ r c`. -/
theorem decode_bulkZIdx (d r c row col : Nat) (hd : 1 < d) (hr : r < d - 1) (hc : c < d - 1)
    (hpar : (r + c) % 2 = 0) :
    decodeStabPauliAt d (bulkIdx d r c) row col
      = if (row = r ∨ row = r + 1) ∧ (col = c ∨ col = c + 1) then Pauli.Z else Pauli.I := by
  unfold decodeStabPauliAt
  rw [if_pos (bulkIdx_lt_bulkCount d r c hr hc)]
  obtain ⟨hdiv, hmod⟩ := bulkIdx_div_mod d r c hd hc
  rw [hdiv, hmod]
  simp only [show (if (r + c) % 2 = 0 then Pauli.Z else Pauli.X) = Pauli.Z from if_pos hpar]

/-- Decode of the right boundary Z-check `rightZ b`. -/
theorem decode_rightZIdx (d b row col : Nat) (_hd : 1 < d) (hb : b < (d - 1) / 2) :
    decodeStabPauliAt d (rightZIdx d b) row col
      = if col = d - 1 ∧ (row = 2 * b ∨ row = 2 * b + 1) then Pauli.Z else Pauli.I := by
  unfold decodeStabPauliAt rightZIdx
  rw [if_neg (Nat.not_lt_of_ge (by omega :
    (d - 1) * (d - 1) ≤ (d - 1) * (d - 1) + (d - 1) / 2 + b))]
  set b' := (d - 1) * (d - 1) + (d - 1) / 2 + b - (d - 1) * (d - 1) with hb'def
  have hb'_eq : b' = (d - 1) / 2 + b := by rw [hb'def]; omega
  rw [if_neg (by rw [hb'_eq]; omega), if_pos (by rw [hb'_eq]; omega)]
  rw [show b' - (d - 1) / 2 = b by rw [hb'_eq]; omega]

/-- Decode of the left boundary Z-check `leftZ b`. -/
theorem decode_leftZIdx (d b row col : Nat) (_hd : 1 < d) (hb : b < (d - 1) / 2) :
    decodeStabPauliAt d (leftZIdx d b) row col
      = if col = 0 ∧ (row = 2 * b + 1 ∨ row = 2 * b + 2) then Pauli.Z else Pauli.I := by
  unfold decodeStabPauliAt leftZIdx
  rw [if_neg (Nat.not_lt_of_ge (by omega :
    (d - 1) * (d - 1) ≤ (d - 1) * (d - 1) + 2 * ((d - 1) / 2) + b))]
  set b' := (d - 1) * (d - 1) + 2 * ((d - 1) / 2) + b - (d - 1) * (d - 1) with hb'def
  have hb'_eq : b' = 2 * ((d - 1) / 2) + b := by rw [hb'def]; omega
  rw [if_neg (by rw [hb'_eq]; omega), if_neg (by rw [hb'_eq]; omega),
    if_pos (by rw [hb'_eq]; omega)]
  rw [show b' - 2 * ((d - 1) / 2) = b by rw [hb'_eq]; omega]

/-! ## The Z-leg invariant and its preservation -/

/-- The pointwise product of two `Z`-type vectors is `Z`-type. -/
theorem ztype_mul {n : Nat} (a b : ErrorVec n) (ha : ∀ i, a i = Pauli.Z ∨ a i = Pauli.I)
    (hb : ∀ i, b i = Pauli.Z ∨ b i = Pauli.I) :
    ∀ i, ErrorVec.mul a b i = Pauli.Z ∨ ErrorVec.mul a b i = Pauli.I := by
  intro i; simp only [ErrorVec.mul]
  rcases ha i with h | h <;> rcases hb i with h2 | h2 <;> rw [h, h2] <;> decide

/-- **Invariant preservation.**  Multiplying the running vector by a Z-check generator keeps it
`Z`-type, in the stabilizer-normalizer (commutes with every generator, via
`stab_commute_parametric`), and commuting with `X̄`. -/
theorem zcheck_preserves (d : Nat) (hd0 : 0 < d) (hodd : d % 2 = 1)
    (j : Fin (numStabFormula d))
    (hjzt : ∀ i, mkSurfaceStabilizers d hd0 j i = Pauli.Z
      ∨ mkSurfaceStabilizers d hd0 j i = Pauli.I)
    (z : ErrorVec (d * d)) (hzt : ∀ q, z q = Pauli.Z ∨ z q = Pauli.I)
    (hcomm : ∀ k, ErrorVec.parity (mkSurfaceStabilizers d hd0 k) z = false)
    (hxbar : ErrorVec.parity (mkSurfaceAttackerX d) z = false) :
    (∀ q, ErrorVec.mul (mkSurfaceStabilizers d hd0 j) z q = Pauli.Z
        ∨ ErrorVec.mul (mkSurfaceStabilizers d hd0 j) z q = Pauli.I)
      ∧ (∀ k, ErrorVec.parity (mkSurfaceStabilizers d hd0 k)
          (ErrorVec.mul (mkSurfaceStabilizers d hd0 j) z) = false)
      ∧ ErrorVec.parity (mkSurfaceAttackerX d)
          (ErrorVec.mul (mkSurfaceStabilizers d hd0 j) z) = false := by
  refine ⟨ztype_mul _ _ hjzt hzt, fun k => ?_, ?_⟩
  · rw [QStab.Paper.LogicalCosets.parity_mul_right,
      stab_commute_parametric d hd0 hodd k j, hcomm k]; rfl
  · rw [QStab.Paper.LogicalCosets.parity_mul_right,
      QStab.Paper.LogicalCosets.parity_symm (mkSurfaceAttackerX d) (mkSurfaceStabilizers d hd0 j),
      mkSurfaceAttackerX_commutes_with_stabilizers d hd0 hodd j, hxbar]; rfl

/-! ## Pivot generators: Z-type + value-at-pivot + pivot-min (all support cells `≥` the pivot) -/

/-- The `bulkZ r c` generator: `Z`-type, `Z` at its top-left pivot `(r,c)`, and `I` on every
row-major-earlier cell (its support is the `2×2` block with `(r,c)` as row-major minimum). -/
theorem bulkZ_gen (d : Nat) (hd0 : 0 < d) (hd : 1 < d) (r c : Nat) (hr : r < d - 1) (hc : c < d - 1)
    (hpar : (r + c) % 2 = 0) :
    (∀ q, mkSurfaceStabilizers d hd0 ⟨bulkIdx d r c, bulkIdx_lt_numStab d r c hd hr hc⟩ q = Pauli.Z
        ∨ mkSurfaceStabilizers d hd0 ⟨bulkIdx d r c, bulkIdx_lt_numStab d r c hd hr hc⟩ q = Pauli.I)
      ∧ mkSurfaceStabilizers d hd0 ⟨bulkIdx d r c, bulkIdx_lt_numStab d r c hd hr hc⟩
          (gridFin d hd0 (r, c)) = Pauli.Z
      ∧ (∀ q : Fin (d * d), q.val < d * r + c →
          mkSurfaceStabilizers d hd0 ⟨bulkIdx d r c, bulkIdx_lt_numStab d r c hd hr hc⟩ q
            = Pauli.I) := by
  have hstab : ∀ q : Fin (d * d),
      mkSurfaceStabilizers d hd0 ⟨bulkIdx d r c, bulkIdx_lt_numStab d r c hd hr hc⟩ q
        = if (q.val / d = r ∨ q.val / d = r + 1) ∧ (q.val % d = c ∨ q.val % d = c + 1)
          then Pauli.Z else Pauli.I := by
    intro q; simp only [mkSurfaceStabilizers]; exact decode_bulkZIdx d r c _ _ hd hr hc hpar
  refine ⟨fun q => ?_, ?_, fun q hq => ?_⟩
  · rw [hstab q]; split_ifs; exacts [Or.inl rfl, Or.inr rfl]
  · rw [hstab _, if_pos ⟨Or.inl (by rw [gridFin_val_of_lt d hd0 (by omega) (by omega),
        Nat.mul_add_div hd0, Nat.div_eq_of_lt (by omega), Nat.add_zero]),
      Or.inl (by rw [gridFin_val_of_lt d hd0 (by omega) (by omega), Nat.mul_add_mod,
        Nat.mod_eq_of_lt (by omega)])⟩]
  · rw [hstab q, if_neg]
    rintro ⟨hrr, hcc⟩
    have hdm := Nat.div_add_mod q.val d
    have h1 : d * r ≤ d * (q.val / d) := Nat.mul_le_mul_left d (by rcases hrr with h | h <;> omega)
    have h2 : c ≤ q.val % d := by rcases hcc with h | h <;> omega
    omega

/-- The `rightZ b` generator: `Z`-type, `Z` at its pivot `(2b, d-1)`, `I` on earlier cells. -/
theorem rightZ_gen (d : Nat) (hd0 : 0 < d) (hd : 1 < d) (bb : Nat) (hbb : bb < (d - 1) / 2) :
    (∀ q, mkSurfaceStabilizers d hd0 ⟨rightZIdx d bb, rightZIdx_lt_numStab d bb hd hbb⟩ q = Pauli.Z
        ∨ mkSurfaceStabilizers d hd0 ⟨rightZIdx d bb, rightZIdx_lt_numStab d bb hd hbb⟩ q = Pauli.I)
      ∧ mkSurfaceStabilizers d hd0 ⟨rightZIdx d bb, rightZIdx_lt_numStab d bb hd hbb⟩
          (gridFin d hd0 (2 * bb, d - 1)) = Pauli.Z
      ∧ (∀ q : Fin (d * d), q.val < d * (2 * bb) + (d - 1) →
          mkSurfaceStabilizers d hd0 ⟨rightZIdx d bb, rightZIdx_lt_numStab d bb hd hbb⟩ q
            = Pauli.I) := by
  have hstab : ∀ q : Fin (d * d),
      mkSurfaceStabilizers d hd0 ⟨rightZIdx d bb, rightZIdx_lt_numStab d bb hd hbb⟩ q
        = if q.val % d = d - 1 ∧ (q.val / d = 2 * bb ∨ q.val / d = 2 * bb + 1)
          then Pauli.Z else Pauli.I := by
    intro q; simp only [mkSurfaceStabilizers]; exact decode_rightZIdx d bb _ _ hd hbb
  refine ⟨fun q => ?_, ?_, fun q hq => ?_⟩
  · rw [hstab q]; split_ifs; exacts [Or.inl rfl, Or.inr rfl]
  · rw [hstab _, if_pos ⟨by rw [gridFin_val_of_lt d hd0 (by omega) (by omega), Nat.mul_add_mod,
        Nat.mod_eq_of_lt (by omega)], Or.inl (by rw [gridFin_val_of_lt d hd0 (by omega) (by omega),
        Nat.mul_add_div hd0, Nat.div_eq_of_lt (by omega), Nat.add_zero])⟩]
  · rw [hstab q, if_neg]
    rintro ⟨hcol, hrow⟩
    have hdm := Nat.div_add_mod q.val d
    have h1 : d * (2 * bb) ≤ d * (q.val / d) :=
      Nat.mul_le_mul_left d (by rcases hrow with h | h <;> omega)
    omega

/-- The `leftZ b` generator: `Z`-type, `Z` at its pivot `(2b+1, 0)`, `I` on earlier cells. -/
theorem leftZ_gen (d : Nat) (hd0 : 0 < d) (hd : 1 < d) (bb : Nat) (hbb : bb < (d - 1) / 2) :
    (∀ q, mkSurfaceStabilizers d hd0 ⟨leftZIdx d bb, leftZIdx_lt_numStab d bb hd hbb⟩ q = Pauli.Z
        ∨ mkSurfaceStabilizers d hd0 ⟨leftZIdx d bb, leftZIdx_lt_numStab d bb hd hbb⟩ q = Pauli.I)
      ∧ mkSurfaceStabilizers d hd0 ⟨leftZIdx d bb, leftZIdx_lt_numStab d bb hd hbb⟩
          (gridFin d hd0 (2 * bb + 1, 0)) = Pauli.Z
      ∧ (∀ q : Fin (d * d), q.val < d * (2 * bb + 1) →
          mkSurfaceStabilizers d hd0 ⟨leftZIdx d bb, leftZIdx_lt_numStab d bb hd hbb⟩ q
            = Pauli.I) := by
  have hstab : ∀ q : Fin (d * d),
      mkSurfaceStabilizers d hd0 ⟨leftZIdx d bb, leftZIdx_lt_numStab d bb hd hbb⟩ q
        = if q.val % d = 0 ∧ (q.val / d = 2 * bb + 1 ∨ q.val / d = 2 * bb + 2)
          then Pauli.Z else Pauli.I := by
    intro q; simp only [mkSurfaceStabilizers]; exact decode_leftZIdx d bb _ _ hd hbb
  refine ⟨fun q => ?_, ?_, fun q hq => ?_⟩
  · rw [hstab q]; split_ifs; exacts [Or.inl rfl, Or.inr rfl]
  · rw [hstab _, if_pos ⟨by rw [gridFin_val_of_lt d hd0 (by omega) hd0, Nat.mul_add_mod,
        Nat.zero_mod], Or.inl (by rw [gridFin_val_of_lt d hd0 (by omega) hd0, Nat.mul_add_div hd0,
        Nat.zero_div, Nat.add_zero])⟩]
  · rw [hstab q, if_neg]
    rintro ⟨hcol, hrow⟩
    have hdm := Nat.div_add_mod q.val d
    have h1 : d * (2 * bb + 1) ≤ d * (q.val / d) :=
      Nat.mul_le_mul_left d (by rcases hrow with h | h <;> omega)
    omega

/-! ## The Z-leg: instantiate the abstract peel with the Z-pivot table + four crux lemmas -/

/-- Row-major ordering on grid cells (centralizes the nonlinear `d·r` arithmetic). -/
theorem cell_lt (d : Nat) (hd0 : 0 < d) (r c cr cc : Nat) (hcc : cc < d)
    (h : cr < r ∨ (cr = r ∧ cc < c)) : d * cr + cc < d * r + c := by
  rcases h with h | ⟨h1, h2⟩
  · have hmul : d * (cr + 1) ≤ d * r := Nat.mul_le_mul_left d (by omega)
    rw [Nat.mul_succ] at hmul; omega
  · subst h1; omega

/-- **The Z-side cleaning leg** (`hgp_zside` signature).  A `Z`-type vector commuting with every
stabilizer and with `X̄` is a stabilizer product — the abstract peel over the Z-check pivot
table, the four crux lemmas discharging the no-pivot cell classes. -/
theorem surface_zside (d : Nat) (hd0 : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (z : ErrorVec (d * d)) (hzt : ∀ q, z q = Pauli.Z ∨ z q = Pauli.I)
    (hcomm : ∀ k, ErrorVec.parity (mkSurfaceStabilizers d hd0 k) z = false)
    (hxbar : ErrorVec.parity (mkSurfaceAttackerX d) z = false) :
    QStab.InStab (mkSurfaceQECParams d hd0 hodd) z := by
  have hd : 1 < d := by omega
  refine abstract_peel (P := mkSurfaceQECParams d hd0 hodd)
    (fun w => (∀ q, w q = Pauli.Z ∨ w q = Pauli.I) ∧
      (∀ k, ErrorVec.parity (mkSurfaceStabilizers d hd0 k) w = false) ∧
      ErrorVec.parity (mkSurfaceAttackerX d) w = false)
    (fun w hw => hw.1) ?_ (d * d) 0 (Nat.sub_zero _) (Nat.zero_le _) z ⟨hzt, hcomm, hxbar⟩
    (fun q hq => absurd hq (Nat.not_lt_zero _))
  rintro k w ⟨hwzt, hwcomm, hwxbar⟩ hcleared hlive
  have hrowlt : k.val / d < d := Nat.div_lt_of_lt_mul k.isLt
  have hcollt : k.val % d < d := Nat.mod_lt _ hd0
  -- fresh coordinate variables to avoid `set`/motive and `r/2`-loop traps
  obtain ⟨r, hrdef⟩ : ∃ r, k.val / d = r := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c, k.val % d = c := ⟨_, rfl⟩
  have hkval : k.val = d * r + c := by rw [← hrdef, ← hcdef]; exact (Nat.div_add_mod k.val d).symm
  rw [hrdef] at hrowlt; rw [hcdef] at hcollt
  -- helper: `k` is the qubit of its own coordinates
  have hkeq : ∀ (row col : Nat), row < d → col < d → k.val = d * row + col →
      k = gridFin d hd0 (row, col) :=
    fun row col hrw hcw h => Fin.ext (by rw [gridFin_val_of_lt d hd0 hrw hcw]; exact h)
  -- helper: an earlier cell is cleared
  have hprev : ∀ (cr cc : Nat), cr < d → cc < d → (cr < r ∨ (cr = r ∧ cc < c)) →
      w (gridFin d hd0 (cr, cc)) = Pauli.I := fun cr cc hcr hcc hlt =>
    hcleared _ (by rw [gridFin_val_of_lt d hd0 hcr hcc, hkval]; exact cell_lt d hd0 r c cr cc hcc hlt)
  by_cases hpar_rc : (r + c) % 2 = 0
  · -- EVEN parity
    by_cases hbulk : r < d - 1 ∧ c < d - 1
    · -- bulkZ pivot at (r, c)
      obtain ⟨hgzt, hgval, hgpre⟩ := bulkZ_gen d hd0 hd r c hbulk.1 hbulk.2 hpar_rc
      exact ⟨_, QStab.InStab.gen ⟨bulkIdx d r c, bulkIdx_lt_numStab d r c hd hbulk.1 hbulk.2⟩,
        hgzt, fun q hq => hgpre q (by rw [hkval] at hq; exact hq),
        by rw [hkeq r c hrowlt hcollt hkval]; exact hgval,
        zcheck_preserves d hd0 hodd _ hgzt w hwzt hwcomm hwxbar⟩
    · by_cases hcd : c = d - 1
      · -- col = d-1, r even; rightZ pivot (r ≤ d-3) or corner (r = d-1)
        by_cases hrle : r ≤ d - 3
        · obtain ⟨bb, hbb⟩ : ∃ bb, r = 2 * bb := ⟨r / 2, by omega⟩
          have hbbb : bb < (d - 1) / 2 := by omega
          obtain ⟨hgzt, hgval, hgpre⟩ := rightZ_gen d hd0 hd bb hbbb
          refine ⟨_, QStab.InStab.gen ⟨rightZIdx d bb, rightZIdx_lt_numStab d bb hd hbbb⟩,
            hgzt, fun q hq => hgpre q (by rw [hkval, hbb, hcd] at hq; exact hq),
            by rw [hkeq (2 * bb) (d - 1) (by omega) (by omega) (by rw [hkval, hbb, hcd])]; exact hgval,
            zcheck_preserves d hd0 hodd _ hgzt w hwzt hwcomm hwxbar⟩
        · -- corner (d-1, d-1): crux_bottomX at bb = (d-3)/2
          exfalso; apply hlive
          obtain ⟨bb, hbb⟩ : ∃ bb, d - 1 = 2 * bb + 2 := ⟨(d - 3) / 2, by omega⟩
          have hrd1 : r = d - 1 := by omega
          have hcbb : c = 2 * bb + 2 := by omega
          rw [hkeq (d - 1) (2 * bb + 2) (by omega) (by omega) (by rw [hkval, hrd1, hcbb])]
          exact crux_bottomX d hd0 hd hodd bb (by omega) w hwzt (hwcomm _)
            (hprev (d - 1) (2 * bb + 1) (by omega) (by omega) (Or.inr ⟨by omega, by omega⟩))
      · -- row = d-1, col ≤ d-2, col even
        by_cases hc0 : c = 0
        · -- Xbar corner (d-1, 0)
          exfalso; apply hlive
          rw [hkeq r c hrowlt hcollt hkval, show r = d - 1 by omega, hc0]
          exact crux_Xbar d hd0 hd w hwzt hwxbar
            (fun rr hrr => hprev rr 0 (by omega) hd0 (Or.inl (by omega)))
        · -- bottomX mid (d-1, c) c even ≥ 2
          exfalso; apply hlive
          obtain ⟨bb, hbb⟩ : ∃ bb, c = 2 * bb + 2 := ⟨(c - 2) / 2, by omega⟩
          have hrd1 : r = d - 1 := by omega
          rw [hkeq (d - 1) (2 * bb + 2) (by omega) (by omega) (by rw [hkval, hrd1, hbb])]
          exact crux_bottomX d hd0 hd hodd bb (by omega) w hwzt (hwcomm _)
            (hprev (d - 1) (2 * bb + 1) (by omega) (by omega) (Or.inr ⟨by omega, by omega⟩))
  · -- ODD parity
    by_cases hr0 : r = 0
    · -- topX (0, c) c odd
      exfalso; apply hlive
      obtain ⟨b, hbb⟩ : ∃ b, c = 2 * b + 1 := ⟨c / 2, by omega⟩
      rw [hkeq r c hrowlt hcollt hkval, hr0, hbb]
      exact crux_topX d hd0 hd b (by omega) w hwzt (hwcomm _)
        (hprev 0 (2 * b) (by omega) (by omega) (Or.inr ⟨hr0.symm, by omega⟩))
    · by_cases hc0 : c = 0
      · -- leftZ pivot (r, 0), r odd
        obtain ⟨bb, hbb⟩ : ∃ bb, r = 2 * bb + 1 := ⟨(r - 1) / 2, by omega⟩
        have hbbb : bb < (d - 1) / 2 := by omega
        obtain ⟨hgzt, hgval, hgpre⟩ := leftZ_gen d hd0 hd bb hbbb
        refine ⟨_, QStab.InStab.gen ⟨leftZIdx d bb, leftZIdx_lt_numStab d bb hd hbbb⟩,
          hgzt, fun q hq => hgpre q (by rw [hkval, hbb, hc0, Nat.add_zero] at hq; exact hq),
          by rw [hkeq (2 * bb + 1) 0 (by omega) hd0 (by rw [hkval, hbb, hc0])]; exact hgval,
          zcheck_preserves d hd0 hodd _ hgzt w hwzt hwcomm hwxbar⟩
      · -- bulkX (r, c) r,c ≥ 1
        exfalso; apply hlive
        obtain ⟨rr, hrr⟩ : ∃ rr, r = rr + 1 := ⟨r - 1, by omega⟩
        obtain ⟨cc, hcc⟩ : ∃ cc, c = cc + 1 := ⟨c - 1, by omega⟩
        rw [hkeq r c hrowlt hcollt hkval, hrr, hcc]
        exact crux_bulkX d hd0 hd rr cc (by omega) (by omega) (by omega) w hwzt (hwcomm _)
          (hprev rr cc (by omega) (by omega) (Or.inl (by omega)))
          (hprev rr (cc + 1) (by omega) (by omega) (Or.inl (by omega)))
          (hprev (rr + 1) cc (by omega) (by omega) (Or.inr ⟨by omega, by omega⟩))

/-! ## X-side crux lemmas (dual of the Z-side; `X`-type vector forced by a `Z`-check / `Z̄`) -/

/-- **X-crux B′** (bulkZ, 4-cell).  An `X`-type vector commuting with `bulkZ r c` (`(r+c)` even)
that is `I` on `(r,c)`, `(r,c+1)`, `(r+1,c)` is `I` on `(r+1,c+1)`. -/
theorem crux_bulkZ (d : Nat) (hd0 : 0 < d) (hd : 1 < d) (r c : Nat)
    (hrd : r + 1 < d) (hcd : c + 1 < d) (hpar_rc : (r + c) % 2 = 0)
    (x : ErrorVec (d * d)) (hxt : ∀ q, x q = Pauli.X ∨ x q = Pauli.I)
    (hpar : ErrorVec.parity
        (mkSurfaceStabilizers d hd0
          ⟨bulkIdx d r c, bulkIdx_lt_numStab d r c hd (by omega) (by omega)⟩) x = false)
    (hp1 : x (gridFin d hd0 (r, c)) = Pauli.I)
    (hp2 : x (gridFin d hd0 (r, c + 1)) = Pauli.I)
    (hp3 : x (gridFin d hd0 (r + 1, c)) = Pauli.I) :
    x (gridFin d hd0 (r + 1, c + 1)) = Pauli.I := by
  have hstab : ∀ q : Fin (d * d),
      mkSurfaceStabilizers d hd0
          ⟨bulkIdx d r c, bulkIdx_lt_numStab d r c hd (by omega) (by omega)⟩ q
        = if (q.val / d = r ∨ q.val / d = r + 1) ∧ (q.val % d = c ∨ q.val % d = c + 1)
          then Pauli.Z else Pauli.I := by
    intro q; simp only [mkSurfaceStabilizers]
    exact decode_bulkZIdx d r c _ _ hd (by omega) (by omega) hpar_rc
  by_contra hne
  have hX : x (gridFin d hd0 (r + 1, c + 1)) = Pauli.X := (hxt _).resolve_right hne
  have hfilter : (Finset.univ.filter fun q =>
      ErrorVec.Pauli.anticommutes
        (mkSurfaceStabilizers d hd0
          ⟨bulkIdx d r c, bulkIdx_lt_numStab d r c hd (by omega) (by omega)⟩ q) (x q) = true)
      = {gridFin d hd0 (r + 1, c + 1)} := by
    apply Finset.ext; intro q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hq
      rw [hstab q] at hq
      by_cases hg : (q.val / d = r ∨ q.val / d = r + 1) ∧ (q.val % d = c ∨ q.val % d = c + 1)
      · rw [if_pos hg] at hq
        obtain ⟨hrow, hcol⟩ := hg
        have hqrc : ∀ (rr cc : Nat), q.val / d = rr → q.val % d = cc → q.val = d * rr + cc := by
          intro rr cc hrr hcc; have h := Nat.div_add_mod q.val d; rw [hrr, hcc] at h; omega
        rcases hrow with hrow | hrow <;> rcases hcol with hcol | hcol
        · exfalso
          have : q = gridFin d hd0 (r, c) :=
            Fin.ext (by rw [gridFin_val_of_lt d hd0 (by omega) (by omega)]; exact hqrc r c hrow hcol)
          rw [this, hp1] at hq; nomatch hq
        · exfalso
          have : q = gridFin d hd0 (r, c + 1) :=
            Fin.ext (by rw [gridFin_val_of_lt d hd0 (by omega) hcd]; exact hqrc r (c + 1) hrow hcol)
          rw [this, hp2] at hq; nomatch hq
        · exfalso
          have : q = gridFin d hd0 (r + 1, c) :=
            Fin.ext (by rw [gridFin_val_of_lt d hd0 hrd (by omega)]; exact hqrc (r + 1) c hrow hcol)
          rw [this, hp3] at hq; nomatch hq
        · exact Fin.ext (by rw [gridFin_val_of_lt d hd0 hrd hcd]; exact hqrc (r + 1) (c + 1) hrow hcol)
      · rw [if_neg hg] at hq; simp [ErrorVec.Pauli.anticommutes] at hq
    · intro hq; subst hq
      have hqd : (gridFin d hd0 (r + 1, c + 1)).val / d = r + 1 := by
        rw [gridFin_val_of_lt d hd0 hrd hcd, Nat.mul_add_div hd0, Nat.div_eq_of_lt hcd, Nat.add_zero]
      have hqm : (gridFin d hd0 (r + 1, c + 1)).val % d = c + 1 := by
        rw [gridFin_val_of_lt d hd0 hrd hcd, Nat.mul_add_mod, Nat.mod_eq_of_lt hcd]
      rw [hstab _, if_pos ⟨Or.inr hqd, Or.inr hqm⟩, hX]
      decide
  rw [ErrorVec.parity, hfilter, Finset.card_singleton] at hpar
  nomatch hpar

/-- **X-crux C′** (rightZ, 2-cell).  An `X`-type vector commuting with `rightZ b` that is `I` on
its pivot `(2b, d-1)` is `I` on `(2b+1, d-1)`. -/
theorem crux_rightZ (d : Nat) (hd0 : 0 < d) (hd : 1 < d) (bb : Nat) (hbb : bb < (d - 1) / 2)
    (x : ErrorVec (d * d)) (hxt : ∀ q, x q = Pauli.X ∨ x q = Pauli.I)
    (hpar : ErrorVec.parity
        (mkSurfaceStabilizers d hd0 ⟨rightZIdx d bb, rightZIdx_lt_numStab d bb hd hbb⟩) x = false)
    (hprev : x (gridFin d hd0 (2 * bb, d - 1)) = Pauli.I) :
    x (gridFin d hd0 (2 * bb + 1, d - 1)) = Pauli.I := by
  have hcd : d - 1 < d := by omega
  have hval0 : (gridFin d hd0 (2 * bb, d - 1)).val = d * (2 * bb) + (d - 1) :=
    gridFin_val_of_lt d hd0 (by omega) hcd
  have hval1 : (gridFin d hd0 (2 * bb + 1, d - 1)).val = d * (2 * bb + 1) + (d - 1) :=
    gridFin_val_of_lt d hd0 (by omega) hcd
  have hstab : ∀ q : Fin (d * d),
      mkSurfaceStabilizers d hd0 ⟨rightZIdx d bb, rightZIdx_lt_numStab d bb hd hbb⟩ q
        = if q.val % d = d - 1 ∧ (q.val / d = 2 * bb ∨ q.val / d = 2 * bb + 1)
          then Pauli.Z else Pauli.I := by
    intro q; simp only [mkSurfaceStabilizers]; exact decode_rightZIdx d bb _ _ hd hbb
  by_contra hne
  have hX : x (gridFin d hd0 (2 * bb + 1, d - 1)) = Pauli.X := (hxt _).resolve_right hne
  have hfilter : (Finset.univ.filter fun q =>
      ErrorVec.Pauli.anticommutes
        (mkSurfaceStabilizers d hd0 ⟨rightZIdx d bb, rightZIdx_lt_numStab d bb hd hbb⟩ q)
        (x q) = true)
      = {gridFin d hd0 (2 * bb + 1, d - 1)} := by
    apply Finset.ext; intro q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hq
      rw [hstab q] at hq
      by_cases hg : q.val % d = d - 1 ∧ (q.val / d = 2 * bb ∨ q.val / d = 2 * bb + 1)
      · rw [if_pos hg] at hq
        obtain ⟨hcol, hrow⟩ := hg
        have hqval : q.val = d * (q.val / d) + (d - 1) := by
          have h := Nat.div_add_mod q.val d; rw [hcol] at h; omega
        rcases hrow with h | h
        · exfalso
          have : q = gridFin d hd0 (2 * bb, d - 1) := Fin.ext (by rw [hval0, hqval, h])
          rw [this, hprev] at hq; nomatch hq
        · exact Fin.ext (by rw [hval1, hqval, h])
      · rw [if_neg hg] at hq; simp [ErrorVec.Pauli.anticommutes] at hq
    · intro hq; subst hq
      rw [hstab _, if_pos ⟨by rw [hval1, Nat.mul_add_mod, Nat.mod_eq_of_lt hcd],
        Or.inr (by rw [hval1, Nat.mul_add_div hd0, Nat.div_eq_of_lt hcd, Nat.add_zero])⟩, hX]
      decide
  rw [ErrorVec.parity, hfilter, Finset.card_singleton] at hpar
  nomatch hpar

/-- **X-crux A′** (leftZ, 2-cell).  An `X`-type vector commuting with `leftZ b` that is `I` on its
pivot `(2b+1, 0)` is `I` on `(2b+2, 0)`. -/
theorem crux_leftZ (d : Nat) (hd0 : 0 < d) (hd : 1 < d) (bb : Nat) (hbb : bb < (d - 1) / 2)
    (x : ErrorVec (d * d)) (hxt : ∀ q, x q = Pauli.X ∨ x q = Pauli.I)
    (hpar : ErrorVec.parity
        (mkSurfaceStabilizers d hd0 ⟨leftZIdx d bb, leftZIdx_lt_numStab d bb hd hbb⟩) x = false)
    (hprev : x (gridFin d hd0 (2 * bb + 1, 0)) = Pauli.I) :
    x (gridFin d hd0 (2 * bb + 2, 0)) = Pauli.I := by
  have hval0 : (gridFin d hd0 (2 * bb + 1, 0)).val = d * (2 * bb + 1) + 0 :=
    gridFin_val_of_lt d hd0 (by omega) hd0
  have hval1 : (gridFin d hd0 (2 * bb + 2, 0)).val = d * (2 * bb + 2) + 0 :=
    gridFin_val_of_lt d hd0 (by omega) hd0
  have hstab : ∀ q : Fin (d * d),
      mkSurfaceStabilizers d hd0 ⟨leftZIdx d bb, leftZIdx_lt_numStab d bb hd hbb⟩ q
        = if q.val % d = 0 ∧ (q.val / d = 2 * bb + 1 ∨ q.val / d = 2 * bb + 2)
          then Pauli.Z else Pauli.I := by
    intro q; simp only [mkSurfaceStabilizers]; exact decode_leftZIdx d bb _ _ hd hbb
  by_contra hne
  have hX : x (gridFin d hd0 (2 * bb + 2, 0)) = Pauli.X := (hxt _).resolve_right hne
  have hfilter : (Finset.univ.filter fun q =>
      ErrorVec.Pauli.anticommutes
        (mkSurfaceStabilizers d hd0 ⟨leftZIdx d bb, leftZIdx_lt_numStab d bb hd hbb⟩ q)
        (x q) = true)
      = {gridFin d hd0 (2 * bb + 2, 0)} := by
    apply Finset.ext; intro q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hq
      rw [hstab q] at hq
      by_cases hg : q.val % d = 0 ∧ (q.val / d = 2 * bb + 1 ∨ q.val / d = 2 * bb + 2)
      · rw [if_pos hg] at hq
        obtain ⟨hcol, hrow⟩ := hg
        have hqval : q.val = d * (q.val / d) + 0 := by
          have h := Nat.div_add_mod q.val d; rw [hcol] at h; omega
        rcases hrow with h | h
        · exfalso
          have : q = gridFin d hd0 (2 * bb + 1, 0) := Fin.ext (by rw [hval0, hqval, h])
          rw [this, hprev] at hq; nomatch hq
        · exact Fin.ext (by rw [hval1, hqval, h])
      · rw [if_neg hg] at hq; simp [ErrorVec.Pauli.anticommutes] at hq
    · intro hq; subst hq
      rw [hstab _, if_pos ⟨by rw [hval1, Nat.mul_add_mod, Nat.zero_mod],
        Or.inr (by rw [hval1, Nat.mul_add_div hd0, Nat.zero_div, Nat.add_zero])⟩, hX]
      decide
  rw [ErrorVec.parity, hfilter, Finset.card_singleton] at hpar
  nomatch hpar

/-- **X-crux D′** (Z̄).  An `X`-type vector commuting with `Z̄` (`mkSurfaceLogicalZ`, the row-0
`Z`-string) that is `I` on every row-0 cell of col `< d-1` is `I` on the corner `(0, d-1)`. -/
theorem crux_Zbar (d : Nat) (hd0 : 0 < d) (hd : 1 < d)
    (x : ErrorVec (d * d)) (hxt : ∀ q, x q = Pauli.X ∨ x q = Pauli.I)
    (hpar : ErrorVec.parity (mkSurfaceLogicalZ d) x = false)
    (hprev : ∀ cc, cc < d - 1 → x (gridFin d hd0 (0, cc)) = Pauli.I) :
    x (gridFin d hd0 (0, d - 1)) = Pauli.I := by
  have hstab : ∀ q : Fin (d * d),
      mkSurfaceLogicalZ d q = if q.val / d = 0 then Pauli.Z else Pauli.I := fun _ => rfl
  have hcorner : (gridFin d hd0 (0, d - 1)).val = d - 1 := by
    rw [gridFin_val_of_lt d hd0 hd0 (by omega)]; omega
  by_contra hne
  have hX : x (gridFin d hd0 (0, d - 1)) = Pauli.X := (hxt _).resolve_right hne
  have hfilter : (Finset.univ.filter fun q =>
      ErrorVec.Pauli.anticommutes (mkSurfaceLogicalZ d q) (x q) = true)
      = {gridFin d hd0 (0, d - 1)} := by
    apply Finset.ext; intro q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hq
      rw [hstab q] at hq
      by_cases hr0 : q.val / d = 0
      · rw [if_pos hr0] at hq
        have hqcol : q.val < d := by
          have h := Nat.div_add_mod q.val d; rw [hr0] at h
          have := Nat.mod_lt q.val hd0; omega
        by_cases hcd : q.val = d - 1
        · exact Fin.ext (by rw [hcorner, hcd])
        · exfalso
          have : q = gridFin d hd0 (0, q.val) := Fin.ext (by
            rw [gridFin_val_of_lt d hd0 hd0 hqcol]; omega)
          rw [this, hprev q.val (by omega)] at hq; nomatch hq
      · rw [if_neg hr0] at hq; simp [ErrorVec.Pauli.anticommutes] at hq
    · intro hq; subst hq
      rw [hstab _, if_pos (by rw [hcorner]; exact Nat.div_eq_of_lt (by omega)), hX]
      decide
  rw [ErrorVec.parity, hfilter, Finset.card_singleton] at hpar
  nomatch hpar

/-! ## X-pivot generators (dual of the Z-pivot generators) -/

/-- The `bulkX r c` generator: `X`-type, `X` at its pivot `(r,c)`, `I` on earlier cells. -/
theorem bulkX_gen (d : Nat) (hd0 : 0 < d) (hd : 1 < d) (r c : Nat) (hr : r < d - 1) (hc : c < d - 1)
    (hpar : (r + c) % 2 = 1) :
    (∀ q, mkSurfaceStabilizers d hd0 ⟨bulkIdx d r c, bulkIdx_lt_numStab d r c hd hr hc⟩ q = Pauli.X
        ∨ mkSurfaceStabilizers d hd0 ⟨bulkIdx d r c, bulkIdx_lt_numStab d r c hd hr hc⟩ q = Pauli.I)
      ∧ mkSurfaceStabilizers d hd0 ⟨bulkIdx d r c, bulkIdx_lt_numStab d r c hd hr hc⟩
          (gridFin d hd0 (r, c)) = Pauli.X
      ∧ (∀ q : Fin (d * d), q.val < d * r + c →
          mkSurfaceStabilizers d hd0 ⟨bulkIdx d r c, bulkIdx_lt_numStab d r c hd hr hc⟩ q
            = Pauli.I) := by
  have hstab : ∀ q : Fin (d * d),
      mkSurfaceStabilizers d hd0 ⟨bulkIdx d r c, bulkIdx_lt_numStab d r c hd hr hc⟩ q
        = if (q.val / d = r ∨ q.val / d = r + 1) ∧ (q.val % d = c ∨ q.val % d = c + 1)
          then Pauli.X else Pauli.I := by
    intro q; simp only [mkSurfaceStabilizers]; exact decode_bulkXIdx d r c _ _ hd hr hc hpar
  refine ⟨fun q => ?_, ?_, fun q hq => ?_⟩
  · rw [hstab q]; split_ifs; exacts [Or.inl rfl, Or.inr rfl]
  · rw [hstab _, if_pos ⟨Or.inl (by rw [gridFin_val_of_lt d hd0 (by omega) (by omega),
        Nat.mul_add_div hd0, Nat.div_eq_of_lt (by omega), Nat.add_zero]),
      Or.inl (by rw [gridFin_val_of_lt d hd0 (by omega) (by omega), Nat.mul_add_mod,
        Nat.mod_eq_of_lt (by omega)])⟩]
  · rw [hstab q, if_neg]
    rintro ⟨hrr, hcc⟩
    have hdm := Nat.div_add_mod q.val d
    have h1 : d * r ≤ d * (q.val / d) := Nat.mul_le_mul_left d (by rcases hrr with h | h <;> omega)
    have h2 : c ≤ q.val % d := by rcases hcc with h | h <;> omega
    omega

/-- The `topX b` generator: `X`-type, `X` at its pivot `(0, 2b)`, `I` on earlier cells. -/
theorem topX_gen (d : Nat) (hd0 : 0 < d) (hd : 1 < d) (b : Nat) (hb : b < (d - 1) / 2) :
    (∀ q, mkSurfaceStabilizers d hd0 ⟨topXIdx d b, topXIdx_lt_numStab d b hd hb⟩ q = Pauli.X
        ∨ mkSurfaceStabilizers d hd0 ⟨topXIdx d b, topXIdx_lt_numStab d b hd hb⟩ q = Pauli.I)
      ∧ mkSurfaceStabilizers d hd0 ⟨topXIdx d b, topXIdx_lt_numStab d b hd hb⟩
          (gridFin d hd0 (0, 2 * b)) = Pauli.X
      ∧ (∀ q : Fin (d * d), q.val < 2 * b →
          mkSurfaceStabilizers d hd0 ⟨topXIdx d b, topXIdx_lt_numStab d b hd hb⟩ q = Pauli.I) := by
  have hstab : ∀ q : Fin (d * d),
      mkSurfaceStabilizers d hd0 ⟨topXIdx d b, topXIdx_lt_numStab d b hd hb⟩ q
        = if q.val / d = 0 ∧ (q.val % d = 2 * b ∨ q.val % d = 2 * b + 1)
          then Pauli.X else Pauli.I := by
    intro q; simp only [mkSurfaceStabilizers]; exact decode_topXIdx d b _ _ hd hb
  refine ⟨fun q => ?_, ?_, fun q hq => ?_⟩
  · rw [hstab q]; split_ifs; exacts [Or.inl rfl, Or.inr rfl]
  · rw [hstab _, if_pos ⟨by rw [gridFin_val_of_lt d hd0 hd0 (by omega), Nat.mul_add_div hd0,
        Nat.div_eq_of_lt (by omega), Nat.add_zero], Or.inl (by rw [gridFin_val_of_lt d hd0 hd0
        (by omega), Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)])⟩]
  · rw [hstab q, if_neg]
    rintro ⟨hrow, hcol⟩
    have hdm := Nat.div_add_mod q.val d; rw [hrow] at hdm
    rcases hcol with h | h <;> omega

/-- The `bottomX b` generator: `X`-type, `X` at its pivot `(d-1, 2b+1)`, `I` on earlier cells. -/
theorem bottomX_gen (d : Nat) (hd0 : 0 < d) (hd : 1 < d) (hodd : d % 2 = 1)
    (b : Nat) (hb : b < (d - 1) / 2) :
    (∀ q, mkSurfaceStabilizers d hd0 ⟨bottomXIdx d b, bottomXIdx_lt_numStab d b hd hodd hb⟩ q = Pauli.X
        ∨ mkSurfaceStabilizers d hd0 ⟨bottomXIdx d b, bottomXIdx_lt_numStab d b hd hodd hb⟩ q = Pauli.I)
      ∧ mkSurfaceStabilizers d hd0 ⟨bottomXIdx d b, bottomXIdx_lt_numStab d b hd hodd hb⟩
          (gridFin d hd0 (d - 1, 2 * b + 1)) = Pauli.X
      ∧ (∀ q : Fin (d * d), q.val < d * (d - 1) + (2 * b + 1) →
          mkSurfaceStabilizers d hd0 ⟨bottomXIdx d b, bottomXIdx_lt_numStab d b hd hodd hb⟩ q
            = Pauli.I) := by
  have hstab : ∀ q : Fin (d * d),
      mkSurfaceStabilizers d hd0 ⟨bottomXIdx d b, bottomXIdx_lt_numStab d b hd hodd hb⟩ q
        = if q.val / d = d - 1 ∧ (q.val % d = 2 * b + 1 ∨ q.val % d = 2 * b + 2)
          then Pauli.X else Pauli.I := by
    intro q; simp only [mkSurfaceStabilizers]; exact decode_bottomXIdx d b _ _ hd hb
  refine ⟨fun q => ?_, ?_, fun q hq => ?_⟩
  · rw [hstab q]; split_ifs; exacts [Or.inl rfl, Or.inr rfl]
  · rw [hstab _, if_pos ⟨by rw [gridFin_val_of_lt d hd0 (by omega) (by omega)]; exact lastRow_div d (2 * b + 1) hd0 (by omega),
      Or.inl (by rw [gridFin_val_of_lt d hd0 (by omega) (by omega)]; exact lastRow_mod d (2 * b + 1) (by omega))⟩]
  · rw [hstab q, if_neg]
    rintro ⟨hrow, hcol⟩
    have hdm := Nat.div_add_mod q.val d
    have h1 : d * (d - 1) ≤ d * (q.val / d) := Nat.mul_le_mul_left d (by omega)
    have h2 : 2 * b + 1 ≤ q.val % d := by rcases hcol with h | h <;> omega
    omega

/-! ## The X-leg: instantiate the abstract peel with the X-pivot table + four X-crux lemmas -/

/-- The pointwise product of two `X`-type vectors is `X`-type. -/
theorem xtype_mul {n : Nat} (a b : ErrorVec n) (ha : ∀ i, a i = Pauli.X ∨ a i = Pauli.I)
    (hb : ∀ i, b i = Pauli.X ∨ b i = Pauli.I) :
    ∀ i, ErrorVec.mul a b i = Pauli.X ∨ ErrorVec.mul a b i = Pauli.I := by
  intro i; simp only [ErrorVec.mul]
  rcases ha i with h | h <;> rcases hb i with h2 | h2 <;> rw [h, h2] <;> decide

/-- **X-side invariant preservation.**  Multiplying by an X-check generator keeps the vector
`X`-type, in the normalizer, and commuting with `Z̄` (via `logicalZ_normalizer_parametric`). -/
theorem xcheck_preserves (d : Nat) (hd0 : 0 < d) (hodd : d % 2 = 1)
    (j : Fin (numStabFormula d))
    (hjxt : ∀ i, mkSurfaceStabilizers d hd0 j i = Pauli.X
      ∨ mkSurfaceStabilizers d hd0 j i = Pauli.I)
    (x : ErrorVec (d * d)) (hxt : ∀ q, x q = Pauli.X ∨ x q = Pauli.I)
    (hcomm : ∀ k, ErrorVec.parity (mkSurfaceStabilizers d hd0 k) x = false)
    (hzbar : ErrorVec.parity (mkSurfaceLogicalZ d) x = false) :
    (∀ q, ErrorVec.mul (mkSurfaceStabilizers d hd0 j) x q = Pauli.X
        ∨ ErrorVec.mul (mkSurfaceStabilizers d hd0 j) x q = Pauli.I)
      ∧ (∀ k, ErrorVec.parity (mkSurfaceStabilizers d hd0 k)
          (ErrorVec.mul (mkSurfaceStabilizers d hd0 j) x) = false)
      ∧ ErrorVec.parity (mkSurfaceLogicalZ d)
          (ErrorVec.mul (mkSurfaceStabilizers d hd0 j) x) = false := by
  refine ⟨xtype_mul _ _ hjxt hxt, fun k => ?_, ?_⟩
  · rw [QStab.Paper.LogicalCosets.parity_mul_right,
      stab_commute_parametric d hd0 hodd k j, hcomm k]; rfl
  · rw [QStab.Paper.LogicalCosets.parity_mul_right,
      QStab.Paper.LogicalCosets.parity_symm (mkSurfaceLogicalZ d) (mkSurfaceStabilizers d hd0 j),
      logicalZ_normalizer_parametric d hd0 j, hzbar]; rfl

/-- X-analog of `mul_clears`. -/
theorem mul_clears_X {n : Nat} (g z : ErrorVec n) (k : Fin n) (hgk : g k = Pauli.X)
    (hzk : z k = Pauli.X) : ErrorVec.mul g z k = Pauli.I := by
  simp only [ErrorVec.mul, hgk, hzk]; decide

/-- X-analog of `mul_ztype_involutive`. -/
theorem mul_xtype_involutive {n : Nat} (g z : ErrorVec n)
    (hg : ∀ i, g i = Pauli.X ∨ g i = Pauli.I) :
    ErrorVec.mul g (ErrorVec.mul g z) = z := by
  funext i; simp only [ErrorVec.mul]; rcases hg i with h | h <;> rw [h] <;> cases z i <;> decide

/-- **The abstract pivot-peel, X-parametrized** (dual of `abstract_peel`, `Pauli.X` live value). -/
theorem abstract_peel_X {P : QECParams} (Inv : ErrorVec P.n → Prop)
    (hInvX : ∀ z, Inv z → ∀ i, z i = Pauli.X ∨ z i = Pauli.I)
    (hdispatch : ∀ (k : Fin P.n) (z : ErrorVec P.n), Inv z →
      (∀ q : Fin P.n, q.val < k.val → z q = Pauli.I) → z k ≠ Pauli.I →
      ∃ g, QStab.InStab P g ∧ (∀ i, g i = Pauli.X ∨ g i = Pauli.I) ∧
        (∀ q : Fin P.n, q.val < k.val → g q = Pauli.I) ∧ g k = Pauli.X
        ∧ Inv (ErrorVec.mul g z)) :
    ∀ (fuel k : Nat), P.n - k = fuel → k ≤ P.n → ∀ z : ErrorVec P.n, Inv z →
      (∀ q : Fin P.n, q.val < k → z q = Pauli.I) → QStab.InStab P z := by
  intro fuel
  induction fuel with
  | zero =>
      intro k _hfuel hk z _hInv hcleared
      have hkeq : k = P.n := by omega
      have hzid : z = ErrorVec.identity P.n :=
        funext fun q => hcleared q (by rw [hkeq]; exact q.isLt)
      rw [hzid]; exact QStab.InStab.identity
  | succ fuel ih =>
      intro k hfuel hk z hInv hcleared
      have hklt : k < P.n := by omega
      by_cases hzk : z ⟨k, hklt⟩ = Pauli.I
      · refine ih (k + 1) (by omega) (by omega) z hInv (fun q hq => ?_)
        rcases Nat.lt_succ_iff_lt_or_eq.mp hq with h | h
        · exact hcleared q h
        · rw [show q = ⟨k, hklt⟩ from Fin.ext h]; exact hzk
      · obtain ⟨g, hg_stab, hg_xt, hg_prefix, hg_k, hg_inv⟩ :=
          hdispatch ⟨k, hklt⟩ z hInv hcleared hzk
        have hz'cleared : ∀ q : Fin P.n, q.val < k + 1 → ErrorVec.mul g z q = Pauli.I := by
          intro q hq
          rcases Nat.lt_succ_iff_lt_or_eq.mp hq with h | h
          · rw [mul_prefix g z q (hg_prefix q h)]; exact hcleared q h
          · rw [show q = ⟨k, hklt⟩ from Fin.ext h,
              mul_clears_X g z ⟨k, hklt⟩ hg_k ((hInvX z hInv ⟨k, hklt⟩).resolve_right hzk)]
        have hz' : QStab.InStab P (ErrorVec.mul g z) :=
          ih (k + 1) (by omega) (by omega) (ErrorVec.mul g z) hg_inv hz'cleared
        rw [← mul_xtype_involutive g z hg_xt]
        exact QStab.InStab.mul hg_stab hz'

/-- **The X-side cleaning leg** (dual of `surface_zside`).  An `X`-type vector commuting with
every stabilizer and with `Z̄` is a stabilizer product. -/
theorem surface_xside (d : Nat) (hd0 : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (x : ErrorVec (d * d)) (hxt : ∀ q, x q = Pauli.X ∨ x q = Pauli.I)
    (hcomm : ∀ k, ErrorVec.parity (mkSurfaceStabilizers d hd0 k) x = false)
    (hzbar : ErrorVec.parity (mkSurfaceLogicalZ d) x = false) :
    QStab.InStab (mkSurfaceQECParams d hd0 hodd) x := by
  have hd : 1 < d := by omega
  refine abstract_peel_X (P := mkSurfaceQECParams d hd0 hodd)
    (fun w => (∀ q, w q = Pauli.X ∨ w q = Pauli.I) ∧
      (∀ k, ErrorVec.parity (mkSurfaceStabilizers d hd0 k) w = false) ∧
      ErrorVec.parity (mkSurfaceLogicalZ d) w = false)
    (fun w hw => hw.1) ?_ (d * d) 0 (Nat.sub_zero _) (Nat.zero_le _) x ⟨hxt, hcomm, hzbar⟩
    (fun q hq => absurd hq (Nat.not_lt_zero _))
  rintro k w ⟨hwxt, hwcomm, hwzbar⟩ hcleared hlive
  have hrowlt : k.val / d < d := Nat.div_lt_of_lt_mul k.isLt
  have hcollt : k.val % d < d := Nat.mod_lt _ hd0
  obtain ⟨r, hrdef⟩ : ∃ r, k.val / d = r := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c, k.val % d = c := ⟨_, rfl⟩
  have hkval : k.val = d * r + c := by rw [← hrdef, ← hcdef]; exact (Nat.div_add_mod k.val d).symm
  rw [hrdef] at hrowlt; rw [hcdef] at hcollt
  have hkeq : ∀ (row col : Nat), row < d → col < d → k.val = d * row + col →
      k = gridFin d hd0 (row, col) :=
    fun row col hrw hcw h => Fin.ext (by rw [gridFin_val_of_lt d hd0 hrw hcw]; exact h)
  have hprev : ∀ (cr cc : Nat), cr < d → cc < d → (cr < r ∨ (cr = r ∧ cc < c)) →
      w (gridFin d hd0 (cr, cc)) = Pauli.I := fun cr cc hcr hcc hlt =>
    hcleared _ (by rw [gridFin_val_of_lt d hd0 hcr hcc, hkval]; exact cell_lt d hd0 r c cr cc hcc hlt)
  by_cases hpar_rc : (r + c) % 2 = 0
  · -- EVEN parity
    by_cases hr0 : r = 0
    · by_cases hcd : c = d - 1
      · -- Zbar corner (0, d-1)
        exfalso; apply hlive
        rw [hkeq r c hrowlt hcollt hkval, hr0, hcd]
        exact crux_Zbar d hd0 hd w hwxt hwzbar
          (fun cc hcc => hprev 0 cc hd0 (by omega) (Or.inr ⟨hr0.symm, by omega⟩))
      · -- topX pivot (0, c), c even ≤ d-3
        obtain ⟨b, hbb⟩ : ∃ b, c = 2 * b := ⟨c / 2, by omega⟩
        have hbbb : b < (d - 1) / 2 := by omega
        obtain ⟨hgzt, hgval, hgpre⟩ := topX_gen d hd0 hd b hbbb
        refine ⟨_, QStab.InStab.gen ⟨topXIdx d b, topXIdx_lt_numStab d b hd hbbb⟩,
          hgzt, fun q hq => hgpre q (by rw [hkval, hr0, Nat.mul_zero, Nat.zero_add, hbb] at hq; exact hq),
          by rw [hkeq 0 (2 * b) hd0 (by omega) (by rw [hkval, hr0, hbb])]; exact hgval,
          xcheck_preserves d hd0 hodd _ hgzt w hwxt hwcomm hwzbar⟩
    · by_cases hc0 : c = 0
      · -- leftZ crux (even r ≥ 2, 0)
        exfalso; apply hlive
        obtain ⟨bb, hbb⟩ : ∃ bb, r = 2 * bb + 2 := ⟨(r - 2) / 2, by omega⟩
        rw [hkeq r c hrowlt hcollt hkval, hbb, hc0]
        exact crux_leftZ d hd0 hd bb (by omega) w hwxt (hwcomm _)
          (hprev (2 * bb + 1) 0 (by omega) hd0 (Or.inl (by omega)))
      · -- bulkZ crux (r, c ≥ 1) → top-left (r-1, c-1)
        exfalso; apply hlive
        obtain ⟨rr, hrr⟩ : ∃ rr, r = rr + 1 := ⟨r - 1, by omega⟩
        obtain ⟨cc, hcc⟩ : ∃ cc, c = cc + 1 := ⟨c - 1, by omega⟩
        rw [hkeq r c hrowlt hcollt hkval, hrr, hcc]
        exact crux_bulkZ d hd0 hd rr cc (by omega) (by omega) (by omega) w hwxt (hwcomm _)
          (hprev rr cc (by omega) (by omega) (Or.inl (by omega)))
          (hprev rr (cc + 1) (by omega) (by omega) (Or.inl (by omega)))
          (hprev (rr + 1) cc (by omega) (by omega) (Or.inr ⟨by omega, by omega⟩))
  · -- ODD parity
    by_cases hbulk : r < d - 1 ∧ c < d - 1
    · -- bulkX pivot (r, c)
      obtain ⟨hgzt, hgval, hgpre⟩ := bulkX_gen d hd0 hd r c hbulk.1 hbulk.2 (by omega)
      exact ⟨_, QStab.InStab.gen ⟨bulkIdx d r c, bulkIdx_lt_numStab d r c hd hbulk.1 hbulk.2⟩,
        hgzt, fun q hq => hgpre q (by rw [hkval] at hq; exact hq),
        by rw [hkeq r c hrowlt hcollt hkval]; exact hgval,
        xcheck_preserves d hd0 hodd _ hgzt w hwxt hwcomm hwzbar⟩
    · by_cases hrd : r = d - 1
      · -- bottomX pivot (d-1, c), c odd
        obtain ⟨b, hbb⟩ : ∃ b, c = 2 * b + 1 := ⟨(c - 1) / 2, by omega⟩
        have hbbb : b < (d - 1) / 2 := by omega
        obtain ⟨hgzt, hgval, hgpre⟩ := bottomX_gen d hd0 hd hodd b hbbb
        refine ⟨_, QStab.InStab.gen ⟨bottomXIdx d b, bottomXIdx_lt_numStab d b hd hodd hbbb⟩,
          hgzt, fun q hq => hgpre q (by rw [hkval, hrd, hbb] at hq; exact hq),
          by rw [hkeq (d - 1) (2 * b + 1) (by omega) (by omega) (by rw [hkval, hrd, hbb])]; exact hgval,
          xcheck_preserves d hd0 hodd _ hgzt w hwxt hwcomm hwzbar⟩
      · -- rightZ crux (odd r, d-1)
        exfalso; apply hlive
        obtain ⟨bb, hbb⟩ : ∃ bb, r = 2 * bb + 1 := ⟨(r - 1) / 2, by omega⟩
        rw [hkeq r c hrowlt hcollt hkval, hbb, show c = d - 1 by omega]
        exact crux_rightZ d hd0 hd bb (by omega) w hwxt (hwcomm _)
          (hprev (2 * bb) (d - 1) (by omega) (by omega) (Or.inl (by omega)))

/-! ## CSS assembly: the maximal-isotropic keystone

The two cleaning legs (`surface_xside`, `surface_zside`) are combined through
the pointwise CSS split `E = (X-part) · (Z-part)`: an X-type row reads only the
Z-content of an error and vice versa (`parity_{x,z}type_{z,x}Part`), so the
axiom splits into the two single-type statements the legs discharge.  All
statements are over the real objects `mkSurfaceStabilizers`,
`mkSurfaceQECParams`, `X̄ = mkSurfaceAttackerX`, `Z̄ = mkSurfaceLogicalZ`. -/

private theorem anticommutes_I_right (p : Pauli) :
    ErrorVec.Pauli.anticommutes p Pauli.I = false := by cases p <;> rfl

private theorem anticommutes_I_left (p : Pauli) :
    ErrorVec.Pauli.anticommutes Pauli.I p = false := rfl

/-- Same-type commutation: a `Z`-type row reads `false` parity against any
`Z`-type vector (all four `{Z,I}×{Z,I}` positions commute). -/
theorem parity_same_ztype {n : Nat} (S w : ErrorVec n)
    (hS : ∀ q, S q = Pauli.Z ∨ S q = Pauli.I)
    (hw : ∀ q, w q = Pauli.Z ∨ w q = Pauli.I) :
    ErrorVec.parity S w = false := by
  unfold ErrorVec.parity
  have h : (Finset.univ.filter fun i =>
      ErrorVec.Pauli.anticommutes (S i) (w i)).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro q _ hP
    rcases hS q with h1 | h1 <;> rcases hw q with h2 | h2 <;>
      simp [h1, h2, ErrorVec.Pauli.anticommutes] at hP
  rw [h]; rfl

/-- Same-type commutation: an `X`-type row reads `false` parity against any
`X`-type vector. -/
theorem parity_same_xtype {n : Nat} (S w : ErrorVec n)
    (hS : ∀ q, S q = Pauli.X ∨ S q = Pauli.I)
    (hw : ∀ q, w q = Pauli.X ∨ w q = Pauli.I) :
    ErrorVec.parity S w = false := by
  unfold ErrorVec.parity
  have h : (Finset.univ.filter fun i =>
      ErrorVec.Pauli.anticommutes (S i) (w i)).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro q _ hP
    rcases hS q with h1 | h1 <;> rcases hw q with h2 | h2 <;>
      simp [h1, h2, ErrorVec.Pauli.anticommutes] at hP
  rw [h]; rfl

/-- Each surface stabilizer generator is pure-type: `X`-type or `Z`-type
(the code is CSS). -/
theorem stab_type_split (d : Nat) (hd0 : 0 < d) (k : Fin (numStabFormula d)) :
    (∀ q, mkSurfaceStabilizers d hd0 k q = Pauli.X ∨ mkSurfaceStabilizers d hd0 k q = Pauli.I)
    ∨ (∀ q, mkSurfaceStabilizers d hd0 k q = Pauli.Z ∨ mkSurfaceStabilizers d hd0 k q = Pauli.I) := by
  have hty : stabType d k.val = Pauli.X ∨ stabType d k.val = Pauli.Z := by
    simp only [stabType]; split_ifs <;> simp
  rcases hty with hX | hZ
  · left; intro q
    show decodeStabPauliAt d k.val (q.val / d) (q.val % d) = Pauli.X ∨
      decodeStabPauliAt d k.val (q.val / d) (q.val % d) = Pauli.I
    rcases decode_I_or_stabType_pub d k.val (q.val / d) (q.val % d) with h | h
    · exact Or.inr h
    · exact Or.inl (h.trans hX)
  · right; intro q
    show decodeStabPauliAt d k.val (q.val / d) (q.val % d) = Pauli.Z ∨
      decodeStabPauliAt d k.val (q.val / d) (q.val % d) = Pauli.I
    rcases decode_I_or_stabType_pub d k.val (q.val / d) (q.val % d) with h | h
    · exact Or.inr h
    · exact Or.inl (h.trans hZ)

/-- `Z̄` (row-0 `Z` string) is `Z`-type. -/
theorem mkSurfaceLogicalZ_ztype (d : Nat) :
    ∀ q, mkSurfaceLogicalZ d q = Pauli.Z ∨ mkSurfaceLogicalZ d q = Pauli.I := by
  intro q; unfold mkSurfaceLogicalZ
  by_cases h : q.val / d = 0
  · rw [if_pos h]; exact Or.inl rfl
  · rw [if_neg h]; exact Or.inr rfl

/-- `X̄` (column-0 `X` string) is `X`-type. -/
theorem mkSurfaceAttackerX_xtype (d : Nat) :
    ∀ q, mkSurfaceAttackerX d q = Pauli.X ∨ mkSurfaceAttackerX d q = Pauli.I := by
  intro q
  have h : mkSurfaceAttackerX d q = if q.val % d = 0 then Pauli.X else Pauli.I := rfl
  rw [h]; by_cases hc : q.val % d = 0
  · rw [if_pos hc]; exact Or.inl rfl
  · rw [if_neg hc]; exact Or.inr rfl

/-- **The maximal-isotropic keystone** for the rotated surface code.  An error
commuting with every stabilizer generator and with both `X̄` and `Z̄` is a
product of stabilizer generators.  Assembled from the two CSS legs
(`surface_xside`, `surface_zside`) via the split `E = (X-part) · (Z-part)`. -/
theorem surface_maximal_isotropic (d : Nat) (hd0 : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (E : ErrorVec (d * d))
    (hstab : ∀ k, ErrorVec.parity (mkSurfaceStabilizers d hd0 k) E = false)
    (hXbar : ErrorVec.parity (mkSurfaceAttackerX d) E = false)
    (hZbar : ErrorVec.parity (mkSurfaceLogicalZ d) E = false) :
    QStab.InStab (mkSurfaceQECParams d hd0 hodd) E := by
  have hsplit : E = ErrorVec.mul (xPartVec E) (zPartVec E) := (xPart_mul_zPart E).symm
  rw [hsplit]
  refine QStab.InStab.mul ?_ ?_
  · -- X-part via surface_xside: reads Z-checks (through E) and X-checks (same-type)
    apply surface_xside d hd0 hd3 hodd (xPartVec E) (xPartVec_xtype E)
    · intro k
      rcases stab_type_split d hd0 k with hkX | hkZ
      · exact parity_same_xtype (mkSurfaceStabilizers d hd0 k) (xPartVec E) hkX (xPartVec_xtype E)
      · rw [← parity_ztype_xPart (mkSurfaceStabilizers d hd0 k) E hkZ]; exact hstab k
    · rw [← parity_ztype_xPart (mkSurfaceLogicalZ d) E (mkSurfaceLogicalZ_ztype d)]; exact hZbar
  · -- Z-part via surface_zside: reads X-checks (through E) and Z-checks (same-type)
    apply surface_zside d hd0 hd3 hodd (zPartVec E) (zPartVec_ztype E)
    · intro k
      rcases stab_type_split d hd0 k with hkX | hkZ
      · rw [← parity_xtype_zPart (mkSurfaceStabilizers d hd0 k) E hkX]; exact hstab k
      · exact parity_same_ztype (mkSurfaceStabilizers d hd0 k) (zPartVec E) hkZ (zPartVec_ztype E)
    · rw [← parity_xtype_zPart (mkSurfaceAttackerX d) E (mkSurfaceAttackerX_xtype d)]; exact hXbar

/-- `X̄` and `Z̄` anticommute: their supports (column 0 / row 0) overlap only at
the corner qubit `0`, with `X` against `Z`. -/
theorem surface_Xbar_anticomm_Zbar (d : Nat) (hd0 : 0 < d) :
    ErrorVec.parity (mkSurfaceAttackerX d) (mkSurfaceLogicalZ d) = true := by
  have h0lt : 0 < d * d := Nat.mul_pos hd0 hd0
  unfold ErrorVec.parity
  have hsingle : (Finset.univ.filter fun i =>
      ErrorVec.Pauli.anticommutes (mkSurfaceAttackerX d i) (mkSurfaceLogicalZ d i)).card = 1 := by
    apply Finset.card_eq_one.mpr
    refine ⟨⟨0, h0lt⟩, ?_⟩
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hq
      apply Fin.ext
      show q.val = 0
      by_cases hx : q.val % d = 0
      · by_cases hz : q.val / d = 0
        · have hdm := Nat.div_add_mod q.val d
          rw [hz, hx, Nat.mul_zero, Nat.add_zero] at hdm
          exact hdm.symm
        · exfalso
          have hzv : mkSurfaceLogicalZ d q = Pauli.I := by
            unfold mkSurfaceLogicalZ; rw [if_neg hz]
          rw [hzv, anticommutes_I_right] at hq
          exact Bool.noConfusion hq
      · exfalso
        have hxv : mkSurfaceAttackerX d q = Pauli.I := by
          have h : mkSurfaceAttackerX d q = if q.val % d = 0 then Pauli.X else Pauli.I := rfl
          rw [h, if_neg hx]
        rw [hxv, anticommutes_I_left] at hq
        exact Bool.noConfusion hq
    · intro hq; subst hq
      have hxv : mkSurfaceAttackerX d ⟨0, h0lt⟩ = Pauli.X := by
        have h : mkSurfaceAttackerX d ⟨0, h0lt⟩ = if (0 : Nat) % d = 0 then Pauli.X else Pauli.I := rfl
        rw [h, if_pos (Nat.zero_mod d)]
      have hzv : mkSurfaceLogicalZ d ⟨0, h0lt⟩ = Pauli.Z := by
        unfold mkSurfaceLogicalZ; rw [if_pos (Nat.zero_div d)]
      rw [hxv, hzv]; rfl
  rw [hsingle]; rfl

/-- **The logical-operator system of the rotated surface code**, over the real
objects `X̄ = mkSurfaceAttackerX`, `Z̄ = mkSurfaceLogicalZ`, with the
maximal-isotropic axiom discharged by constructive pivot-peel cleaning. -/
def surfaceLogicalOps (d : Nat) (hd0 : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1) :
    QStab.Paper.LogicalCosets.LogicalOps (mkSurfaceQECParams d hd0 hodd) where
  Xbar := mkSurfaceAttackerX d
  Zbar := mkSurfaceLogicalZ d
  Xbar_comm := mkSurfaceAttackerX_commutes_with_stabilizers d hd0 hodd
  Zbar_comm := logicalZ_normalizer_parametric d hd0
  Xbar_anticomm_Zbar := surface_Xbar_anticomm_Zbar d hd0
  maximal_isotropic := surface_maximal_isotropic d hd0 hd3 hodd

/-- **Coverage** for the rotated surface code: a centralizer element outside the
stabilizer subgroup anticommutes with `X̄` or with `Z̄` (else the keystone would
place it inside). -/
theorem surface_coverage (d : Nat) (hd0 : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (E : ErrorVec (mkSurfaceQECParams d hd0 hodd).n)
    (hcent : ∀ j : Fin (mkSurfaceQECParams d hd0 hodd).numStab,
      ErrorVec.parity ((mkSurfaceQECParams d hd0 hodd).stabilizers j) E = false)
    (hnot : ¬ QStab.InStab (mkSurfaceQECParams d hd0 hodd) E) :
    ErrorVec.parity (mkSurfaceAttackerX d) E = true
      ∨ ErrorVec.parity (mkSurfaceLogicalZ d) E = true :=
  QStab.Paper.LogicalCosets.LogicalOps.coverage (surfaceLogicalOps d hd0 hd3 hodd) E hcent hnot

/-- **Four-coset normalizer decomposition** for the rotated surface code: every
centralizer element lies in one of `S`, `X̄·S`, `Z̄·S`, `(X̄ Z̄)·S`. -/
theorem surface_normalizer_decomposition (d : Nat) (hd0 : 0 < d) (hd3 : 3 ≤ d) (hodd : d % 2 = 1)
    (E : ErrorVec (mkSurfaceQECParams d hd0 hodd).n)
    (hE : ∀ s, ErrorVec.parity ((mkSurfaceQECParams d hd0 hodd).stabilizers s) E = false) :
    QStab.InStab (mkSurfaceQECParams d hd0 hodd) E
    ∨ QStab.InStab (mkSurfaceQECParams d hd0 hodd) (ErrorVec.mul (mkSurfaceAttackerX d) E)
    ∨ QStab.InStab (mkSurfaceQECParams d hd0 hodd) (ErrorVec.mul (mkSurfaceLogicalZ d) E)
    ∨ QStab.InStab (mkSurfaceQECParams d hd0 hodd)
        (ErrorVec.mul (mkSurfaceAttackerX d) (ErrorVec.mul (mkSurfaceLogicalZ d) E)) :=
  QStab.Paper.LogicalCosets.normalizer_decomposition (surfaceLogicalOps d hd0 hd3 hodd) E hE

/-! ## `d = 3` fingerprints against the Python oracle (`notes/validate_surface_maxiso.py`)

Interpreter-checked `#eval` cross-checks of the CSS-assembly logic plus
(kernel-checked) axiom pins for the keystone headliners. -/

-- `X̄` (column 0) and `Z̄` (row 0) overlap at exactly the corner qubit `0`
-- (the `surface_Xbar_anticomm_Zbar` support).
/-- info: [0] -/
#guard_msgs in
#eval (List.finRange 9).filter (fun q =>
    ErrorVec.Pauli.anticommutes (mkSurfaceAttackerX 3 q) (mkSurfaceLogicalZ 3 q)) |>.map (·.val)

-- `d = 3` stabilizer type table (`true` = `Z`-type): the CSS split's per-check
-- classification (`stab_type_split`), matching `entry` in the oracle.
/-- info: [true, false, false, true, false, true, true, false] -/
#guard_msgs in
#eval (List.finRange (numStabFormula 3)).map fun k =>
  (List.finRange 9).all fun q => match mkSurfaceStabilizers 3 (by decide) k q with
    | Pauli.Z => true | Pauli.I => true | _ => false

/-- info: 'QStab.QClifford.Compile.surface_maximal_isotropic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms surface_maximal_isotropic

/-- info: 'QStab.QClifford.Compile.surfaceLogicalOps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms surfaceLogicalOps

/-- info: 'QStab.QClifford.Compile.surface_coverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms surface_coverage

/-- info: 'QStab.QClifford.Compile.surface_normalizer_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms surface_normalizer_decomposition

end QStab.QClifford.Compile
