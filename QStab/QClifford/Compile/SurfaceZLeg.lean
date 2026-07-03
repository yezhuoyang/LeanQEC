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

end QStab.QClifford.Compile
