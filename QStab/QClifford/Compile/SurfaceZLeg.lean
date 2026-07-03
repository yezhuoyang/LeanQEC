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
          rw [this, hprev] at hq; exact absurd hq (by decide)
        · exact Fin.ext (by rw [hval1, hqval, h])
      · rw [if_neg hg] at hq; simp [ErrorVec.Pauli.anticommutes] at hq
    · intro hq; subst hq
      rw [hstab _, if_pos ⟨by rw [hval1]; exact Nat.div_eq_of_lt hb2,
        Or.inr (by rw [hval1]; exact Nat.mod_eq_of_lt hb2)⟩, hZ]
      decide
  rw [ErrorVec.parity, hfilter, Finset.card_singleton] at hpar
  exact absurd hpar (by decide)

end QStab.QClifford.Compile
