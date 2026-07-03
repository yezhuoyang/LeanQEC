import QStab.Examples.SurfaceRowEquiv

/-!
# X-check index helpers

The X-side mirror of `SurfaceRowEquiv`'s Z-check index helpers (`bulkIdx`/`rightZIdx`/
`leftZIdx` + `classifyStab_*Idx`): named indices for the odd-parity bulk X-checks and the
`topX`/`bottomX` boundary bands, with their `classifyStab` characterizations.  These connect
the cleaning leg's `∀ k`-stabilizer hypotheses to the specific geometric X-check each
no-pivot crux lemma consumes.  (`SurfaceRowEquiv.lean` is frozen, so the X-side lives here.)
-/

namespace QStab.Examples.SurfaceParametric

/-- Index of the boundary X-check `topX b` (the first boundary band). -/
def topXIdx (d b : Nat) : Nat := (d - 1) * (d - 1) + b

/-- Index of the boundary X-check `bottomX b` (the last boundary band). -/
def bottomXIdx (d b : Nat) : Nat := (d - 1) * (d - 1) + 3 * ((d - 1) / 2) + b

theorem topXIdx_lt_numStab (d b : Nat) (_hd : 1 < d) (hb : b < (d - 1) / 2) :
    topXIdx d b < numStabFormula d := by
  unfold topXIdx numStabFormula
  have h2 : (d - 1) / 2 ≤ d - 1 := Nat.div_le_self _ _
  omega

theorem bottomXIdx_lt_numStab (d b : Nat) (hd : 1 < d) (hodd : d % 2 = 1)
    (hb : b < (d - 1) / 2) :
    bottomXIdx d b < numStabFormula d := by
  unfold bottomXIdx numStabFormula
  have h2 : 2 * ((d - 1) / 2) = d - 1 := by omega
  omega

/-- The odd-parity mirror of `classifyStab_bulkIdx_even`: bulk indices with odd
row-plus-column parity classify as `bulkX`. -/
theorem classifyStab_bulkIdx_odd (d r c : Nat) (hd : 1 < d)
    (hr : r < d - 1) (hc : c < d - 1) (hpar : (r + c) % 2 = 1) :
    classifyStab d (bulkIdx d r c) = StabKind.bulkX r c := by
  unfold classifyStab
  have hlt := bulkIdx_lt_bulkCount d r c hr hc
  rw [if_pos hlt]
  obtain ⟨hdiv, hmod⟩ := bulkIdx_div_mod d r c hd hc
  rw [hdiv, hmod, if_neg (by omega)]

theorem classifyStab_topXIdx (d b : Nat) (_hd : 1 < d) (hb : b < (d - 1) / 2) :
    classifyStab d (topXIdx d b) = StabKind.topX b := by
  unfold classifyStab topXIdx
  have hge : (d - 1) * (d - 1) ≤ (d - 1) * (d - 1) + b := by omega
  rw [if_neg (Nat.not_lt_of_ge hge)]
  set b' := (d - 1) * (d - 1) + b - (d - 1) * (d - 1) with hb'def
  have hb'_eq : b' = b := by rw [hb'def]; omega
  rw [if_pos (by rw [hb'_eq]; exact hb), hb'_eq]

theorem classifyStab_bottomXIdx (d b : Nat) (_hd : 1 < d) (_hb : b < (d - 1) / 2) :
    classifyStab d (bottomXIdx d b) = StabKind.bottomX b := by
  unfold classifyStab bottomXIdx
  have hge : (d - 1) * (d - 1)
      ≤ (d - 1) * (d - 1) + 3 * ((d - 1) / 2) + b := by omega
  rw [if_neg (Nat.not_lt_of_ge hge)]
  set b' := (d - 1) * (d - 1) + 3 * ((d - 1) / 2) + b - (d - 1) * (d - 1) with hb'def
  have hb'_eq : b' = 3 * ((d - 1) / 2) + b := by rw [hb'def]; omega
  have hnot_top : ¬ b' < (d - 1) / 2 := by rw [hb'_eq]; omega
  have hnot_right : ¬ b' < 2 * ((d - 1) / 2) := by rw [hb'_eq]; omega
  have hnot_left : ¬ b' < 3 * ((d - 1) / 2) := by rw [hb'_eq]; omega
  rw [if_neg hnot_top, if_neg hnot_right, if_neg hnot_left]
  have h_sub : b' - 3 * ((d - 1) / 2) = b := by rw [hb'_eq]; omega
  rw [h_sub]

end QStab.Examples.SurfaceParametric
