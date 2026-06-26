import QStab.QHL.Verify.SurfaceRowCharacterizationKeystone

/-!
# META-level (Nat) surface-code self-similarity

The `div`/`mod`-level single-step self-similarity identities for the surface
code at distance `d = oddDistance m = 2*m+3` (so `d-1 = 2m+2`, `d-2 = 2m+1`).

These are ordinary `Nat` theorems (no object logic), proved with the full power
of `omega`/`simp`/`Nat` lemmas.  They are the genuine hard content underlying the
object-logic self-similarity bridge: under the active cell/inside context, the
inner flat classifier at the mapped inner cell equals the outer bulk band/kind.

The KEY parity fact: the inner plaquette coordinates `(r', c') = (r-1, c-1)`
satisfy `r' + c' = r + c - 2`, same parity, so `bulkKind` is preserved.
-/

namespace QHL.CodeLang.Surface.Verify

open QHL.CodeLang
open QHL.CodeLang.Surface

/-! ## Generic grid bound

`a * n + b < n * n` whenever `a < n` and `b < n` — the 2-D grid linearization
bound used to discharge `k < bulkCount` for both the inner and outer cells. -/

private theorem cellLinIndexLt {a b n : Nat} (ha : a < n) (hb : b < n) :
    a * n + b < n * n := by
  have h1 : a + 1 ≤ n := ha
  have h2 : (a + 1) * n ≤ n * n := Nat.mul_le_mul_right _ h1
  have h3 : a * n + n = (a + 1) * n := by rw [Nat.succ_mul]
  omega

/-! ## Interior self-similarity -/

/-- Interior single-step self-similarity (Nat-level).  Under the interior-cell and
inside contexts at distance `d = 2m+3`, the inner flat classifier at the mapped
inner interior cell equals the outer bulk band/kind classifier. -/
theorem interiorSelfSimNat (m k q : Nat)
    (hI : isInteriorCell (2*m+3) k = true)
    (hIn : isInside (2*m+3) q = true) :
    surfaceCellPauli (2*m+1) (innerInteriorK (2*m+3) k) (innerQval (2*m+3) q)
      = surfaceCellPauli (2*m+3) k q := by
  simp only [isInteriorCell, isInside, cellLastCell, cellR, cellC, cellRow, cellCol,
    Bool.and_eq_true, decide_eq_true_eq] at hI hIn
  obtain ⟨hr1, hr2, hc1, hc2⟩ := hI
  obtain ⟨hrow1, hrow2, hcol1, hcol2⟩ := hIn
  -- Normalize subtractions in the hypotheses.
  simp only [show 2 * m + 3 - 1 = 2 * m + 2 from by omega,
      show 2 * m + 2 - 1 = 2 * m + 1 from by omega] at hr1 hr2 hc1 hc2 hrow2 hcol2
  -- Outer plaquette / qubit coordinates.
  set r := k / (2 * m + 2) with hr
  set c := k % (2 * m + 2) with hc
  set row := q / (2 * m + 3) with hrowdef
  set col := q % (2 * m + 3) with hcoldef
  -- so: 1 ≤ r < 2m+1, 1 ≤ c < 2m+1, 1 ≤ row < 2m+2, 1 ≤ col < 2m+2
  -- Compute the inner stab index and inner qubit.
  have hK : innerInteriorK (2 * m + 3) k = (r - 1) * (2 * m) + (c - 1) := by
    unfold innerInteriorK
    simp only [cellR, cellC, show 2 * m + 3 - 1 = 2 * m + 2 from by omega,
      show 2 * m + 3 - 2 - 1 = 2 * m from by omega, ← hr, ← hc]
  have hQ : innerQval (2 * m + 3) q = (row - 1) * (2 * m + 1) + (col - 1) := by
    unfold innerQval
    simp only [cellRow, cellCol, show 2 * m + 3 - 2 = 2 * m + 1 from by omega,
      ← hrowdef, ← hcoldef]
  rw [hK, hQ]
  -- Inner plaquette / qubit coordinates from the mapped index.
  have hKR : ((r - 1) * (2 * m) + (c - 1)) / (2 * m) = r - 1 := by
    rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), Nat.add_zero]
  have hKC : ((r - 1) * (2 * m) + (c - 1)) % (2 * m) = c - 1 := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  have hQR : ((row - 1) * (2 * m + 1) + (col - 1)) / (2 * m + 1) = row - 1 := by
    rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), Nat.add_zero]
  have hQC : ((row - 1) * (2 * m + 1) + (col - 1)) % (2 * m + 1) = col - 1 := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  -- Both sides are bulk cells.
  have hKbulk : (r - 1) * (2 * m) + (c - 1) < 2 * m * (2 * m) :=
    cellLinIndexLt (by omega) (by omega)
  have hkbulk : k < (2 * m + 2) * (2 * m + 2) := by
    have hk : k = r * (2 * m + 2) + c := by
      rw [hr, hc, Nat.mul_comm]; exact (Nat.div_add_mod k (2 * m + 2)).symm
    rw [hk]; exact cellLinIndexLt (by omega) (by omega)
  -- Unfold and reduce both to the bulk branch.
  unfold surfaceCellPauli
  simp only [show 2 * m + 1 - 1 = 2 * m from by omega,
    show 2 * m + 3 - 1 = 2 * m + 2 from by omega,
    if_pos hKbulk, if_pos hkbulk]
  -- The two bulk branches: `inBulkBand` membership and `bulkKind` must correspond.
  -- bulkKind: parity of (r-1)+(c-1) = r+c-2 equals parity of r+c.
  have hKind : bulkKind (2 * m + 1) ((r - 1) * (2 * m) + (c - 1)) = bulkKind (2 * m + 3) k := by
    unfold bulkKind
    simp only [cellR, cellC, show 2 * m + 1 - 1 = 2 * m from by omega,
      show 2 * m + 3 - 1 = 2 * m + 2 from by omega, hKR, hKC, ← hr, ← hc]
    have hpar : (r - 1 + (c - 1)) % 2 = (r + c) % 2 := by omega
    rw [hpar]
  -- inBulkBand: band membership corresponds coordinate-by-coordinate.
  have hBand : inBulkBand (2 * m + 1) ((r - 1) * (2 * m) + (c - 1))
      ((row - 1) * (2 * m + 1) + (col - 1)) = inBulkBand (2 * m + 3) k q := by
    unfold inBulkBand
    simp only [cellRow, cellCol, cellR, cellC,
      show 2 * m + 1 - 1 = 2 * m from by omega,
      show 2 * m + 3 - 1 = 2 * m + 2 from by omega,
      hKR, hKC, hQR, hQC, ← hr, ← hc, ← hrowdef, ← hcoldef]
    -- Band membership corresponds coordinate-by-coordinate (all coords ≥ 1).
    simp only [show (row - 1 = r - 1) = (row = r) from by simp only [eq_iff_iff]; omega,
        show (row - 1 = r - 1 + 1) = (row = r + 1) from by simp only [eq_iff_iff]; omega,
        show (col - 1 = c - 1) = (col = c) from by simp only [eq_iff_iff]; omega,
        show (col - 1 = c - 1 + 1) = (col = c + 1) from by simp only [eq_iff_iff]; omega,
        decide_eq_true hKbulk, decide_eq_true hkbulk]
  rw [hKind, hBand]

/-! ## Top promoted-boundary self-similarity -/

/-- Top single-step self-similarity (Nat-level).  Under the top-cell and inside
contexts at distance `d = 2m+3`, the inner top-X boundary entry at the mapped
inner index equals the outer bulk band/kind entry. -/
theorem topSelfSimNat (m k q : Nat)
    (hT : isTopCell (2*m+3) k = true)
    (hIn : isInside (2*m+3) q = true) :
    surfaceCellPauli (2*m+1) (innerTopK (2*m+3) k) (innerQval (2*m+3) q)
      = surfaceCellPauli (2*m+3) k q := by
  simp only [isTopCell, isInside, cellInnerHalf, cellR, cellC, cellRow, cellCol,
    Bool.and_eq_true, decide_eq_true_eq] at hT hIn
  obtain ⟨hr0, hcEq, htb⟩ := hT
  obtain ⟨hrow1, hrow2, hcol1, hcol2⟩ := hIn
  simp only [show 2 * m + 3 - 1 = 2 * m + 2 from by omega,
      show 2 * m + 3 - 2 = 2 * m + 1 from by omega,
      show 2 * m + 1 - 1 = 2 * m from by omega] at hr0 hcEq htb hrow2 hcol2
  set c := k % (2 * m + 2) with hc
  set row := q / (2 * m + 3) with hrowdef
  set col := q % (2 * m + 3) with hcoldef
  set tb := (c - 1) / 2 with htbdef
  -- r = 0 ⇒ k = c < 2m+2.
  have hklt : k < 2 * m + 2 := by
    have := (Nat.div_eq_zero_iff (a := k) (b := 2 * m + 2)).mp hr0
    omega
  have hkc : k = c := by
    rw [hc, Nat.mod_eq_of_lt hklt]
  -- inner top-X half = m, and tb < m.
  have htbm : tb < m := by rw [Nat.mul_div_cancel_left m (by omega : 0 < 2)] at htb; exact htb
  -- Inner index and inner qubit.
  have hK : innerTopK (2 * m + 3) k = 2 * m * (2 * m) + tb := by
    unfold innerTopK
    simp only [cellC, show 2 * m + 3 - 2 - 1 = 2 * m from by omega,
      show 2 * m + 3 - 1 = 2 * m + 2 from by omega, ← hc, ← htbdef]
  have hQ : innerQval (2 * m + 3) q = (row - 1) * (2 * m + 1) + (col - 1) := by
    unfold innerQval
    simp only [cellRow, cellCol, show 2 * m + 3 - 2 = 2 * m + 1 from by omega,
      ← hrowdef, ← hcoldef]
  rw [hK, hQ]
  -- Inner qubit coordinates.
  have hQR : ((row - 1) * (2 * m + 1) + (col - 1)) / (2 * m + 1) = row - 1 := by
    rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), Nat.add_zero]
  have hQC : ((row - 1) * (2 * m + 1) + (col - 1)) % (2 * m + 1) = col - 1 := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  -- Inner is NOT bulk (index ≥ bulkCount), takes top-X branch (b' = tb < m).
  have hnotbulk : ¬ 2 * m * (2 * m) + tb < 2 * m * (2 * m) := by omega
  have hbprime : 2 * m * (2 * m) + tb - 2 * m * (2 * m) = tb := by omega
  -- Outer IS bulk (r = 0 ⇒ k < (d-1)^2).
  have hkbulk : k < (2 * m + 2) * (2 * m + 2) := by
    have : k < 2 * m + 2 := hklt
    have h2 : 2 * m + 2 ≤ (2 * m + 2) * (2 * m + 2) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  -- Reduce the inner side to its top-X branch and the outer to its bulk branch.
  conv_lhs => rw [surfaceCellPauli]
  conv_rhs => rw [surfaceCellPauli]
  simp only [cellRow, cellCol,
    show 2 * m + 1 - 1 = 2 * m from by omega,
    show 2 * m + 3 - 1 = 2 * m + 2 from by omega,
    hQR, hQC, ← hrowdef, ← hcoldef,
    if_neg hnotbulk, if_pos hkbulk, hbprime]
  rw [if_pos (show tb < 2 * m / 2 from htb)]
  -- Inner top-X first conjunct (k' < d'^2 - 1) is true.
  have hk'lt : 2 * m * (2 * m) + tb < (2 * m + 1) * (2 * m + 1) - 1 := by
    have h2 : (2 * m + 1) * (2 * m + 1) = 2 * m * (2 * m) + 2 * m + (2 * m + 1) := by
      rw [Nat.add_one_mul, Nat.mul_add_one]
    omega
  -- bulkKind at (r=0, c=2tb+1 odd) = X.
  have hKind : bulkKind (2 * m + 3) k = Pauli.X := by
    unfold bulkKind
    simp only [cellR, cellC, show 2 * m + 3 - 1 = 2 * m + 2 from by omega, hr0, ← hc, hcEq]
    rw [if_neg (by omega)]
  -- inBulkBand at the top edge.
  have hBand : inBulkBand (2 * m + 3) k q =
      ((decide (row = 1)) && (decide (col = 2 * tb + 1) || decide (col = 2 * tb + 2))) := by
    unfold inBulkBand
    simp only [cellRow, cellCol, cellR, cellC, show 2 * m + 3 - 1 = 2 * m + 2 from by omega,
      hr0, ← hc, hcEq, ← hrowdef, ← hcoldef]
    simp only [decide_eq_true hkbulk, Bool.and_true,
        show (row = 0) = False from eq_false (by omega),
        decide_false, Bool.false_or]
  rw [hKind, hBand]
  simp only [show (row - 1 = 0) = (row = 1) from by simp only [eq_iff_iff]; omega,
      show (col - 1 = 2 * tb) = (col = 2 * tb + 1) from by simp only [eq_iff_iff]; omega,
      show (col - 1 = 2 * tb + 1) = (col = 2 * tb + 2) from by simp only [eq_iff_iff]; omega,
      decide_eq_true hk'lt, Bool.true_and]

/-! ## Interior, not-inside: the outer bulk band is empty -/

/-- Under interior-cell `∧ ¬inside`, the outer bulk band membership is `false`:
an interior plaquette's band lies entirely inside the interior block, so a qubit
outside the block cannot be in-band. -/
theorem interiorNotInsideNat (m k q : Nat)
    (hI : isInteriorCell (2*m+3) k = true)
    (hIn : isInside (2*m+3) q = false) :
    inBulkBand (2*m+3) k q = false := by
  simp only [isInteriorCell, cellLastCell, cellR, cellC,
    Bool.and_eq_true, decide_eq_true_eq] at hI
  obtain ⟨hr1, hr2, hc1, hc2⟩ := hI
  simp only [show 2 * m + 3 - 1 = 2 * m + 2 from by omega,
      show 2 * m + 2 - 1 = 2 * m + 1 from by omega] at hr1 hr2 hc1 hc2
  -- `¬isInside`: not all of 1 ≤ row < 2m+2, 1 ≤ col < 2m+2.
  simp only [isInside, cellRow, cellCol, show 2 * m + 3 - 1 = 2 * m + 2 from by omega,
    Bool.and_eq_false_iff, decide_eq_false_iff_not] at hIn
  -- Reduce `inBulkBand` to a Boolean over coordinates and discharge by `omega`.
  unfold inBulkBand
  simp only [cellRow, cellCol, cellR, cellC, show 2 * m + 3 - 1 = 2 * m + 2 from by omega,
    Bool.and_eq_false_iff, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  -- A row/col mismatch or `k` out of bulk count follows from `¬isInside`.
  omega

/-! ## Right promoted-boundary self-similarity -/

/-- Right single-step self-similarity (Nat-level).  Under the right-cell and inside
contexts at distance `d = 2m+3`, the inner right-Z boundary entry at the mapped
inner index equals the outer bulk band/kind entry. -/
theorem rightSelfSimNat (m k q : Nat)
    (hT : isTopCell (2*m+3) k = false)
    (hR : isRightCell (2*m+3) k = true)
    (hIn : isInside (2*m+3) q = true) :
    surfaceCellPauli (2*m+1) (innerRightK (2*m+3) k) (innerQval (2*m+3) q)
      = surfaceCellPauli (2*m+3) k q := by
  simp only [isRightCell, isInside, cellLastCell, cellInnerHalf, cellR, cellC, cellRow, cellCol,
    Bool.and_eq_true, decide_eq_true_eq] at hR hIn
  obtain ⟨hcEq, hrEq, hrb⟩ := hR
  obtain ⟨hrow1, hrow2, hcol1, hcol2⟩ := hIn
  simp only [show 2 * m + 3 - 1 = 2 * m + 2 from by omega,
      show 2 * m + 3 - 2 = 2 * m + 1 from by omega,
      show 2 * m + 1 - 1 = 2 * m from by omega] at hcEq hrEq hrb hrow2 hcol2
  set r := k / (2 * m + 2) with hr
  set c := k % (2 * m + 2) with hc
  set row := q / (2 * m + 3) with hrowdef
  set col := q % (2 * m + 3) with hcoldef
  set rb := (r - 1) / 2 with hrbdef
  -- Normalize `c = 2m+1` and the half bound `rb < m`.
  have hcEq' : c = 2 * m + 1 := by omega
  have hrbm : rb < m := by rw [Nat.mul_div_cancel_left m (by omega : 0 < 2)] at hrb; exact hrb
  -- Inner index and inner qubit.
  have hK : innerRightK (2 * m + 3) k = 2 * m * (2 * m) + (m + rb) := by
    unfold innerRightK
    simp only [cellR, cellInnerHalf,
      show 2 * m + 3 - 2 = 2 * m + 1 from by omega,
      show 2 * m + 1 - 1 = 2 * m from by omega,
      show 2 * m + 3 - 1 = 2 * m + 2 from by omega, ← hr, ← hrbdef,
      Nat.mul_div_cancel_left m (by omega : 0 < 2)]
  have hQ : innerQval (2 * m + 3) q = (row - 1) * (2 * m + 1) + (col - 1) := by
    unfold innerQval
    simp only [cellRow, cellCol, show 2 * m + 3 - 2 = 2 * m + 1 from by omega,
      ← hrowdef, ← hcoldef]
  rw [hK, hQ]
  -- Inner qubit coordinates.
  have hQR : ((row - 1) * (2 * m + 1) + (col - 1)) / (2 * m + 1) = row - 1 := by
    rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), Nat.add_zero]
  have hQC : ((row - 1) * (2 * m + 1) + (col - 1)) % (2 * m + 1) = col - 1 := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  -- Inner is NOT bulk, NOT top-X (b' = m+rb ≥ m), takes right-Z branch (b' = m+rb < 2m).
  have hnotbulk : ¬ 2 * m * (2 * m) + (m + rb) < 2 * m * (2 * m) := by omega
  have hbprime : 2 * m * (2 * m) + (m + rb) - 2 * m * (2 * m) = m + rb := by omega
  have hnottop : ¬ m + rb < (2 * m) / 2 := by
    rw [Nat.mul_div_cancel_left m (by omega : 0 < 2)]; omega
  have hright : m + rb < 2 * ((2 * m) / 2) := by
    rw [Nat.mul_div_cancel_left m (by omega : 0 < 2)]; omega
  have hbbR : m + rb - (2 * m) / 2 = rb := by
    rw [Nat.mul_div_cancel_left m (by omega : 0 < 2)]; omega
  -- Outer IS bulk (r = 2rb+1 ≤ 2m-1, c = 2m+1 ⇒ k < (2m+2)^2).
  have hkbulk : k < (2 * m + 2) * (2 * m + 2) := by
    have hk : k = r * (2 * m + 2) + c := by
      rw [hr, hc, Nat.mul_comm]; exact (Nat.div_add_mod k (2 * m + 2)).symm
    rw [hk]; exact cellLinIndexLt (by omega) (by omega)
  -- Reduce inner side to its right-Z branch and the outer to its bulk branch.
  conv_lhs => rw [surfaceCellPauli]
  conv_rhs => rw [surfaceCellPauli]
  simp only [cellRow, cellCol,
    show 2 * m + 1 - 1 = 2 * m from by omega,
    show 2 * m + 3 - 1 = 2 * m + 2 from by omega,
    hQR, hQC, ← hrowdef, ← hcoldef,
    if_neg hnotbulk, if_pos hkbulk, hbprime, if_neg hnottop, if_pos hright, hbbR]
  -- bulkKind at (r = 2rb+1 odd, c = 2m+1 odd) ⇒ (r+c) even ⇒ Z.
  have hKind : bulkKind (2 * m + 3) k = Pauli.Z := by
    unfold bulkKind
    simp only [cellR, cellC, show 2 * m + 3 - 1 = 2 * m + 2 from by omega, ← hr, ← hc, hrEq, hcEq']
    rw [if_pos (by omega)]
  -- inBulkBand at the right edge: col = c = 2m+1 (col = 2m+2 impossible), row ∈ {r, r+1}.
  have hBand : inBulkBand (2 * m + 3) k q =
      ((decide (row = 2 * rb + 1) || decide (row = 2 * rb + 2)) && decide (col = 2 * m + 1)) := by
    unfold inBulkBand
    simp only [cellRow, cellCol, cellR, cellC, show 2 * m + 3 - 1 = 2 * m + 2 from by omega,
      ← hr, ← hc, hrEq, hcEq', ← hrowdef, ← hcoldef]
    simp only [decide_eq_true hkbulk, Bool.and_true,
        show (col = 2 * m + 1 + 1) = False from eq_false (by omega),
        decide_false, Bool.or_false]
  rw [hKind, hBand]
  simp only [show (col - 1 = 2 * m) = (col = 2 * m + 1) from by simp only [eq_iff_iff]; omega,
      show (row - 1 = 2 * rb) = (row = 2 * rb + 1) from by simp only [eq_iff_iff]; omega,
      show (row - 1 = 2 * rb + 1) = (row = 2 * rb + 2) from by simp only [eq_iff_iff]; omega,
      Bool.and_comm]

/-! ## Left promoted-boundary self-similarity -/

/-- Left single-step self-similarity (Nat-level).  Under the left-cell and inside
contexts at distance `d = 2m+3`, the inner left-Z boundary entry at the mapped
inner index equals the outer bulk band/kind entry. -/
theorem leftSelfSimNat (m k q : Nat)
    (hT : isTopCell (2*m+3) k = false)
    (hR : isRightCell (2*m+3) k = false)
    (hL : isLeftCell (2*m+3) k = true)
    (hIn : isInside (2*m+3) q = true) :
    surfaceCellPauli (2*m+1) (innerLeftK (2*m+3) k) (innerQval (2*m+3) q)
      = surfaceCellPauli (2*m+3) k q := by
  simp only [isLeftCell, isInside, cellInnerHalf, cellR, cellC, cellRow, cellCol,
    Bool.and_eq_true, decide_eq_true_eq] at hL hIn
  obtain ⟨hcEq, hrEq, hlb⟩ := hL
  obtain ⟨hrow1, hrow2, hcol1, hcol2⟩ := hIn
  simp only [show 2 * m + 3 - 1 = 2 * m + 2 from by omega,
      show 2 * m + 3 - 2 = 2 * m + 1 from by omega,
      show 2 * m + 1 - 1 = 2 * m from by omega] at hcEq hrEq hlb hrow2 hcol2
  set r := k / (2 * m + 2) with hr
  set c := k % (2 * m + 2) with hc
  set row := q / (2 * m + 3) with hrowdef
  set col := q % (2 * m + 3) with hcoldef
  set lb := (r - 2) / 2 with hlbdef
  -- lb < m, and k = r*(2m+2) since c = 0.
  have hlbm : lb < m := by rw [Nat.mul_div_cancel_left m (by omega : 0 < 2)] at hlb; exact hlb
  -- Inner index and inner qubit.
  have hK : innerLeftK (2 * m + 3) k = 2 * m * (2 * m) + (2 * m + lb) := by
    unfold innerLeftK
    simp only [cellR, cellInnerHalf,
      show 2 * m + 3 - 2 = 2 * m + 1 from by omega,
      show 2 * m + 1 - 1 = 2 * m from by omega,
      show 2 * m + 3 - 1 = 2 * m + 2 from by omega, ← hr, ← hlbdef,
      Nat.mul_div_cancel_left m (by omega : 0 < 2)]
  have hQ : innerQval (2 * m + 3) q = (row - 1) * (2 * m + 1) + (col - 1) := by
    unfold innerQval
    simp only [cellRow, cellCol, show 2 * m + 3 - 2 = 2 * m + 1 from by omega,
      ← hrowdef, ← hcoldef]
  rw [hK, hQ]
  -- Inner qubit coordinates.
  have hQR : ((row - 1) * (2 * m + 1) + (col - 1)) / (2 * m + 1) = row - 1 := by
    rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), Nat.add_zero]
  have hQC : ((row - 1) * (2 * m + 1) + (col - 1)) % (2 * m + 1) = col - 1 := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  -- Inner is NOT bulk (index ≥ bulkCount), and b' = 2m + lb.
  have hnotbulk : ¬ 2 * m * (2 * m) + (2 * m + lb) < 2 * m * (2 * m) := by omega
  have hbprime : 2 * m * (2 * m) + (2 * m + lb) - 2 * m * (2 * m) = 2 * m + lb := by omega
  -- Inner half = 2m/2 = m.
  have hhalf : 2 * m / 2 = m := Nat.mul_div_cancel_left m (by omega : 0 < 2)
  -- b' = 2m+lb is NOT < half' (=m), NOT < 2*half' (=2m); IS < 3*half' (=3m).
  have hnotTop : ¬ 2 * m + lb < 2 * m / 2 := by rw [hhalf]; omega
  have hnotRight : ¬ 2 * m + lb < 2 * (2 * m / 2) := by rw [hhalf]; omega
  have hLeftPos : 2 * m + lb < 3 * (2 * m / 2) := by rw [hhalf]; omega
  -- bbL' = b' - 2*half' = lb.
  have hbbL : 2 * m + lb - 2 * (2 * m / 2) = lb := by rw [hhalf]; omega
  -- Outer IS bulk: k = r*(2m+2) < (2m+2)^2 since r = 2lb+2 ≤ 2m < 2m+2 and c = 0.
  have hkbulk : k < (2 * m + 2) * (2 * m + 2) := by
    have hk : k = r * (2 * m + 2) + c := by
      rw [hr, hc, Nat.mul_comm]; exact (Nat.div_add_mod k (2 * m + 2)).symm
    rw [hk]; exact cellLinIndexLt (by omega) (by omega)
  -- Reduce inner side to its left-Z branch and the outer to its bulk branch.
  conv_lhs => rw [surfaceCellPauli]
  conv_rhs => rw [surfaceCellPauli]
  simp only [cellRow, cellCol,
    show 2 * m + 1 - 1 = 2 * m from by omega,
    show 2 * m + 3 - 1 = 2 * m + 2 from by omega,
    hQR, hQC, ← hrowdef, ← hcoldef,
    if_neg hnotbulk, if_pos hkbulk, hbprime,
    if_neg hnotTop, if_neg hnotRight, if_pos hLeftPos, hbbL]
  -- bulkKind at (r = 2lb+2 even, c = 0) ⇒ (r+c) even ⇒ Z.
  have hKind : bulkKind (2 * m + 3) k = Pauli.Z := by
    unfold bulkKind
    simp only [cellR, cellC, show 2 * m + 3 - 1 = 2 * m + 2 from by omega, ← hr, ← hc, hcEq, hrEq]
    rw [if_pos (by omega)]
  -- inBulkBand at the left edge: col = 1 (col = 0 impossible), row ∈ {2lb+2, 2lb+3}.
  have hBand : inBulkBand (2 * m + 3) k q =
      ((decide (row = 2 * lb + 2) || decide (row = 2 * lb + 3)) && decide (col = 1)) := by
    unfold inBulkBand
    simp only [cellRow, cellCol, cellR, cellC, show 2 * m + 3 - 1 = 2 * m + 2 from by omega,
      ← hr, ← hc, hcEq, hrEq, ← hrowdef, ← hcoldef]
    simp only [decide_eq_true hkbulk, Bool.and_true,
        show (col = 0) = False from eq_false (by omega),
        decide_false, Bool.false_or]
  rw [hKind, hBand]
  -- coordinate equalities: col' = 0 ⟺ col = 1; row' = 2lb+1 ⟺ row = 2lb+2; row' = 2lb+2 ⟺ row = 2lb+3.
  simp only [show (col - 1 = 0) = (col = 1) from by simp only [eq_iff_iff]; omega,
      show (row - 1 = 2 * lb + 1) = (row = 2 * lb + 2) from by simp only [eq_iff_iff]; omega,
      show (row - 1 = 2 * lb + 2) = (row = 2 * lb + 3) from by simp only [eq_iff_iff]; omega,
      Bool.and_comm]

/-! ## Bottom promoted-boundary self-similarity -/

/-- Bottom single-step self-similarity (Nat-level).  Under the bottom-cell and
inside contexts at distance `d = 2m+3`, the inner bottom-X boundary entry at the
mapped inner index equals the outer bulk band/kind entry. -/
theorem bottomSelfSimNat (m k q : Nat)
    (hT : isTopCell (2*m+3) k = false)
    (hR : isRightCell (2*m+3) k = false)
    (hL : isLeftCell (2*m+3) k = false)
    (hB : isBottomCell (2*m+3) k = true)
    (hIn : isInside (2*m+3) q = true) :
    surfaceCellPauli (2*m+1) (innerBottomK (2*m+3) k) (innerQval (2*m+3) q)
      = surfaceCellPauli (2*m+3) k q := by
  simp only [isBottomCell, isInside, cellLastCell, cellInnerHalf, cellR, cellC, cellRow, cellCol,
    Bool.and_eq_true, decide_eq_true_eq] at hB hIn
  obtain ⟨hrEq, hcEq, hbb⟩ := hB
  obtain ⟨hrow1, hrow2, hcol1, hcol2⟩ := hIn
  simp only [show 2 * m + 3 - 1 = 2 * m + 2 from by omega,
      show 2 * m + 3 - 2 = 2 * m + 1 from by omega,
      show 2 * m + 1 - 1 = 2 * m from by omega] at hrEq hcEq hbb hrow2 hcol2
  set r := k / (2 * m + 2) with hr
  set c := k % (2 * m + 2) with hc
  set row := q / (2 * m + 3) with hrowdef
  set col := q % (2 * m + 3) with hcoldef
  set bb := (c - 2) / 2 with hbbdef
  -- Normalize `r = 2m+1` and the half bound `bb < m`.
  have hrEq' : r = 2 * m + 1 := by omega
  have hbbm : bb < m := by rw [Nat.mul_div_cancel_left m (by omega : 0 < 2)] at hbb; exact hbb
  -- `c = 2*bb + 2`.
  have hcVal : c = 2 * bb + 2 := by omega
  -- `c < 2m+2`.
  have hcLt : c < 2 * m + 2 := Nat.mod_lt _ (by omega)
  -- Inner index and inner qubit.
  have hK : innerBottomK (2 * m + 3) k = 2 * m * (2 * m) + (3 * m + bb) := by
    unfold innerBottomK
    simp only [cellC, cellInnerHalf,
      show 2 * m + 3 - 2 = 2 * m + 1 from by omega,
      show 2 * m + 1 - 1 = 2 * m from by omega,
      show 2 * m + 3 - 1 = 2 * m + 2 from by omega, ← hc, ← hbbdef,
      Nat.mul_div_cancel_left m (by omega : 0 < 2)]
  have hQ : innerQval (2 * m + 3) q = (row - 1) * (2 * m + 1) + (col - 1) := by
    unfold innerQval
    simp only [cellRow, cellCol, show 2 * m + 3 - 2 = 2 * m + 1 from by omega,
      ← hrowdef, ← hcoldef]
  rw [hK, hQ]
  -- Inner qubit coordinates.
  have hQR : ((row - 1) * (2 * m + 1) + (col - 1)) / (2 * m + 1) = row - 1 := by
    rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega), Nat.add_zero]
  have hQC : ((row - 1) * (2 * m + 1) + (col - 1)) % (2 * m + 1) = col - 1 := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  -- Inner is NOT bulk (index ≥ bulkCount).
  have hnotbulk : ¬ 2 * m * (2 * m) + (3 * m + bb) < 2 * m * (2 * m) := by omega
  -- inner b' = 3m + bb.
  have hbprime : 2 * m * (2 * m) + (3 * m + bb) - 2 * m * (2 * m) = 3 * m + bb := by omega
  -- inner half = m.
  have hhalf : (2 * m) / 2 = m := Nat.mul_div_cancel_left m (by omega : 0 < 2)
  -- Outer IS bulk (k = r*(2m+2)+c, r = 2m+1, c < 2m+2 ⇒ k < (2m+2)^2).
  have hkbulk : k < (2 * m + 2) * (2 * m + 2) := by
    have hk : k = r * (2 * m + 2) + c := by
      rw [hr, hc, Nat.mul_comm]; exact (Nat.div_add_mod k (2 * m + 2)).symm
    rw [hk]; exact cellLinIndexLt (by omega) (by omega)
  -- Reduce the inner side to its bottom-X branch and the outer to its bulk branch.
  conv_lhs => rw [surfaceCellPauli]
  conv_rhs => rw [surfaceCellPauli]
  simp only [cellRow, cellCol,
    show 2 * m + 1 - 1 = 2 * m from by omega,
    show 2 * m + 3 - 1 = 2 * m + 2 from by omega,
    hQR, hQC, ← hrowdef, ← hcoldef,
    if_neg hnotbulk, if_pos hkbulk, hbprime, hhalf]
  -- inner b' = 3m+bb: not in top/right/left branches, lands in bottom-X else.
  rw [if_neg (show ¬ 3 * m + bb < m from by omega),
    if_neg (show ¬ 3 * m + bb < 2 * m from by omega),
    if_neg (show ¬ 3 * m + bb < 3 * m from by omega)]
  -- inner bbB = (3m+bb) - 3m = bb.
  simp only [show 3 * m + bb - 3 * m = bb from by omega]
  -- bulkKind at (r=2m+1, c=2bb+2): (r+c) odd ⇒ X.
  have hKind : bulkKind (2 * m + 3) k = Pauli.X := by
    unfold bulkKind
    simp only [cellR, cellC, show 2 * m + 3 - 1 = 2 * m + 2 from by omega, ← hr, ← hc,
      hrEq', hcVal]
    rw [if_neg (by omega)]
  -- inBulkBand at the bottom edge: row = 2m+1 ∧ (col = 2bb+2 ∨ col = 2bb+3).
  have hBand : inBulkBand (2 * m + 3) k q =
      ((decide (row = 2 * m + 1)) &&
        (decide (col = 2 * bb + 2) || decide (col = 2 * bb + 3))) := by
    unfold inBulkBand
    simp only [cellRow, cellCol, cellR, cellC, show 2 * m + 3 - 1 = 2 * m + 2 from by omega,
      ← hr, ← hc, hrEq', hcVal, ← hrowdef, ← hcoldef]
    simp only [decide_eq_true hkbulk, Bool.and_true,
        show (row = 2 * m + 1 + 1) = False from eq_false (by omega),
        show (col = 2 * bb + 2 + 1) = (col = 2 * bb + 3) from rfl,
        decide_false, Bool.or_false]
  rw [hKind, hBand]
  -- coordinate equalities: row' = 2m ⟺ row = 2m+1; col' = 2bb+1 ⟺ col = 2bb+2; col' = 2bb+2 ⟺ col = 2bb+3.
  simp only [show (row - 1 = 2 * m) = (row = 2 * m + 1) from by simp only [eq_iff_iff]; omega,
      show (col - 1 = 2 * bb + 1) = (col = 2 * bb + 2) from by simp only [eq_iff_iff]; omega,
      show (col - 1 = 2 * bb + 2) = (col = 2 * bb + 3) from by simp only [eq_iff_iff]; omega]

end QHL.CodeLang.Surface.Verify
