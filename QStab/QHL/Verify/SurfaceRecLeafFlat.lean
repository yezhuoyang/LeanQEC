import QStab.QHL.Verify.SurfaceSelfSimNat

/-!
# Nat-level global self-similarity: `recLeaf = surfaceCellPauli`

`recLeaf m k q` is the recursion-faithful leaf of stabilizer `k` at qubit `q`
(distance index `m`): interior / promoted-boundary cells delegate one layer down.
`surfaceCellPauli (oddDistance m) k q` is the *flat* (non-recursing) distance-uniform
classifier.

This file proves they are equal for **every** `(m, k, q)` — the genuine global
surface-code self-similarity statement — by structural recursion on `m`, using the
six single-step `Nat`-level self-similarity identities of `SurfaceSelfSimNat.lean`.

This is an ordinary `Nat`/`Pauli` theorem (no object logic); `omega`/`simp`/`Nat`
lemmas are used freely.  It is the linchpin the object-logic flat bridge composes
with the two row characterizations (`recLeaf`-form and `rowSymTreeA`-form).
-/

namespace QHL.CodeLang.Surface.Verify

open QHL.CodeLang
open QHL.CodeLang.Surface

set_option maxRecDepth 65536

/-- An interior-cell qubit that is *not inside* the interior block forces the flat
classifier to `I`: the bulk band is empty (`interiorNotInsideNat`) and an interior
index is a bulk index, so `surfaceCellPauli` takes the `inBulkBand … = false`
branch. -/
private theorem surfaceCellPauli_interior_notInside (m k q : Nat)
    (hI : isInteriorCell (2 * m + 3) k = true)
    (hIn : isInside (2 * m + 3) q = false) :
    surfaceCellPauli (2 * m + 3) k q = Pauli.I := by
  -- interior ⟹ bulk index (`k < (d-1)^2`).
  have hbulk : k < (2 * m + 3 - 1) * (2 * m + 3 - 1) := by
    simp only [isInteriorCell, cellLastCell, cellR, cellC, Bool.and_eq_true,
      decide_eq_true_eq] at hI
    obtain ⟨hr1, hr2, hc1, hc2⟩ := hI
    -- r = k/(d-1) < (d-1)-1, c = k%(d-1) < (d-1)-1 ⟹ k < (d-1)^2.
    have hdm1 : 2 * m + 3 - 1 = 2 * m + 2 := by omega
    rw [hdm1] at hr2 hc2 ⊢
    have hkdiv : k / (2 * m + 2) * (2 * m + 2) + k % (2 * m + 2) = k := by
      rw [Nat.mul_comm]; exact Nat.div_add_mod k (2 * m + 2)
    have hmod : k % (2 * m + 2) < 2 * m + 2 := Nat.mod_lt _ (by omega)
    have hdiv : k / (2 * m + 2) + 1 ≤ 2 * m + 2 := by omega
    -- (div + 1) * (2m+2) ≤ (2m+2) * (2m+2), and div*(2m+2)+mod < (div+1)*(2m+2).
    have hstep : (k / (2 * m + 2) + 1) * (2 * m + 2) ≤ (2 * m + 2) * (2 * m + 2) :=
      Nat.mul_le_mul_right _ hdiv
    have hexpand : (k / (2 * m + 2) + 1) * (2 * m + 2)
        = k / (2 * m + 2) * (2 * m + 2) + (2 * m + 2) := by rw [Nat.succ_mul]
    omega
  have hband : inBulkBand (2 * m + 3) k q = false :=
    interiorNotInsideNat m k q hI hIn
  unfold surfaceCellPauli
  simp only [if_pos hbulk, hband, if_false, Bool.false_eq_true]

/-- **Global self-similarity (Nat-level).**  For every distance index `m`,
stabilizer index `k` and qubit `q`, the recursion-faithful leaf equals the flat
distance-uniform classifier. -/
theorem recLeaf_eq_surfaceCellPauli :
    (m k q : Nat) → recLeaf m k q = surfaceCellPauli (oddDistance m) k q
  | 0, k, q => by simp only [recLeaf]
  | m + 1, k, q => by
      -- d = oddDistance (m+1) = 2(m+1)+3 = 2m+5; inner = oddDistance m = 2m+3.
      have hd : oddDistance (m + 1) = 2 * m + 3 + 2 := by simp only [oddDistance]; omega
      have hinner : oddDistance m = 2 * m + 3 := by simp only [oddDistance]
      -- Use `2 * m + 3` as the SelfSimNat outer-distance parameter (= oddDistance (m+1) - 2 ... wait)
      -- Actually instantiate SelfSimNat at `m+1`: outer = 2*(m+1)+3, inner = 2*(m+1)+1.
      have hd' : oddDistance (m + 1) = 2 * (m + 1) + 3 := by simp only [oddDistance]
      have hinner' : oddDistance m = 2 * (m + 1) + 1 := by simp only [oddDistance]; omega
      set d := oddDistance (m + 1) with hd_def
      simp only [recLeaf, ← hd_def]
      by_cases hbulk : k < (d - 1) * (d - 1)
      · simp only [if_pos hbulk]
        by_cases hint : isInteriorCell d k = true
        · simp only [hint, if_true]
          by_cases hin : isInside d q = true
          · simp only [hin, if_true]
            rw [recLeaf_eq_surfaceCellPauli m (innerInteriorK d k) (innerQval d q), hinner']
            rw [hd'] at hint hin ⊢
            exact interiorSelfSimNat (m + 1) k q hint hin
          · have hinF : isInside d q = false := by simpa using hin
            simp only [hinF, Bool.false_eq_true, if_false]
            rw [hd'] at hint hinF ⊢
            exact (surfaceCellPauli_interior_notInside (m + 1) k q hint hinF).symm
        · have hintF : isInteriorCell d k = false := by simpa using hint
          simp only [hintF, Bool.false_eq_true, if_false]
          by_cases htop : isTopCell d k = true
          · simp only [htop, if_true]
            by_cases hin : isInside d q = true
            · simp only [hin, if_true]
              rw [recLeaf_eq_surfaceCellPauli m (innerTopK d k) (innerQval d q), hinner']
              rw [hd'] at htop hin ⊢
              exact topSelfSimNat (m + 1) k q htop hin
            · have hinF : isInside d q = false := by simpa using hin
              simp only [hinF, Bool.false_eq_true, if_false]
          · have htopF : isTopCell d k = false := by simpa using htop
            simp only [htopF, Bool.false_eq_true, if_false]
            by_cases hright : isRightCell d k = true
            · simp only [hright, if_true]
              by_cases hin : isInside d q = true
              · simp only [hin, if_true]
                rw [recLeaf_eq_surfaceCellPauli m (innerRightK d k) (innerQval d q), hinner']
                rw [hd'] at htopF hright hin ⊢
                exact rightSelfSimNat (m + 1) k q htopF hright hin
              · have hinF : isInside d q = false := by simpa using hin
                simp only [hinF, Bool.false_eq_true, if_false]
            · have hrightF : isRightCell d k = false := by simpa using hright
              simp only [hrightF, Bool.false_eq_true, if_false]
              by_cases hleft : isLeftCell d k = true
              · simp only [hleft, if_true]
                by_cases hin : isInside d q = true
                · simp only [hin, if_true]
                  rw [recLeaf_eq_surfaceCellPauli m (innerLeftK d k) (innerQval d q), hinner']
                  rw [hd'] at htopF hrightF hleft hin ⊢
                  exact leftSelfSimNat (m + 1) k q htopF hrightF hleft hin
                · have hinF : isInside d q = false := by simpa using hin
                  simp only [hinF, Bool.false_eq_true, if_false]
              · have hleftF : isLeftCell d k = false := by simpa using hleft
                simp only [hleftF, Bool.false_eq_true, if_false]
                by_cases hbottom : isBottomCell d k = true
                · simp only [hbottom, if_true]
                  by_cases hin : isInside d q = true
                  · simp only [hin, if_true]
                    rw [recLeaf_eq_surfaceCellPauli m (innerBottomK d k) (innerQval d q), hinner']
                    rw [hd'] at htopF hrightF hleftF hbottom hin ⊢
                    exact bottomSelfSimNat (m + 1) k q htopF hrightF hleftF hbottom hin
                  · have hinF : isInside d q = false := by simpa using hin
                    simp only [hinF, Bool.false_eq_true, if_false]
                · have hbottomF : isBottomCell d k = false := by simpa using hbottom
                  simp only [hbottomF, Bool.false_eq_true, if_false]
      · simp only [if_neg hbulk]

end QHL.CodeLang.Surface.Verify
