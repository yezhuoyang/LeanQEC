import QStab.Invariant

/-! # G-freshness invariant

Classical register entries at coordinates strictly after the current
coordinate are always false (untouched since initialization).

  gFreshStrict(σ) := ∀ (a,b), (a,b) > coord → G[a,b] = false

This is a step-by-step invariant from σ_init. It captures the fact
that G entries are only modified when they are the current coordinate
(via Type-III errors or measurement), and coordinates only advance.

We also prove that right after a measurement step where C = 0,
the non-strict version holds:
  ∀ (a,b), (a,b) ≥ new_coord → G'[a,b] = false
-/

namespace QStab.Invariants

open QECParams

/-- Helper: if (a,b) is strictly after coord, it cannot equal coord. -/
private theorem coord_ne_of_gt {P : QECParams}
    {c : Coord P} {a : Fin P.numStab} {b : Fin P.R}
    (h : c.toLinear < (Coord.mk a b).toLinear) :
    ¬(a = c.x ∧ b = c.y) := by
  intro ⟨ha, hb⟩
  simp [Coord.toLinear] at h
  subst ha; subst hb
  omega

/-- G-freshness strict invariant:
    G entries strictly after the current coordinate are false. -/
def gFreshStrictInvariant (P : QECParams) : Invariant P where
  holds := fun s => ∀ (a : Fin P.numStab) (b : Fin P.R),
    s.coord.toLinear < (Coord.mk a b).toLinear → s.G a b = false
  holds_init := by
    intro a b _
    simp [State.init]
  preservation := by
    intro s s' h step
    cases step with
    | type0 s i p' hp hC =>
      -- coord and G unchanged
      exact h
    | type1 s i p' hp mf hC =>
      intro a b hab
      have hne : ¬(a = s.coord.x ∧ b = s.coord.y) := coord_ne_of_gt hab
      simp only []
      split
      · exfalso; rename_i hcond
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        -- hcond : (mf = true ∧ a = coord.x) ∧ b = coord.y
        exact hne ⟨hcond.1.2, hcond.2⟩
      · exact h a b hab
    | type2 s ev he mf hC =>
      intro a b hab
      have hne : ¬(a = s.coord.x ∧ b = s.coord.y) := coord_ne_of_gt hab
      simp only []
      split
      · exfalso; rename_i hcond
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        -- hcond : (mf = true ∧ a = coord.x) ∧ b = coord.y
        exact hne ⟨hcond.1.2, hcond.2⟩
      · exact h a b hab
    | type3 s hC =>
      -- G flipped at current coord, but coord unchanged
      -- For (a,b) strictly after coord, G(a,b) = old G(a,b) = false
      intro a b hab
      simp only []
      split
      · exact absurd (by assumption) (coord_ne_of_gt hab)
      · exact h a b hab
    | measure s nc hN =>
      -- coord advances to nc; G written at old coord but not at nc or after
      intro a b hab
      have h_coord_lt : s.coord.toLinear < nc.toLinear :=
        Coord.next_toLinear_lt hN
      -- (a,b) > nc > old_coord, so (a,b) > old_coord
      have hab_old : s.coord.toLinear < (Coord.mk a b).toLinear := by
        show s.coord.toLinear < (Coord.mk a b).toLinear
        have : nc.toLinear < (Coord.mk a b).toLinear := by
          simp only [measureStep_coord] at hab; exact hab
        omega
      -- Unfold measureStep G field
      show (measureStep P s nc).G a b = false
      unfold measureStep; simp only []
      split
      · -- Case (a,b) = old coord: impossible since (a,b) > old coord
        exact absurd (by assumption) (coord_ne_of_gt hab_old)
      · -- Case (a,b) ≠ old coord: G unchanged, use IH
        exact h a b hab_old

/-- After a measurement step where C = 0, G entries at or after the
    new coordinate are false (non-strict freshness).
    This is because the new coordinate hasn't been visited yet. -/
theorem gFresh_after_measure_C_zero {P : QECParams}
    (s : State P) (nc : Coord P)
    (hN : s.coord.next = some nc)
    (hG_strict : ∀ (a : Fin P.numStab) (b : Fin P.R),
      s.coord.toLinear < (Coord.mk a b).toLinear → s.G a b = false) :
    ∀ (a : Fin P.numStab) (b : Fin P.R),
      nc.toLinear ≤ (Coord.mk a b).toLinear →
      (measureStep P s nc).G a b = false := by
  intro a b hab
  have h_coord_lt : s.coord.toLinear < nc.toLinear :=
    Coord.next_toLinear_lt hN
  -- (a,b) ≥ nc > old_coord
  have hab_old : s.coord.toLinear < (Coord.mk a b).toLinear := by omega
  unfold measureStep; simp only []
  split
  · exact absurd (by assumption) (coord_ne_of_gt hab_old)
  · exact hG_strict a b hab_old

end QStab.Invariants
