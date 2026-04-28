import QStab.Invariant

/-! # Register initialization invariant (Lemma 4)

For any fixed budget level t:
  p(σ) = (C < t) ∨ { (C = t) ∧ ∀ (a,b) with (x,y) ≤ (a,b), G[a,b] = 0 }

Unvisited classical registers remain zero.
-/

namespace QStab.Invariants

open QECParams

/-- Key helper: if toLinear of two coords differ, they can't be component-equal. -/
private theorem coord_ne_of_toLinear_lt {P : QECParams}
    {c : Coord P} {a : Fin P.numStab} {b : Fin P.R}
    (h : c.toLinear < (Coord.mk a b).toLinear) :
    ¬(a = c.x ∧ b = c.y) := by
  intro ⟨ha, hb⟩
  simp [Coord.toLinear] at h
  subst ha; subst hb
  omega

/-- Preservation of the register initialization property. -/
theorem registerInit_preservation {P : QECParams} (t : Nat)
    (s s' : State P)
    (h : s.C < t ∨ (s.C = t ∧ ∀ (a : Fin P.numStab) (b : Fin P.R),
           s.coord ≤ Coord.mk a b → s.G a b = false))
    (step : Step P (.active s) (.active s')) :
    s'.C < t ∨ (s'.C = t ∧ ∀ (a : Fin P.numStab) (b : Fin P.R),
           s'.coord ≤ Coord.mk a b → s'.G a b = false) := by
  cases step with
  | type0 s i p' hp hC =>
    left; show s.C - 1 < t
    cases h with | inl h => omega | inr h => omega
  | type1 s i p' hp hC =>
    left; show s.C - 1 < t
    cases h with | inl h => omega | inr h => omega
  | type2 s ev he hC =>
    left; show s.C - 1 < t
    cases h with | inl h => omega | inr h => omega
  | type3 s hC =>
    -- type3 flips G at current position but also decreases C
    left; show s.C - 1 < t
    cases h with | inl h => omega | inr h => omega
  | measure s nc hN =>
    -- Measurement: C unchanged, coord advances, G[old] written
    cases h with
    | inl h => left; rw [measureStep_C]; exact h
    | inr h =>
      obtain ⟨hCt, hG⟩ := h
      right
      constructor
      · rw [measureStep_C]; exact hCt
      · -- Need: ∀ (a,b) ≥ nc, new_G a b = false
        intro a b hab
        have h_coord_lt : s.coord.toLinear < nc.toLinear :=
          QECParams.Coord.next_toLinear_lt hN
        -- hab : nc ≤ (a,b), i.e. nc.toLinear ≤ (Coord.mk a b).toLinear
        -- after measureStep, coord = nc
        have hab' : nc.toLinear ≤ (Coord.mk a b).toLinear := by
          have hc_eq : (measureStep P s nc).coord = nc := measureStep_coord P s nc
          simp only [LE.le] at hab
          rw [hc_eq] at hab
          exact hab
        have h_old_le : s.coord.toLinear ≤ (Coord.mk a b).toLinear := by omega
        have h_old_lt : s.coord.toLinear < (Coord.mk a b).toLinear := by omega
        -- Now unfold to see G field
        unfold measureStep
        simp only []
        split
        · -- Case: a = s.coord.x ∧ b = s.coord.y — contradicts h_old_lt
          rename_i heq
          exact absurd heq (coord_ne_of_toLinear_lt h_old_lt)
        · -- Case: ¬(a = s.coord.x ∧ b = s.coord.y) — falls through to old G
          exact hG a b h_old_le

end QStab.Invariants
