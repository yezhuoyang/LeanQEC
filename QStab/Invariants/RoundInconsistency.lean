import QStab.Invariant

/-! # Round inconsistency invariant (Theorem 6)

`RI ≤ 2 * (C_budget - C)` — at most 2 rounds of inconsistency per error.

The tight bound uses ghost variables `C_prev` (C at start of current round)
and `C_prev2` (C at start of previous round). When at least one round is
error-free, the RI bound inherits a slack of 1; with two consecutive
error-free rounds, the slack absorbs the round-end F firing.

**Error-step preservation is proved here.** The measurement-step preservation
remains `sorry` and is the single structural gap for this invariant. The RI
bound has been validated empirically on 111,805 reachable states (see
`notes/section2_invariants_harsh_test.py`) with zero violations.
-/

namespace QStab.Invariants

open QECParams

/-- Coord.next at round end: y increments. -/
private theorem coord_next_roundEnd_y {P : QECParams} {c nc : Coord P}
    (h : c.next = some nc) (hre : c.isRoundEnd) :
    nc.y.val = c.y.val + 1 := by
  unfold Coord.isRoundEnd at hre
  unfold Coord.next at h
  split at h
  · rename_i hx; omega
  · split at h
    · cases h; simp
    · contradiction

/-- Coord.next always preserves or increases y. -/
private theorem coord_next_y_ge {P : QECParams} {c nc : Coord P}
    (h : c.next = some nc) : c.y.val ≤ nc.y.val := by
  unfold Coord.next at h
  split at h
  · cases h; simp
  · split at h
    · cases h; simp
    · contradiction

/-- measureStep RI when not at round end: unchanged. -/
private theorem measureStep_RI_not_roundEnd {P : QECParams}
    (s : State P) (nc : Coord P) (h : ¬s.coord.isRoundEnd) :
    (measureStep P s nc).RI = s.RI := by
  unfold measureStep Coord.isRoundEnd at *
  simp [h]

/-- measureStep RI is bounded by s.RI + 1. -/
private theorem measureStep_RI_le {P : QECParams}
    (s : State P) (nc : Coord P) :
    (measureStep P s nc).RI ≤ s.RI + 1 := by
  unfold measureStep
  simp only []
  split <;> omega

/-- Maximum RI bound: `RI ≤ y` (round index). Fully proved step-by-step. -/
def maxRI_Invariant (P : QECParams) : Invariant P where
  holds := fun s => s.RI ≤ s.coord.y.val
  holds_init := by simp [State.init, Coord.first]
  preservation := by
    intro s s' h step
    cases step with
    | type0 s i p' hp hC => exact h
    | type1 s i p' hp hC => exact h
    | type2 s ev he hC => exact h
    | type3 s hC => exact h
    | measure s nc hN =>
      show (measureStep P s nc).RI ≤ nc.y.val
      by_cases hre : s.coord.isRoundEnd
      · have hny := coord_next_roundEnd_y hN hre
        have hri := measureStep_RI_le s nc
        omega
      · have hny := coord_next_y_ge hN
        rw [measureStep_RI_not_roundEnd s nc hre]
        omega

-- ============================================================
-- Strengthened RI invariant with CCR (Consistent Consecutive Rounds)
-- ============================================================

/-- Strengthened RI invariant with ghost variables `C_prev` (C at start of
    current round) and `C_prev2` (C at start of previous round). Nine
    conjuncts; see inline comments. -/
private def riStrengthened (P : QECParams) (s : State P) : Prop :=
  ∃ C_prev C_prev2 : Nat,
    -- (1) RI bound with 1-offset when current & prev round both clean
    s.RI ≤ 2 * (P.C_budget - C_prev2) - (if C_prev = C_prev2 then 1 else 0)
    -- (2) s.C ≤ C_prev (can only decrease during current round)
    ∧ s.C ≤ C_prev
    -- (3) C_prev ≤ C_prev2
    ∧ C_prev ≤ C_prev2
    -- (4) C_prev2 ≤ P.C_budget
    ∧ C_prev2 ≤ P.C_budget
    -- (5) G strict freshness (entries strictly after coord are false)
    ∧ (∀ (a : Fin P.numStab) (b : Fin P.R),
         s.coord.toLinear < (Coord.mk a b).toLinear → s.G a b = false)
    -- (6) G at current coord is false when current round is clean
    ∧ (s.C = C_prev → s.G s.coord.x s.coord.y = false)
    -- (7) CCR I_syn: when 2 consecutive rounds clean, I_syn matches parity
    ∧ (s.C = C_prev → C_prev = C_prev2 →
         ∀ j : Fin P.numStab,
           s.I_syn j = ErrorVec.parity (P.stabilizers j) s.E_tilde)
    -- (8) CCR F: when 2 consecutive rounds clean, F is all-false
    ∧ (s.C = C_prev → C_prev = C_prev2 →
         ∀ j : Fin P.numStab, s.F j = false)
    -- (9) Ẽ = identity when C = C_budget (no errors ever)
    ∧ (s.C = P.C_budget → s.E_tilde = ErrorVec.identity P.n)

/-- riStrengthened implies `RI ≤ 2*(C_budget - C)`. -/
theorem riStrengthened_ri_bound {P : QECParams} {s : State P}
    (h : riStrengthened P s) : s.RI ≤ 2 * (P.C_budget - s.C) := by
  obtain ⟨C_prev, C_prev2, hRI, hCle, hCp, hCp2, _⟩ := h
  have hsub : 2 * (P.C_budget - C_prev2) -
              (if C_prev = C_prev2 then 1 else 0) ≤
              2 * (P.C_budget - C_prev2) := Nat.sub_le _ _
  calc s.RI ≤ 2 * (P.C_budget - C_prev2) := Nat.le_trans hRI hsub
    _ ≤ 2 * (P.C_budget - s.C) := Nat.mul_le_mul_left 2 (by omega)

/-- riStrengthened holds at init. Witnesses C_prev = C_prev2 = C_budget. -/
private theorem riStrengthened_init (P : QECParams) :
    riStrengthened P (State.init P) := by
  refine ⟨P.C_budget, P.C_budget, ?_, le_refl _, le_refl _, le_refl _,
          ?_, ?_, ?_, ?_, ?_⟩
  · simp [State.init]
  · intro _ b; simp [State.init]
  · intro _; simp [State.init]
  · intro _ _ j
    simp [State.init, ErrorVec.parity_identity]
  · intro _ _ j; simp [State.init]
  · intro _; rfl

-- ============================================================
-- Error-step preservation: all four error types decrement C by 1,
-- making conditional conjuncts vacuous.
-- ============================================================

/-- Shared proof: error steps preserve `riStrengthened` by keeping witnesses
    unchanged and noting that `s'.C = s.C - 1 < C_prev` makes every
    condition `s'.C = C_prev` false. -/
private theorem riStrengthened_error_preserve {P : QECParams}
    {s s' : State P} (h : riStrengthened P s) (hC : 0 < s.C)
    (hRI' : s'.RI = s.RI) (hC' : s'.C = s.C - 1)
    (hCoord' : s'.coord = s.coord)
    (hG_preserve : ∀ (a : Fin P.numStab) (b : Fin P.R),
       s.coord.toLinear < (Coord.mk a b).toLinear → s'.G a b = s.G a b) :
    riStrengthened P s' := by
  obtain ⟨C_prev, C_prev2, hRI, hCle, hCp12, hCp2, hGstrict, _, _, _, _⟩ := h
  refine ⟨C_prev, C_prev2, ?_, ?_, hCp12, hCp2, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) RI bound: s'.RI = s.RI and C_prev2 unchanged
    rw [hRI']; exact hRI
  · -- (2) s'.C ≤ C_prev
    rw [hC']; omega
  · -- (5) G strict freshness: G unchanged on strict-future coords
    intro a b hab
    rw [hCoord'] at hab
    rw [hG_preserve a b hab]
    exact hGstrict a b hab
  · -- (6) G at current coord: vacuous (s.C - 1 ≠ C_prev under chain + hC)
    intro hCeq
    rw [hC'] at hCeq
    exfalso; omega
  · -- (7) CCR I_syn: vacuous (same reason)
    intro hCeq _
    rw [hC'] at hCeq
    exfalso; omega
  · -- (8) CCR F: vacuous
    intro hCeq _
    rw [hC'] at hCeq
    exfalso; omega
  · -- (9) Ẽ = identity when C = C_budget: vacuous
    -- (s.C - 1 = C_budget would need s.C = C_budget + 1 > C_budget, impossible)
    intro hCB
    rw [hC'] at hCB
    exfalso; omega

-- Note: The step-by-step riStrengthened_Invariant was removed because
-- the round-end measurement case could not be proved step-by-step.
-- The RI bound is now proved via the round-inductive approach in
-- RoundInv.lean (zero sorry), which supersedes this file.

end QStab.Invariants
