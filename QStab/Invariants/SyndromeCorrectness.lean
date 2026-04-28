import QStab.Invariants.ConstantErrorFlow
import QStab.Invariants.RegisterInit

/-! # Syndrome correctness invariant (Theorem 4 & Second Syndrome Correctness)

The parameterized version:
  p(σ) = (C < t) ∨ { (C = t) ∧ ∀ s < x, I[T_s] = Parity(T_s, E⃗) }

Note: The non-parameterized version (C = 0 → syndrome correct) cannot be
a standalone `Invariant P` from σ_init because error injections that bring
C from 1 to 0 change Ẽ without updating I_syn. Instead, syndrome correctness
is derived from the two-phase proof using the parameterized version at t = 0
with RegisterInit and ConstantErrorFlow as auxiliary invariants.
-/

namespace QStab.Invariants

open QECParams

/-- Helper: Coord.next produces x+1 in same round or x=0 in next round. -/
private theorem coord_next_x_cases {P : QECParams} {c nc : Coord P}
    (h : c.next = some nc) :
    nc.x.val = c.x.val + 1 ∨ nc.x.val = 0 := by
  unfold Coord.next at h
  split at h
  · cases h; left; simp
  · split at h
    · cases h; right; simp
    · contradiction

/-- xor false b = b for Bool. -/
private theorem xor_false_left (b : Bool) : xor false b = b := by
  cases b <;> rfl

/-- Parameterized syndrome correctness preservation (Second Syndrome Correctness).
    Assumes RegisterInit and ConstantErrorFlow hold at the same budget level t. -/
theorem syndromeCorrectnessParam_preservation {P : QECParams} (t : Nat) (E_const : ErrorVec P.n)
    (s s' : State P)
    (h_syn : s.C < t ∨ (s.C = t ∧ ∀ (j : Fin P.numStab), j < s.coord.x →
               s.I_syn j = ErrorVec.parity (P.stabilizers j) E_const))
    (h_reg : s.C < t ∨ (s.C = t ∧ ∀ (a : Fin P.numStab) (b : Fin P.R),
               s.coord ≤ Coord.mk a b → s.G a b = false))
    (h_eflow : s.C < t ∨ (s.C = t ∧ s.E_tilde = E_const))
    (step : Step P (.active s) (.active s')) :
    s'.C < t ∨ (s'.C = t ∧ ∀ (j : Fin P.numStab), j < s'.coord.x →
      s'.I_syn j = ErrorVec.parity (P.stabilizers j) E_const) := by
  cases step with
  | type0 s i p' hp hC =>
    left; show s.C - 1 < t
    cases h_syn with | inl h => omega | inr h => omega
  | type1 s i p' hp hC =>
    left; show s.C - 1 < t
    cases h_syn with | inl h => omega | inr h => omega
  | type2 s ev he hC =>
    left; show s.C - 1 < t
    cases h_syn with | inl h => omega | inr h => omega
  | type3 s hC =>
    left; show s.C - 1 < t
    cases h_syn with | inl h => omega | inr h => omega
  | measure s nc hN =>
    cases h_syn with
    | inl h => left; rw [measureStep_C]; exact h
    | inr h =>
      obtain ⟨hCt, hSyn⟩ := h
      right
      constructor
      · rw [measureStep_C]; exact hCt
      · intro j hj
        simp only [measureStep_coord] at hj
        -- RegisterInit: G at current coord is zero (Lemma 4)
        have hG_zero : s.G s.coord.x s.coord.y = false := by
          cases h_reg with
          | inl h => omega
          | inr h =>
            exact h.2 s.coord.x s.coord.y (show s.coord.toLinear ≤
              (Coord.mk s.coord.x s.coord.y).toLinear by simp [Coord.toLinear])
        -- ConstantErrorFlow: E_tilde = E_const (Lemma 5)
        have hE_eq : s.E_tilde = E_const := by
          cases h_eflow with
          | inl h => omega
          | inr h => exact h.2
        -- Unfold measureStep to access I_syn field
        unfold measureStep; simp only []
        split
        · -- Case j = s.coord.x: measurement gives correct syndrome
          -- I[T_x]' = xor(G[x,y], Parity(T_x, Ẽ)) = xor(0, Parity(T_x, E_const)) = Parity(T_x, E_const)
          rename_i heq; subst heq
          rw [hG_zero, hE_eq]
          exact xor_false_left _
        · -- Case j ≠ s.coord.x: I_syn unchanged, use induction hypothesis
          rename_i hne
          apply hSyn
          -- Need: j < s.coord.x (from j < nc.x and j ≠ s.coord.x)
          rcases coord_next_x_cases hN with h_nc | h_nc
          · -- nc.x = s.coord.x + 1: j < x+1 ∧ j ≠ x → j < x
            show j.val < s.coord.x.val
            have : j.val ≠ s.coord.x.val := fun h => hne (Fin.ext h)
            omega
          · -- nc.x = 0: j < 0 impossible
            exfalso; omega

/-- Previous-round syndrome correctness preservation.
    Tracks that I_syn entries for stabilizers j ≥ coord.x are correct when y > 0.
    At round boundaries (x wraps to 0), this captures all stabilizers from the
    previous round. Combined with the main syndrome correctness (j < coord.x),
    this covers all stabilizers — including the last one at done.

    The key insight: when coord wraps from (numStab-1, y) to (0, y+1),
    the main syndrome correctness becomes vacuous (j < 0). But the previous-round
    invariant captures that ALL I_syn entries are correct (set during round y).
    As measurements in round y+1 progress (coord.x increases), I_syn entries
    for j < coord.x are re-established by the main invariant, while entries
    for j ≥ coord.x remain correct from the previous round. -/
theorem prevRoundSyndromeParam_preservation {P : QECParams} (t : Nat) (E_const : ErrorVec P.n)
    (s s' : State P)
    (h_prev : s.C < t ∨ (s.C = t ∧ (0 < s.coord.y.val →
      ∀ (j : Fin P.numStab), s.coord.x ≤ j →
        s.I_syn j = ErrorVec.parity (P.stabilizers j) E_const)))
    (h_syn : s.C < t ∨ (s.C = t ∧ ∀ (j : Fin P.numStab), j < s.coord.x →
               s.I_syn j = ErrorVec.parity (P.stabilizers j) E_const))
    (h_reg : s.C < t ∨ (s.C = t ∧ ∀ (a : Fin P.numStab) (b : Fin P.R),
               s.coord ≤ Coord.mk a b → s.G a b = false))
    (h_eflow : s.C < t ∨ (s.C = t ∧ s.E_tilde = E_const))
    (step : Step P (.active s) (.active s')) :
    s'.C < t ∨ (s'.C = t ∧ (0 < s'.coord.y.val →
      ∀ (j : Fin P.numStab), s'.coord.x ≤ j →
        s'.I_syn j = ErrorVec.parity (P.stabilizers j) E_const)) := by
  cases step with
  | type0 s i p' hp hC =>
    left; show s.C - 1 < t
    cases h_prev with | inl h => omega | inr h => omega
  | type1 s i p' hp hC =>
    left; show s.C - 1 < t
    cases h_prev with | inl h => omega | inr h => omega
  | type2 s ev he hC =>
    left; show s.C - 1 < t
    cases h_prev with | inl h => omega | inr h => omega
  | type3 s hC =>
    left; show s.C - 1 < t
    cases h_prev with | inl h => omega | inr h => omega
  | measure s nc hN =>
    cases h_prev with
    | inl h => left; rw [measureStep_C]; exact h
    | inr h =>
      obtain ⟨hCt, hPrev⟩ := h
      right
      constructor
      · rw [measureStep_C]; exact hCt
      · intro hy_pos j hj
        simp only [measureStep_coord] at hj hy_pos
        -- RegisterInit: G at current coord is zero
        have hG_zero : s.G s.coord.x s.coord.y = false := by
          cases h_reg with
          | inl h => omega
          | inr h =>
            exact h.2 s.coord.x s.coord.y (show s.coord.toLinear ≤
              (Coord.mk s.coord.x s.coord.y).toLinear by simp [Coord.toLinear])
        -- ConstantErrorFlow: E_tilde = E_const
        have hE_eq : s.E_tilde = E_const := by
          cases h_eflow with
          | inl h => omega
          | inr h => exact h.2
        -- Case analysis on whether nc.x = 0 (round boundary) or nc.x = x+1 (same round)
        rcases coord_next_x_cases hN with h_nc | h_nc
        · -- Same round: nc.x = s.coord.x + 1
          -- j ≥ nc.x = s.coord.x + 1, so j > s.coord.x, so j ≠ s.coord.x
          have hj_gt : s.coord.x.val < j.val := by omega
          have hj_ne : j ≠ s.coord.x := by
            intro heq; subst heq; omega
          -- I_syn[j] unchanged by measurement (j ≠ coord.x)
          rw [measureStep_I_syn_ne s nc j hj_ne]
          -- Use previous-round hypothesis (j ≥ s.coord.x)
          have hj_ge : s.coord.x ≤ j := by
            show s.coord.x.val ≤ j.val; omega
          -- y didn't change (same round), so coord.y preserved
          have hy_same : nc.y = s.coord.y := by
            unfold Coord.next at hN
            split at hN
            · cases hN; rfl
            · split at hN
              · cases hN; simp at h_nc
              · contradiction
          have hy_old : 0 < s.coord.y.val := by rw [← hy_same]; exact hy_pos
          exact hPrev hy_old j hj_ge
        · -- Round boundary: nc.x = 0, so nc.y = s.coord.y + 1
          -- j ≥ 0, so we need all I_syn entries correct
          -- measureStep updates I_syn[s.coord.x], preserves others
          by_cases hj_eq : j = s.coord.x
          · -- j = s.coord.x: just measured, correct
            subst hj_eq
            rw [measureStep_I_syn_eq]
            rw [hG_zero, hE_eq]
            exact xor_false_left _
          · -- j ≠ s.coord.x: I_syn[j] unchanged
            rw [measureStep_I_syn_ne s nc j hj_eq]
            -- j ≠ s.coord.x and s.coord.x = numStab-1 (since nc.x = 0 means round end)
            -- so j < s.coord.x (since s.coord.x = numStab-1 and j : Fin numStab, j ≠ numStab-1)
            -- Use main syndrome correctness (j < coord.x)
            have h_round_end : s.coord.x.val = P.numStab - 1 := by
              unfold Coord.next at hN
              split at hN
              · cases hN; simp at h_nc
              · split at hN
                · cases hN; simp at h_nc
                  -- nc.x = 0 and nc.y = s.coord.y + 1
                  -- This means s.coord.x + 1 ≥ P.numStab (first branch failed)
                  rename_i hx _
                  omega
                · contradiction
            have hj_lt : j < s.coord.x := by
              show j.val < s.coord.x.val
              have := j.isLt
              have : j.val ≠ s.coord.x.val := fun h => hj_eq (Fin.ext h)
              omega
            cases h_syn with
            | inl h => omega
            | inr h => exact h.2 j hj_lt

end QStab.Invariants
