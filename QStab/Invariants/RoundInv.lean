import QStab.Invariant
import QStab.MultiStep
import QStab.Invariants.SyndromeCorrectness
import QStab.Invariants.RegisterInit
import QStab.Invariants.ConstantErrorFlow
import QStab.Invariants.GFresh

/-! # Round-boundary invariant for the RI bound

This file proves `s.RI ≤ 2·(C_budget − s.C)` as a **round invariant** —
a property holding at every state where `coord.x = 0` (round boundary).

The step-by-step formulation fails because at a round-end measurement,
RI can increment by 1 from a tight state, momentarily violating the
bound. At the NEXT round boundary, however, the bound is re-established:
either errors in the round made room (+2 slack per error), or the
2-clean property guarantees F=0 at round-end (so RI doesn't increment).

The invariant uses a **tight conditional**: when the RI bound is
exactly tight (`s.RI = 2·(C_budget − s.C)`), all G entries at/after
coord are false AND all I_syn entries match parity of Ẽ:

    s.RI = 2·(C_budget − s.C)  →  G-fresh ∧ I_syn correct

This is verified on 100k+ simulation traces with zero violations.
The key insight is that tight ⟹ G-fresh ∧ I_syn correct is ALWAYS
true, whereas the previous formulation using a ghost C_prev was
wrong at non-tight boundaries.

When a round transits cleanly (`s'.C = s.C`) from a tight state, the
2-clean property guarantees F=0 at round-end. This is formalized via
two new parameterized invariants `fullSynParam` and `fZero_param`
below, whose preservation chains through the round's MultiStep. -/

namespace QStab.Invariants

open QECParams

-- ============================================================
-- Section 1: Local helpers
-- ============================================================

private theorem coord_ne_of_toLinear_lt' {P : QECParams}
    {c : Coord P} {a : Fin P.numStab} {b : Fin P.R}
    (h : c.toLinear < (Coord.mk a b).toLinear) :
    ¬(a = c.x ∧ b = c.y) := by
  intro ⟨ha, hb⟩
  simp [Coord.toLinear] at h
  subst ha; subst hb
  omega

private theorem xor_false_left_r (b : Bool) : xor false b = b := by
  cases b <;> rfl

private theorem coord_next_x_cases_r {P : QECParams} {c nc : Coord P}
    (h : c.next = some nc) :
    nc.x.val = c.x.val + 1 ∨ nc.x.val = 0 := by
  unfold Coord.next at h
  split at h
  · cases h; left; simp
  · split at h
    · cases h; right; simp
    · contradiction

private theorem measureStep_RI_not_roundEnd' {P : QECParams}
    (s : State P) (nc : Coord P) (h : ¬s.coord.isRoundEnd) :
    (measureStep P s nc).RI = s.RI := by
  unfold measureStep Coord.isRoundEnd at *
  simp [h]

private theorem measureStep_RI_le' {P : QECParams}
    (s : State P) (nc : Coord P) :
    (measureStep P s nc).RI ≤ s.RI + 1 := by
  unfold measureStep
  simp only []
  split <;> omega

private theorem coord_next_y_ge' {P : QECParams} {c nc : Coord P}
    (h : c.next = some nc) : c.y.val ≤ nc.y.val := by
  unfold Coord.next at h
  split at h
  · cases h; simp
  · split at h
    · cases h; simp
    · contradiction

private theorem coord_next_roundEnd_y' {P : QECParams} {c nc : Coord P}
    (h : c.next = some nc) (hre : c.isRoundEnd) :
    nc.y.val = c.y.val + 1 := by
  unfold Coord.isRoundEnd at hre
  unfold Coord.next at h
  split at h
  · rename_i hx; omega
  · split at h
    · cases h; simp
    · contradiction

private theorem coord_next_y_le_succ' {P : QECParams} {c nc : Coord P}
    (h : c.next = some nc) : nc.y.val ≤ c.y.val + 1 := by
  unfold Coord.next at h
  split at h
  · cases h; simp
  · split at h
    · cases h; simp
    · contradiction

private theorem coord_next_y_inc_x_zero' {P : QECParams} {c nc : Coord P}
    (h : c.next = some nc) (hy : c.y.val < nc.y.val) : nc.x.val = 0 := by
  unfold Coord.next at h
  split at h
  · cases h; simp at hy
  · split at h
    · cases h; simp
    · contradiction

-- ============================================================
-- Section 2: Parameterized "full syndrome correctness" invariant
-- "∀ j, I_syn[j] = parity(T_j, E_const)" at level t.
-- Stronger than SyndromeCorrectness+PrevRound: no y-restriction.
-- ============================================================

theorem fullSynParam_preservation {P : QECParams} (t : Nat) (E_const : ErrorVec P.n)
    (s s' : State P)
    (h_full : s.C < t ∨ (s.C = t ∧ ∀ j : Fin P.numStab,
               s.I_syn j = ErrorVec.parity (P.stabilizers j) E_const))
    (h_reg : s.C < t ∨ (s.C = t ∧ ∀ (a : Fin P.numStab) (b : Fin P.R),
               s.coord ≤ Coord.mk a b → s.G a b = false))
    (h_eflow : s.C < t ∨ (s.C = t ∧ s.E_tilde = E_const))
    (step : Step P (.active s) (.active s')) :
    s'.C < t ∨ (s'.C = t ∧ ∀ j : Fin P.numStab,
      s'.I_syn j = ErrorVec.parity (P.stabilizers j) E_const) := by
  cases step with
  | type0 s i p' hp hC =>
    left; show s.C - 1 < t
    cases h_full with | inl h => omega | inr h => omega
  | type1 s i p' hp _mf hC =>
    left; show s.C - 1 < t
    cases h_full with | inl h => omega | inr h => omega
  | type2 s ev he _mf hC =>
    left; show s.C - 1 < t
    cases h_full with | inl h => omega | inr h => omega
  | type3 s hC =>
    left; show s.C - 1 < t
    cases h_full with | inl h => omega | inr h => omega
  | measure s nc hN =>
    cases h_full with
    | inl h => left; rw [measureStep_C]; exact h
    | inr h =>
      obtain ⟨hCt, hSyn⟩ := h
      right
      refine ⟨by rw [measureStep_C]; exact hCt, ?_⟩
      intro j
      have hG_zero : s.G s.coord.x s.coord.y = false := by
        cases h_reg with
        | inl h => omega
        | inr h =>
          exact h.2 s.coord.x s.coord.y (show s.coord.toLinear ≤
            (Coord.mk s.coord.x s.coord.y).toLinear by simp [Coord.toLinear])
      have hE_eq : s.E_tilde = E_const := by
        cases h_eflow with
        | inl h => omega
        | inr h => exact h.2
      by_cases hj : j = s.coord.x
      · subst hj
        rw [measureStep_I_syn_eq, hG_zero, hE_eq]
        exact xor_false_left_r _
      · rw [measureStep_I_syn_ne s nc j hj]
        exact hSyn j

-- ============================================================
-- Section 3: Parameterized "F zero" invariant
-- "F[j < coord.x] = false" at level t, i.e., F entries already
-- measured in the current round are all zero.
-- ============================================================

theorem fZero_param_preservation {P : QECParams} (t : Nat) (E_const : ErrorVec P.n)
    (s s' : State P)
    (h_fZero : s.C < t ∨ (s.C = t ∧ ∀ j : Fin P.numStab,
                j.val < s.coord.x.val → s.F j = false))
    (h_full : s.C < t ∨ (s.C = t ∧ ∀ j : Fin P.numStab,
               s.I_syn j = ErrorVec.parity (P.stabilizers j) E_const))
    (h_reg : s.C < t ∨ (s.C = t ∧ ∀ (a : Fin P.numStab) (b : Fin P.R),
               s.coord ≤ Coord.mk a b → s.G a b = false))
    (h_eflow : s.C < t ∨ (s.C = t ∧ s.E_tilde = E_const))
    (step : Step P (.active s) (.active s')) :
    s'.C < t ∨ (s'.C = t ∧ ∀ j : Fin P.numStab,
      j.val < s'.coord.x.val → s'.F j = false) := by
  cases step with
  | type0 s i p' hp hC =>
    left; show s.C - 1 < t
    cases h_fZero with | inl h => omega | inr h => omega
  | type1 s i p' hp _mf hC =>
    left; show s.C - 1 < t
    cases h_fZero with | inl h => omega | inr h => omega
  | type2 s ev he _mf hC =>
    left; show s.C - 1 < t
    cases h_fZero with | inl h => omega | inr h => omega
  | type3 s hC =>
    left; show s.C - 1 < t
    cases h_fZero with | inl h => omega | inr h => omega
  | measure s nc hN =>
    cases h_fZero with
    | inl h => left; rw [measureStep_C]; exact h
    | inr h =>
      obtain ⟨hCt, hF⟩ := h
      right
      refine ⟨by rw [measureStep_C]; exact hCt, ?_⟩
      intro j hj_lt
      simp only [measureStep_coord] at hj_lt
      have hG_zero : s.G s.coord.x s.coord.y = false := by
        cases h_reg with
        | inl h => omega
        | inr h =>
          exact h.2 s.coord.x s.coord.y (show s.coord.toLinear ≤
            (Coord.mk s.coord.x s.coord.y).toLinear by simp [Coord.toLinear])
      have hE_eq : s.E_tilde = E_const := by
        cases h_eflow with
        | inl h => omega
        | inr h => exact h.2
      have hI_correct : s.I_syn s.coord.x =
          ErrorVec.parity (P.stabilizers s.coord.x) E_const := by
        cases h_full with
        | inl h => omega
        | inr h => exact h.2 s.coord.x
      by_cases hj : j = s.coord.x
      · -- j = s.coord.x: newly set to (I_syn[x] != (G[x,y] xor parity))
        subst hj
        rw [measureStep_F_eq, hG_zero, hE_eq, hI_correct, xor_false_left_r]
        simp
      · -- j ≠ s.coord.x: F[j] unchanged, use IH
        rw [measureStep_F_ne s nc j hj]
        rcases coord_next_x_cases_r hN with h_nc | h_nc
        · -- same round: nc.x = s.coord.x + 1
          apply hF
          have hj_ne : j.val ≠ s.coord.x.val := fun heq => hj (Fin.ext heq)
          omega
        · -- round wrap: nc.x = 0
          exfalso; omega

-- ============================================================
-- Section 4: The RoundInv predicate (strengthened)
-- ============================================================

/-- State at the start of a round. -/
def atRoundStart {P : QECParams} (s : State P) : Prop :=
  s.coord.x.val = 0

/-- The round-boundary invariant (simplified, no ghost).

    Carries two conjuncts:
    (1) RI bound: `s.RI ≤ 2·(C_budget − s.C)`.
    (2) Tight conditional: when the bound is exactly tight, all G entries
        at/after coord are false AND all I_syn entries match parity of Ẽ.

    The tight conditional enables the 2-clean argument: if two consecutive
    rounds are clean, then the RI bound was tight at the start of the first
    clean round, giving G-freshness + I_syn correctness, which propagates
    through the round to show F=0 at round-end (so RI doesn't increment). -/
def RoundInv (P : QECParams) (s : State P) : Prop :=
  atRoundStart s ∧
  s.C ≤ P.C_budget ∧
  s.RI ≤ 2 * (P.C_budget - s.C) ∧
  (s.RI = 2 * (P.C_budget - s.C) →
     (∀ (a : Fin P.numStab) (b : Fin P.R),
        s.coord ≤ Coord.mk a b → s.G a b = false)
     ∧ (∀ j : Fin P.numStab,
          s.I_syn j = ErrorVec.parity (P.stabilizers j) s.E_tilde))

/-- Extract the primary bound from `RoundInv`. -/
theorem RoundInv.ri_bound {P : QECParams} {s : State P}
    (h : RoundInv P s) : s.RI ≤ 2 * (P.C_budget - s.C) := by
  obtain ⟨_, _, h_ri, _⟩ := h
  exact h_ri

/-- `RoundInv` holds at the initial state.
    At init: RI = 0, C = C_budget, so 2*(CB-CB) = 0 and tight.
    Need G = 0 (trivial) and I_syn = 0 = parity(T_j, identity) ✓. -/
theorem roundInv_init (P : QECParams) : RoundInv P (State.init P) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (State.init P).coord.x.val = 0
    simp [State.init, Coord.first]
  · simp [State.init]
  · simp [State.init]
  · intro _
    exact ⟨fun a b _ => by simp [State.init],
           fun j => by simp [State.init, ErrorVec.parity_identity]⟩

-- ============================================================
-- Section 5: Core monotonicity lemmas over MultiStep
-- ============================================================

/-- `C` is monotonically non-increasing along any MultiStep trace. -/
theorem C_monotone {P : QECParams} {s : State P} {e : ExecState P}
    (hrun : MultiStep P (.active s) e) :
    ∀ s' : State P, e = .active s' → s'.C ≤ s.C := by
  induction hrun with
  | refl =>
    intro s' heq; cases heq; exact Nat.le_refl _
  | tail _ step ih =>
    intro s' heq
    cases step with
    | type0 s_mid i p' hp hC =>
      cases heq
      exact Nat.le_trans (Nat.sub_le _ _) (ih s_mid rfl)
    | type1 s_mid i p' hp _mf hC =>
      cases heq
      exact Nat.le_trans (Nat.sub_le _ _) (ih s_mid rfl)
    | type2 s_mid ev he _mf hC =>
      cases heq
      exact Nat.le_trans (Nat.sub_le _ _) (ih s_mid rfl)
    | type3 s_mid hC =>
      cases heq
      exact Nat.le_trans (Nat.sub_le _ _) (ih s_mid rfl)
    | measure s_mid nc hN =>
      cases heq
      rw [measureStep_C]
      exact ih s_mid rfl
    | halt s_mid _ => contradiction
    | budget_exhausted s_mid _ => contradiction

/-- Along any `MultiStep` trace, `coord.y` is non-decreasing and `RI`
    increases by at most `(Δy)` — one round-end per round transition. -/
theorem RI_coord_bound_aux {P : QECParams} {s : State P} {e : ExecState P}
    (hrun : MultiStep P (.active s) e) :
    ∀ s' : State P, e = .active s' →
      s.coord.y.val ≤ s'.coord.y.val ∧
      s'.RI ≤ s.RI + (s'.coord.y.val - s.coord.y.val) := by
  induction hrun with
  | refl =>
    intro s' heq; cases heq
    exact ⟨Nat.le_refl _, by simp⟩
  | tail _ step ih =>
    intro s' heq
    cases step with
    | type0 s_mid i p' hp hC =>
      cases heq
      obtain ⟨hy, hRI⟩ := ih s_mid rfl
      refine ⟨hy, ?_⟩
      show s_mid.RI ≤ s.RI + (s_mid.coord.y.val - s.coord.y.val)
      exact hRI
    | type1 s_mid i p' hp _mf hC =>
      cases heq
      obtain ⟨hy, hRI⟩ := ih s_mid rfl
      refine ⟨hy, ?_⟩
      show s_mid.RI ≤ s.RI + (s_mid.coord.y.val - s.coord.y.val)
      exact hRI
    | type2 s_mid ev he _mf hC =>
      cases heq
      obtain ⟨hy, hRI⟩ := ih s_mid rfl
      refine ⟨hy, ?_⟩
      show s_mid.RI ≤ s.RI + (s_mid.coord.y.val - s.coord.y.val)
      exact hRI
    | type3 s_mid hC =>
      cases heq
      obtain ⟨hy, hRI⟩ := ih s_mid rfl
      refine ⟨hy, ?_⟩
      show s_mid.RI ≤ s.RI + (s_mid.coord.y.val - s.coord.y.val)
      exact hRI
    | measure s_mid nc hN =>
      cases heq
      obtain ⟨hy_mid, hRI_mid⟩ := ih s_mid rfl
      have hy_nc : s_mid.coord.y.val ≤ nc.y.val := coord_next_y_ge' hN
      refine ⟨Nat.le_trans hy_mid hy_nc, ?_⟩
      show (measureStep P s_mid nc).RI
          ≤ s.RI + ((measureStep P s_mid nc).coord.y.val - s.coord.y.val)
      rw [measureStep_coord]
      have hri_bound : (measureStep P s_mid nc).RI ≤ s_mid.RI + 1 :=
        measureStep_RI_le' s_mid nc
      by_cases hre : s_mid.coord.isRoundEnd
      · have hy_eq : nc.y.val = s_mid.coord.y.val + 1 :=
          coord_next_roundEnd_y' hN hre
        rw [hy_eq]; omega
      · rw [measureStep_RI_not_roundEnd' s_mid nc hre]
        have hy_same : nc.y.val = s_mid.coord.y.val := by
          unfold Coord.isRoundEnd at hre
          unfold Coord.next at hN
          split at hN
          · cases hN; simp
          · split at hN
            · rename_i hx _; omega
            · contradiction
        rw [hy_same]
        exact hRI_mid
    | halt s_mid _ => contradiction
    | budget_exhausted s_mid _ => contradiction

-- ============================================================
-- Section 6: Quad + F_zero propagation through clean traces
-- ============================================================

/-- Combined invariant at level `t` with error vector `E_const`:
    ConstantErrorFlow + RegisterInit + fullSynParam + fZero_param. -/
private def roundBody (P : QECParams) (t : Nat) (E_const : ErrorVec P.n)
    (s : State P) : Prop :=
  (s.C < t ∨ (s.C = t ∧ s.E_tilde = E_const))
  ∧ (s.C < t ∨ (s.C = t ∧ ∀ (a : Fin P.numStab) (b : Fin P.R),
      s.coord ≤ Coord.mk a b → s.G a b = false))
  ∧ (s.C < t ∨ (s.C = t ∧ ∀ j : Fin P.numStab,
      s.I_syn j = ErrorVec.parity (P.stabilizers j) E_const))
  ∧ (s.C < t ∨ (s.C = t ∧ ∀ j : Fin P.numStab,
      j.val < s.coord.x.val → s.F j = false))

/-- Step preservation of roundBody. -/
private theorem roundBody_preservation {P : QECParams} (t : Nat) (E_const : ErrorVec P.n)
    (s s' : State P) (h : roundBody P t E_const s)
    (step : Step P (.active s) (.active s')) :
    roundBody P t E_const s' := by
  obtain ⟨h_eflow, h_reg, h_full, h_fZero⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact constantErrorFlow_preservation t E_const s s' h_eflow step
  · exact registerInit_preservation t s s' h_reg step
  · exact fullSynParam_preservation t E_const s s' h_full h_reg h_eflow step
  · exact fZero_param_preservation t E_const s s' h_fZero h_full h_reg h_eflow step

/-- MultiStep propagation of roundBody, generalized over ExecState. -/
private theorem roundBody_of_multistep_aux {P : QECParams} (t : Nat) (E_const : ErrorVec P.n)
    {s : State P} {e : ExecState P}
    (h_start : roundBody P t E_const s)
    (hrun : MultiStep P (.active s) e) :
    ∀ s' : State P, e = .active s' → roundBody P t E_const s' := by
  induction hrun with
  | refl => intro s' heq; cases heq; exact h_start
  | tail _ step ih =>
    intro s' heq
    cases step with
    | type0 s_mid i p' hp hC =>
      cases heq
      exact roundBody_preservation t E_const s_mid _ (ih s_mid rfl)
        (Step.type0 s_mid i p' hp hC)
    | type1 s_mid i p' hp _mf hC =>
      cases heq
      exact roundBody_preservation t E_const s_mid _ (ih s_mid rfl)
        (Step.type1 s_mid i p' hp _mf hC)
    | type2 s_mid ev he _mf hC =>
      cases heq
      exact roundBody_preservation t E_const s_mid _ (ih s_mid rfl)
        (Step.type2 s_mid ev he _mf hC)
    | type3 s_mid hC =>
      cases heq
      exact roundBody_preservation t E_const s_mid _ (ih s_mid rfl)
        (Step.type3 s_mid hC)
    | measure s_mid nc hN =>
      cases heq
      exact roundBody_preservation t E_const s_mid _ (ih s_mid rfl)
        (Step.measure s_mid nc hN)
    | halt s_mid _ => contradiction
    | budget_exhausted s_mid _ => contradiction

private theorem roundBody_of_multistep {P : QECParams} (t : Nat) (E_const : ErrorVec P.n)
    {s s' : State P}
    (h_start : roundBody P t E_const s)
    (hrun : MultiStep P (.active s) (.active s')) :
    roundBody P t E_const s' :=
  roundBody_of_multistep_aux t E_const h_start hrun s' rfl

/-- Extract `roundBody P s.C s.E_tilde s` from a RoundInv state where
    we have G-fresh and I_syn correct (e.g., from the tight conditional). -/
private theorem roundBody_of_RoundInv_tight {P : QECParams} {s : State P}
    (hbdry : atRoundStart s)
    (hG : ∀ (a : Fin P.numStab) (b : Fin P.R),
       s.coord ≤ Coord.mk a b → s.G a b = false)
    (hSyn : ∀ j : Fin P.numStab,
       s.I_syn j = ErrorVec.parity (P.stabilizers j) s.E_tilde) :
    roundBody P s.C s.E_tilde s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · right; exact ⟨rfl, rfl⟩
  · right; exact ⟨rfl, hG⟩
  · right; exact ⟨rfl, hSyn⟩
  · right
    refine ⟨rfl, ?_⟩
    intro j hj
    rw [hbdry] at hj
    exact absurd hj (Nat.not_lt_zero _)

-- ============================================================
-- Section 7: Clean-round no-RI-increment lemma
-- ============================================================

/-- Inside a clean round (no error steps, so C preserved), RI is not
    incremented at any measurement step. -/
private theorem measure_no_RI_increment_clean {P : QECParams} (t : Nat) (E_const : ErrorVec P.n)
    (s_mid : State P) (nc : Coord P)
    (hN : s_mid.coord.next = some nc)
    (h_body : roundBody P t E_const s_mid)
    (h_Ct : s_mid.C = t) :
    (measureStep P s_mid nc).RI = s_mid.RI := by
  by_cases hre : s_mid.coord.isRoundEnd
  · -- Round-end measurement: RI might increment by 1 unless F is all-false.
    -- Show F is all-false via roundBody (F_zero for j < coord.x, and
    -- newly-set F[coord.x] = 0 via full syndrome + G fresh).
    obtain ⟨h_eflow, h_reg, h_full, h_fZero⟩ := h_body
    have hE_eq : s_mid.E_tilde = E_const := by
      cases h_eflow with
      | inl h => omega
      | inr h => exact h.2
    have hG_zero : s_mid.G s_mid.coord.x s_mid.coord.y = false := by
      cases h_reg with
      | inl h => omega
      | inr h =>
        exact h.2 s_mid.coord.x s_mid.coord.y (show s_mid.coord.toLinear ≤
          (Coord.mk s_mid.coord.x s_mid.coord.y).toLinear by simp [Coord.toLinear])
    have hI_correct : s_mid.I_syn s_mid.coord.x =
        ErrorVec.parity (P.stabilizers s_mid.coord.x) E_const := by
      cases h_full with
      | inl h => omega
      | inr h => exact h.2 s_mid.coord.x
    have hF_prefix : ∀ j : Fin P.numStab, j.val < s_mid.coord.x.val → s_mid.F j = false := by
      cases h_fZero with
      | inl h => omega
      | inr h => exact h.2
    -- At round-end: s_mid.coord.x = numStab - 1.
    have hx_last : s_mid.coord.x.val = P.numStab - 1 := by
      unfold Coord.isRoundEnd at hre
      exact hre
    -- Compute new F.
    -- new_F[x] = (I[x] != G[x,y] xor parity) = (parity != 0 xor parity) = 0.
    -- new_F[j ≠ x] = F[j]. For j < x = numStab-1, hF_prefix gives 0.
    -- j > x impossible since j : Fin numStab.
    -- Show all new_F = false, so any_inconsistent = false, RI unchanged.
    unfold measureStep
    simp only []
    -- Direct computation: need to unfold the if-then-else structure.
    have h_all_F_false :
        (∀ j : Fin P.numStab,
           (if j = s_mid.coord.x
             then (s_mid.I_syn s_mid.coord.x !=
                   xor (s_mid.G s_mid.coord.x s_mid.coord.y)
                     (ErrorVec.parity (P.stabilizers s_mid.coord.x) s_mid.E_tilde))
             else s_mid.F j) = false) := by
      intro j
      by_cases hj : j = s_mid.coord.x
      · subst hj
        simp only [ite_true]
        rw [hG_zero, hE_eq, hI_correct, xor_false_left_r]
        simp
      · simp only [hj, ite_false]
        have hj_lt : j.val < s_mid.coord.x.val := by
          rw [hx_last]
          have := j.isLt
          have hj_ne : j.val ≠ s_mid.coord.x.val :=
            fun heq => hj (Fin.ext heq)
          omega
        exact hF_prefix j hj_lt
    have h_not_exists :
        ¬ (∃ j : Fin P.numStab,
             (if j = s_mid.coord.x
               then (s_mid.I_syn s_mid.coord.x !=
                     xor (s_mid.G s_mid.coord.x s_mid.coord.y)
                       (ErrorVec.parity (P.stabilizers s_mid.coord.x) s_mid.E_tilde))
               else s_mid.F j) = true) := by
      intro ⟨j, hj⟩
      rw [h_all_F_false j] at hj
      exact Bool.false_ne_true hj
    have h_decide : (decide (∃ j : Fin P.numStab,
             (if j = s_mid.coord.x
               then (s_mid.I_syn s_mid.coord.x !=
                     xor (s_mid.G s_mid.coord.x s_mid.coord.y)
                       (ErrorVec.parity (P.stabilizers s_mid.coord.x) s_mid.E_tilde))
               else s_mid.F j) = true)) = false :=
      decide_eq_false h_not_exists
    -- Now the RI computation uses this decide.
    have h_and : (decide s_mid.coord.isRoundEnd && decide (∃ j : Fin P.numStab,
             (if j = s_mid.coord.x
               then (s_mid.I_syn s_mid.coord.x !=
                     xor (s_mid.G s_mid.coord.x s_mid.coord.y)
                       (ErrorVec.parity (P.stabilizers s_mid.coord.x) s_mid.E_tilde))
               else s_mid.F j) = true)) = false := by
      rw [h_decide]; simp
    rw [h_and]; rfl
  · -- Non-round-end: RI unchanged directly.
    exact measureStep_RI_not_roundEnd' s_mid nc hre

/-- Within a clean trace (no error steps, C constant), RI is preserved.

    Generalized over `ExecState` endpoint so induction unifies cleanly. -/
private theorem RI_unchanged_clean_aux {P : QECParams} (t : Nat) (E_const : ErrorVec P.n)
    {s : State P} {e : ExecState P}
    (h_body : roundBody P t E_const s)
    (h_Ct : s.C = t)
    (hrun : MultiStep P (.active s) e) :
    ∀ s' : State P, e = .active s' →
      s'.C = s.C → s'.RI = s.RI := by
  induction hrun with
  | refl => intro s' heq _; cases heq; rfl
  | tail hrun' step ih =>
    intro s' heq hC'
    cases step with
    | type0 s_mid i p' hp hC =>
      cases heq
      -- s' has C = s.C, but error step decrements C, so s_mid.C = s.C + 1.
      -- But C_monotone gives s_mid.C ≤ s.C. Contradiction unless C=0 at s.
      have h_mid_le : s_mid.C ≤ s.C := C_monotone hrun' s_mid rfl
      -- s'.C = s_mid.C - 1 = s.C ⟹ s_mid.C = s.C + 1, contradicts h_mid_le.
      -- Need s_mid.C > 0 from hC, but if s_mid.C ≤ s.C and s_mid.C - 1 = s.C, impossible.
      exfalso
      -- hC' : (type0-result).C = s.C, and (type0-result).C = s_mid.C - 1.
      -- Together with h_mid_le : s_mid.C ≤ s.C, this gives contradiction.
      change s_mid.C - 1 = s.C at hC'
      omega
    | type1 s_mid i p' hp _mf hC =>
      cases heq
      have h_mid_le : s_mid.C ≤ s.C := C_monotone hrun' s_mid rfl
      exfalso
      change s_mid.C - 1 = s.C at hC'
      omega
    | type2 s_mid ev he _mf hC =>
      cases heq
      have h_mid_le : s_mid.C ≤ s.C := C_monotone hrun' s_mid rfl
      exfalso
      change s_mid.C - 1 = s.C at hC'
      omega
    | type3 s_mid hC =>
      cases heq
      have h_mid_le : s_mid.C ≤ s.C := C_monotone hrun' s_mid rfl
      exfalso
      change s_mid.C - 1 = s.C at hC'
      omega
    | measure s_mid nc hN =>
      cases heq
      -- Measurement preserves C. Need s_mid.C = s.C via monotonicity + hC'.
      have h_mid_le : s_mid.C ≤ s.C := C_monotone hrun' s_mid rfl
      have h_mid_ge : s.C ≤ s_mid.C := by
        have h_meas_C : (measureStep P s_mid nc).C = s_mid.C := measureStep_C P s_mid nc
        change (measureStep P s_mid nc).C = s.C at hC'
        rw [h_meas_C] at hC'
        omega
      have h_mid_eq : s_mid.C = s.C := Nat.le_antisymm h_mid_le h_mid_ge
      -- Use IH
      have ih_eq : s_mid.RI = s.RI := ih s_mid rfl h_mid_eq
      -- Use measure_no_RI_increment_clean
      have h_mid_body : roundBody P t E_const s_mid :=
        roundBody_of_multistep t E_const h_body hrun'
      have h_mid_Ct : s_mid.C = t := by rw [h_mid_eq]; exact h_Ct
      have h_no_inc : (measureStep P s_mid nc).RI = s_mid.RI :=
        measure_no_RI_increment_clean t E_const s_mid nc hN h_mid_body h_mid_Ct
      show (measureStep P s_mid nc).RI = s.RI
      rw [h_no_inc, ih_eq]
    | halt s_mid _ => contradiction
    | budget_exhausted s_mid _ => contradiction

private theorem RI_unchanged_clean {P : QECParams} (t : Nat) (E_const : ErrorVec P.n)
    {s s' : State P}
    (h_body : roundBody P t E_const s)
    (h_Ct : s.C = t)
    (hrun : MultiStep P (.active s) (.active s'))
    (hC' : s'.C = s.C) :
    s'.RI = s.RI :=
  RI_unchanged_clean_aux t E_const h_body h_Ct hrun s' rfl hC'

-- ============================================================
-- Section 8: two_clean_no_increment
-- ============================================================

/-- **Main lemma**: when transiting from a tight round-boundary with
    G-fresh and I_syn correct at s, and the current round is also
    clean (`s'.C = s.C`), RI does not increment.

    Proof: build `roundBody` at `s` with `t = s.C`, `E_const = s.E_tilde`,
    then propagate through the MultiStep using `RI_unchanged_clean`.
    At every measurement (including round-end), F=0 across all j is
    established by the roundBody's fullSynParam + fZero components,
    so RI is not incremented. -/
theorem two_clean_no_increment {P : QECParams} {s s' : State P}
    (hs : RoundInv P s)
    (hstep : MultiStep P (.active s) (.active s'))
    (h_clean : s'.C = s.C)
    (hG : ∀ (a : Fin P.numStab) (b : Fin P.R),
       s.coord ≤ Coord.mk a b → s.G a b = false)
    (hSyn : ∀ j : Fin P.numStab,
       s.I_syn j = ErrorVec.parity (P.stabilizers j) s.E_tilde) :
    s'.RI = s.RI := by
  obtain ⟨hbdry, _, _, _⟩ := hs
  have h_body : roundBody P s.C s.E_tilde s :=
    roundBody_of_RoundInv_tight hbdry hG hSyn
  exact RI_unchanged_clean s.C s.E_tilde h_body rfl hstep h_clean

-- ============================================================
-- Section 8b: I_syn propagation for clean rounds with G-fresh
-- ============================================================

/-- Partial I_syn correctness within a clean round.  Tracks four conditions:
    1. E_tilde is constant
    2. G-fresh at/after coord
    3. I_syn correct for already-measured stabilizers (j < x) in the current round
    4. Once past the base round, ALL I_syn entries are correct -/
private def partialSynClean (P : QECParams) (E_const : ErrorVec P.n)
    (base_y : Nat) (s : State P) : Prop :=
  s.E_tilde = E_const ∧
  (∀ (a : Fin P.numStab) (b : Fin P.R),
     s.coord ≤ Coord.mk a b → s.G a b = false) ∧
  base_y ≤ s.coord.y.val ∧
  (s.coord.y.val = base_y →
     ∀ j : Fin P.numStab, j.val < s.coord.x.val →
       s.I_syn j = ErrorVec.parity (P.stabilizers j) E_const) ∧
  (base_y < s.coord.y.val →
     ∀ j : Fin P.numStab,
       s.I_syn j = ErrorVec.parity (P.stabilizers j) E_const)

/-- Step preservation of partialSynClean for measurement steps.
    Error steps are handled by the caller (they contradict C constancy). -/
private theorem partialSynClean_measure {P : QECParams} (E_const : ErrorVec P.n)
    (base_y : Nat) (s_mid : State P) (nc : Coord P)
    (hN : s_mid.coord.next = some nc)
    (h : partialSynClean P E_const base_y s_mid) :
    partialSynClean P E_const base_y (measureStep P s_mid nc) := by
  obtain ⟨hE, hG, hBase, hPartial, hFull⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- E_tilde preserved by measurement
    rw [measureStep_E_tilde]; exact hE
  · -- G-fresh propagation: at the new coordinate and beyond, G = false.
    -- The strict invariant holds at s_mid (from hG at ≥ old coord),
    -- so gFresh_after_measure_C_zero gives non-strict at nc.
    intro a b hab
    have h_strict : ∀ (a' : Fin P.numStab) (b' : Fin P.R),
        s_mid.coord.toLinear < (Coord.mk a' b').toLinear → s_mid.G a' b' = false := by
      intro a' b' h_lt
      exact hG a' b' (Nat.le_of_lt h_lt)
    exact gFresh_after_measure_C_zero s_mid nc hN h_strict a b
      (by rw [measureStep_coord] at hab; exact hab)
  · -- base_y ≤ nc.y
    show base_y ≤ (measureStep P s_mid nc).coord.y.val
    rw [measureStep_coord]
    exact Nat.le_trans hBase (coord_next_y_ge' hN)
  · -- Partial I_syn: for j < new_x when still in base round
    intro h_y j hj_lt
    simp only [measureStep_coord] at h_y hj_lt
    -- nc.y = base_y. Determine whether nc.x = s_mid.coord.x + 1 or nc.x = 0.
    rcases coord_next_x_cases_r hN with h_nc_x | h_nc_x
    · -- Same round: nc.x = s_mid.x + 1, nc.y = s_mid.y
      by_cases hj : j = s_mid.coord.x
      · -- j = s_mid.coord.x: newly measured
        subst hj
        rw [measureStep_I_syn_eq]
        have hG_zero : s_mid.G s_mid.coord.x s_mid.coord.y = false :=
          hG s_mid.coord.x s_mid.coord.y (Nat.le_refl _)
        rw [hG_zero, hE, xor_false_left_r]
      · -- j < s_mid.coord.x: already measured, IH
        rw [measureStep_I_syn_ne s_mid nc j hj]
        have h_mid_y : s_mid.coord.y.val = base_y := by
          unfold Coord.next at hN
          split at hN
          · cases hN; exact h_y
          · split at hN
            · cases hN; simp at h_nc_x
            · contradiction
        exact hPartial h_mid_y j (by
          have hj_ne : j.val ≠ s_mid.coord.x.val := fun heq => hj (Fin.ext heq)
          omega)
    · -- Round wrap: nc.x = 0, nc.y = s_mid.y + 1
      exfalso; omega
  · -- Full I_syn: once past the base round
    intro h_past j
    rw [measureStep_coord] at h_past
    -- Check if s_mid was already past the base round
    by_cases h_mid_past : base_y < s_mid.coord.y.val
    · -- Already past: I_syn was already fully correct, just propagate
      by_cases hj : j = s_mid.coord.x
      · subst hj
        rw [measureStep_I_syn_eq]
        have hG_zero : s_mid.G s_mid.coord.x s_mid.coord.y = false :=
          hG s_mid.coord.x s_mid.coord.y (Nat.le_refl _)
        rw [hG_zero, hE, xor_false_left_r]
      · rw [measureStep_I_syn_ne s_mid nc j hj]
        exact hFull h_mid_past j
    · -- s_mid was in the base round: s_mid.coord.y = base_y
      push_neg at h_mid_past
      have h_mid_y : s_mid.coord.y.val = base_y := by
        have h_ge := coord_next_y_ge' hN
        omega
      -- nc.y > base_y, so nc.y = base_y + 1, meaning round wrap
      -- This means s_mid was at round-end (x = numStab - 1)
      have h_nc_y : nc.y.val = s_mid.coord.y.val + 1 := by
        have h_le := coord_next_y_le_succ' hN
        have h_ge := coord_next_y_ge' hN
        omega
      have h_wrap : nc.x.val = 0 :=
        coord_next_y_inc_x_zero' hN (by omega)
      -- At round-end, s_mid.coord.x = numStab - 1
      have h_x_last : s_mid.coord.x.val = P.numStab - 1 := by
        unfold Coord.next at hN
        split at hN
        · rename_i hx; cases hN; simp at h_nc_y
        · split at hN
          · rename_i hx _; have := s_mid.coord.x.isLt; omega
          · contradiction
      -- For j = s_mid.coord.x (= numStab - 1): newly measured
      by_cases hj : j = s_mid.coord.x
      · subst hj
        rw [measureStep_I_syn_eq]
        have hG_zero : s_mid.G s_mid.coord.x s_mid.coord.y = false :=
          hG s_mid.coord.x s_mid.coord.y (Nat.le_refl _)
        rw [hG_zero, hE, xor_false_left_r]
      · -- j ≠ s_mid.coord.x, so j < numStab - 1 = s_mid.coord.x
        rw [measureStep_I_syn_ne s_mid nc j hj]
        have hj_lt : j.val < s_mid.coord.x.val := by
          have := j.isLt
          have hj_ne : j.val ≠ s_mid.coord.x.val := fun heq => hj (Fin.ext heq)
          omega
        exact hPartial h_mid_y j hj_lt

/-- Generalized MultiStep propagation of partialSynClean. Error steps
    are ruled out by the C-constancy hypothesis (they'd decrement C). -/
private theorem partialSynClean_of_multistep_aux {P : QECParams} (E_const : ErrorVec P.n)
    (base_y : Nat) {s : State P} {e : ExecState P}
    (h_start : partialSynClean P E_const base_y s)
    (hrun : MultiStep P (.active s) e) :
    ∀ s' : State P, e = .active s' → s'.C = s.C →
      partialSynClean P E_const base_y s' := by
  induction hrun with
  | refl => intro s' heq _; cases heq; exact h_start
  | tail hrun' step ih =>
    intro s' heq hC'
    cases step with
    | type0 s_mid i p' hp hC =>
      cases heq; exfalso
      have h_mid_le : s_mid.C ≤ s.C := C_monotone hrun' s_mid rfl
      change s_mid.C - 1 = s.C at hC'; omega
    | type1 s_mid i p' hp _mf hC =>
      cases heq; exfalso
      have h_mid_le : s_mid.C ≤ s.C := C_monotone hrun' s_mid rfl
      change s_mid.C - 1 = s.C at hC'; omega
    | type2 s_mid ev he _mf hC =>
      cases heq; exfalso
      have h_mid_le : s_mid.C ≤ s.C := C_monotone hrun' s_mid rfl
      change s_mid.C - 1 = s.C at hC'; omega
    | type3 s_mid hC =>
      cases heq; exfalso
      have h_mid_le : s_mid.C ≤ s.C := C_monotone hrun' s_mid rfl
      change s_mid.C - 1 = s.C at hC'; omega
    | measure s_mid nc hN =>
      cases heq
      have h_mid_C : s_mid.C = s.C := by
        have := C_monotone hrun' s_mid rfl
        change (measureStep P s_mid nc).C = s.C at hC'
        rw [measureStep_C] at hC'; omega
      have h_mid : partialSynClean P E_const base_y s_mid :=
        ih s_mid rfl h_mid_C
      exact partialSynClean_measure E_const base_y s_mid nc hN h_mid
    | halt s_mid _ => cases heq
    | budget_exhausted s_mid _ => cases heq

/-- **Clean-round I_syn propagation**: in a clean round (C constant) starting
    from a G-fresh state at (0, y), all I_syn entries are correct at the
    next round boundary (0, y+1).

    This is the key lemma for Case B of the tight conditional proof.
    Unlike roundBody propagation, this does NOT require I_syn correct
    at the start — the I_syn values are overwritten during the round. -/
theorem I_syn_after_clean_round_gfresh {P : QECParams} {s s' : State P}
    (hbdry : atRoundStart s)
    (hG : ∀ (a : Fin P.numStab) (b : Fin P.R),
       s.coord ≤ Coord.mk a b → s.G a b = false)
    (hstep : MultiStep P (.active s) (.active s'))
    (hClean : s'.C = s.C)
    (hy' : s'.coord.y.val = s.coord.y.val + 1) :
    ∀ j : Fin P.numStab,
       s'.I_syn j = ErrorVec.parity (P.stabilizers j) s'.E_tilde := by
  -- Build initial partialSynClean at s
  have h_init : partialSynClean P s.E_tilde s.coord.y.val s := by
    refine ⟨rfl, hG, Nat.le_refl _, ?_, ?_⟩
    · intro _ j hj; rw [hbdry] at hj; exact absurd hj (Nat.not_lt_zero _)
    · intro h_past; omega
  -- Propagate through the MultiStep
  have h_end : partialSynClean P s.E_tilde s.coord.y.val s' :=
    partialSynClean_of_multistep_aux s.E_tilde s.coord.y.val h_init hstep s' rfl hClean
  -- Extract full I_syn from the fifth component
  obtain ⟨hE', _, _, _, hFull⟩ := h_end
  rw [hE']
  exact hFull (by omega)

-- ============================================================
-- Section 9: Round-transit preservation
-- ============================================================

/-- **Round-transit preservation**.

    If `RoundInv P s` holds and we reach `s'` via `MultiStep` with
    `s'.coord.y = s.coord.y + 1` and `s'.coord.x = 0`, then `RoundInv P s'`.

    G-freshness at both `s` and `s'` is supplied externally: the caller
    (typically `RoundInv_reachable`) derives them from the crossing lemma
    and `gFresh_after_measure_C_zero`. The `hG_s` hypothesis enables
    the Case B proof (not-tight at s, tight at s'). -/
theorem roundInv_preserve {P : QECParams} {s s' : State P}
    (hs : RoundInv P s)
    (hstep : MultiStep P (.active s) (.active s'))
    (hx' : s'.coord.x.val = 0)
    (hy' : s'.coord.y.val = s.coord.y.val + 1)
    (hG_s : ∀ (a : Fin P.numStab) (b : Fin P.R),
       s.coord ≤ Coord.mk a b → s.G a b = false)
    (hG_s' : ∀ (a : Fin P.numStab) (b : Fin P.R),
       s'.coord ≤ Coord.mk a b → s'.G a b = false) :
    RoundInv P s' := by
  obtain ⟨hbdry, hCb, hRI, h_tight_cond⟩ := hs
  -- Mechanical bounds
  have hC_mono : s'.C ≤ s.C := C_monotone hstep s' rfl
  have hRI_coord : s.coord.y.val ≤ s'.coord.y.val ∧
                    s'.RI ≤ s.RI + (s'.coord.y.val - s.coord.y.val) :=
    RI_coord_bound_aux hstep s' rfl
  have hRI_bound : s'.RI ≤ s.RI + 1 := by
    have := hRI_coord.2
    rw [hy'] at this
    simp at this
    exact this
  refine ⟨hx', Nat.le_trans hC_mono hCb, ?_, ?_⟩
  · -- RI bound at s'
    by_cases hDelta : s'.C < s.C
    · have : 2 * (P.C_budget - s'.C) ≥ 2 * (P.C_budget - s.C) + 2 := by omega
      calc s'.RI ≤ s.RI + 1 := hRI_bound
        _ ≤ 2 * (P.C_budget - s.C) + 1 := by omega
        _ ≤ 2 * (P.C_budget - s'.C) := by omega
    · push_neg at hDelta
      have hCeq : s'.C = s.C := Nat.le_antisymm hC_mono hDelta
      by_cases h_tight : s.RI = 2 * (P.C_budget - s.C)
      · -- Tight at s + clean round => 2-clean => RI unchanged.
        obtain ⟨hG, hSyn⟩ := h_tight_cond h_tight
        have h_no_inc : s'.RI = s.RI :=
          two_clean_no_increment ⟨hbdry, hCb, hRI, h_tight_cond⟩ hstep hCeq hG hSyn
        rw [h_no_inc, hCeq]
        exact h_tight.le
      · push_neg at h_tight
        have h_lt : s.RI < 2 * (P.C_budget - s.C) :=
          lt_of_le_of_ne hRI h_tight
        rw [hCeq]
        calc s'.RI ≤ s.RI + 1 := hRI_bound
          _ ≤ 2 * (P.C_budget - s.C) := h_lt
  · -- Tight conditional at s': tight at s' => G-fresh ∧ I_syn correct at s'
    intro h_tight_s'
    constructor
    · -- G-fresh at s'
      exact hG_s'
    · -- I_syn correct at s'
      -- Tight at s' means s'.RI = 2*(CB - s'.C).
      -- Since s'.RI ≤ s.RI + 1 and s.RI ≤ 2*(CB - s.C), and s'.C ≤ s.C,
      -- tight at s' with s'.C < s.C is impossible (slack ≥ 2 from error).
      -- So s'.C = s.C (clean round).
      have hCeq : s'.C = s.C := by
        by_contra h_ne
        have hDelta : s'.C < s.C := lt_of_le_of_ne hC_mono h_ne
        have : 2 * (P.C_budget - s'.C) ≥ 2 * (P.C_budget - s.C) + 2 := by omega
        omega
      -- Case split: was s also tight?
      by_cases h_tight_s : s.RI = 2 * (P.C_budget - s.C)
      · -- Case A: s was tight, round is clean.
        -- Tight at s gives G-fresh + I_syn correct at s.
        -- Build roundBody and propagate through the clean round.
        obtain ⟨hG, hSyn⟩ := h_tight_cond h_tight_s
        have h_body : roundBody P s.C s.E_tilde s :=
          roundBody_of_RoundInv_tight hbdry hG hSyn
        -- Propagate roundBody through the MultiStep
        have h_body' : roundBody P s.C s.E_tilde s' :=
          roundBody_of_multistep s.C s.E_tilde h_body hstep
        obtain ⟨h_eflow', _, h_full', _⟩ := h_body'
        -- Extract E_tilde constant and I_syn correct at s'
        have hE' : s'.E_tilde = s.E_tilde := by
          cases h_eflow' with
          | inl h => omega
          | inr h => exact h.2
        have hI' : ∀ j : Fin P.numStab,
            s'.I_syn j = ErrorVec.parity (P.stabilizers j) s.E_tilde := by
          cases h_full' with
          | inl h => omega
          | inr h => exact h.2
        intro j
        rw [hE']
        exact hI' j
      · -- Case B: s not tight, s' tight from RI increment.
        -- The round from s to s' is clean (hCeq). G-fresh at s (hG_s).
        -- By I_syn_after_clean_round_gfresh, all I_syn at s' are correct.
        exact I_syn_after_clean_round_gfresh hbdry hG_s hstep hCeq hy'

-- ============================================================
-- Section 10: Reachability and trace decomposition
-- ============================================================

/-- `coord.toLinear` is monotonically non-decreasing in any MultiStep trace.
    Error steps preserve coord; measurement steps strictly advance it. -/
private theorem coord_toLinear_mono {P : QECParams} {s : State P} {e : ExecState P}
    (hrun : MultiStep P (.active s) e) :
    ∀ s' : State P, e = .active s' → s.coord.toLinear ≤ s'.coord.toLinear := by
  induction hrun with
  | refl => intro s' heq; cases heq; exact Nat.le_refl _
  | tail _ step ih =>
    intro s' heq
    cases step with
    | type0 s_mid i p' hp hC =>
      cases heq; exact ih s_mid rfl  -- type0 preserves coord
    | type1 s_mid i p' hp _mf hC =>
      cases heq; exact ih s_mid rfl
    | type2 s_mid ev he _mf hC =>
      cases heq; exact ih s_mid rfl
    | type3 s_mid hC =>
      cases heq; exact ih s_mid rfl
    | measure s_mid nc hN =>
      cases heq
      have h1 : s.coord.toLinear ≤ s_mid.coord.toLinear := ih s_mid rfl
      have h2 : s_mid.coord.toLinear < nc.toLinear := Coord.next_toLinear_lt hN
      show s.coord.toLinear ≤ (measureStep P s_mid nc).coord.toLinear
      rw [measureStep_coord]
      omega
    | halt _ _ => cases heq
    | budget_exhausted _ _ => cases heq

/-- In a MultiStep where C and coord don't change, the trace is trivial
    (no steps at all). All fields are preserved. This is because every
    active→active step either decrements C (type0/1/2/3) or advances
    coord (measure). -/
private theorem trivial_trace_of_C_coord_eq {P : QECParams} {s : State P} {e : ExecState P}
    (hrun : MultiStep P (.active s) e) :
    ∀ s' : State P, e = .active s' → s'.C = s.C → s'.coord = s.coord →
      s' = s := by
  induction hrun with
  | refl => intro s' heq _ _; cases heq; rfl
  | tail hrun' step ih =>
    intro s' heq hC hcoord
    cases step with
    | type0 s_mid i p' hp hC_pos =>
      cases heq
      -- type0 decrements C: s'.C = s_mid.C - 1. But s'.C = s.C.
      -- s_mid.C ≤ s.C (C monotone in prefix). s'.C = s_mid.C - 1 = s.C.
      -- So s_mid.C = s.C + 1 > s.C. But s_mid.C ≤ s.C. Contradiction.
      exfalso
      have h_mid_le : s_mid.C ≤ s.C := C_monotone hrun' s_mid rfl
      change s_mid.C - 1 = s.C at hC
      omega
    | type1 s_mid i p' hp _mf hC_pos =>
      cases heq; exfalso
      have h_mid_le : s_mid.C ≤ s.C := C_monotone hrun' s_mid rfl
      change s_mid.C - 1 = s.C at hC; omega
    | type2 s_mid ev he _mf hC_pos =>
      cases heq; exfalso
      have h_mid_le : s_mid.C ≤ s.C := C_monotone hrun' s_mid rfl
      change s_mid.C - 1 = s.C at hC; omega
    | type3 s_mid hC_pos =>
      cases heq; exfalso
      have h_mid_le : s_mid.C ≤ s.C := C_monotone hrun' s_mid rfl
      change s_mid.C - 1 = s.C at hC; omega
    | measure s_mid nc hN =>
      cases heq; exfalso
      -- measureStep advances coord. If s'.C = s.C and s'.coord = s.coord,
      -- then s_mid.C = s.C (measureStep preserves C, C monotone in prefix)
      -- and s_mid = s (by IH). Then nc > s.coord but nc = s.coord. Contradiction.
      have h_mid_C : s_mid.C = s.C := by
        have := C_monotone hrun' s_mid rfl
        change (measureStep P s_mid nc).C = s.C at hC
        rw [measureStep_C] at hC; omega
      have h_nc_eq : nc = s.coord := by
        change (measureStep P s_mid nc).coord = s.coord at hcoord
        rw [measureStep_coord] at hcoord; exact hcoord
      -- IH: s_mid = s (same C, need same coord)
      -- s_mid.coord: by IH, if s_mid.C = s.C and s_mid.coord = s.coord, then s_mid = s.
      -- But we need s_mid.coord = s.coord. This follows from:
      -- nc = s.coord (from above), nc > s_mid.coord (next_toLinear_lt),
      -- so s.coord > s_mid.coord. But coord is non-decreasing in the prefix.
      -- Actually, coord.toLinear non-decreasing: at each step,
      -- error steps preserve coord, measurement advances. So
      -- s.coord.toLinear ≤ s_mid.coord.toLinear.
      -- Combined with s.coord.toLinear > s_mid.coord.toLinear: contradiction.
      have h_lt := Coord.next_toLinear_lt hN
      rw [h_nc_eq] at h_lt
      -- s.coord.toLinear > s_mid.coord.toLinear
      -- But coord.toLinear is non-decreasing in the prefix:
      have h_mono : s.coord.toLinear ≤ s_mid.coord.toLinear :=
        coord_toLinear_mono hrun' s_mid rfl
      omega
    | halt _ _ => cases heq
    | budget_exhausted _ _ => cases heq

-- ============================================================
-- Trace crossing lemma (moved before RoundInv_reachable)
-- ============================================================

/-- If coord.y starts below `target` and ends at or above `target`, some
    intermediate state in the `MultiStep` is at `(0, target)` with G-fresh.

    The G-freshness comes from `gFresh_after_measure_C_zero`: the crossing
    state is a `measureStep` output, and the pre-measurement state has
    strict G-freshness (from `gFreshStrictInvariant` via the Run). -/
private theorem coord_y_crossing {P : QECParams} {s : State P} {e : ExecState P}
    (hrun : MultiStep P (.active s) e)
    (hrun_from_init : Run P (.active s))
    (target : Nat) (h_start : s.coord.y.val < target) :
    ∀ s_end : State P, e = .active s_end → target ≤ s_end.coord.y.val →
    ∃ s_mid : State P,
      s_mid.coord.x.val = 0 ∧ s_mid.coord.y.val = target ∧
      (∀ (a : Fin P.numStab) (b : Fin P.R),
         s_mid.coord ≤ Coord.mk a b → s_mid.G a b = false) ∧
      MultiStep P (.active s) (.active s_mid) ∧
      MultiStep P (.active s_mid) (.active s_end) := by
  induction hrun with
  | refl =>
    intro s_end heq h_end; cases heq; omega
  | tail h_prefix step_last ih =>
    intro s_end heq h_end
    cases step_last with
    | type0 s_mid i p' hp hC =>
      cases heq
      obtain ⟨sm, h1, h2, h2G, h3, h4⟩ := ih s_mid rfl h_end
      exact ⟨sm, h1, h2, h2G, h3, h4.tail (Step.type0 s_mid i p' hp hC)⟩
    | type1 s_mid i p' hp _mf hC =>
      cases heq
      obtain ⟨sm, h1, h2, h2G, h3, h4⟩ := ih s_mid rfl h_end
      exact ⟨sm, h1, h2, h2G, h3, h4.tail (Step.type1 s_mid i p' hp _mf hC)⟩
    | type2 s_mid ev he _mf hC =>
      cases heq
      obtain ⟨sm, h1, h2, h2G, h3, h4⟩ := ih s_mid rfl h_end
      exact ⟨sm, h1, h2, h2G, h3, h4.tail (Step.type2 s_mid ev he _mf hC)⟩
    | type3 s_mid hC =>
      cases heq
      obtain ⟨sm, h1, h2, h2G, h3, h4⟩ := ih s_mid rfl h_end
      exact ⟨sm, h1, h2, h2G, h3, h4.tail (Step.type3 s_mid hC)⟩
    | measure s_mid nc hN =>
      cases heq
      by_cases h_mid : target ≤ s_mid.coord.y.val
      · obtain ⟨sm, h1, h2, h2G, h3, h4⟩ := ih s_mid rfl h_mid
        exact ⟨sm, h1, h2, h2G, h3, h4.tail (Step.measure s_mid nc hN)⟩
      · push_neg at h_mid
        have h_nc_le : nc.y.val ≤ s_mid.coord.y.val + 1 := coord_next_y_le_succ' hN
        have h_nc_y : nc.y.val = target := by
          have : target ≤ nc.y.val := by
            simp only [measureStep_coord] at h_end; exact h_end
          omega
        have h_nc_x : nc.x.val = 0 :=
          coord_next_y_inc_x_zero' hN (by omega)
        have h_run_mid : Run P (.active s_mid) :=
          multi_step_trans hrun_from_init h_prefix
        have h_strict : ∀ (a : Fin P.numStab) (b : Fin P.R),
            s_mid.coord.toLinear < (Coord.mk a b).toLinear → s_mid.G a b = false :=
          (gFreshStrictInvariant P).holds_of_reachable s_mid h_run_mid
        have h_G_fresh : ∀ (a : Fin P.numStab) (b : Fin P.R),
            nc.toLinear ≤ (Coord.mk a b).toLinear →
            (measureStep P s_mid nc).G a b = false :=
          gFresh_after_measure_C_zero s_mid nc hN h_strict
        exact ⟨measureStep P s_mid nc,
          by rw [measureStep_coord]; exact h_nc_x,
          by rw [measureStep_coord]; exact h_nc_y,
          by rw [measureStep_coord]; exact h_G_fresh,
          h_prefix.tail (Step.measure s_mid nc hN),
          Relation.ReflTransGen.refl⟩
    | halt s_mid _ => cases heq
    | budget_exhausted s_mid _ => cases heq

/-- Transfer RoundInv from a crossing state to a later state with the same coord.
    The trace between them is error-only (no measurements, since coord is unchanged).
    RI is bounded by the crossing's RI (from RI_coord_bound), and the tight case
    forces C equality, making the trace trivial (s = s_cross). -/
private theorem RoundInv_transfer_from_crossing {P : QECParams} {s_cross s : State P}
    (h_inv : RoundInv P s_cross)
    (hstep : MultiStep P (.active s_cross) (.active s))
    (hbdry : atRoundStart s)
    (h_coord : s.coord = s_cross.coord) :
    RoundInv P s := by
  obtain ⟨hbdry_c, hCb_c, hRI_c, h_tight_c⟩ := h_inv
  have hC_le : s.C ≤ s_cross.C := C_monotone hstep s rfl
  have hRI_le : s.RI ≤ s_cross.RI := by
    have h := (RI_coord_bound_aux hstep s rfl).2
    rw [h_coord] at h
    simp at h
    exact h
  refine ⟨hbdry, Nat.le_trans hC_le hCb_c, ?_, ?_⟩
  · -- RI bound: s.RI ≤ s_cross.RI ≤ 2*(CB - s_cross.C) ≤ 2*(CB - s.C)
    calc s.RI ≤ s_cross.RI := hRI_le
      _ ≤ 2 * (P.C_budget - s_cross.C) := hRI_c
      _ ≤ 2 * (P.C_budget - s.C) := by omega
  · -- Tight conditional: tight at s forces s = s_cross
    intro h_tight
    -- From tight: s.RI = 2*(CB - s.C)
    -- Chain: s.RI ≤ s_cross.RI ≤ 2*(CB - s_cross.C) ≤ 2*(CB - s.C) = s.RI
    -- All equalities hold: s_cross.C = s.C and s_cross.RI = s.RI
    have hC_eq : s.C = s_cross.C := by omega
    -- Since C and coord are both the same, trace is trivial
    have h_triv : s = s_cross :=
      trivial_trace_of_C_coord_eq hstep s rfl hC_eq h_coord
    rw [h_triv]
    have h_tight_c' : s_cross.RI = 2 * (P.C_budget - s_cross.C) := by
      rw [← h_triv]; exact h_tight
    exact h_tight_c h_tight_c'

/-- **The RI bound holds at every round-boundary reachable state.**

    Proved by strong induction on `coord.y`. At each round boundary `(0, y)`:
    - Base (y = 0): RI = 0 from init, tight forces s = init.
    - Step (y > 0): crossing lemma finds `s_cross` at `(0, y)` with G-fresh.
      Crossing at `(0, y-1)` (or init for y = 1) provides `s_prev` with
      RoundInv (by IH). `roundInv_preserve` gives RoundInv at `s_cross`.
      `RoundInv_transfer_from_crossing` extends to `s`. -/
theorem RoundInv_reachable {P : QECParams} {s : State P}
    (hrun : Run P (.active s))
    (hbdry : atRoundStart s) :
    RoundInv P s := by
  -- Suffices to prove for all y by strong induction
  suffices h_all : ∀ y : Nat, ∀ t : State P,
      Run P (.active t) → atRoundStart t → t.coord.y.val = y → RoundInv P t by
    exact h_all s.coord.y.val s hrun hbdry rfl
  intro y
  induction y using Nat.strongRecOn with
  | ind y ih =>
    intro t hrun_t hbdry_t hy_t
    -- Find s_cross at (0, y) in the trace from init to t via crossing lemma,
    -- then transfer RoundInv from s_cross to t.
    by_cases hy0 : y = 0
    · -- Base case: y = 0
      subst hy0
      -- RI = 0 at t (no round-end measurements since coord.y stayed at 0)
      have hRI_zero : t.RI = 0 := by
        have h := (RI_coord_bound_aux hrun_t t rfl).2
        simp [State.init, Coord.first] at h
        omega
      -- C ≤ CB
      have hC_le : t.C ≤ P.C_budget := C_monotone hrun_t t rfl
      refine ⟨hbdry_t, hC_le, ?_, ?_⟩
      · -- RI ≤ 2*(CB - C): 0 ≤ 2*(CB - C)
        rw [hRI_zero]; omega
      · -- Tight conditional: 0 = 2*(CB - C) → C = CB → t = init
        intro h_tight
        rw [hRI_zero] at h_tight
        have hC_eq : t.C = P.C_budget := by omega
        -- t has same C and coord as init, so t = init
        have h_init_C : (State.init P).C = P.C_budget := by simp [State.init]
        have h_init_coord : (State.init P).coord = Coord.first P := by simp [State.init]
        have h_t_coord : t.coord = Coord.first P := by
          have hx : t.coord.x = ⟨0, P.hns⟩ := Fin.ext hbdry_t
          have hy : t.coord.y = ⟨0, P.hR⟩ := Fin.ext hy_t
          show t.coord = ⟨⟨0, P.hns⟩, ⟨0, P.hR⟩⟩
          rw [show t.coord = ⟨t.coord.x, t.coord.y⟩ from rfl, hx, hy]
        have h_triv : t = State.init P :=
          trivial_trace_of_C_coord_eq hrun_t t rfl
            (by rw [hC_eq, h_init_C]) (by rw [h_t_coord, h_init_coord])
        rw [h_triv]
        exact (roundInv_init P).2.2.2 (by simp [State.init])
    · -- Inductive case: y > 0
      have hy_pos : 0 < y := Nat.pos_of_ne_zero hy0
      -- Step 1: Find s_cross at (0, y) in the trace from init to t
      have h_init_y : (State.init P).coord.y.val = 0 := by simp [State.init, Coord.first]
      have h_init_lt_y : (State.init P).coord.y.val < y := by omega
      obtain ⟨s_cross, hx_cross, hy_cross, hG_cross, h_to_cross, h_from_cross⟩ :=
        coord_y_crossing hrun_t (Relation.ReflTransGen.refl) y h_init_lt_y t rfl (by omega)
      -- Step 2: Find s_prev at (0, y-1) for the predecessor round boundary
      -- Decompose: init →* s_cross →* t. We need to find s_prev in init →* s_cross.
      have h_run_cross : Run P (.active s_cross) := h_to_cross
      -- For y = 1, use init directly. For y ≥ 2, use crossing lemma.
      by_cases hy1 : y = 1
      · -- y = 1: predecessor is init at (0, 0)
        subst hy1
        have h_prev_inv : RoundInv P (State.init P) := roundInv_init P
        have h_prev_G : ∀ (a : Fin P.numStab) (b : Fin P.R),
            (State.init P).coord ≤ Coord.mk a b → (State.init P).G a b = false :=
          fun a b _ => by simp [State.init]
        have h_prev_bdry : atRoundStart (State.init P) := by simp [atRoundStart, State.init, Coord.first]
        have h_prev_y : (State.init P).coord.y.val = 0 := by simp [State.init, Coord.first]
        -- roundInv_preserve from init to s_cross
        have h_cross_inv : RoundInv P s_cross :=
          roundInv_preserve h_prev_inv h_to_cross hx_cross
            (by rw [hy_cross, h_prev_y]) h_prev_G hG_cross
        -- Transfer from s_cross to t
        have h_coord_eq : t.coord = s_cross.coord := by
          cases hc1 : t.coord; cases hc2 : s_cross.coord
          simp only [Coord.mk.injEq]
          exact ⟨Fin.ext (by unfold atRoundStart at hbdry_t; rw [hc1] at hbdry_t; rw [hc2] at hx_cross; simp at hbdry_t hx_cross; omega),
                 Fin.ext (by rw [hc1] at hy_t; rw [hc2] at hy_cross; simp at hy_t hy_cross; omega)⟩
        exact RoundInv_transfer_from_crossing h_cross_inv h_from_cross hbdry_t h_coord_eq
      · -- y ≥ 2: use crossing lemma to find s_prev at (0, y-1)
        have hy_ge2 : 2 ≤ y := by omega
        have h_init_lt_y1 : (State.init P).coord.y.val < y - 1 := by omega
        -- Find s_prev at (0, y-1) in the trace init →* s_cross
        -- coord_y_crossing needs s_cross.coord.y ≥ y-1
        -- We know s_cross.coord.y = y ≥ y-1 ✓
        obtain ⟨s_prev, hx_prev, hy_prev, hG_prev, h_to_prev, h_from_prev⟩ :=
          coord_y_crossing h_to_cross (Relation.ReflTransGen.refl) (y - 1) h_init_lt_y1
            s_cross rfl (by omega)
        -- IH at y-1 gives RoundInv at s_prev
        have h_run_prev : Run P (.active s_prev) := h_to_prev
        have h_prev_bdry : atRoundStart s_prev := hx_prev
        have h_prev_inv : RoundInv P s_prev :=
          ih (y - 1) (by omega) s_prev h_run_prev h_prev_bdry hy_prev
        -- roundInv_preserve from s_prev to s_cross
        have h_cross_inv : RoundInv P s_cross :=
          roundInv_preserve h_prev_inv h_from_prev hx_cross
            (by rw [hy_cross, hy_prev]; omega) hG_prev hG_cross
        -- Transfer from s_cross to t
        have h_coord_eq : t.coord = s_cross.coord := by
          cases hc1 : t.coord; cases hc2 : s_cross.coord
          simp only [Coord.mk.injEq]
          exact ⟨Fin.ext (by unfold atRoundStart at hbdry_t; rw [hc1] at hbdry_t; rw [hc2] at hx_cross; simp at hbdry_t hx_cross; omega),
                 Fin.ext (by rw [hc1] at hy_t; rw [hc2] at hy_cross; simp at hy_t hy_cross; omega)⟩
        exact RoundInv_transfer_from_crossing h_cross_inv h_from_cross hbdry_t h_coord_eq

/-- Auxiliary: within a trace starting at y = R-1, coord.y stays at R-1,
    RI stays constant, and C only decreases. -/
theorem stay_in_last_round_aux {P : QECParams} {s : State P} {e : ExecState P}
    (hrun : MultiStep P (.active s) e)
    (h_s_y : s.coord.y.val = P.R - 1) :
    ∀ s' : State P, e = .active s' →
      s'.coord.y.val = P.R - 1 ∧ s'.RI = s.RI ∧ s'.C ≤ s.C := by
  induction hrun with
  | refl =>
    intro s' heq
    cases heq
    exact ⟨h_s_y, rfl, Nat.le_refl _⟩
  | tail _ step ih =>
    intro s' heq
    cases step with
    | type0 s_mid i p' hp hC =>
      cases heq
      obtain ⟨hy_mid, hRI_mid, hC_mid⟩ := ih s_mid rfl
      exact ⟨hy_mid, hRI_mid, Nat.le_trans (Nat.sub_le _ _) hC_mid⟩
    | type1 s_mid i p' hp _mf hC =>
      cases heq
      obtain ⟨hy_mid, hRI_mid, hC_mid⟩ := ih s_mid rfl
      exact ⟨hy_mid, hRI_mid, Nat.le_trans (Nat.sub_le _ _) hC_mid⟩
    | type2 s_mid ev he _mf hC =>
      cases heq
      obtain ⟨hy_mid, hRI_mid, hC_mid⟩ := ih s_mid rfl
      exact ⟨hy_mid, hRI_mid, Nat.le_trans (Nat.sub_le _ _) hC_mid⟩
    | type3 s_mid hC =>
      cases heq
      obtain ⟨hy_mid, hRI_mid, hC_mid⟩ := ih s_mid rfl
      exact ⟨hy_mid, hRI_mid, Nat.le_trans (Nat.sub_le _ _) hC_mid⟩
    | measure s_mid nc hN =>
      cases heq
      obtain ⟨hy_mid, hRI_mid, hC_mid⟩ := ih s_mid rfl
      have h_not_round_end : ¬ s_mid.coord.isRoundEnd := by
        intro hre
        unfold Coord.isRoundEnd at hre
        unfold Coord.next at hN
        split at hN
        · rename_i hx; omega
        · split at hN
          · rename_i _ hy
            have := s_mid.coord.y.isLt
            omega
          · contradiction
      refine ⟨?_, ?_, ?_⟩
      · show nc.y.val = P.R - 1
        unfold Coord.next at hN
        split at hN
        · cases hN; exact hy_mid
        · split at hN
          · rename_i _ hy
            have := s_mid.coord.y.isLt
            omega
          · contradiction
      · rw [measureStep_RI_not_roundEnd' s_mid nc h_not_round_end]
        exact hRI_mid
      · show (measureStep P s_mid nc).C ≤ s.C
        rw [measureStep_C]
        exact hC_mid
    | halt s_mid _ => contradiction
    | budget_exhausted s_mid _ => contradiction

/-- Within the last round, `RI` does not change. -/
theorem RI_constant_last_round {P : QECParams} (s s_end : State P)
    (hrun : MultiStep P (.active s) (.active s_end))
    (h_s_y : s.coord.y.val = P.R - 1) :
    s_end.RI = s.RI ∧ s_end.C ≤ s.C := by
  obtain ⟨_, h_ri, h_c⟩ := stay_in_last_round_aux hrun h_s_y s_end rfl
  exact ⟨h_ri, h_c⟩

/-- **Conditional RI bound at σ_done**, given a round-boundary `s_last`
    at `(0, R-1)` reachable to `s_done`. -/
theorem RI_bound_at_done_given_last_start {P : QECParams}
    {s_last s_done : State P}
    (h_s_last_y : s_last.coord.y.val = P.R - 1)
    (h_last_inv : RoundInv P s_last)
    (hrun : MultiStep P (.active s_last) (.active s_done)) :
    s_done.RI ≤ 2 * (P.C_budget - s_done.C) := by
  obtain ⟨h_ri_eq, h_c_le⟩ := RI_constant_last_round s_last s_done hrun h_s_last_y
  have h_bound := h_last_inv.ri_bound
  calc s_done.RI
      = s_last.RI := h_ri_eq
    _ ≤ 2 * (P.C_budget - s_last.C) := h_bound
    _ ≤ 2 * (P.C_budget - s_done.C) := by
        apply Nat.mul_le_mul_left
        omega

-- ============================================================
-- Coord.next y-increment helpers
-- ============================================================

private theorem coord_next_y_le_succ {P : QECParams} {c nc : Coord P}
    (h : c.next = some nc) : nc.y.val ≤ c.y.val + 1 := by
  unfold Coord.next at h
  split at h
  · cases h; simp
  · split at h
    · cases h; simp
    · contradiction

private theorem coord_next_y_inc_x_zero {P : QECParams} {c nc : Coord P}
    (h : c.next = some nc) (hy : c.y.val < nc.y.val) : nc.x.val = 0 := by
  unfold Coord.next at h
  split at h
  · cases h; simp at hy
  · split at h
    · cases h; simp
    · contradiction

-- ============================================================
-- Trace crossing lemma
-- ============================================================

/-- If coord.y starts below `target` and ends at or above `target`, some
    intermediate state in the `MultiStep` is at `(0, target)` with G-fresh.

    The G-freshness comes from `gFresh_after_measure_C_zero`: the crossing
    state is a `measureStep` output, and the pre-measurement state has
    strict G-freshness (from `gFreshStrictInvariant` via the Run). -/
private theorem coord_y_crossing_aux {P : QECParams} {s : State P} {e : ExecState P}
    (hrun : MultiStep P (.active s) e)
    (hrun_from_init : Run P (.active s))
    (target : Nat) (h_start : s.coord.y.val < target) :
    ∀ s_end : State P, e = .active s_end → target ≤ s_end.coord.y.val →
    ∃ s_mid : State P,
      s_mid.coord.x.val = 0 ∧ s_mid.coord.y.val = target ∧
      (∀ (a : Fin P.numStab) (b : Fin P.R),
         s_mid.coord ≤ Coord.mk a b → s_mid.G a b = false) ∧
      MultiStep P (.active s) (.active s_mid) ∧
      MultiStep P (.active s_mid) (.active s_end) := by
  induction hrun with
  | refl =>
    intro s_end heq h_end; cases heq; omega
  | tail h_prefix step_last ih =>
    intro s_end heq h_end
    cases step_last with
    | type0 s_mid i p' hp hC =>
      cases heq
      obtain ⟨sm, h1, h2, h2G, h3, h4⟩ := ih s_mid rfl h_end
      exact ⟨sm, h1, h2, h2G, h3, h4.tail (Step.type0 s_mid i p' hp hC)⟩
    | type1 s_mid i p' hp _mf hC =>
      cases heq
      obtain ⟨sm, h1, h2, h2G, h3, h4⟩ := ih s_mid rfl h_end
      exact ⟨sm, h1, h2, h2G, h3, h4.tail (Step.type1 s_mid i p' hp _mf hC)⟩
    | type2 s_mid ev he _mf hC =>
      cases heq
      obtain ⟨sm, h1, h2, h2G, h3, h4⟩ := ih s_mid rfl h_end
      exact ⟨sm, h1, h2, h2G, h3, h4.tail (Step.type2 s_mid ev he _mf hC)⟩
    | type3 s_mid hC =>
      cases heq
      obtain ⟨sm, h1, h2, h2G, h3, h4⟩ := ih s_mid rfl h_end
      exact ⟨sm, h1, h2, h2G, h3, h4.tail (Step.type3 s_mid hC)⟩
    | measure s_mid nc hN =>
      cases heq
      by_cases h_mid : target ≤ s_mid.coord.y.val
      · obtain ⟨sm, h1, h2, h2G, h3, h4⟩ := ih s_mid rfl h_mid
        exact ⟨sm, h1, h2, h2G, h3, h4.tail (Step.measure s_mid nc hN)⟩
      · push_neg at h_mid
        have h_nc_le : nc.y.val ≤ s_mid.coord.y.val + 1 := coord_next_y_le_succ hN
        have h_nc_y : nc.y.val = target := by
          have : target ≤ nc.y.val := by
            simp only [measureStep_coord] at h_end; exact h_end
          omega
        have h_nc_x : nc.x.val = 0 := by
          apply coord_next_y_inc_x_zero hN
          omega
        -- G-freshness: use gFreshStrictInvariant at s_mid (reachable) +
        -- gFresh_after_measure_C_zero to get non-strict freshness.
        have h_run_mid : Run P (.active s_mid) :=
          multi_step_trans hrun_from_init h_prefix
        have h_strict : ∀ (a : Fin P.numStab) (b : Fin P.R),
            s_mid.coord.toLinear < (Coord.mk a b).toLinear → s_mid.G a b = false :=
          (gFreshStrictInvariant P).holds_of_reachable s_mid h_run_mid
        have h_G_fresh : ∀ (a : Fin P.numStab) (b : Fin P.R),
            nc.toLinear ≤ (Coord.mk a b).toLinear →
            (measureStep P s_mid nc).G a b = false :=
          gFresh_after_measure_C_zero s_mid nc hN h_strict
        exact ⟨measureStep P s_mid nc,
          by rw [measureStep_coord]; exact h_nc_x,
          by rw [measureStep_coord]; exact h_nc_y,
          by rw [measureStep_coord]; exact h_G_fresh,
          h_prefix.tail (Step.measure s_mid nc hN),
          Relation.ReflTransGen.refl⟩
    | halt s_mid _ => cases heq
    | budget_exhausted s_mid _ => cases heq

/-- **Structural witness**: any reachable `s_done` contains a round-boundary
    state `s_last` at `(0, R-1)` from which it's reachable, with G-fresh.

    Uses `coord_y_crossing_aux` on the prefix `σ_init →* s_done` obtained
    by peeling off the halt step from the Run. -/
theorem last_round_start_exists {P : QECParams} {s_done : State P}
    (hrun : Run P (.done s_done))
    (hR : 2 ≤ P.R) :
    ∃ s_last : State P,
      atRoundStart s_last
      ∧ s_last.coord.y.val = P.R - 1
      ∧ (∀ (a : Fin P.numStab) (b : Fin P.R),
           s_last.coord ≤ Coord.mk a b → s_last.G a b = false)
      ∧ MultiStep P (.active (State.init P)) (.active s_last)
      ∧ MultiStep P (.active s_last) (.active s_done) := by
  -- Peel off the halt step: Run = init →* s_done →halt→ done.
  -- But Run goes to .done s_done, so the last step is halt.
  -- Use cases_tail to extract the prefix.
  rcases Relation.ReflTransGen.cases_tail hrun with heq | ⟨mid, h_prefix, h_last⟩
  · exact absurd heq (by simp [ExecState.active, ExecState.done])
  · -- h_last : Step P mid (.done s_done)
    -- mid must be .active s_done (halt preserves state)
    cases h_last with
    | halt s_pre hDone =>
      -- s_pre = s_done at the state level (halt doesn't change state)
      -- h_prefix : MultiStep P (.active init) (.active s_pre)
      -- where s_pre has coord.y = R-1, coord.x = numStab - 1
      have h_done_y : s_done.coord.y.val = P.R - 1 := by
        unfold Coord.next at hDone
        split at hDone
        · contradiction
        · split at hDone
          · contradiction
          · have := s_done.coord.y.isLt; omega
      have h_init_y : (State.init P).coord.y.val = 0 := by
        simp [State.init, Coord.first]
      have h_init_lt : (State.init P).coord.y.val < P.R - 1 := by omega
      -- h_prefix is a Run from init to s_done
      have h_run_init : Run P (.active (State.init P)) :=
        Relation.ReflTransGen.refl
      -- Apply crossing lemma on the prefix init →* s_done (as active).
      obtain ⟨s_last, hx, hy, hG_last, h_to, h_from⟩ :=
        coord_y_crossing_aux h_prefix h_run_init (P.R - 1) h_init_lt
          s_done rfl (by omega)
      exact ⟨s_last, hx, hy, hG_last, h_to, h_from⟩

/-- **RI bound at σ_done** — the statement used by the main theorem. -/
theorem RI_bound_at_done {P : QECParams} {s_done : State P}
    (hrun : Run P (.done s_done))
    (hR : 2 ≤ P.R) :
    s_done.RI ≤ 2 * (P.C_budget - s_done.C) := by
  obtain ⟨s_last, h_bdry, h_y, _, h_run_to_last, h_run_from_last⟩ :=
    last_round_start_exists hrun hR
  have h_last_run : Run P (.active s_last) := h_run_to_last
  have h_last_inv : RoundInv P s_last :=
    RoundInv_reachable h_last_run h_bdry
  exact RI_bound_at_done_given_last_start h_y h_last_inv h_run_from_last

end QStab.Invariants
