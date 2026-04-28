import QStab.Invariants.ErrorCount
import QStab.Invariants.ZeroBudget
import QStab.Invariants.RegisterInit
import QStab.Invariants.ConstantErrorFlow
import QStab.Invariants.SyndromeCorrectness
import QStab.Invariants.ErrorPropagation
import QStab.Invariants.RoundInconsistency
import QStab.Invariants.GFresh
import QStab.Invariants.RoundInv

/-! # Main fault-tolerance theorem

Combines all invariants to prove that under a sufficient error budget,
any execution reaching σ_done satisfies the fault-tolerance predicate p_FT:
  p_FT(σ) = (λ_E ≤ d/2) ∧ ∀ s, I[T_s] = Parity(T_s, Ẽ)
-/

namespace QStab

open Invariants

/-- The fault-tolerance predicate p_FT (Eq. 7):
    The error weight is correctable and syndrome is correct. -/
def faultTolerant (P : QECParams) (s : State P) : Prop :=
  2 * s.lam_E ≤ P.d ∧
  ∀ j : Fin P.numStab,
    s.I_syn j = ErrorVec.parity (P.stabilizers j) s.E_tilde

/-- Error count invariant at done state:
    totalErrors + C = C_budget. -/
theorem error_count_at_done (P : QECParams) (s : State P)
    (hrun : Run P (.done s)) :
    s.totalErrors + s.C = P.C_budget :=
  (errorCountInvariant P).holds_at_done s hrun

/-- C ≤ C_budget at done state. -/
theorem C_le_budget_at_done (P : QECParams) (s : State P)
    (hrun : Run P (.done s)) :
    s.C ≤ P.C_budget := by
  have := error_count_at_done P s hrun; omega

/-- Error propagation bound at done state:
    lam_E ≤ cnt0 + cnt1 + r * cnt2 + cnt3. -/
theorem error_propagation_bound_at_done (P : QECParams) (s : State P)
    (hrun : Run P (.done s)) :
    s.lam_E ≤ s.cnt0 + s.cnt1 + P.r * s.cnt2 + s.cnt3 :=
  (errorPropagationInvariant P).holds_at_done s hrun

/-- Error propagation at done: lam_E ≤ r * C_budget.
    Requires r ≥ 1 so that cnt0 + cnt1 + r*cnt2 + cnt3 ≤ r * totalErrors.
    Note: if r = 0, the bound degrades to lam_E ≤ C_budget (weaker). -/
theorem error_propagation_at_done (P : QECParams) (s : State P)
    (hrun : Run P (.done s))
    (hr : 1 ≤ P.r) :
    s.lam_E ≤ P.r * P.C_budget := by
  have hep := error_propagation_bound_at_done P s hrun
  have hec := error_count_at_done P s hrun
  simp only [State.totalErrors] at hec
  have h_te_le : s.cnt0 + s.cnt1 + s.cnt2 + s.cnt3 ≤ P.C_budget := by omega
  -- cnt_i ≤ r * cnt_i when r ≥ 1
  have h0 : s.cnt0 ≤ P.r * s.cnt0 := Nat.le_mul_of_pos_left s.cnt0 hr
  have h1 : s.cnt1 ≤ P.r * s.cnt1 := Nat.le_mul_of_pos_left s.cnt1 hr
  have h3 : s.cnt3 ≤ P.r * s.cnt3 := Nat.le_mul_of_pos_left s.cnt3 hr
  have h_mid : s.cnt0 + s.cnt1 + P.r * s.cnt2 + s.cnt3 ≤
               P.r * s.cnt0 + P.r * s.cnt1 + P.r * s.cnt2 + P.r * s.cnt3 := by omega
  have h_factor : P.r * s.cnt0 + P.r * s.cnt1 + P.r * s.cnt2 + P.r * s.cnt3 =
                  P.r * (s.cnt0 + s.cnt1 + s.cnt2 + s.cnt3) := by
    simp only [Nat.left_distrib]
  have h_r_le : P.r * (s.cnt0 + s.cnt1 + s.cnt2 + s.cnt3) ≤ P.r * P.C_budget :=
    Nat.mul_le_mul_left P.r h_te_le
  calc s.lam_E ≤ s.cnt0 + s.cnt1 + P.r * s.cnt2 + s.cnt3 := hep
    _ ≤ P.r * s.cnt0 + P.r * s.cnt1 + P.r * s.cnt2 + P.r * s.cnt3 := h_mid
    _ = P.r * (s.cnt0 + s.cnt1 + s.cnt2 + s.cnt3) := h_factor
    _ ≤ P.r * P.C_budget := h_r_le

/-- Round inconsistency bound at done state:
    RI ≤ 2 * (C_budget - C).
    Now follows from the fully proved RoundInv.lean (0 sorry). -/
theorem round_inconsistency_at_done (P : QECParams) (s : State P)
    (hrun : Run P (.done s))
    (hR : 2 ≤ P.R) :
    s.RI ≤ 2 * (P.C_budget - s.C) :=
  Invariants.RI_bound_at_done hrun hR

/-- Post-selection: if RI ≥ 2 * C_budget, then C = 0.
    From RI ≤ 2*(C_budget - C) and RI ≥ 2*C_budget,
    we get C_budget ≤ C_budget - C, so C = 0. -/
theorem budget_zero_last_round (P : QECParams) (s : State P)
    (hrun : Run P (.done s))
    (hR : 2 ≤ P.R)
    (hRI : s.RI ≥ 2 * P.C_budget) :
    s.C = 0 := by
  have hri := round_inconsistency_at_done P s hrun hR
  have hec := error_count_at_done P s hrun
  simp only [State.totalErrors] at hec
  have h_le : s.C ≤ P.C_budget := by omega
  by_contra hne
  have hpos : 0 < s.C := Nat.pos_of_ne_zero hne
  have h_sub_strict : P.C_budget - s.C < P.C_budget := Nat.sub_lt (by omega) hpos
  have h_2_strict : 2 * (P.C_budget - s.C) < 2 * P.C_budget :=
    Nat.mul_lt_mul_of_pos_left h_sub_strict (by omega : 0 < 2)
  have : s.RI < s.RI := Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt hri h_2_strict) hRI
  exact Nat.lt_irrefl _ this

-- ============================================================
-- Two-phase proof infrastructure
-- ============================================================

/-- At a done state, coord.next = none, which means coord is at the last position:
    coord.x = numStab - 1 and coord.y = R - 1. -/
private theorem done_coord_last {P : QECParams} {s s_done : State P}
    (hstep : Step P (.active s) (.done s_done)) :
    s_done.coord.x.val = P.numStab - 1 ∧ s_done.coord.y.val = P.R - 1 := by
  cases hstep with
  | halt s hDone =>
    unfold QECParams.Coord.next at hDone
    split at hDone
    · contradiction
    · split at hDone
      · contradiction
      · constructor
        · have := s.coord.x.isLt; omega
        · have := s.coord.y.isLt; omega

/-- Any done state reachable via multi-step has coord at the last position. -/
private theorem done_reachable_coord {P : QECParams} {s_start s_done : State P}
    (h : MultiStep P (.active s_start) (.done s_done)) :
    s_done.coord.x.val = P.numStab - 1 ∧ s_done.coord.y.val = P.R - 1 := by
  rcases Relation.ReflTransGen.cases_tail h with heq | ⟨c, _, hstep⟩
  · exact absurd heq (by simp)
  · cases c with
    | active s => exact done_coord_last hstep
    | done s => exact absurd hstep (done_is_stuck P s _)
    | error s => exact absurd hstep (error_is_stuck P s _)

/-- Combined predicate for four parameterized invariants at budget level 0.
    Extends the triple with the previous-round syndrome correctness invariant
    to handle the last stabilizer (numStab-1) which isn't measured in the last round. -/
private def syndromeQuad (P : QECParams) (E_const : ErrorVec P.n) (s : State P) : Prop :=
  (s.C = 0 ∧ s.E_tilde = E_const) ∧
  (s.C = 0 ∧ ∀ (a : Fin P.numStab) (b : Fin P.R),
    s.coord ≤ QECParams.Coord.mk a b → s.G a b = false) ∧
  (s.C = 0 ∧ ∀ (j : Fin P.numStab), j < s.coord.x →
    s.I_syn j = ErrorVec.parity (P.stabilizers j) E_const) ∧
  (s.C = 0 ∧ (0 < s.coord.y.val →
    ∀ (j : Fin P.numStab), s.coord.x ≤ j →
      s.I_syn j = ErrorVec.parity (P.stabilizers j) E_const))

/-- The syndrome quad is preserved by every active→active transition. -/
private theorem syndromeQuad_preservation (P : QECParams) (E_const : ErrorVec P.n)
    (s s' : State P)
    (h : syndromeQuad P E_const s)
    (step : Step P (.active s) (.active s')) :
    syndromeQuad P E_const s' := by
  obtain ⟨⟨hC, hE⟩, ⟨hC', hG⟩, ⟨hC'', hSyn⟩, ⟨hC''', hPrev⟩⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h_eflow := constantErrorFlow_preservation 0 E_const s s'
      (Or.inr ⟨hC, hE⟩) step
    cases h_eflow with | inl h => exact absurd h (by omega) | inr h => exact h
  · have h_reg := registerInit_preservation 0 s s'
      (Or.inr ⟨hC', hG⟩) step
    cases h_reg with | inl h => exact absurd h (by omega) | inr h => exact h
  · have h_syn := syndromeCorrectnessParam_preservation 0 E_const s s'
      (Or.inr ⟨hC'', hSyn⟩) (Or.inr ⟨hC', hG⟩) (Or.inr ⟨hC, hE⟩) step
    cases h_syn with | inl h => exact absurd h (by omega) | inr h => exact h
  · have h_prev := prevRoundSyndromeParam_preservation 0 E_const s s'
      (Or.inr ⟨hC''', hPrev⟩) (Or.inr ⟨hC'', hSyn⟩)
      (Or.inr ⟨hC', hG⟩) (Or.inr ⟨hC, hE⟩) step
    cases h_prev with | inl h => exact absurd h (by omega) | inr h => exact h

/-- The syndrome quad holds for any state reachable from where it holds. -/
private theorem syndromeQuad_of_reachable (P : QECParams) (E_const : ErrorVec P.n)
    (e : ExecState P) (s_mid : State P)
    (h_init : syndromeQuad P E_const s_mid)
    (hreach : MultiStep P (.active s_mid) e) :
    syndromeQuad P E_const e.state := by
  induction hreach with
  | refl => exact h_init
  | tail _ step ih =>
    cases step with
    | type0 s i p' hp hC =>
      exact syndromeQuad_preservation P E_const _ _ ih (Step.type0 s i p' hp hC)
    | type1 s i p' hp _mf hC =>
      exact syndromeQuad_preservation P E_const _ _ ih (Step.type1 s i p' hp _mf hC)
    | type2 s ev he _mf hC =>
      exact syndromeQuad_preservation P E_const _ _ ih (Step.type2 s ev he _mf hC)
    | type3 s hC =>
      exact syndromeQuad_preservation P E_const _ _ ih (Step.type3 s hC)
    | measure s nc hN =>
      exact syndromeQuad_preservation P E_const _ _ ih (Step.measure s nc hN)
    | halt s _ => exact ih
    | budget_exhausted s _ => exact ih

/-- Full syndrome correctness from an intermediate state σ_mid with C=0 and x=0.

    The quad is initialized at σ_mid. The main syndrome (j < coord.x) and
    previous-round (j ≥ coord.x when y > 0) invariants together cover all
    stabilizers at done.

    The `hI_prev` hypothesis handles the previous-round initialization:
    if σ_mid is at y > 0, I_syn must already be correct for all j ≥ 0 = coord.x.
    This is typically established by running the triple for one round before σ_mid.
    If σ_mid is at y = 0, this is vacuously true. -/
theorem syndrome_correct_from_mid (P : QECParams) (E_const : ErrorVec P.n)
    (s_mid s_done : State P)
    (hC : s_mid.C = 0)
    (hx : s_mid.coord.x.val = 0)
    (hE : s_mid.E_tilde = E_const)
    (hG : ∀ (a : Fin P.numStab) (b : Fin P.R),
      s_mid.coord ≤ QECParams.Coord.mk a b → s_mid.G a b = false)
    (hI_prev : 0 < s_mid.coord.y.val →
      ∀ (j : Fin P.numStab),
        s_mid.I_syn j = ErrorVec.parity (P.stabilizers j) E_const)
    (hreach : MultiStep P (.active s_mid) (.done s_done))
    (hR : 2 ≤ P.R) :
    s_done.E_tilde = E_const ∧
    ∀ (j : Fin P.numStab),
      s_done.I_syn j = ErrorVec.parity (P.stabilizers j) E_const := by
  have h_init : syndromeQuad P E_const s_mid := by
    refine ⟨⟨hC, hE⟩, ⟨hC, hG⟩, ⟨hC, ?_⟩, ⟨hC, ?_⟩⟩
    · intro j hj; have : j.val < s_mid.coord.x.val := hj; omega
    · intro hy j hj_ge
      have h_all := hI_prev hy j
      exact h_all
  -- Extract the quad at done
  have h_done := syndromeQuad_of_reachable P E_const (.done s_done) s_mid h_init hreach
  obtain ⟨⟨_, hE_done⟩, _, ⟨_, hSyn⟩, ⟨_, hPrev⟩⟩ := h_done
  constructor
  · exact hE_done
  · intro j
    by_cases hj : j < s_done.coord.x
    · exact hSyn j hj
    · -- j ≥ coord.x: use prev-round invariant
      -- At done, coord.y = R - 1 ≥ 1 (since R ≥ 2)
      have ⟨_, hy⟩ := done_reachable_coord hreach
      have hy_pos : 0 < s_done.coord.y.val := by omega
      exact hPrev hy_pos j (Nat.le_of_not_lt hj)

-- ============================================================
-- Budget exhaustion and syndrome correctness at done
-- ============================================================

/-- **Budget exhaustion before final round** (Lemma BudgetExhaust from the paper).
    Under the post-selection condition RI ≥ 2·C_budget, there exists an intermediate
    state σ_mid in the execution with:
    - C = 0, coord.x = 0 (start of a round)
    - All G entries at positions ≥ coord are false
    - I_syn at σ_mid is correct for all stabilizers (when y > 0)
    - The execution decomposes as σ_init →* σ_mid →* σ_done

    For C_budget = 0: σ_mid = σ_init (I_syn vacuously correct since y = 0).
    For C_budget > 0: uses `last_round_start_exists` to find the last round
    boundary s_last at (0, R-1). The RI bound at s_last (from RoundInv) combined
    with the post-selection condition forces s_last.C = 0 and the tight RoundInv
    condition gives I_syn correct. -/
theorem mid_state_exists (P : QECParams) (s_done : State P)
    (hrun : Run P (.done s_done))
    (_hC : s_done.C = 0)
    (hR : 2 ≤ P.R)
    (hRI : s_done.RI ≥ 2 * P.C_budget) :
    ∃ (s_mid : State P) (E_const : ErrorVec P.n),
      s_mid.C = 0 ∧
      s_mid.coord.x.val = 0 ∧
      s_mid.E_tilde = E_const ∧
      (∀ (a : Fin P.numStab) (b : Fin P.R),
        s_mid.coord ≤ QECParams.Coord.mk a b → s_mid.G a b = false) ∧
      (0 < s_mid.coord.y.val →
        ∀ j : Fin P.numStab,
          s_mid.I_syn j = ErrorVec.parity (P.stabilizers j) E_const) ∧
      MultiStep P (.active s_mid) (.done s_done) := by
  by_cases hcb : P.C_budget = 0
  · -- C_budget = 0: use init state directly
    refine ⟨State.init P, (State.init P).E_tilde,
      by simp [State.init, hcb],
      by simp [State.init, QECParams.Coord.first],
      rfl,
      by intro a b _; simp [State.init],
      by intro hy; simp [State.init, QECParams.Coord.first] at hy,
      hrun⟩
  · -- C_budget > 0: use tight RoundInv at the last round boundary.
    -- Extract the halt step from hrun for reuse.
    have h_halt_info : s_done.coord.next = none ∧
        MultiStep P (.active (State.init P)) (.active s_done) := by
      rcases Relation.ReflTransGen.cases_tail hrun with heq | ⟨mid, h_prefix, h_last⟩
      · exact absurd heq (by simp)
      · cases h_last with
        | halt s hDone => exact ⟨hDone, h_prefix⟩
    obtain ⟨h_halt, h_run_active⟩ := h_halt_info
    have h_done_y : s_done.coord.y.val = P.R - 1 := by
      unfold QECParams.Coord.next at h_halt
      split at h_halt
      · contradiction
      · split at h_halt
        · contradiction
        · have := s_done.coord.y.isLt; omega
    -- Step 1: Find s_last at (0, R-1) with G-fresh.
    obtain ⟨s_last, h_bdry_last, h_y_last, hG_last, h_to_last, h_from_last⟩ :=
      last_round_start_exists hrun hR
    -- Step 2: RI is non-decreasing from s_last to s_done (same round R-1).
    have h_ri_nondec : s_done.RI ≤ s_last.RI := by
      have ⟨_, h_ri⟩ := RI_coord_bound_aux h_from_last s_done rfl
      rw [h_y_last, h_done_y] at h_ri; omega
    -- Step 3: RoundInv at s_last gives RI bound and tight condition.
    have h_last_inv : RoundInv P s_last := RoundInv_reachable h_to_last h_bdry_last
    -- Step 4: Deduce s_last.C = 0 from tight RI.
    -- 2 * C_budget ≤ s_done.RI ≤ s_last.RI ≤ 2 * (C_budget - s_last.C)
    have hC_last : s_last.C = 0 := by
      obtain ⟨_, hCb, h_ri_bound, _⟩ := h_last_inv; omega
    -- Step 5: The bound is tight, so extract I_syn from tight condition.
    have h_tight_val : s_last.RI = 2 * (P.C_budget - s_last.C) := by
      have := h_last_inv.ri_bound; omega
    obtain ⟨_, _, _, h_tight_cond⟩ := h_last_inv
    have ⟨_, hI_tight⟩ := h_tight_cond h_tight_val
    -- Step 6: Assemble the witness. s_mid = s_last, E_const = s_last.E_tilde.
    refine ⟨s_last, s_last.E_tilde, hC_last, h_bdry_last, rfl, hG_last, ?_,
      h_from_last.tail (Step.halt s_done h_halt)⟩
    -- I_syn correct at s_last (from tight RoundInv)
    intro _hy j
    exact hI_tight j

/-- Syndrome correctness at done state.

    Uses the two-phase proof: find σ_mid via mid_state_exists, then
    propagate the syndrome quad from σ_mid to σ_done.

    Requires R ≥ 2 for the previous-round invariant to cover the last stabilizer. -/
theorem syndrome_correct_at_done (P : QECParams) (s : State P)
    (hrun : Run P (.done s))
    (hC : s.C = 0)
    (hR : 2 ≤ P.R)
    (hRI : s.RI ≥ 2 * P.C_budget) :
    ∀ j : Fin P.numStab,
      s.I_syn j = ErrorVec.parity (P.stabilizers j) s.E_tilde := by
  obtain ⟨s_mid, E_const, hC_mid, hx_mid, hE_mid, hG_mid, hI_mid, hreach⟩ :=
    mid_state_exists P s hrun hC hR hRI
  have ⟨hE_done, hSyn⟩ := syndrome_correct_from_mid P E_const s_mid s
    hC_mid hx_mid hE_mid hG_mid hI_mid hreach hR
  intro j
  rw [hSyn j, hE_done]

/-- **Main Theorem: Fault-tolerance under error budget.**

    For an [[n,k,d]] code with back-action bound r and
    error budget C_budget = ⌊(d-1)/(2r)⌋,
    any execution reaching σ_done with RI ≥ 2*C_budget satisfies p_FT.

    Requires R ≥ 2 (at least 2 measurement rounds). -/
theorem fault_tolerance (P : QECParams) (s_final : State P)
    (hrun : Run P (.done s_final))
    (hbudget : 2 * P.r * P.C_budget < P.d)
    (hr : 1 ≤ P.r) (hR : 2 ≤ P.R)
    (hRI : s_final.RI ≥ 2 * P.C_budget) :
    faultTolerant P s_final := by
  constructor
  · -- 2 * lam_E ≤ d
    have hep := error_propagation_at_done P s_final hrun hr
    have : 2 * s_final.lam_E ≤ 2 * (P.r * P.C_budget) :=
      Nat.mul_le_mul_left 2 hep
    rw [← Nat.mul_assoc] at this
    omega
  · -- Syndrome correctness
    exact syndrome_correct_at_done P s_final hrun
      (budget_zero_last_round P s_final hrun hR hRI) hR hRI

/-- Corollary: with C_budget = ⌊(d-1)/(2r)⌋ and d > 0, the error is correctable. -/
theorem correctable_under_threshold (P : QECParams) (s_final : State P)
    (hrun : Run P (.done s_final))
    (hr : 1 ≤ P.r) (hd : 0 < P.d)
    (hbudget : P.C_budget = (P.d - 1) / (2 * P.r)) :
    2 * s_final.lam_E < P.d := by
  have hep := error_propagation_at_done P s_final hrun hr
  have h_div : (P.d - 1) / (2 * P.r) * (2 * P.r) ≤ P.d - 1 :=
    Nat.div_mul_le_self (P.d - 1) (2 * P.r)
  rw [Nat.mul_comm, ← hbudget] at h_div
  have h_2lam : 2 * s_final.lam_E ≤ 2 * (P.r * P.C_budget) :=
    Nat.mul_le_mul_left 2 hep
  rw [← Nat.mul_assoc] at h_2lam
  omega

end QStab
