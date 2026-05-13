import QStab.Paper.SurfaceD3OperationalIffParam
import QStab.Paper.SurfaceD3OperationalIffParamZ
import QStab.MultiStep
import QStab.Invariant
import Mathlib.GroupTheory.Perm.Basic

/-!
# Gadget-order invariance of the d=3 surface scheduling characterisation

`SurfaceD3OperationalIffParam.lean` (X-side) and
`SurfaceD3OperationalIffParamZ.lean` (Z-side) both fix one specific
**gadget order** within a round: the QStab Run measures stabiliser
indices in the order 0, 1, 2, ..., 7. This file lifts those theorems
to **all `8! = 40320` gadget orders**.

## Why it works

Given a gadget-order permutation `σ : Equiv.Perm (Fin 8)`, define
`permutedSchedCode σ sched` whose stabiliser at index `i` is
`parametricStabilizers (σ i)` and whose back-action set at `i` is the
hooks of physical stab `σ i`. The reachable-`E_tilde` set
`schedReachableE sched n` is **defined** in terms of
`schedAllHooks sched` (a union — invariant under reordering), so the
bridge invariant for the permuted code uses the **same** reachable set.

The success predicate `isSuccessState E` checks parity vs the multi-set
of all 8 stabilisers, which is a multiset invariant (equally
`parametricStabilizers ∘ σ` and `parametricStabilizers` give the same
8-element multiset). Hence the canonical native-decide finite check
`schedReachableE_2_not_success_if_not_failing` directly fires.

The Z-side mirrors symmetrically.

## What this file proves (zero `sorry`, standard axioms only)

For any gadget order `σ : Equiv.Perm (Fin 8)`:
  * X-side: `classOf sched ≠ Failing` → operational `d_circ` ≥ 3
    for `permutedSchedCode σ sched` against L_Z attacks.
  * Z-side: `classOfZ sched ≠ Failing` → operational `d_circ` ≥ 3
    for `permutedSchedCodeZ σ sched` against L_X attacks.

Combined with `SurfaceD3JointXZ`, this yields a uniform statement over
the full Cartesian product:
  (CX orderings) × (gadget orders) = 2304 × 40320 ≈ 93M schedulings,
each times 3 logical operators ≈ 280M scheduling-logical combinations.

**Zero `sorry`. Standard axioms only.**
-/

namespace QStab.Paper.SurfaceD3GadgetOrderInvariance

open QStab QStab.Examples QStab.Examples.SurfaceD3
     QStab.Paper.SurfaceD3Classification
     QStab.Paper.SurfaceD3OperationalIffParam
     QStab.Paper.SurfaceD3OperationalIffParamZ

/-- Gadget-order = permutation of QStab stab indices. -/
abbrev GadgetOrder := Equiv.Perm (Fin 8)

/-! ## X-side: gadget-permuted parametric code -/

def permutedStabilizers (σ : GadgetOrder) : Fin 8 → ErrorVec 9 :=
  fun i => parametricStabilizers (σ i)

def permutedHooksAt (σ : GadgetOrder) (sched : Surface3Sched) (i : Fin 8) :
    List (ErrorVec 9) :=
  schedHooksAt sched (σ i)

def permutedBackActionSet (σ : GadgetOrder) (sched : Surface3Sched) (i : Fin 8) :
    Set (ErrorVec 9) :=
  fun e => e ∈ permutedHooksAt σ sched i

theorem permutedHooksAt_subset (σ : GadgetOrder) (sched : Surface3Sched) (i : Fin 8) :
    ∀ e ∈ permutedHooksAt σ sched i, e ∈ schedAllHooks sched := by
  intro e he
  exact schedHooksAt_subset sched (σ i) e he

def permutedSchedCode (σ : GadgetOrder) (sched : Surface3Sched) : QECParams where
  n := 9; k := 1; d := 3; R := 1; numStab := 8
  stabilizers := permutedStabilizers σ
  backActionSet := permutedBackActionSet σ sched
  r := 3
  backAction_weight_bound := by
    intro stab_idx e he
    have h_e_in : e ∈ permutedHooksAt σ sched stab_idx := he
    have h_e_in_all : e ∈ schedAllHooks sched :=
      permutedHooksAt_subset σ sched stab_idx e h_e_in
    exact schedAllHooks_weight_bound sched e h_e_in_all
  C_budget := 2
  hn := by omega
  hns := by omega
  hR := by omega

/-! ## Bridge invariant for the gadget-permuted X-side code

Crucially, the reachable set `schedReachableE sched n` doesn't change:
it's defined in terms of `schedAllHooks sched` (union over all i),
which is gadget-order-invariant. So we directly reuse it. -/

def permutedReachInvPred (σ : GadgetOrder) (sched : Surface3Sched)
    (s : State (permutedSchedCode σ sched)) : Prop :=
  s.E_tilde ∈ schedReachableE sched
    ((permutedSchedCode σ sched).C_budget - s.C) ∧
  s.C ≤ (permutedSchedCode σ sched).C_budget

theorem permutedReachInv_init (σ : GadgetOrder) (sched : Surface3Sched) :
    permutedReachInvPred σ sched (State.init (permutedSchedCode σ sched)) := by
  refine ⟨?_, ?_⟩
  · show (State.init (permutedSchedCode σ sched)).E_tilde ∈
          schedReachableE sched
            ((permutedSchedCode σ sched).C_budget -
              (State.init (permutedSchedCode σ sched)).C)
    have h1 : (State.init (permutedSchedCode σ sched)).E_tilde = ErrorVec.identity 9 := rfl
    have h2 : (permutedSchedCode σ sched).C_budget -
                (State.init (permutedSchedCode σ sched)).C = 0 := by
      show (permutedSchedCode σ sched).C_budget - (permutedSchedCode σ sched).C_budget = 0
      omega
    rw [h1, h2]
    show ErrorVec.identity 9 ∈ schedReachableE sched 0
    simp [schedReachableE]
  · show (State.init (permutedSchedCode σ sched)).C ≤ (permutedSchedCode σ sched).C_budget
    show (permutedSchedCode σ sched).C_budget ≤ (permutedSchedCode σ sched).C_budget
    omega

theorem permutedReachInv_preserve (σ : GadgetOrder) (sched : Surface3Sched)
    (s s' : State (permutedSchedCode σ sched))
    (h_inv : permutedReachInvPred σ sched s)
    (hstep : Step (permutedSchedCode σ sched) (.active s) (.active s')) :
    permutedReachInvPred σ sched s' := by
  obtain ⟨h_in, h_C⟩ := h_inv
  set n := (permutedSchedCode σ sched).C_budget - s.C with h_n_def
  cases hstep with
  | type0 _ i p hp _ =>
    refine ⟨?_, ?_⟩
    · have h_n' : (permutedSchedCode σ sched).C_budget - (s.C - 1) = n + 1 := by
        show (permutedSchedCode σ sched).C_budget - (s.C - 1) =
             ((permutedSchedCode σ sched).C_budget - s.C) + 1
        omega
      show ErrorVec.update s.E_tilde i p ∈
            schedReachableE sched ((permutedSchedCode σ sched).C_budget - (s.C - 1))
      rw [h_n']
      have hp_cases : p = .X ∨ p = .Y ∨ p = .Z := by
        cases p with
        | I => exact absurd rfl hp
        | X => left; rfl
        | Y => right; left; rfl
        | Z => right; right; rfl
      exact schedReachableE_t01 sched n s.E_tilde i p h_in hp_cases
    · show s.C - 1 ≤ (permutedSchedCode σ sched).C_budget; omega
  | type1 _ i p hp _ _ =>
    refine ⟨?_, ?_⟩
    · have h_n' : (permutedSchedCode σ sched).C_budget - (s.C - 1) = n + 1 := by
        show (permutedSchedCode σ sched).C_budget - (s.C - 1) =
             ((permutedSchedCode σ sched).C_budget - s.C) + 1
        omega
      show ErrorVec.update s.E_tilde i p ∈
            schedReachableE sched ((permutedSchedCode σ sched).C_budget - (s.C - 1))
      rw [h_n']
      have hp_cases : p = .X ∨ p = .Y ∨ p = .Z := by
        cases p with
        | I => exact absurd rfl hp
        | X => left; rfl
        | Y => right; left; rfl
        | Z => right; right; rfl
      exact schedReachableE_t01 sched n s.E_tilde i p h_in hp_cases
    · show s.C - 1 ≤ (permutedSchedCode σ sched).C_budget; omega
  | type2 _ e he _ _ =>
    refine ⟨?_, ?_⟩
    · -- e ∈ permutedBackActionSet σ sched s.coord.x = schedHooksAt sched (σ s.coord.x)
      have h_n' : (permutedSchedCode σ sched).C_budget - (s.C - 1) = n + 1 := by
        show (permutedSchedCode σ sched).C_budget - (s.C - 1) =
             ((permutedSchedCode σ sched).C_budget - s.C) + 1
        omega
      show ErrorVec.mul e s.E_tilde ∈
            schedReachableE sched ((permutedSchedCode σ sched).C_budget - (s.C - 1))
      rw [h_n']
      have h_e_in : e ∈ permutedHooksAt σ sched s.coord.x := he
      have h_e_in_all : e ∈ schedAllHooks sched :=
        permutedHooksAt_subset σ sched s.coord.x e h_e_in
      exact schedReachableE_t2 sched n s.E_tilde e h_in h_e_in_all
    · show s.C - 1 ≤ (permutedSchedCode σ sched).C_budget; omega
  | type3 _ _ =>
    refine ⟨?_, ?_⟩
    · have h_n' : (permutedSchedCode σ sched).C_budget - (s.C - 1) = n + 1 := by
        show (permutedSchedCode σ sched).C_budget - (s.C - 1) =
             ((permutedSchedCode σ sched).C_budget - s.C) + 1
        omega
      show s.E_tilde ∈
            schedReachableE sched ((permutedSchedCode σ sched).C_budget - (s.C - 1))
      rw [h_n']
      exact schedReachableE_mono sched n s.E_tilde h_in
    · show s.C - 1 ≤ (permutedSchedCode σ sched).C_budget; omega
  | measure _ nc _ =>
    refine ⟨?_, ?_⟩
    · show (measureStep (permutedSchedCode σ sched) s nc).E_tilde ∈
            schedReachableE sched
              ((permutedSchedCode σ sched).C_budget -
                (measureStep (permutedSchedCode σ sched) s nc).C)
      rw [measureStep_E_tilde, measureStep_C]
      exact h_in
    · show (measureStep (permutedSchedCode σ sched) s nc).C ≤
            (permutedSchedCode σ sched).C_budget
      rw [measureStep_C]; exact h_C

def permutedReachInv (σ : GadgetOrder) (sched : Surface3Sched) :
    Invariant (permutedSchedCode σ sched) where
  holds := permutedReachInvPred σ sched
  holds_init := permutedReachInv_init σ sched
  preservation := permutedReachInv_preserve σ sched

theorem permuted_etilde_in_reachableE (σ : GadgetOrder) (sched : Surface3Sched)
    (s : State (permutedSchedCode σ sched))
    (hreach : MultiStep (permutedSchedCode σ sched)
                (.active (State.init (permutedSchedCode σ sched))) (.active s)) :
    s.E_tilde ∈ schedReachableE sched
      ((permutedSchedCode σ sched).C_budget - s.C) :=
  ((permutedReachInv σ sched).holds_of_reachable s hreach).1

/-! ## Permutation invariance of `isSuccessState`

`isSuccessState E` checks parity vs `parametricStabilizers i` for all
`i : Fin 8`. Permuting via `σ` gives parity vs `parametricStabilizers (σ i)`
for all `i`, which is the same multiset (since `σ` is a bijection). -/

def permutedIsSuccessState (σ : GadgetOrder) (E : ErrorVec 9) : Bool :=
  ((List.finRange 8).all fun i =>
    ErrorVec.parity (permutedStabilizers σ i) E = false) &&
  ErrorVec.parity SurfaceD3.logicalZ E

theorem permutedIsSuccess_iff_canonical (σ : GadgetOrder) (E : ErrorVec 9) :
    permutedIsSuccessState σ E = isSuccessState E := by
  unfold permutedIsSuccessState isSuccessState permutedStabilizers
  congr 1
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  constructor
  · intro h_perm i _
    have := h_perm (σ.symm i) (List.mem_finRange _)
    simp at this ⊢
    exact this
  · intro h_canon i _
    have := h_canon (σ i) (List.mem_finRange _)
    simp at this ⊢
    exact this

/-! ## X-side gadget-permuted headline -/

theorem permuted_nonFailing_op_d_circ_ge_3 :
    ∀ (σ : GadgetOrder) (sched : Surface3Sched),
      classOf sched ≠ SchedClass.Failing →
      ∀ (s : State (permutedSchedCode σ sched)),
        MultiStep (permutedSchedCode σ sched)
          (.active (State.init (permutedSchedCode σ sched))) (.active s) →
        (permutedSchedCode σ sched).C_budget - s.C ≤ 2 →
        permutedIsSuccessState σ s.E_tilde = false := by
  intro σ sched h_not_failing s hreach hbudget
  rw [permutedIsSuccess_iff_canonical]
  have h_in : s.E_tilde ∈ schedReachableE sched
                ((permutedSchedCode σ sched).C_budget - s.C) :=
    permuted_etilde_in_reachableE σ sched s hreach
  have h_in_2 : s.E_tilde ∈ schedReachableE sched 2 := by
    rcases Nat.lt_or_ge ((permutedSchedCode σ sched).C_budget - s.C) 2 with hlt | hge
    · rcases Nat.lt_or_ge ((permutedSchedCode σ sched).C_budget - s.C) 1 with hlt' | hge'
      · have : (permutedSchedCode σ sched).C_budget - s.C = 0 := by omega
        rw [this] at h_in
        exact schedReachableE_mono sched _ _ (schedReachableE_mono sched _ _ h_in)
      · have : (permutedSchedCode σ sched).C_budget - s.C = 1 := by omega
        rw [this] at h_in
        exact schedReachableE_mono sched _ _ h_in
    · have : (permutedSchedCode σ sched).C_budget - s.C = 2 := by omega
      rw [this] at h_in
      exact h_in
  have h_check := schedReachableE_2_not_success_if_not_failing sched h_not_failing
  rw [List.all_eq_true] at h_check
  have := h_check s.E_tilde h_in_2
  simpa using this

/-! ## Z-side: gadget-permuted parametric code (mirror) -/

def permutedHooksAtZ (σ : GadgetOrder) (sched : Surface3Sched) (i : Fin 8) :
    List (ErrorVec 9) :=
  schedHooksAtZ sched (σ i)

def permutedBackActionSetZ (σ : GadgetOrder) (sched : Surface3Sched) (i : Fin 8) :
    Set (ErrorVec 9) :=
  fun e => e ∈ permutedHooksAtZ σ sched i

theorem permutedHooksAtZ_subset (σ : GadgetOrder) (sched : Surface3Sched) (i : Fin 8) :
    ∀ e ∈ permutedHooksAtZ σ sched i, e ∈ schedAllHooksZ sched := by
  intro e he
  exact schedHooksAtZ_subset sched (σ i) e he

def permutedSchedCodeZ (σ : GadgetOrder) (sched : Surface3Sched) : QECParams where
  n := 9; k := 1; d := 3; R := 1; numStab := 8
  stabilizers := permutedStabilizers σ
  backActionSet := permutedBackActionSetZ σ sched
  r := 3
  backAction_weight_bound := by
    intro stab_idx e he
    have h_e_in : e ∈ permutedHooksAtZ σ sched stab_idx := he
    have h_e_in_all : e ∈ schedAllHooksZ sched :=
      permutedHooksAtZ_subset σ sched stab_idx e h_e_in
    exact schedAllHooksZ_weight_bound sched e h_e_in_all
  C_budget := 2
  hn := by omega
  hns := by omega
  hR := by omega

def permutedReachInvPredZ (σ : GadgetOrder) (sched : Surface3Sched)
    (s : State (permutedSchedCodeZ σ sched)) : Prop :=
  s.E_tilde ∈ schedReachableEZ sched
    ((permutedSchedCodeZ σ sched).C_budget - s.C) ∧
  s.C ≤ (permutedSchedCodeZ σ sched).C_budget

theorem permutedReachInvZ_init (σ : GadgetOrder) (sched : Surface3Sched) :
    permutedReachInvPredZ σ sched (State.init (permutedSchedCodeZ σ sched)) := by
  refine ⟨?_, ?_⟩
  · show (State.init (permutedSchedCodeZ σ sched)).E_tilde ∈
          schedReachableEZ sched
            ((permutedSchedCodeZ σ sched).C_budget -
              (State.init (permutedSchedCodeZ σ sched)).C)
    have h1 : (State.init (permutedSchedCodeZ σ sched)).E_tilde = ErrorVec.identity 9 := rfl
    have h2 : (permutedSchedCodeZ σ sched).C_budget -
                (State.init (permutedSchedCodeZ σ sched)).C = 0 := by
      show (permutedSchedCodeZ σ sched).C_budget - (permutedSchedCodeZ σ sched).C_budget = 0
      omega
    rw [h1, h2]
    show ErrorVec.identity 9 ∈ schedReachableEZ sched 0
    simp [schedReachableEZ]
  · show (State.init (permutedSchedCodeZ σ sched)).C ≤ (permutedSchedCodeZ σ sched).C_budget
    show (permutedSchedCodeZ σ sched).C_budget ≤ (permutedSchedCodeZ σ sched).C_budget
    omega

theorem permutedReachInvZ_preserve (σ : GadgetOrder) (sched : Surface3Sched)
    (s s' : State (permutedSchedCodeZ σ sched))
    (h_inv : permutedReachInvPredZ σ sched s)
    (hstep : Step (permutedSchedCodeZ σ sched) (.active s) (.active s')) :
    permutedReachInvPredZ σ sched s' := by
  obtain ⟨h_in, h_C⟩ := h_inv
  set n := (permutedSchedCodeZ σ sched).C_budget - s.C with h_n_def
  cases hstep with
  | type0 _ i p hp _ =>
    refine ⟨?_, ?_⟩
    · have h_n' : (permutedSchedCodeZ σ sched).C_budget - (s.C - 1) = n + 1 := by
        show (permutedSchedCodeZ σ sched).C_budget - (s.C - 1) =
             ((permutedSchedCodeZ σ sched).C_budget - s.C) + 1
        omega
      show ErrorVec.update s.E_tilde i p ∈
            schedReachableEZ sched ((permutedSchedCodeZ σ sched).C_budget - (s.C - 1))
      rw [h_n']
      have hp_cases : p = .X ∨ p = .Y ∨ p = .Z := by
        cases p with
        | I => exact absurd rfl hp
        | X => left; rfl
        | Y => right; left; rfl
        | Z => right; right; rfl
      exact schedReachableEZ_t01 sched n s.E_tilde i p h_in hp_cases
    · show s.C - 1 ≤ (permutedSchedCodeZ σ sched).C_budget; omega
  | type1 _ i p hp _ _ =>
    refine ⟨?_, ?_⟩
    · have h_n' : (permutedSchedCodeZ σ sched).C_budget - (s.C - 1) = n + 1 := by
        show (permutedSchedCodeZ σ sched).C_budget - (s.C - 1) =
             ((permutedSchedCodeZ σ sched).C_budget - s.C) + 1
        omega
      show ErrorVec.update s.E_tilde i p ∈
            schedReachableEZ sched ((permutedSchedCodeZ σ sched).C_budget - (s.C - 1))
      rw [h_n']
      have hp_cases : p = .X ∨ p = .Y ∨ p = .Z := by
        cases p with
        | I => exact absurd rfl hp
        | X => left; rfl
        | Y => right; left; rfl
        | Z => right; right; rfl
      exact schedReachableEZ_t01 sched n s.E_tilde i p h_in hp_cases
    · show s.C - 1 ≤ (permutedSchedCodeZ σ sched).C_budget; omega
  | type2 _ e he _ _ =>
    refine ⟨?_, ?_⟩
    · have h_n' : (permutedSchedCodeZ σ sched).C_budget - (s.C - 1) = n + 1 := by
        show (permutedSchedCodeZ σ sched).C_budget - (s.C - 1) =
             ((permutedSchedCodeZ σ sched).C_budget - s.C) + 1
        omega
      show ErrorVec.mul e s.E_tilde ∈
            schedReachableEZ sched ((permutedSchedCodeZ σ sched).C_budget - (s.C - 1))
      rw [h_n']
      have h_e_in : e ∈ permutedHooksAtZ σ sched s.coord.x := he
      have h_e_in_all : e ∈ schedAllHooksZ sched :=
        permutedHooksAtZ_subset σ sched s.coord.x e h_e_in
      exact schedReachableEZ_t2 sched n s.E_tilde e h_in h_e_in_all
    · show s.C - 1 ≤ (permutedSchedCodeZ σ sched).C_budget; omega
  | type3 _ _ =>
    refine ⟨?_, ?_⟩
    · have h_n' : (permutedSchedCodeZ σ sched).C_budget - (s.C - 1) = n + 1 := by
        show (permutedSchedCodeZ σ sched).C_budget - (s.C - 1) =
             ((permutedSchedCodeZ σ sched).C_budget - s.C) + 1
        omega
      show s.E_tilde ∈
            schedReachableEZ sched ((permutedSchedCodeZ σ sched).C_budget - (s.C - 1))
      rw [h_n']
      exact schedReachableEZ_mono sched n s.E_tilde h_in
    · show s.C - 1 ≤ (permutedSchedCodeZ σ sched).C_budget; omega
  | measure _ nc _ =>
    refine ⟨?_, ?_⟩
    · show (measureStep (permutedSchedCodeZ σ sched) s nc).E_tilde ∈
            schedReachableEZ sched
              ((permutedSchedCodeZ σ sched).C_budget -
                (measureStep (permutedSchedCodeZ σ sched) s nc).C)
      rw [measureStep_E_tilde, measureStep_C]
      exact h_in
    · show (measureStep (permutedSchedCodeZ σ sched) s nc).C ≤
            (permutedSchedCodeZ σ sched).C_budget
      rw [measureStep_C]; exact h_C

def permutedReachInvZ (σ : GadgetOrder) (sched : Surface3Sched) :
    Invariant (permutedSchedCodeZ σ sched) where
  holds := permutedReachInvPredZ σ sched
  holds_init := permutedReachInvZ_init σ sched
  preservation := permutedReachInvZ_preserve σ sched

theorem permuted_etilde_in_reachableEZ (σ : GadgetOrder) (sched : Surface3Sched)
    (s : State (permutedSchedCodeZ σ sched))
    (hreach : MultiStep (permutedSchedCodeZ σ sched)
                (.active (State.init (permutedSchedCodeZ σ sched))) (.active s)) :
    s.E_tilde ∈ schedReachableEZ sched
      ((permutedSchedCodeZ σ sched).C_budget - s.C) :=
  ((permutedReachInvZ σ sched).holds_of_reachable s hreach).1

def permutedIsSuccessStateZ (σ : GadgetOrder) (E : ErrorVec 9) : Bool :=
  ((List.finRange 8).all fun i =>
    ErrorVec.parity (permutedStabilizers σ i) E = false) &&
  ErrorVec.parity SurfaceD3.logicalX E

theorem permutedIsSuccessZ_iff_canonical (σ : GadgetOrder) (E : ErrorVec 9) :
    permutedIsSuccessStateZ σ E = isSuccessStateZ E := by
  unfold permutedIsSuccessStateZ isSuccessStateZ permutedStabilizers
  congr 1
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  constructor
  · intro h_perm i _
    have := h_perm (σ.symm i) (List.mem_finRange _)
    simp at this ⊢
    exact this
  · intro h_canon i _
    have := h_canon (σ i) (List.mem_finRange _)
    simp at this ⊢
    exact this

theorem permutedZ_nonFailing_op_d_circ_ge_3 :
    ∀ (σ : GadgetOrder) (sched : Surface3Sched),
      classOfZ sched ≠ SchedClass.Failing →
      ∀ (s : State (permutedSchedCodeZ σ sched)),
        MultiStep (permutedSchedCodeZ σ sched)
          (.active (State.init (permutedSchedCodeZ σ sched))) (.active s) →
        (permutedSchedCodeZ σ sched).C_budget - s.C ≤ 2 →
        permutedIsSuccessStateZ σ s.E_tilde = false := by
  intro σ sched h_not_failing s hreach hbudget
  rw [permutedIsSuccessZ_iff_canonical]
  have h_in : s.E_tilde ∈ schedReachableEZ sched
                ((permutedSchedCodeZ σ sched).C_budget - s.C) :=
    permuted_etilde_in_reachableEZ σ sched s hreach
  have h_in_2 : s.E_tilde ∈ schedReachableEZ sched 2 := by
    rcases Nat.lt_or_ge ((permutedSchedCodeZ σ sched).C_budget - s.C) 2 with hlt | hge
    · rcases Nat.lt_or_ge ((permutedSchedCodeZ σ sched).C_budget - s.C) 1 with hlt' | hge'
      · have : (permutedSchedCodeZ σ sched).C_budget - s.C = 0 := by omega
        rw [this] at h_in
        exact schedReachableEZ_mono sched _ _ (schedReachableEZ_mono sched _ _ h_in)
      · have : (permutedSchedCodeZ σ sched).C_budget - s.C = 1 := by omega
        rw [this] at h_in
        exact schedReachableEZ_mono sched _ _ h_in
    · have : (permutedSchedCodeZ σ sched).C_budget - s.C = 2 := by omega
      rw [this] at h_in
      exact h_in
  have h_check := schedReachableEZ_2_not_success_if_not_failing sched h_not_failing
  rw [List.all_eq_true] at h_check
  have := h_check s.E_tilde h_in_2
  simpa using this

end QStab.Paper.SurfaceD3GadgetOrderInvariance
