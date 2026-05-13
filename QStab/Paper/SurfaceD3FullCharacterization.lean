import QStab.Paper.SurfaceD3JointXZ
import QStab.Paper.SurfaceD3GadgetOrderInvariance
import QStab.MultiStep
import QStab.Invariant
import Mathlib.GroupTheory.Perm.Basic

/-!
# Full d=3 surface scheduling characterisation (joint × gadget order × logicals)

This file is the capstone of the d=3 surface scheduling pipeline.

## Total scope

  Scheduling space = (X-CX orderings) × (Z-CX orderings) × (gadget orders)
                   = 2304 × 2304 × 8!
                   = 213,909,504,000  (≈ 2.14 × 10¹¹) scheduling triples.

For each scheduling triple, the theorem rules out as 2-fault-reachable
the entire set `N(S) \ S` of non-trivial logical-error vectors —
that is, all 3 × 2^numStab = 3 × 256 = 768 distinct `ErrorVec 9` values
that act as a non-trivial logical operation.

Concretely, `N(S) \ S` decomposes into three cosets (since k = 1):

  * `L_X · S` — 256 representatives that act as logical X̄ (e.g.
    `X{0,3,6}`, `X{1,3,6}` = `X{0,3,6} · s5`, …)
  * `L_Z · S` — 256 representatives that act as logical Z̄ (e.g.
    `Z{0,1,2}`, `Z{0,1,2} · s1`, …)
  * `L_Y · S` — 256 representatives that act as logical Ȳ = X̄ · Z̄.

The success predicate `isSuccessStateFull` is **exactly** the
characteristic predicate of `N(S) \ S`:

  (parity vs all 8 stabs zero) ∧ (L_X parity ∨ L_Z parity)

  = (E ∈ N(S))                ∧ (E ∉ S)

so a single `isSuccessStateFull E = false` rules out membership of `E`
in any of the 768 non-trivial logical-error vectors.

## Headline statement

For ANY:
  * X-CX ordering `sched.1 : Surface3Sched` (one of 2304),
  * Z-CX ordering `sched.2 : Surface3Sched` (one of 2304),
  * Gadget order `σ : GadgetOrder = Equiv.Perm (Fin 8)` (one of 40320),

if the X-CX side is non-Failing under `classOf` AND the Z-CX side is
non-Failing under `classOfZ`, then NO `ErrorVec 9` reachable as a
2-fault product in `fullSchedCode σ sched` is in `N(S) \ S`. Hence
`d_circ ≥ 3` for that scheduling triple, against the entire non-trivial
logical group.

## The fully-general code

`fullSchedCode σ schedFull` has:
  * Stabilisers indexed by `Fin 8`, with stab at index `i` =
    `parametricStabilizers (σ i)`.
  * Back-action set at index `i` = X-hooks of `schedFull.1` at physical
    stab `σ i`, ∪ Z-hooks of `schedFull.2` at physical stab `σ i`.

This composes:
  * Cartesian product `X-CX × Z-CX = Surface3SchedFull` from
    `SurfaceD3JointXZ`.
  * Gadget order σ : `Equiv.Perm (Fin 8)` from
    `SurfaceD3GadgetOrderInvariance`.

## Proof structure

The bridge invariant tracks `xPart(s.E_tilde) ∈ schedReachableE sched.1`
and `zPart(s.E_tilde) ∈ schedReachableEZ sched.2`, both of which are
gadget-order-invariant (defined via `schedAllHooks` / `schedAllHooksZ`,
which are unions). The Type-2 case uses `permutedHooksAt σ` and
`permutedHooksAtZ σ`, which are still subsets of the respective
all-hooks unions. The success predicate `isSuccessStateFull` is
permutation-invariant via the same multiset argument as the X-side.

**Zero `sorry`. Standard axioms only.**
-/

namespace QStab.Paper.SurfaceD3FullCharacterization

open QStab QStab.Examples QStab.Examples.SurfaceD3
     QStab.Paper.SurfaceD3Classification
     QStab.Paper.SurfaceD3OperationalIffParam
     QStab.Paper.SurfaceD3OperationalIffParamZ
     QStab.Paper.SurfaceD3JointXZ
     QStab.Paper.SurfaceD3GadgetOrderInvariance

/-! ## Fully-general code -/

def fullHooksAt (σ : GadgetOrder) (sched : Surface3SchedFull) (i : Fin 8) :
    List (ErrorVec 9) :=
  schedHooksAt sched.1 (σ i) ++ schedHooksAtZ sched.2 (σ i)

def fullBackActionSet (σ : GadgetOrder) (sched : Surface3SchedFull) (i : Fin 8) :
    Set (ErrorVec 9) :=
  fun e => e ∈ fullHooksAt σ sched i

theorem fullHooksAt_subset_X (σ : GadgetOrder) (sched : Surface3SchedFull) (i : Fin 8) :
    ∀ e ∈ schedHooksAt sched.1 (σ i), e ∈ schedAllHooks sched.1 := by
  intro e he
  exact schedHooksAt_subset sched.1 (σ i) e he

theorem fullHooksAt_subset_Z (σ : GadgetOrder) (sched : Surface3SchedFull) (i : Fin 8) :
    ∀ e ∈ schedHooksAtZ sched.2 (σ i), e ∈ schedAllHooksZ sched.2 := by
  intro e he
  exact schedHooksAtZ_subset sched.2 (σ i) e he

theorem fullHooksAt_weight_bound (σ : GadgetOrder) (sched : Surface3SchedFull) (i : Fin 8) :
    ∀ e ∈ fullHooksAt σ sched i, ErrorVec.weight e ≤ 3 := by
  intro e he
  rcases List.mem_append.mp he with h_x | h_z
  · exact schedAllHooks_weight_bound sched.1 e (fullHooksAt_subset_X σ sched i e h_x)
  · exact schedAllHooksZ_weight_bound sched.2 e (fullHooksAt_subset_Z σ sched i e h_z)

def fullSchedCode (σ : GadgetOrder) (sched : Surface3SchedFull) : QECParams where
  n := 9; k := 1; d := 3; R := 1; numStab := 8
  stabilizers := permutedStabilizers σ
  backActionSet := fullBackActionSet σ sched
  r := 3
  backAction_weight_bound := by
    intro stab_idx e he
    exact fullHooksAt_weight_bound σ sched stab_idx e he
  C_budget := 2
  hn := by omega
  hns := by omega
  hR := by omega

/-! ## Joint bridge invariant for the fully-general code -/

def fullBridgePred (σ : GadgetOrder) (sched : Surface3SchedFull)
    (s : State (fullSchedCode σ sched)) : Prop :=
  xPartE s.E_tilde ∈ schedReachableE sched.1
    ((fullSchedCode σ sched).C_budget - s.C) ∧
  zPartE s.E_tilde ∈ schedReachableEZ sched.2
    ((fullSchedCode σ sched).C_budget - s.C) ∧
  s.C ≤ (fullSchedCode σ sched).C_budget

theorem fullBridge_init (σ : GadgetOrder) (sched : Surface3SchedFull) :
    fullBridgePred σ sched (State.init (fullSchedCode σ sched)) := by
  refine ⟨?_, ?_, ?_⟩
  · show xPartE (State.init (fullSchedCode σ sched)).E_tilde ∈
        schedReachableE sched.1
          ((fullSchedCode σ sched).C_budget - (State.init (fullSchedCode σ sched)).C)
    have h1 : (State.init (fullSchedCode σ sched)).E_tilde = ErrorVec.identity 9 := rfl
    have h2 : (fullSchedCode σ sched).C_budget -
                (State.init (fullSchedCode σ sched)).C = 0 := by
      show (fullSchedCode σ sched).C_budget - (fullSchedCode σ sched).C_budget = 0
      omega
    rw [h1, h2]
    show ErrorVec.identity 9 ∈ schedReachableE sched.1 0
    simp [schedReachableE]
  · show zPartE (State.init (fullSchedCode σ sched)).E_tilde ∈
        schedReachableEZ sched.2
          ((fullSchedCode σ sched).C_budget - (State.init (fullSchedCode σ sched)).C)
    have h1 : (State.init (fullSchedCode σ sched)).E_tilde = ErrorVec.identity 9 := rfl
    have h2 : (fullSchedCode σ sched).C_budget -
                (State.init (fullSchedCode σ sched)).C = 0 := by
      show (fullSchedCode σ sched).C_budget - (fullSchedCode σ sched).C_budget = 0
      omega
    rw [h1, h2]
    show ErrorVec.identity 9 ∈ schedReachableEZ sched.2 0
    simp [schedReachableEZ]
  · show (State.init (fullSchedCode σ sched)).C ≤ (fullSchedCode σ sched).C_budget
    show (fullSchedCode σ sched).C_budget ≤ (fullSchedCode σ sched).C_budget
    omega

theorem fullBridge_preserve (σ : GadgetOrder) (sched : Surface3SchedFull)
    (s s' : State (fullSchedCode σ sched))
    (h_inv : fullBridgePred σ sched s)
    (hstep : Step (fullSchedCode σ sched) (.active s) (.active s')) :
    fullBridgePred σ sched s' := by
  obtain ⟨h_in_x, h_in_z, h_C⟩ := h_inv
  set n := (fullSchedCode σ sched).C_budget - s.C with h_n_def
  cases hstep with
  | type0 _ i p hp _ =>
    refine ⟨?_, ?_, ?_⟩
    · have h_n' : (fullSchedCode σ sched).C_budget - (s.C - 1) = n + 1 := by
        show (fullSchedCode σ sched).C_budget - (s.C - 1) =
             ((fullSchedCode σ sched).C_budget - s.C) + 1
        omega
      show xPartE (ErrorVec.update s.E_tilde i p) ∈
            schedReachableE sched.1 ((fullSchedCode σ sched).C_budget - (s.C - 1))
      rw [h_n', xPartE_update]
      cases p with
      | I => exact absurd rfl hp
      | X =>
        exact schedReachableE_t01 sched.1 n (xPartE s.E_tilde) i .X h_in_x (Or.inl rfl)
      | Y =>
        exact schedReachableE_t01 sched.1 n (xPartE s.E_tilde) i .X h_in_x (Or.inl rfl)
      | Z =>
        show ErrorVec.update (xPartE s.E_tilde) i .I ∈ schedReachableE sched.1 (n+1)
        have h_eq : ErrorVec.update (xPartE s.E_tilde) i .I = xPartE s.E_tilde := by
          funext j
          unfold ErrorVec.update
          by_cases h : j = i
          · subst h; simp [Pauli.mul]
          · simp [Function.update_of_ne h]
        rw [h_eq]
        exact schedReachableE_mono sched.1 n (xPartE s.E_tilde) h_in_x
    · have h_n' : (fullSchedCode σ sched).C_budget - (s.C - 1) = n + 1 := by
        show (fullSchedCode σ sched).C_budget - (s.C - 1) =
             ((fullSchedCode σ sched).C_budget - s.C) + 1
        omega
      show zPartE (ErrorVec.update s.E_tilde i p) ∈
            schedReachableEZ sched.2 ((fullSchedCode σ sched).C_budget - (s.C - 1))
      rw [h_n', zPartE_update]
      cases p with
      | I => exact absurd rfl hp
      | X =>
        show ErrorVec.update (zPartE s.E_tilde) i .I ∈ schedReachableEZ sched.2 (n+1)
        have h_eq : ErrorVec.update (zPartE s.E_tilde) i .I = zPartE s.E_tilde := by
          funext j
          unfold ErrorVec.update
          by_cases h : j = i
          · subst h; simp [Pauli.mul]
          · simp [Function.update_of_ne h]
        rw [h_eq]
        exact schedReachableEZ_mono sched.2 n (zPartE s.E_tilde) h_in_z
      | Y =>
        exact schedReachableEZ_t01 sched.2 n (zPartE s.E_tilde) i .Z h_in_z (Or.inr (Or.inr rfl))
      | Z =>
        exact schedReachableEZ_t01 sched.2 n (zPartE s.E_tilde) i .Z h_in_z (Or.inr (Or.inr rfl))
    · show s.C - 1 ≤ (fullSchedCode σ sched).C_budget; omega
  | type1 _ i p hp _ _ =>
    refine ⟨?_, ?_, ?_⟩
    · have h_n' : (fullSchedCode σ sched).C_budget - (s.C - 1) = n + 1 := by
        show (fullSchedCode σ sched).C_budget - (s.C - 1) =
             ((fullSchedCode σ sched).C_budget - s.C) + 1
        omega
      show xPartE (ErrorVec.update s.E_tilde i p) ∈
            schedReachableE sched.1 ((fullSchedCode σ sched).C_budget - (s.C - 1))
      rw [h_n', xPartE_update]
      cases p with
      | I => exact absurd rfl hp
      | X =>
        exact schedReachableE_t01 sched.1 n (xPartE s.E_tilde) i .X h_in_x (Or.inl rfl)
      | Y =>
        exact schedReachableE_t01 sched.1 n (xPartE s.E_tilde) i .X h_in_x (Or.inl rfl)
      | Z =>
        show ErrorVec.update (xPartE s.E_tilde) i .I ∈ schedReachableE sched.1 (n+1)
        have h_eq : ErrorVec.update (xPartE s.E_tilde) i .I = xPartE s.E_tilde := by
          funext j
          unfold ErrorVec.update
          by_cases h : j = i
          · subst h; simp [Pauli.mul]
          · simp [Function.update_of_ne h]
        rw [h_eq]
        exact schedReachableE_mono sched.1 n (xPartE s.E_tilde) h_in_x
    · have h_n' : (fullSchedCode σ sched).C_budget - (s.C - 1) = n + 1 := by
        show (fullSchedCode σ sched).C_budget - (s.C - 1) =
             ((fullSchedCode σ sched).C_budget - s.C) + 1
        omega
      show zPartE (ErrorVec.update s.E_tilde i p) ∈
            schedReachableEZ sched.2 ((fullSchedCode σ sched).C_budget - (s.C - 1))
      rw [h_n', zPartE_update]
      cases p with
      | I => exact absurd rfl hp
      | X =>
        show ErrorVec.update (zPartE s.E_tilde) i .I ∈ schedReachableEZ sched.2 (n+1)
        have h_eq : ErrorVec.update (zPartE s.E_tilde) i .I = zPartE s.E_tilde := by
          funext j
          unfold ErrorVec.update
          by_cases h : j = i
          · subst h; simp [Pauli.mul]
          · simp [Function.update_of_ne h]
        rw [h_eq]
        exact schedReachableEZ_mono sched.2 n (zPartE s.E_tilde) h_in_z
      | Y =>
        exact schedReachableEZ_t01 sched.2 n (zPartE s.E_tilde) i .Z h_in_z (Or.inr (Or.inr rfl))
      | Z =>
        exact schedReachableEZ_t01 sched.2 n (zPartE s.E_tilde) i .Z h_in_z (Or.inr (Or.inr rfl))
    · show s.C - 1 ≤ (fullSchedCode σ sched).C_budget; omega
  | type2 _ e he _ _ =>
    refine ⟨?_, ?_, ?_⟩
    · have h_n' : (fullSchedCode σ sched).C_budget - (s.C - 1) = n + 1 := by
        show (fullSchedCode σ sched).C_budget - (s.C - 1) =
             ((fullSchedCode σ sched).C_budget - s.C) + 1
        omega
      show xPartE (ErrorVec.mul e s.E_tilde) ∈
            schedReachableE sched.1 ((fullSchedCode σ sched).C_budget - (s.C - 1))
      rw [h_n', xPartE_mul]
      have h_e_in : e ∈ fullHooksAt σ sched s.coord.x := he
      have h_e_in' : e ∈ schedHooksAt sched.1 (σ s.coord.x) ++
                          schedHooksAtZ sched.2 (σ s.coord.x) := h_e_in
      rcases List.mem_append.mp h_e_in' with h_x | h_z
      · -- X-hook: xPartE e = e
        have h_xonly : ∀ j, e j = .X ∨ e j = .I := schedHooksAt_xOnly sched.1 _ e h_x
        have h_xPart_eq : xPartE e = e := xOnly_implies_xPartE_self e h_xonly
        rw [h_xPart_eq]
        have h_e_all : e ∈ schedAllHooks sched.1 :=
          schedHooksAt_subset sched.1 (σ s.coord.x) e h_x
        exact schedReachableE_t2 sched.1 n (xPartE s.E_tilde) e h_in_x h_e_all
      · -- Z-hook: xPartE e = identity
        have h_zonly : ∀ j, e j = .Z ∨ e j = .I := schedHooksAtZ_zOnly sched.2 _ e h_z
        have h_xPart_eq : xPartE e = ErrorVec.identity 9 :=
          zOnly_implies_xPartE_identity e h_zonly
        rw [h_xPart_eq]
        show ErrorVec.mul (ErrorVec.identity 9) (xPartE s.E_tilde) ∈ schedReachableE sched.1 (n+1)
        have h_id_mul : ErrorVec.mul (ErrorVec.identity 9) (xPartE s.E_tilde) =
                        xPartE s.E_tilde := by
          funext j
          show Pauli.mul Pauli.I (xPartE s.E_tilde j) = xPartE s.E_tilde j
          cases xPartE s.E_tilde j <;> rfl
        rw [h_id_mul]
        exact schedReachableE_mono sched.1 n (xPartE s.E_tilde) h_in_x
    · have h_n' : (fullSchedCode σ sched).C_budget - (s.C - 1) = n + 1 := by
        show (fullSchedCode σ sched).C_budget - (s.C - 1) =
             ((fullSchedCode σ sched).C_budget - s.C) + 1
        omega
      show zPartE (ErrorVec.mul e s.E_tilde) ∈
            schedReachableEZ sched.2 ((fullSchedCode σ sched).C_budget - (s.C - 1))
      rw [h_n', zPartE_mul]
      have h_e_in : e ∈ fullHooksAt σ sched s.coord.x := he
      have h_e_in' : e ∈ schedHooksAt sched.1 (σ s.coord.x) ++
                          schedHooksAtZ sched.2 (σ s.coord.x) := h_e_in
      rcases List.mem_append.mp h_e_in' with h_x | h_z
      · -- X-hook: zPartE e = identity
        have h_xonly : ∀ j, e j = .X ∨ e j = .I := schedHooksAt_xOnly sched.1 _ e h_x
        have h_zPart_eq : zPartE e = ErrorVec.identity 9 :=
          xOnly_implies_zPartE_identity e h_xonly
        rw [h_zPart_eq]
        show ErrorVec.mul (ErrorVec.identity 9) (zPartE s.E_tilde) ∈ schedReachableEZ sched.2 (n+1)
        have h_id_mul : ErrorVec.mul (ErrorVec.identity 9) (zPartE s.E_tilde) =
                        zPartE s.E_tilde := by
          funext j
          show Pauli.mul Pauli.I (zPartE s.E_tilde j) = zPartE s.E_tilde j
          cases zPartE s.E_tilde j <;> rfl
        rw [h_id_mul]
        exact schedReachableEZ_mono sched.2 n (zPartE s.E_tilde) h_in_z
      · -- Z-hook: zPartE e = e
        have h_zonly : ∀ j, e j = .Z ∨ e j = .I := schedHooksAtZ_zOnly sched.2 _ e h_z
        have h_zPart_eq : zPartE e = e := zOnly_implies_zPartE_self e h_zonly
        rw [h_zPart_eq]
        have h_e_all : e ∈ schedAllHooksZ sched.2 :=
          schedHooksAtZ_subset sched.2 (σ s.coord.x) e h_z
        exact schedReachableEZ_t2 sched.2 n (zPartE s.E_tilde) e h_in_z h_e_all
    · show s.C - 1 ≤ (fullSchedCode σ sched).C_budget; omega
  | type3 _ _ =>
    refine ⟨?_, ?_, ?_⟩
    · have h_n' : (fullSchedCode σ sched).C_budget - (s.C - 1) = n + 1 := by
        show (fullSchedCode σ sched).C_budget - (s.C - 1) =
             ((fullSchedCode σ sched).C_budget - s.C) + 1
        omega
      show xPartE s.E_tilde ∈ schedReachableE sched.1
              ((fullSchedCode σ sched).C_budget - (s.C - 1))
      rw [h_n']
      exact schedReachableE_mono sched.1 n (xPartE s.E_tilde) h_in_x
    · have h_n' : (fullSchedCode σ sched).C_budget - (s.C - 1) = n + 1 := by
        show (fullSchedCode σ sched).C_budget - (s.C - 1) =
             ((fullSchedCode σ sched).C_budget - s.C) + 1
        omega
      show zPartE s.E_tilde ∈ schedReachableEZ sched.2
              ((fullSchedCode σ sched).C_budget - (s.C - 1))
      rw [h_n']
      exact schedReachableEZ_mono sched.2 n (zPartE s.E_tilde) h_in_z
    · show s.C - 1 ≤ (fullSchedCode σ sched).C_budget; omega
  | measure _ nc _ =>
    refine ⟨?_, ?_, ?_⟩
    · show xPartE (measureStep (fullSchedCode σ sched) s nc).E_tilde ∈
            schedReachableE sched.1
              ((fullSchedCode σ sched).C_budget -
                (measureStep (fullSchedCode σ sched) s nc).C)
      rw [measureStep_E_tilde, measureStep_C]
      exact h_in_x
    · show zPartE (measureStep (fullSchedCode σ sched) s nc).E_tilde ∈
            schedReachableEZ sched.2
              ((fullSchedCode σ sched).C_budget -
                (measureStep (fullSchedCode σ sched) s nc).C)
      rw [measureStep_E_tilde, measureStep_C]
      exact h_in_z
    · show (measureStep (fullSchedCode σ sched) s nc).C ≤
            (fullSchedCode σ sched).C_budget
      rw [measureStep_C]; exact h_C

def fullBridgeInv (σ : GadgetOrder) (sched : Surface3SchedFull) :
    Invariant (fullSchedCode σ sched) where
  holds := fullBridgePred σ sched
  holds_init := fullBridge_init σ sched
  preservation := fullBridge_preserve σ sched

theorem full_xPart_in_X_reachable (σ : GadgetOrder) (sched : Surface3SchedFull)
    (s : State (fullSchedCode σ sched))
    (hreach : MultiStep (fullSchedCode σ sched)
                (.active (State.init (fullSchedCode σ sched))) (.active s)) :
    xPartE s.E_tilde ∈ schedReachableE sched.1
      ((fullSchedCode σ sched).C_budget - s.C) :=
  ((fullBridgeInv σ sched).holds_of_reachable s hreach).1

theorem full_zPart_in_Z_reachable (σ : GadgetOrder) (sched : Surface3SchedFull)
    (s : State (fullSchedCode σ sched))
    (hreach : MultiStep (fullSchedCode σ sched)
                (.active (State.init (fullSchedCode σ sched))) (.active s)) :
    zPartE s.E_tilde ∈ schedReachableEZ sched.2
      ((fullSchedCode σ sched).C_budget - s.C) :=
  ((fullBridgeInv σ sched).holds_of_reachable s hreach).2.1

/-! ## Joint success predicate (under gadget permutation) -/

def fullIsSuccessState (σ : GadgetOrder) (E : ErrorVec 9) : Bool :=
  ((List.finRange 8).all fun i =>
    ErrorVec.parity (permutedStabilizers σ i) E = false) &&
  (ErrorVec.parity SurfaceD3.logicalZ E ||
   ErrorVec.parity SurfaceD3.logicalX E)

theorem fullIsSuccess_iff_canonical (σ : GadgetOrder) (E : ErrorVec 9) :
    fullIsSuccessState σ E = isSuccessStateFull E := by
  unfold fullIsSuccessState isSuccessStateFull permutedStabilizers
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

/-! ## The capstone theorem -/

/-- **Full d=3 surface scheduling characterisation.**

    For ANY:
      * X-CX ordering `sched.1 : Surface3Sched` (one of 2304),
      * Z-CX ordering `sched.2 : Surface3Sched` (one of 2304),
      * Gadget order `σ : GadgetOrder = Equiv.Perm (Fin 8)` (one of 40320),
    if the X-CX side is non-Failing under `classOf` AND the Z-CX side
    is non-Failing under `classOfZ`, then no `ErrorVec 9` reachable as
    a 2-fault product in `fullSchedCode σ sched` lies in `N(S) \ S`.

    Equivalently, for every reachable 2-fault `E_tilde`,

      ¬ (E_tilde ∈ N(S) ∧ E_tilde ∉ S),

    which excludes all 768 = 3 × 2^numStab representatives of the three
    non-trivial logical cosets `L_X · S`, `L_Z · S`, `L_Y · S` (i.e. the
    full non-trivial logical Pauli group of the [[9,1,3]] code).

    Total scope:
      * Scheduling triples: 2304 × 2304 × 8! ≈ 2.14 × 10¹¹.
      * Logical-error coverage per triple: full `N(S) \ S` (768 vectors).

    Proof reduces, via the bridge invariant + `xPart`/`zPart`
    decomposition, to two prior native-decide finite checks (each over
    2304 schedulings):
      * `schedReachableE_2_not_success_if_not_failing` (X-side, 2304 cases)
      * `schedReachableEZ_2_not_success_if_not_failing` (Z-side, 2304 cases)
    Combined with permutation invariance of the success predicate
    (same multiset of stabilisers under `σ`).

    No additional finite checks are needed for the gadget-order or
    Cartesian-product extension; their treatment is purely structural
    via the bridge invariant. -/
theorem full_nonFailing_op_d_circ_ge_3 :
    ∀ (σ : GadgetOrder) (sched : Surface3SchedFull),
      classOf sched.1 ≠ SchedClass.Failing →
      classOfZ sched.2 ≠ SchedClass.Failing →
      ∀ (s : State (fullSchedCode σ sched)),
        MultiStep (fullSchedCode σ sched)
          (.active (State.init (fullSchedCode σ sched))) (.active s) →
        (fullSchedCode σ sched).C_budget - s.C ≤ 2 →
        fullIsSuccessState σ s.E_tilde = false := by
  intro σ sched h_X_nf h_Z_nf s hreach hbudget
  rw [fullIsSuccess_iff_canonical]
  -- xPart in X-side reachable
  have h_x_in : xPartE s.E_tilde ∈ schedReachableE sched.1
                  ((fullSchedCode σ sched).C_budget - s.C) :=
    full_xPart_in_X_reachable σ sched s hreach
  have h_x_in_2 : xPartE s.E_tilde ∈ schedReachableE sched.1 2 := by
    rcases Nat.lt_or_ge ((fullSchedCode σ sched).C_budget - s.C) 2 with hlt | hge
    · rcases Nat.lt_or_ge ((fullSchedCode σ sched).C_budget - s.C) 1 with hlt' | hge'
      · have : (fullSchedCode σ sched).C_budget - s.C = 0 := by omega
        rw [this] at h_x_in
        exact schedReachableE_mono sched.1 _ _ (schedReachableE_mono sched.1 _ _ h_x_in)
      · have : (fullSchedCode σ sched).C_budget - s.C = 1 := by omega
        rw [this] at h_x_in
        exact schedReachableE_mono sched.1 _ _ h_x_in
    · have : (fullSchedCode σ sched).C_budget - s.C = 2 := by omega
      rw [this] at h_x_in
      exact h_x_in
  have h_z_in : zPartE s.E_tilde ∈ schedReachableEZ sched.2
                  ((fullSchedCode σ sched).C_budget - s.C) :=
    full_zPart_in_Z_reachable σ sched s hreach
  have h_z_in_2 : zPartE s.E_tilde ∈ schedReachableEZ sched.2 2 := by
    rcases Nat.lt_or_ge ((fullSchedCode σ sched).C_budget - s.C) 2 with hlt | hge
    · rcases Nat.lt_or_ge ((fullSchedCode σ sched).C_budget - s.C) 1 with hlt' | hge'
      · have : (fullSchedCode σ sched).C_budget - s.C = 0 := by omega
        rw [this] at h_z_in
        exact schedReachableEZ_mono sched.2 _ _ (schedReachableEZ_mono sched.2 _ _ h_z_in)
      · have : (fullSchedCode σ sched).C_budget - s.C = 1 := by omega
        rw [this] at h_z_in
        exact schedReachableEZ_mono sched.2 _ _ h_z_in
    · have : (fullSchedCode σ sched).C_budget - s.C = 2 := by omega
      rw [this] at h_z_in
      exact h_z_in
  have h_x_check := schedReachableE_2_not_success_if_not_failing sched.1 h_X_nf
  rw [List.all_eq_true] at h_x_check
  have h_x_no := h_x_check (xPartE s.E_tilde) h_x_in_2
  simp at h_x_no
  have h_z_check := schedReachableEZ_2_not_success_if_not_failing sched.2 h_Z_nf
  rw [List.all_eq_true] at h_z_check
  have h_z_no := h_z_check (zPartE s.E_tilde) h_z_in_2
  simp at h_z_no
  unfold isSuccessStateFull
  by_contra h_succ
  have h_succ_true : (((List.finRange 8).all fun i =>
        ErrorVec.parity (parametricStabilizers i) s.E_tilde = false) &&
      (ErrorVec.parity SurfaceD3.logicalZ s.E_tilde ||
       ErrorVec.parity SurfaceD3.logicalX s.E_tilde)) = true := by
    cases hh : (((List.finRange 8).all fun i =>
        ErrorVec.parity (parametricStabilizers i) s.E_tilde = false) &&
        (ErrorVec.parity SurfaceD3.logicalZ s.E_tilde ||
         ErrorVec.parity SurfaceD3.logicalX s.E_tilde))
    · exact absurd hh h_succ
    · rfl
  rw [Bool.and_eq_true] at h_succ_true
  obtain ⟨h_zero_syn, h_some_l⟩ := h_succ_true
  rw [List.all_eq_true] at h_zero_syn
  rw [Bool.or_eq_true] at h_some_l
  have h_zPartLZ : ErrorVec.parity SurfaceD3.logicalZ s.E_tilde =
                   ErrorVec.parity SurfaceD3.logicalZ (xPartE s.E_tilde) :=
    parity_zStab_eq_xPart SurfaceD3.logicalZ s.E_tilde logicalZ_zOnly
  have h_xPartLX : ErrorVec.parity SurfaceD3.logicalX s.E_tilde =
                   ErrorVec.parity SurfaceD3.logicalX (zPartE s.E_tilde) :=
    parity_xStab_eq_zPart SurfaceD3.logicalX s.E_tilde logicalX_xOnly
  rcases h_some_l with h_lZ | h_lX
  · -- L_Z parity = 1: derive xPart-side success
    rw [h_zPartLZ] at h_lZ
    have h_zSyn_x : ∀ i : Fin 8,
        ErrorVec.parity (parametricStabilizers i) (xPartE s.E_tilde) = false := by
      intro i
      by_cases hi_z : i.val = 1 ∨ i.val = 3 ∨ i.val = 5 ∨ i.val = 6
      · have h_zonly := parametricStabilizers_zOnly_at_zStabIdx i hi_z
        have h_eq : ErrorVec.parity (parametricStabilizers i) s.E_tilde =
                    ErrorVec.parity (parametricStabilizers i) (xPartE s.E_tilde) :=
          parity_zStab_eq_xPart _ _ h_zonly
        rw [← h_eq]
        have := h_zero_syn i (List.mem_finRange i)
        simpa using this
      · have hi_x : i.val = 0 ∨ i.val = 2 ∨ i.val = 4 ∨ i.val = 7 := by
          have := i.isLt
          interval_cases i.val
          · left; rfl
          · exact absurd (Or.inl rfl) hi_z
          · right; left; rfl
          · exact absurd (Or.inr (Or.inl rfl)) hi_z
          · right; right; left; rfl
          · exact absurd (Or.inr (Or.inr (Or.inl rfl))) hi_z
          · exact absurd (Or.inr (Or.inr (Or.inr rfl))) hi_z
          · right; right; right; rfl
        have h_xonly := parametricStabilizers_xOnly_at_xStabIdx i hi_x
        have h_xPart_xonly : ∀ j, (xPartE s.E_tilde) j = .X ∨ (xPartE s.E_tilde) j = .I := by
          intro j
          unfold xPartE Pauli.xPartL
          cases s.E_tilde j <;> simp
        exact parity_xStab_xOnly_zero _ _ h_xonly h_xPart_xonly
    have h_xSucc : QStab.Paper.SurfaceD3OperationalIffParam.isSuccessState
                     (xPartE s.E_tilde) = true := by
      unfold QStab.Paper.SurfaceD3OperationalIffParam.isSuccessState
      rw [Bool.and_eq_true]
      refine ⟨?_, h_lZ⟩
      rw [List.all_eq_true]
      intro i _
      simpa using h_zSyn_x i
    rw [h_xSucc] at h_x_no
    exact absurd h_x_no (by decide)
  · -- L_X parity = 1: derive zPart-side success
    rw [h_xPartLX] at h_lX
    have h_xSyn_z : ∀ i : Fin 8,
        ErrorVec.parity (parametricStabilizers i) (zPartE s.E_tilde) = false := by
      intro i
      by_cases hi_x : i.val = 0 ∨ i.val = 2 ∨ i.val = 4 ∨ i.val = 7
      · have h_xonly := parametricStabilizers_xOnly_at_xStabIdx i hi_x
        have h_eq : ErrorVec.parity (parametricStabilizers i) s.E_tilde =
                    ErrorVec.parity (parametricStabilizers i) (zPartE s.E_tilde) :=
          parity_xStab_eq_zPart _ _ h_xonly
        rw [← h_eq]
        have := h_zero_syn i (List.mem_finRange i)
        simpa using this
      · have hi_z : i.val = 1 ∨ i.val = 3 ∨ i.val = 5 ∨ i.val = 6 := by
          have := i.isLt
          interval_cases i.val
          · exact absurd (Or.inl rfl) hi_x
          · left; rfl
          · exact absurd (Or.inr (Or.inl rfl)) hi_x
          · right; left; rfl
          · exact absurd (Or.inr (Or.inr (Or.inl rfl))) hi_x
          · right; right; left; rfl
          · right; right; right; rfl
          · exact absurd (Or.inr (Or.inr (Or.inr rfl))) hi_x
        have h_zonly := parametricStabilizers_zOnly_at_zStabIdx i hi_z
        have h_zPart_zonly : ∀ j, (zPartE s.E_tilde) j = .Z ∨ (zPartE s.E_tilde) j = .I := by
          intro j
          unfold zPartE Pauli.zPartL
          cases s.E_tilde j <;> simp
        exact parity_zStab_zOnly_zero _ _ h_zonly h_zPart_zonly
    have h_zSucc : QStab.Paper.SurfaceD3OperationalIffParamZ.isSuccessStateZ
                     (zPartE s.E_tilde) = true := by
      unfold QStab.Paper.SurfaceD3OperationalIffParamZ.isSuccessStateZ
      rw [Bool.and_eq_true]
      refine ⟨?_, h_lX⟩
      rw [List.all_eq_true]
      intro i _
      simpa using h_xSyn_z i
    rw [h_zSucc] at h_z_no
    exact absurd h_z_no (by decide)

end QStab.Paper.SurfaceD3FullCharacterization
