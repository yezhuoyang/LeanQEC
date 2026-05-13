import QStab.Paper.SurfaceD3OperationalIffParam
import QStab.Paper.SurfaceD3OperationalIffParamZ
import QStab.MultiStep
import QStab.Invariant
import Mathlib.Tactic.FinCases

/-!
# Joint X-CX × Z-CX scheduling: operational `d_circ ≥ 3` (all logicals)

This file combines `SurfaceD3OperationalIffParam` (X-side) and
`SurfaceD3OperationalIffParamZ` (Z-side) into a single joint
characterisation:

For any joint d=3 surface scheduling = (X-CX ordering, Z-CX ordering),
if BOTH sides are non-Failing under their respective structural
classifications, then no 2-fault QStab trajectory in the joint code
reaches a success state on **any** of the three logical operators
`L_X`, `L_Z`, `L_Y`.

## Joint code

`schedCodeFull (sched_X, sched_Z)` has back-action set:
  * X-stab indices (0, 2, 4, 7) carry the X-CX hooks of `sched_X`.
  * Z-stab indices (1, 3, 5, 6) carry the Z-CX hooks of `sched_Z`.
A QStab trajectory in this code uses both X-hooks (via Type-II at
X-stab indices) and Z-hooks (via Type-II at Z-stab indices).

## Decomposition argument

Every Pauli `E_tilde` decomposes into `xPart E` (X-only) and
`zPart E` (Z-only), with:

  parity(Z-stab, E) = parity(Z-stab, xPart E)        — Z-stab sees only X-content
  parity(X-stab, E) = parity(X-stab, zPart E)        — X-stab sees only Z-content
  parity(L_Z, E)    = parity(L_Z, xPart E)
  parity(L_X, E)    = parity(L_X, zPart E)

Joint success on (L_X ∨ L_Z ∨ L_Y):
  * zero syndrome on E ⟹ zero Z-syndrome on xPart AND zero X-syndrome on zPart.
  * L_Z parity = 1 ⟹ xPart is a successful L_Z attack (excluded by X-side).
  * L_X parity = 1 ⟹ zPart is a successful L_X attack (excluded by Z-side).
  * L_Y parity = 1 ⟹ exactly one of L_X / L_Z parity is 1, reduce to above.

For X-side: `xPart` of the joint trajectory's `E_tilde` lies in
`schedReachableE sched_X 2` (the X-side reachable set). Hence the
existing X-side `schedReachableE_2_not_success_if_not_failing`
applies, excluding L_Z attacks.

Z-side is symmetric.

**Zero `sorry`. Standard axioms only.**
-/

namespace QStab.Paper.SurfaceD3JointXZ

open QStab QStab.Examples QStab.Examples.SurfaceD3
     QStab.Paper.SurfaceD3Classification
     QStab.Paper.SurfaceD3OperationalIffParam
     QStab.Paper.SurfaceD3OperationalIffParamZ

/-! ## Joint scheduling type -/

abbrev Surface3SchedFull := Surface3Sched × Surface3Sched

instance : Fintype Surface3SchedFull :=
  inferInstanceAs (Fintype (Surface3Sched × Surface3Sched))
instance : DecidableEq Surface3SchedFull :=
  inferInstanceAs (DecidableEq (Surface3Sched × Surface3Sched))

/-! ## Joint hooks and joint code -/

def schedHooksAtFull (sched : Surface3SchedFull) (i : Fin 8) : List (ErrorVec 9) :=
  schedHooksAt sched.1 i ++ schedHooksAtZ sched.2 i

def schedAllHooksFull (sched : Surface3SchedFull) : List (ErrorVec 9) :=
  schedAllHooks sched.1 ++ schedAllHooksZ sched.2

def schedBackActionSetFull (sched : Surface3SchedFull) (i : Fin 8) :
    Set (ErrorVec 9) :=
  fun e => e ∈ schedHooksAtFull sched i

theorem schedAllHooksFull_weight_bound :
    ∀ sched : Surface3SchedFull, ∀ e ∈ schedAllHooksFull sched,
      ErrorVec.weight e ≤ 3 := by
  intro sched e he
  simp only [schedAllHooksFull, List.mem_append] at he
  rcases he with h | h
  · exact schedAllHooks_weight_bound sched.1 e h
  · exact schedAllHooksZ_weight_bound sched.2 e h

theorem schedHooksAtFull_subset (sched : Surface3SchedFull) (i : Fin 8) :
    ∀ e ∈ schedHooksAtFull sched i, e ∈ schedAllHooksFull sched := by
  intro e he
  simp only [schedHooksAtFull, List.mem_append] at he
  rcases he with h | h
  · simp only [schedAllHooksFull, List.mem_append]; left
    exact schedHooksAt_subset sched.1 i e h
  · simp only [schedAllHooksFull, List.mem_append]; right
    exact schedHooksAtZ_subset sched.2 i e h

def schedCodeFull (sched : Surface3SchedFull) : QECParams where
  n := 9; k := 1; d := 3; R := 1; numStab := 8
  stabilizers := parametricStabilizers
  backActionSet := schedBackActionSetFull sched
  r := 3
  backAction_weight_bound := by
    intro stab_idx e he
    have h_e_in : e ∈ schedHooksAtFull sched stab_idx := he
    have h_e_in_all : e ∈ schedAllHooksFull sched :=
      schedHooksAtFull_subset sched stab_idx e h_e_in
    exact schedAllHooksFull_weight_bound sched e h_e_in_all
  C_budget := 2
  hn := by omega
  hns := by omega
  hR := by omega

/-! ## Membership of joint hooks in factor sides

Given that `schedHooksAt sched_X i` is non-empty only at X-stab indices
(0, 2, 4, 7), and `schedHooksAtZ sched_Z i` is non-empty only at Z-stab
indices (1, 3, 5, 6), we can recover side membership from joint membership. -/

theorem schedHooksAt_at_zStabIdx_empty (sched_X : Surface3Sched) (i : Fin 8)
    (h : i.val = 1 ∨ i.val = 3 ∨ i.val = 5 ∨ i.val = 6) :
    schedHooksAt sched_X i = [] := by
  fin_cases i <;> simp [schedHooksAt] <;> rcases h with h|h|h|h <;> simp at h

theorem schedHooksAtZ_at_xStabIdx_empty (sched_Z : Surface3Sched) (i : Fin 8)
    (h : i.val = 0 ∨ i.val = 2 ∨ i.val = 4 ∨ i.val = 7) :
    schedHooksAtZ sched_Z i = [] := by
  fin_cases i <;> simp [schedHooksAtZ] <;> rcases h with h|h|h|h <;> simp at h

/-! ## xPart / zPart Pauli projections -/

def Pauli.xPartL : Pauli → Pauli
  | .X => .X
  | .Y => .X
  | _  => .I

def Pauli.zPartL : Pauli → Pauli
  | .Z => .Z
  | .Y => .Z
  | _  => .I

def xPartE {n} (E : ErrorVec n) : ErrorVec n := fun i => Pauli.xPartL (E i)
def zPartE {n} (E : ErrorVec n) : ErrorVec n := fun i => Pauli.zPartL (E i)

theorem xPartE_identity (n : Nat) : xPartE (ErrorVec.identity n) = ErrorVec.identity n := by
  funext i; rfl

theorem zPartE_identity (n : Nat) : zPartE (ErrorVec.identity n) = ErrorVec.identity n := by
  funext i; rfl

theorem Pauli.xPartL_mul (a b : Pauli) :
    Pauli.xPartL (Pauli.mul a b) = Pauli.mul (Pauli.xPartL a) (Pauli.xPartL b) := by
  cases a <;> cases b <;> rfl

theorem Pauli.zPartL_mul (a b : Pauli) :
    Pauli.zPartL (Pauli.mul a b) = Pauli.mul (Pauli.zPartL a) (Pauli.zPartL b) := by
  cases a <;> cases b <;> rfl

theorem xPartE_mul {n} (a b : ErrorVec n) :
    xPartE (ErrorVec.mul a b) = ErrorVec.mul (xPartE a) (xPartE b) := by
  funext i; simp [xPartE, ErrorVec.mul, Pauli.xPartL_mul]

theorem zPartE_mul {n} (a b : ErrorVec n) :
    zPartE (ErrorVec.mul a b) = ErrorVec.mul (zPartE a) (zPartE b) := by
  funext i; simp [zPartE, ErrorVec.mul, Pauli.zPartL_mul]

theorem xPartE_update {n} (e : ErrorVec n) (i : Fin n) (p : Pauli) :
    xPartE (ErrorVec.update e i p) = ErrorVec.update (xPartE e) i (Pauli.xPartL p) := by
  funext j
  unfold xPartE ErrorVec.update
  by_cases h : j = i
  · rw [h, Function.update_self, Function.update_self]
    exact Pauli.xPartL_mul p (e i)
  · rw [Function.update_of_ne h, Function.update_of_ne h]

theorem zPartE_update {n} (e : ErrorVec n) (i : Fin n) (p : Pauli) :
    zPartE (ErrorVec.update e i p) = ErrorVec.update (zPartE e) i (Pauli.zPartL p) := by
  funext j
  unfold zPartE ErrorVec.update
  by_cases h : j = i
  · rw [h, Function.update_self, Function.update_self]
    exact Pauli.zPartL_mul p (e i)
  · rw [Function.update_of_ne h, Function.update_of_ne h]

/-! ## Z-only and X-only stabiliser predicates -/

/-- Each entry of stabiliser is .Z or .I (i.e. Z-only stabiliser). -/
def isZOnly {n} (s : ErrorVec n) : Prop := ∀ i, s i = .Z ∨ s i = .I

/-- Each entry of stabiliser is .X or .I (i.e. X-only stabiliser). -/
def isXOnly {n} (s : ErrorVec n) : Prop := ∀ i, s i = .X ∨ s i = .I

/-! ## Same-Pauli stabiliser commutation lemmas

X-stabs commute with X-only errors (parity 0); Z-stabs commute with
Z-only errors (parity 0). -/

theorem parity_xStab_xOnly_zero {n} (s e : ErrorVec n)
    (hs : isXOnly s) (he : ∀ j, e j = .X ∨ e j = .I) :
    ErrorVec.parity s e = false := by
  unfold ErrorVec.parity
  suffices h_filter_emp : (Finset.univ.filter fun j =>
      ErrorVec.Pauli.anticommutes (s j) (e j)) = ∅ by
    rw [h_filter_emp]; rfl
  apply Finset.filter_eq_empty_iff.mpr
  intro j _
  rcases hs j with hX | hI
  · rcases he j with hXe | hIe
    · rw [hX, hXe]; decide
    · rw [hX, hIe]; decide
  · rw [hI]; cases e j <;> decide

theorem parity_zStab_zOnly_zero {n} (s e : ErrorVec n)
    (hs : isZOnly s) (he : ∀ j, e j = .Z ∨ e j = .I) :
    ErrorVec.parity s e = false := by
  unfold ErrorVec.parity
  suffices h_filter_emp : (Finset.univ.filter fun j =>
      ErrorVec.Pauli.anticommutes (s j) (e j)) = ∅ by
    rw [h_filter_emp]; rfl
  apply Finset.filter_eq_empty_iff.mpr
  intro j _
  rcases hs j with hZ | hI
  · rcases he j with hZe | hIe
    · rw [hZ, hZe]; decide
    · rw [hZ, hIe]; decide
  · rw [hI]; cases e j <;> decide

/-! ## Parity decomposition lemmas -/

theorem parity_zStab_eq_xPart {n} (s e : ErrorVec n) (h : isZOnly s) :
    ErrorVec.parity s e = ErrorVec.parity s (xPartE e) := by
  have h_eq : ∀ i, ErrorVec.Pauli.anticommutes (s i) (e i) =
                   ErrorVec.Pauli.anticommutes (s i) (xPartE e i) := by
    intro i
    rcases h i with hZ | hI
    · rw [hZ]
      show ErrorVec.Pauli.anticommutes .Z (e i) =
           ErrorVec.Pauli.anticommutes .Z (Pauli.xPartL (e i))
      cases e i <;> rfl
    · rw [hI]; rfl
  unfold ErrorVec.parity
  simp only [h_eq]

theorem parity_xStab_eq_zPart {n} (s e : ErrorVec n) (h : isXOnly s) :
    ErrorVec.parity s e = ErrorVec.parity s (zPartE e) := by
  have h_eq : ∀ i, ErrorVec.Pauli.anticommutes (s i) (e i) =
                   ErrorVec.Pauli.anticommutes (s i) (zPartE e i) := by
    intro i
    rcases h i with hX | hI
    · rw [hX]
      show ErrorVec.Pauli.anticommutes .X (e i) =
           ErrorVec.Pauli.anticommutes .X (Pauli.zPartL (e i))
      cases e i <;> rfl
    · rw [hI]; rfl
  unfold ErrorVec.parity
  simp only [h_eq]

/-! ## Stab/logical Z/X-only proofs (paper-convention surface code) -/

theorem parametricStabilizers_zOnly_at_zStabIdx :
    ∀ i : Fin 8, i.val = 1 ∨ i.val = 3 ∨ i.val = 5 ∨ i.val = 6 →
      isZOnly (parametricStabilizers i) := by
  intro i hi
  fin_cases i
  · exact absurd hi (by decide)
  · intro j; fin_cases j <;> first | (left; rfl) | (right; rfl)
  · exact absurd hi (by decide)
  · intro j; fin_cases j <;> first | (left; rfl) | (right; rfl)
  · exact absurd hi (by decide)
  · intro j; fin_cases j <;> first | (left; rfl) | (right; rfl)
  · intro j; fin_cases j <;> first | (left; rfl) | (right; rfl)
  · exact absurd hi (by decide)

theorem parametricStabilizers_xOnly_at_xStabIdx :
    ∀ i : Fin 8, i.val = 0 ∨ i.val = 2 ∨ i.val = 4 ∨ i.val = 7 →
      isXOnly (parametricStabilizers i) := by
  intro i hi
  fin_cases i
  · intro j; fin_cases j <;> first | (left; rfl) | (right; rfl)
  · exact absurd hi (by decide)
  · intro j; fin_cases j <;> first | (left; rfl) | (right; rfl)
  · exact absurd hi (by decide)
  · intro j; fin_cases j <;> first | (left; rfl) | (right; rfl)
  · exact absurd hi (by decide)
  · exact absurd hi (by decide)
  · intro j; fin_cases j <;> first | (left; rfl) | (right; rfl)

theorem logicalZ_zOnly : isZOnly SurfaceD3.logicalZ := by
  intro j; fin_cases j <;> first | (left; rfl) | (right; rfl)

theorem logicalX_xOnly : isXOnly SurfaceD3.logicalX := by
  intro j; fin_cases j <;> first | (left; rfl) | (right; rfl)

/-! ## X-only / Z-only joint hook membership -/

theorem qubitsToVec_xOnly (qs : List (Fin 9)) :
    ∀ j, qubitsToVec qs j = .X ∨ qubitsToVec qs j = .I := by
  induction qs with
  | nil => intro j; right; rfl
  | cons q rest ih =>
    intro j
    have h_eq : qubitsToVec (q :: rest) = ErrorVec.update (qubitsToVec rest) q .X := rfl
    rw [h_eq]
    unfold ErrorVec.update
    by_cases hq : j = q
    · rw [hq, Function.update_self]
      rcases ih q with hX | hI
      · rw [hX]; right; rfl
      · rw [hI]; left; rfl
    · rw [Function.update_of_ne hq]
      exact ih j

theorem qubitsToVecZ_zOnly (qs : List (Fin 9)) :
    ∀ j, qubitsToVecZ qs j = .Z ∨ qubitsToVecZ qs j = .I := by
  induction qs with
  | nil => intro j; right; rfl
  | cons q rest ih =>
    intro j
    have h_eq : qubitsToVecZ (q :: rest) = ErrorVec.update (qubitsToVecZ rest) q .Z := rfl
    rw [h_eq]
    unfold ErrorVec.update
    by_cases hq : j = q
    · rw [hq, Function.update_self]
      rcases ih q with hZ | hI
      · rw [hZ]; right; rfl
      · rw [hI]; left; rfl
    · rw [Function.update_of_ne hq]
      exact ih j

theorem schedHooksAt_xOnly (sched_X : Surface3Sched) (i : Fin 8)
    (e : ErrorVec 9) (h : e ∈ schedHooksAt sched_X i) :
    ∀ j, e j = .X ∨ e j = .I := by
  intro j
  fin_cases i
  · -- i = 0
    have h' : ∃ l ∈ hooksOf (perm4 sched_X.1 xStab0), qubitsToVec l = e := by
      simpa [schedHooksAt] using h
    rcases h' with ⟨l, _, hl⟩
    rw [← hl]; exact qubitsToVec_xOnly l j
  · simp [schedHooksAt] at h
  · -- i = 2
    have h' : ∃ l ∈ hooksOf (perm4 sched_X.2.1 xStab1), qubitsToVec l = e := by
      simpa [schedHooksAt] using h
    rcases h' with ⟨l, _, hl⟩
    rw [← hl]; exact qubitsToVec_xOnly l j
  · simp [schedHooksAt] at h
  · -- i = 4
    have h' : ∃ l ∈ hooksOf (perm2 sched_X.2.2.1 xStab2), qubitsToVec l = e := by
      simpa [schedHooksAt] using h
    rcases h' with ⟨l, _, hl⟩
    rw [← hl]; exact qubitsToVec_xOnly l j
  · simp [schedHooksAt] at h
  · simp [schedHooksAt] at h
  · -- i = 7
    have h' : ∃ l ∈ hooksOf (perm2 sched_X.2.2.2 xStab3), qubitsToVec l = e := by
      simpa [schedHooksAt] using h
    rcases h' with ⟨l, _, hl⟩
    rw [← hl]; exact qubitsToVec_xOnly l j

theorem schedHooksAtZ_zOnly (sched_Z : Surface3Sched) (i : Fin 8)
    (e : ErrorVec 9) (h : e ∈ schedHooksAtZ sched_Z i) :
    ∀ j, e j = .Z ∨ e j = .I := by
  intro j
  fin_cases i
  · simp [schedHooksAtZ] at h
  · -- i = 1
    have h' : ∃ l ∈ hooksOf (perm4 sched_Z.1 zStab0), qubitsToVecZ l = e := by
      simpa [schedHooksAtZ] using h
    rcases h' with ⟨l, _, hl⟩
    rw [← hl]; exact qubitsToVecZ_zOnly l j
  · simp [schedHooksAtZ] at h
  · -- i = 3
    have h' : ∃ l ∈ hooksOf (perm4 sched_Z.2.1 zStab1), qubitsToVecZ l = e := by
      simpa [schedHooksAtZ] using h
    rcases h' with ⟨l, _, hl⟩
    rw [← hl]; exact qubitsToVecZ_zOnly l j
  · simp [schedHooksAtZ] at h
  · -- i = 5
    have h' : ∃ l ∈ hooksOf (perm2 sched_Z.2.2.1 zStab2), qubitsToVecZ l = e := by
      simpa [schedHooksAtZ] using h
    rcases h' with ⟨l, _, hl⟩
    rw [← hl]; exact qubitsToVecZ_zOnly l j
  · -- i = 6
    have h' : ∃ l ∈ hooksOf (perm2 sched_Z.2.2.2 zStab3), qubitsToVecZ l = e := by
      simpa [schedHooksAtZ] using h
    rcases h' with ⟨l, _, hl⟩
    rw [← hl]; exact qubitsToVecZ_zOnly l j
  · simp [schedHooksAtZ] at h

theorem xOnly_implies_xPartE_self {n} (e : ErrorVec n)
    (h : ∀ j, e j = .X ∨ e j = .I) : xPartE e = e := by
  funext j
  unfold xPartE
  rcases h j with hX | hI
  · rw [hX]; rfl
  · rw [hI]; rfl

theorem zOnly_implies_zPartE_self {n} (e : ErrorVec n)
    (h : ∀ j, e j = .Z ∨ e j = .I) : zPartE e = e := by
  funext j
  unfold zPartE
  rcases h j with hZ | hI
  · rw [hZ]; rfl
  · rw [hI]; rfl

theorem xOnly_implies_zPartE_identity {n} (e : ErrorVec n)
    (h : ∀ j, e j = .X ∨ e j = .I) : zPartE e = ErrorVec.identity n := by
  funext j
  unfold zPartE ErrorVec.identity
  rcases h j with hX | hI
  · rw [hX]; rfl
  · rw [hI]; rfl

theorem zOnly_implies_xPartE_identity {n} (e : ErrorVec n)
    (h : ∀ j, e j = .Z ∨ e j = .I) : xPartE e = ErrorVec.identity n := by
  funext j
  unfold xPartE ErrorVec.identity
  rcases h j with hZ | hI
  · rw [hZ]; rfl
  · rw [hI]; rfl

/-! ## Joint trajectory bridge invariant

We carry **both** xPart and zPart bridges simultaneously: for any
joint reachable state `s`, `xPart(s.E_tilde)` lies in the X-side
reachable set `schedReachableE sched.1 (C_budget − s.C)`, and
`zPart(s.E_tilde)` lies in the Z-side reachable set
`schedReachableEZ sched.2 (C_budget − s.C)`. -/

def jointBridgePred (sched : Surface3SchedFull)
    (s : State (schedCodeFull sched)) : Prop :=
  xPartE s.E_tilde ∈ schedReachableE sched.1
    ((schedCodeFull sched).C_budget - s.C) ∧
  zPartE s.E_tilde ∈ schedReachableEZ sched.2
    ((schedCodeFull sched).C_budget - s.C) ∧
  s.C ≤ (schedCodeFull sched).C_budget

theorem jointBridge_init (sched : Surface3SchedFull) :
    jointBridgePred sched (State.init (schedCodeFull sched)) := by
  refine ⟨?_, ?_, ?_⟩
  · show xPartE (State.init (schedCodeFull sched)).E_tilde ∈
        schedReachableE sched.1
          ((schedCodeFull sched).C_budget - (State.init (schedCodeFull sched)).C)
    have h1 : (State.init (schedCodeFull sched)).E_tilde = ErrorVec.identity 9 := rfl
    have h2 : (schedCodeFull sched).C_budget - (State.init (schedCodeFull sched)).C = 0 := by
      show (schedCodeFull sched).C_budget - (schedCodeFull sched).C_budget = 0; omega
    rw [h1, h2]
    show ErrorVec.identity 9 ∈ schedReachableE sched.1 0
    simp [schedReachableE]
  · show zPartE (State.init (schedCodeFull sched)).E_tilde ∈
        schedReachableEZ sched.2
          ((schedCodeFull sched).C_budget - (State.init (schedCodeFull sched)).C)
    have h1 : (State.init (schedCodeFull sched)).E_tilde = ErrorVec.identity 9 := rfl
    have h2 : (schedCodeFull sched).C_budget - (State.init (schedCodeFull sched)).C = 0 := by
      show (schedCodeFull sched).C_budget - (schedCodeFull sched).C_budget = 0; omega
    rw [h1, h2]
    show ErrorVec.identity 9 ∈ schedReachableEZ sched.2 0
    simp [schedReachableEZ]
  · show (State.init (schedCodeFull sched)).C ≤ (schedCodeFull sched).C_budget
    show (schedCodeFull sched).C_budget ≤ (schedCodeFull sched).C_budget
    omega

theorem jointBridge_preserve (sched : Surface3SchedFull)
    (s s' : State (schedCodeFull sched))
    (h_inv : jointBridgePred sched s)
    (hstep : Step (schedCodeFull sched) (.active s) (.active s')) :
    jointBridgePred sched s' := by
  obtain ⟨h_in_x, h_in_z, h_C⟩ := h_inv
  set n := (schedCodeFull sched).C_budget - s.C with h_n_def
  cases hstep with
  | type0 _ i p hp _ =>
    refine ⟨?_, ?_, ?_⟩
    · -- xPart: update by xPartL p ∈ {X, I}
      have h_n' : (schedCodeFull sched).C_budget - (s.C - 1) = n + 1 := by
        show (schedCodeFull sched).C_budget - (s.C - 1) = ((schedCodeFull sched).C_budget - s.C) + 1
        omega
      show xPartE (ErrorVec.update s.E_tilde i p) ∈
            schedReachableE sched.1 ((schedCodeFull sched).C_budget - (s.C - 1))
      rw [h_n', xPartE_update]
      cases p with
      | I => exact absurd rfl hp
      | X =>
        show ErrorVec.update (xPartE s.E_tilde) i .X ∈ schedReachableE sched.1 (n+1)
        exact schedReachableE_t01 sched.1 n (xPartE s.E_tilde) i .X h_in_x (Or.inl rfl)
      | Y =>
        show ErrorVec.update (xPartE s.E_tilde) i .X ∈ schedReachableE sched.1 (n+1)
        exact schedReachableE_t01 sched.1 n (xPartE s.E_tilde) i .X h_in_x (Or.inl rfl)
      | Z =>
        -- xPartL .Z = .I, so update by .I is no-op; use mono
        show ErrorVec.update (xPartE s.E_tilde) i .I ∈ schedReachableE sched.1 (n+1)
        have h_eq : ErrorVec.update (xPartE s.E_tilde) i .I = xPartE s.E_tilde := by
          funext j
          unfold ErrorVec.update
          by_cases h : j = i
          · subst h; simp [Pauli.mul]
          · simp [Function.update_of_ne h]
        rw [h_eq]
        exact schedReachableE_mono sched.1 n (xPartE s.E_tilde) h_in_x
    · -- zPart symmetric
      have h_n' : (schedCodeFull sched).C_budget - (s.C - 1) = n + 1 := by
        show (schedCodeFull sched).C_budget - (s.C - 1) = ((schedCodeFull sched).C_budget - s.C) + 1
        omega
      show zPartE (ErrorVec.update s.E_tilde i p) ∈
            schedReachableEZ sched.2 ((schedCodeFull sched).C_budget - (s.C - 1))
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
        show ErrorVec.update (zPartE s.E_tilde) i .Z ∈ schedReachableEZ sched.2 (n+1)
        exact schedReachableEZ_t01 sched.2 n (zPartE s.E_tilde) i .Z h_in_z (Or.inr (Or.inr rfl))
      | Z =>
        show ErrorVec.update (zPartE s.E_tilde) i .Z ∈ schedReachableEZ sched.2 (n+1)
        exact schedReachableEZ_t01 sched.2 n (zPartE s.E_tilde) i .Z h_in_z (Or.inr (Or.inr rfl))
    · show s.C - 1 ≤ (schedCodeFull sched).C_budget; omega
  | type1 _ i p hp _ _ =>
    refine ⟨?_, ?_, ?_⟩
    · have h_n' : (schedCodeFull sched).C_budget - (s.C - 1) = n + 1 := by
        show (schedCodeFull sched).C_budget - (s.C - 1) = ((schedCodeFull sched).C_budget - s.C) + 1
        omega
      show xPartE (ErrorVec.update s.E_tilde i p) ∈
            schedReachableE sched.1 ((schedCodeFull sched).C_budget - (s.C - 1))
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
    · have h_n' : (schedCodeFull sched).C_budget - (s.C - 1) = n + 1 := by
        show (schedCodeFull sched).C_budget - (s.C - 1) = ((schedCodeFull sched).C_budget - s.C) + 1
        omega
      show zPartE (ErrorVec.update s.E_tilde i p) ∈
            schedReachableEZ sched.2 ((schedCodeFull sched).C_budget - (s.C - 1))
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
    · show s.C - 1 ≤ (schedCodeFull sched).C_budget; omega
  | type2 _ e he _ _ =>
    refine ⟨?_, ?_, ?_⟩
    · have h_n' : (schedCodeFull sched).C_budget - (s.C - 1) = n + 1 := by
        show (schedCodeFull sched).C_budget - (s.C - 1) = ((schedCodeFull sched).C_budget - s.C) + 1
        omega
      show xPartE (ErrorVec.mul e s.E_tilde) ∈
            schedReachableE sched.1 ((schedCodeFull sched).C_budget - (s.C - 1))
      rw [h_n', xPartE_mul]
      -- e ∈ schedHooksAtFull sched s.coord.x = schedHooksAt sched.1 ++ schedHooksAtZ sched.2
      have h_e_in : e ∈ schedHooksAtFull sched s.coord.x := he
      have h_e_in' : e ∈ schedHooksAt sched.1 s.coord.x ++ schedHooksAtZ sched.2 s.coord.x :=
        h_e_in
      rcases List.mem_append.mp h_e_in' with h_x | h_z
      · -- X-hook: e is X-only, so xPartE e = e and xPartE e ∈ schedAllHooks sched.1
        have h_xonly : ∀ j, e j = .X ∨ e j = .I := schedHooksAt_xOnly sched.1 _ e h_x
        have h_xPart_eq : xPartE e = e := xOnly_implies_xPartE_self e h_xonly
        rw [h_xPart_eq]
        have h_e_all : e ∈ schedAllHooks sched.1 :=
          schedHooksAt_subset sched.1 s.coord.x e h_x
        exact schedReachableE_t2 sched.1 n (xPartE s.E_tilde) e h_in_x h_e_all
      · -- Z-hook: e is Z-only, so xPartE e = identity, mul identity = no-op
        have h_zonly : ∀ j, e j = .Z ∨ e j = .I := schedHooksAtZ_zOnly sched.2 _ e h_z
        have h_xPart_eq : xPartE e = ErrorVec.identity 9 :=
          zOnly_implies_xPartE_identity e h_zonly
        rw [h_xPart_eq]
        show ErrorVec.mul (ErrorVec.identity 9) (xPartE s.E_tilde) ∈ schedReachableE sched.1 (n+1)
        have h_id_mul : ErrorVec.mul (ErrorVec.identity 9) (xPartE s.E_tilde) = xPartE s.E_tilde := by
          funext j
          show Pauli.mul Pauli.I (xPartE s.E_tilde j) = xPartE s.E_tilde j
          cases xPartE s.E_tilde j <;> rfl
        rw [h_id_mul]
        exact schedReachableE_mono sched.1 n (xPartE s.E_tilde) h_in_x
    · have h_n' : (schedCodeFull sched).C_budget - (s.C - 1) = n + 1 := by
        show (schedCodeFull sched).C_budget - (s.C - 1) = ((schedCodeFull sched).C_budget - s.C) + 1
        omega
      show zPartE (ErrorVec.mul e s.E_tilde) ∈
            schedReachableEZ sched.2 ((schedCodeFull sched).C_budget - (s.C - 1))
      rw [h_n', zPartE_mul]
      have h_e_in : e ∈ schedHooksAtFull sched s.coord.x := he
      have h_e_in' : e ∈ schedHooksAt sched.1 s.coord.x ++ schedHooksAtZ sched.2 s.coord.x :=
        h_e_in
      rcases List.mem_append.mp h_e_in' with h_x | h_z
      · -- X-hook: zPartE e = identity, mul identity = no-op
        have h_xonly : ∀ j, e j = .X ∨ e j = .I := schedHooksAt_xOnly sched.1 _ e h_x
        have h_zPart_eq : zPartE e = ErrorVec.identity 9 :=
          xOnly_implies_zPartE_identity e h_xonly
        rw [h_zPart_eq]
        show ErrorVec.mul (ErrorVec.identity 9) (zPartE s.E_tilde) ∈ schedReachableEZ sched.2 (n+1)
        have h_id_mul : ErrorVec.mul (ErrorVec.identity 9) (zPartE s.E_tilde) = zPartE s.E_tilde := by
          funext j
          show Pauli.mul Pauli.I (zPartE s.E_tilde j) = zPartE s.E_tilde j
          cases zPartE s.E_tilde j <;> rfl
        rw [h_id_mul]
        exact schedReachableEZ_mono sched.2 n (zPartE s.E_tilde) h_in_z
      · -- Z-hook: zPartE e = e, in schedAllHooksZ
        have h_zonly : ∀ j, e j = .Z ∨ e j = .I := schedHooksAtZ_zOnly sched.2 _ e h_z
        have h_zPart_eq : zPartE e = e := zOnly_implies_zPartE_self e h_zonly
        rw [h_zPart_eq]
        have h_e_all : e ∈ schedAllHooksZ sched.2 :=
          schedHooksAtZ_subset sched.2 s.coord.x e h_z
        exact schedReachableEZ_t2 sched.2 n (zPartE s.E_tilde) e h_in_z h_e_all
    · show s.C - 1 ≤ (schedCodeFull sched).C_budget; omega
  | type3 _ _ =>
    refine ⟨?_, ?_, ?_⟩
    · have h_n' : (schedCodeFull sched).C_budget - (s.C - 1) = n + 1 := by
        show (schedCodeFull sched).C_budget - (s.C - 1) = ((schedCodeFull sched).C_budget - s.C) + 1
        omega
      show xPartE s.E_tilde ∈ schedReachableE sched.1
              ((schedCodeFull sched).C_budget - (s.C - 1))
      rw [h_n']
      exact schedReachableE_mono sched.1 n (xPartE s.E_tilde) h_in_x
    · have h_n' : (schedCodeFull sched).C_budget - (s.C - 1) = n + 1 := by
        show (schedCodeFull sched).C_budget - (s.C - 1) = ((schedCodeFull sched).C_budget - s.C) + 1
        omega
      show zPartE s.E_tilde ∈ schedReachableEZ sched.2
              ((schedCodeFull sched).C_budget - (s.C - 1))
      rw [h_n']
      exact schedReachableEZ_mono sched.2 n (zPartE s.E_tilde) h_in_z
    · show s.C - 1 ≤ (schedCodeFull sched).C_budget; omega
  | measure _ nc _ =>
    refine ⟨?_, ?_, ?_⟩
    · show xPartE (measureStep (schedCodeFull sched) s nc).E_tilde ∈
            schedReachableE sched.1
              ((schedCodeFull sched).C_budget - (measureStep (schedCodeFull sched) s nc).C)
      rw [measureStep_E_tilde, measureStep_C]
      exact h_in_x
    · show zPartE (measureStep (schedCodeFull sched) s nc).E_tilde ∈
            schedReachableEZ sched.2
              ((schedCodeFull sched).C_budget - (measureStep (schedCodeFull sched) s nc).C)
      rw [measureStep_E_tilde, measureStep_C]
      exact h_in_z
    · show (measureStep (schedCodeFull sched) s nc).C ≤ (schedCodeFull sched).C_budget
      rw [measureStep_C]; exact h_C

def jointBridgeInv (sched : Surface3SchedFull) : Invariant (schedCodeFull sched) where
  holds := jointBridgePred sched
  holds_init := jointBridge_init sched
  preservation := jointBridge_preserve sched

theorem joint_xPart_in_X_reachable (sched : Surface3SchedFull)
    (s : State (schedCodeFull sched))
    (hreach : MultiStep (schedCodeFull sched)
                (.active (State.init (schedCodeFull sched))) (.active s)) :
    xPartE s.E_tilde ∈ schedReachableE sched.1
      ((schedCodeFull sched).C_budget - s.C) :=
  ((jointBridgeInv sched).holds_of_reachable s hreach).1

theorem joint_zPart_in_Z_reachable (sched : Surface3SchedFull)
    (s : State (schedCodeFull sched))
    (hreach : MultiStep (schedCodeFull sched)
                (.active (State.init (schedCodeFull sched))) (.active s)) :
    zPartE s.E_tilde ∈ schedReachableEZ sched.2
      ((schedCodeFull sched).C_budget - s.C) :=
  ((jointBridgeInv sched).holds_of_reachable s hreach).2.1

/-! ## Joint success predicate (covers L_X, L_Z, L_Y) -/

/-- A joint state is a "success" iff `E_tilde ∈ N(S) \ S` AND it flips
    at least one logical (L_X or L_Z, which covers L_Y = L_X · L_Z). -/
def isSuccessStateFull (E : ErrorVec 9) : Bool :=
  ((List.finRange 8).all fun i =>
    ErrorVec.parity (parametricStabilizers i) E = false) &&
  (ErrorVec.parity SurfaceD3.logicalZ E ||
   ErrorVec.parity SurfaceD3.logicalX E)

/-! ## Headline theorem -/

/-- **Joint X+Z operational `d_circ ≥ 3` for all non-Failing pairs.**

    For any joint scheduling (X-CX, Z-CX) where both sides are
    non-Failing under their respective structural classifications, no
    QStab Run with budget consumed ≤ 2 reaches a success state on any
    of the three logical operators (L_X, L_Z, or L_Y).

    Proof outline:
      * `xPart(E_tilde) ∈ schedReachableE sched.1 2` (joint bridge).
      * `zPart(E_tilde) ∈ schedReachableEZ sched.2 2` (joint bridge).
      * Z-stab parity & L_Z parity decompose through `xPart`.
      * X-stab parity & L_X parity decompose through `zPart`.
      * Joint success on L_Z ⟹ X-side parametric theorem fires ⟹ false.
      * Joint success on L_X ⟹ Z-side parametric theorem fires ⟹ false.
      * Joint success on L_Y splits into one of the above. -/
theorem joint_nonFailing_op_d_circ_ge_3 :
    ∀ sched : Surface3SchedFull,
      classOf sched.1 ≠ SchedClass.Failing →
      classOfZ sched.2 ≠ SchedClass.Failing →
      ∀ (s : State (schedCodeFull sched)),
        MultiStep (schedCodeFull sched)
          (.active (State.init (schedCodeFull sched))) (.active s) →
        (schedCodeFull sched).C_budget - s.C ≤ 2 →
        isSuccessStateFull s.E_tilde = false := by
  intro sched h_X_nf h_Z_nf s hreach hbudget
  -- xPart in X-side reachable
  have h_x_in : xPartE s.E_tilde ∈ schedReachableE sched.1
                  ((schedCodeFull sched).C_budget - s.C) :=
    joint_xPart_in_X_reachable sched s hreach
  have h_x_in_2 : xPartE s.E_tilde ∈ schedReachableE sched.1 2 := by
    rcases Nat.lt_or_ge ((schedCodeFull sched).C_budget - s.C) 2 with hlt | hge
    · rcases Nat.lt_or_ge ((schedCodeFull sched).C_budget - s.C) 1 with hlt' | hge'
      · have : (schedCodeFull sched).C_budget - s.C = 0 := by omega
        rw [this] at h_x_in
        exact schedReachableE_mono sched.1 _ _ (schedReachableE_mono sched.1 _ _ h_x_in)
      · have : (schedCodeFull sched).C_budget - s.C = 1 := by omega
        rw [this] at h_x_in
        exact schedReachableE_mono sched.1 _ _ h_x_in
    · have : (schedCodeFull sched).C_budget - s.C = 2 := by omega
      rw [this] at h_x_in
      exact h_x_in
  have h_z_in : zPartE s.E_tilde ∈ schedReachableEZ sched.2
                  ((schedCodeFull sched).C_budget - s.C) :=
    joint_zPart_in_Z_reachable sched s hreach
  have h_z_in_2 : zPartE s.E_tilde ∈ schedReachableEZ sched.2 2 := by
    rcases Nat.lt_or_ge ((schedCodeFull sched).C_budget - s.C) 2 with hlt | hge
    · rcases Nat.lt_or_ge ((schedCodeFull sched).C_budget - s.C) 1 with hlt' | hge'
      · have : (schedCodeFull sched).C_budget - s.C = 0 := by omega
        rw [this] at h_z_in
        exact schedReachableEZ_mono sched.2 _ _ (schedReachableEZ_mono sched.2 _ _ h_z_in)
      · have : (schedCodeFull sched).C_budget - s.C = 1 := by omega
        rw [this] at h_z_in
        exact schedReachableEZ_mono sched.2 _ _ h_z_in
    · have : (schedCodeFull sched).C_budget - s.C = 2 := by omega
      rw [this] at h_z_in
      exact h_z_in
  -- Apply X-side and Z-side native_decide checks.
  have h_x_check := schedReachableE_2_not_success_if_not_failing sched.1 h_X_nf
  rw [List.all_eq_true] at h_x_check
  have h_x_no := h_x_check (xPartE s.E_tilde) h_x_in_2
  simp at h_x_no
  -- h_x_no : isSuccessState (xPartE s.E_tilde) = false
  have h_z_check := schedReachableEZ_2_not_success_if_not_failing sched.2 h_Z_nf
  rw [List.all_eq_true] at h_z_check
  have h_z_no := h_z_check (zPartE s.E_tilde) h_z_in_2
  simp at h_z_no
  -- Now combine: derive joint success false from xPart-side and zPart-side.
  -- isSuccessStateFull s.E_tilde = false iff
  --   parity vs all 8 stabs zero is false OR (L_Z parity = 0 AND L_X parity = 0).
  unfold isSuccessStateFull
  -- Strategy: assume joint success, derive contradiction.
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
  -- Decompose syndrome zero through xPart and zPart.
  -- For Z-stab indices, parity E = parity (xPart E)
  have h_zPartLZ : ErrorVec.parity SurfaceD3.logicalZ s.E_tilde =
                   ErrorVec.parity SurfaceD3.logicalZ (xPartE s.E_tilde) :=
    parity_zStab_eq_xPart SurfaceD3.logicalZ s.E_tilde logicalZ_zOnly
  have h_xPartLX : ErrorVec.parity SurfaceD3.logicalX s.E_tilde =
                   ErrorVec.parity SurfaceD3.logicalX (zPartE s.E_tilde) :=
    parity_xStab_eq_zPart SurfaceD3.logicalX s.E_tilde logicalX_xOnly
  rcases h_some_l with h_lZ | h_lX
  · -- L_Z parity = 1: derive xPart-side success → contradicts h_x_no.
    rw [h_zPartLZ] at h_lZ
    -- Need: parity vs Z-stabs zero on xPart E_tilde.
    have h_zSyn_x : ∀ i : Fin 8,
        ErrorVec.parity (parametricStabilizers i) (xPartE s.E_tilde) = false := by
      intro i
      by_cases hi_z : i.val = 1 ∨ i.val = 3 ∨ i.val = 5 ∨ i.val = 6
      · -- Z-stab index: parity decomposes
        have h_zonly := parametricStabilizers_zOnly_at_zStabIdx i hi_z
        have h_eq : ErrorVec.parity (parametricStabilizers i) s.E_tilde =
                    ErrorVec.parity (parametricStabilizers i) (xPartE s.E_tilde) :=
          parity_zStab_eq_xPart _ _ h_zonly
        rw [← h_eq]
        have := h_zero_syn i (List.mem_finRange i)
        simpa using this
      · -- X-stab index: xPart vs X-stab is auto false (X-only E vs X-stab commute)
        have hi_x : i.val = 0 ∨ i.val = 2 ∨ i.val = 4 ∨ i.val = 7 := by
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
    -- xPart success!
    have h_xSucc : QStab.Paper.SurfaceD3OperationalIffParam.isSuccessState (xPartE s.E_tilde) = true := by
      unfold QStab.Paper.SurfaceD3OperationalIffParam.isSuccessState
      rw [Bool.and_eq_true]
      refine ⟨?_, h_lZ⟩
      rw [List.all_eq_true]
      intro i _
      simpa using h_zSyn_x i
    rw [h_xSucc] at h_x_no
    exact absurd h_x_no (by decide)
  · -- L_X parity = 1: derive zPart-side success → contradicts h_z_no.
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
    have h_zSucc : QStab.Paper.SurfaceD3OperationalIffParamZ.isSuccessStateZ (zPartE s.E_tilde) = true := by
      unfold QStab.Paper.SurfaceD3OperationalIffParamZ.isSuccessStateZ
      rw [Bool.and_eq_true]
      refine ⟨?_, h_lX⟩
      rw [List.all_eq_true]
      intro i _
      simpa using h_xSyn_z i
    rw [h_zSucc] at h_z_no
    exact absurd h_z_no (by decide)

end QStab.Paper.SurfaceD3JointXZ
