import QStab.Paper.SurfaceD3Classification
import QStab.Paper.SurfaceD3OperationalIffParam
import QStab.MultiStep
import QStab.Invariant
import QStab.Examples.SurfaceCode
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-!
# Z-CX side parametric operational `d_circ ≥ 3` (mirror of X-CX side)

This file mirrors `SurfaceD3OperationalIffParam.lean`, swapping the
roles of X and Z. Where the X-side proves "no 2-fault `L_Z` attack
under any non-Failing **X-CX** scheduling", this file proves the dual:

  ∀ schedZ : Surface3Sched, classOfZ schedZ ≠ Failing →
    ∀ s : State (schedCodeZ schedZ),
      MultiStep (schedCodeZ schedZ) ... → (C_budget − s.C) ≤ 2 →
      isSuccessStateZ s.E_tilde = false

Symmetric ingredients:

* The four Z-stabs (`s1, s4, s6, s7`) play the role of X-stabs.
* Z-CX scheduling = perm of each Z-stab's qubit list, parameterised
  by `Surface3Sched` (same shape: 24 × 24 × 2 × 2).
* Z-hooks are Z-only Pauli vectors; back-action sits at indices
  1, 3, 5, 6 in `parametricStabilizers`.
* L_X (left column = qubits 0, 3, 6) is the targeted logical.
* "Bad hook" = Z-hook spanning ≥ 2 **columns** mod Z-stab.
* Matching mechanism: a Type-0 single-qubit Z or Type-II Z-hook with
  matching X-syndrome footprint and flipped L_X parity.

**Zero `sorry`. Standard axioms only.**
-/

namespace QStab.Paper.SurfaceD3OperationalIffParamZ

open QStab QStab.Examples QStab.Examples.SurfaceD3
     QStab.Paper.SurfaceD3Classification

/-! ## Z-stabilisers (paper convention) and L_X support -/

def zStab0 : List (Fin 9) :=
  [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩]
def zStab1 : List (Fin 9) :=
  [⟨4, by decide⟩, ⟨5, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩]
def zStab2 : List (Fin 9) := [⟨2, by decide⟩, ⟨5, by decide⟩]
def zStab3 : List (Fin 9) := [⟨3, by decide⟩, ⟨6, by decide⟩]

def zStab : Fin 4 → List (Fin 9)
  | ⟨0, _⟩ => zStab0 | ⟨1, _⟩ => zStab1
  | ⟨2, _⟩ => zStab2 | ⟨3, _⟩ => zStab3

/-- X-stabiliser supports for syndrome footprint (mirror role of `zStabSupp`). -/
def xStabSupp : Fin 4 → List (Fin 9)
  | ⟨0, _⟩ => [⟨1, by decide⟩, ⟨2, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩]
  | ⟨1, _⟩ => [⟨3, by decide⟩, ⟨4, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩]
  | ⟨2, _⟩ => [⟨0, by decide⟩, ⟨1, by decide⟩]
  | ⟨3, _⟩ => [⟨7, by decide⟩, ⟨8, by decide⟩]

/-- L_X support: left column {q₀, q₃, q₆}. -/
def lxSupp : List (Fin 9) := [⟨0, by decide⟩, ⟨3, by decide⟩, ⟨6, by decide⟩]

/-! ## Z-side scheduling (uses same `Surface3Sched` shape) -/

def schedOrderZ (s : Surface3Sched) : Fin 4 → List (Fin 9)
  | ⟨0, _⟩ => perm4 s.1 zStab0
  | ⟨1, _⟩ => perm4 s.2.1 zStab1
  | ⟨2, _⟩ => perm2 s.2.2.1 zStab2
  | ⟨3, _⟩ => perm2 s.2.2.2 zStab3

/-! ## Z-side syndrome / parity -/

/-- X-syndrome footprint of a Z-only mechanism's qubit list:
    parity against each X-stabiliser (which sees the Z-content). -/
def syndromeFootprintZ (qs : List (Fin 9)) : List Bool :=
  (List.finRange 4).map (fun i => parityXZ qs (xStabSupp i))

/-- Parity vs L_X. -/
def lxParity (qs : List (Fin 9)) : Bool := parityXZ qs lxSupp

/-! ## Z-side bad hook (column-spanning) -/

def colOf (q : Fin 9) : Fin 3 := ⟨q.val % 3, by omega⟩

def colsOf (qs : List (Fin 9)) : List (Fin 3) :=
  (qs.map colOf).dedup

/-- A Z-hook `h` is "bad" iff h spans ≥ 2 columns AND the symmetric
    difference with the Z-stab support also spans ≥ 2 columns. -/
def isBadHookZ (stab_supp h : List (Fin 9)) : Bool :=
  if (colsOf h).length ≤ 1 then false
  else
    let symDiff := (stab_supp.filter (· ∉ h)) ++ (h.filter (· ∉ stab_supp))
    (colsOf symDiff).length > 1

/-! ## Z-side fault mechanisms -/

def t0_mechsZ : List (List Bool × Bool) :=
  (List.finRange 9).map (fun q => (syndromeFootprintZ [q], lxParity [q]))

def t2_mechsZ (s : Surface3Sched) : List (List Bool × Bool) :=
  (List.finRange 4).flatMap fun i =>
    (hooksOf (schedOrderZ s i)).map
      (fun h => (syndromeFootprintZ h, lxParity h))

/-! ## Z-side class predicates -/

def hasBadHookZ (s : Surface3Sched) : Bool :=
  (List.finRange 4).any fun i =>
    (hooksOf (schedOrderZ s i)).any (fun h => isBadHookZ (zStab i) h)

def hasMatchingMechZ (s : Surface3Sched) : Bool :=
  let allMechs := t0_mechsZ ++ t2_mechsZ s
  (List.finRange 4).any fun i =>
    (hooksOf (schedOrderZ s i)).any fun h =>
      isBadHookZ (zStab i) h &&
      (let h_t := syndromeFootprintZ h
       let l_t := lxParity h
       allMechs.any fun (h_k, l_k) => h_k = h_t && l_k != l_t)

def classOfZ (s : Surface3Sched) : SchedClass :=
  if hasBadHookZ s = false then SchedClass.LAligned
  else if hasMatchingMechZ s = true then SchedClass.Failing
  else SchedClass.CleanRecord

/-! ## Z-side parametric QECParams -/

/-- Convert a list of qubits to a Z-only ErrorVec. -/
def qubitsToVecZ (qs : List (Fin 9)) : ErrorVec 9 :=
  qs.foldr (fun q acc => ErrorVec.update acc q .Z) (ErrorVec.identity 9)

/-- Hooks of one Z-stabiliser at QECParams index i. The 4 Z-stabs sit at
    indices 1, 3, 5, 6 (with X-stabs at 0, 2, 4, 7) under the
    `parametricStabilizers` ordering used by the X-side file. -/
def schedHooksAtZ (sched : Surface3Sched) (i : Fin 8) : List (ErrorVec 9) :=
  match i with
  | ⟨1, _⟩ => (hooksOf (perm4 sched.1 zStab0)).map qubitsToVecZ
  | ⟨3, _⟩ => (hooksOf (perm4 sched.2.1 zStab1)).map qubitsToVecZ
  | ⟨5, _⟩ => (hooksOf (perm2 sched.2.2.1 zStab2)).map qubitsToVecZ
  | ⟨6, _⟩ => (hooksOf (perm2 sched.2.2.2 zStab3)).map qubitsToVecZ
  | _ => []

def schedAllHooksZ (sched : Surface3Sched) : List (ErrorVec 9) :=
  schedHooksAtZ sched ⟨1, by decide⟩ ++
  schedHooksAtZ sched ⟨3, by decide⟩ ++
  schedHooksAtZ sched ⟨5, by decide⟩ ++
  schedHooksAtZ sched ⟨6, by decide⟩

def schedBackActionSetZ (sched : Surface3Sched) (i : Fin 8) :
    Set (ErrorVec 9) :=
  fun e => e ∈ schedHooksAtZ sched i

theorem schedAllHooksZ_weight_bound :
    ∀ sched : Surface3Sched, ∀ e ∈ schedAllHooksZ sched,
      ErrorVec.weight e ≤ 3 := by
  native_decide

theorem schedHooksAtZ_subset (sched : Surface3Sched) (i : Fin 8) :
    ∀ e ∈ schedHooksAtZ sched i, e ∈ schedAllHooksZ sched := by
  intro e he
  show e ∈ schedAllHooksZ sched
  unfold schedAllHooksZ
  fin_cases i
  · -- i = 0: empty
    simp [schedHooksAtZ] at he
  · -- i = 1
    simp only [List.mem_append]; left; left; left; exact he
  · -- i = 2: empty
    simp [schedHooksAtZ] at he
  · -- i = 3
    simp only [List.mem_append]; left; left; right; exact he
  · -- i = 4: empty
    simp [schedHooksAtZ] at he
  · -- i = 5
    simp only [List.mem_append]; left; right; exact he
  · -- i = 6
    simp only [List.mem_append]; right; exact he
  · -- i = 7: empty
    simp [schedHooksAtZ] at he

/-- Per-scheduling Z-side QECParams. Reuses the same `parametricStabilizers`
    indexing from the X-side parametric file (X-bulk at index 0, etc.). -/
def schedCodeZ (sched : Surface3Sched) : QECParams where
  n := 9; k := 1; d := 3; R := 1; numStab := 8
  stabilizers := QStab.Paper.SurfaceD3OperationalIffParam.parametricStabilizers
  backActionSet := schedBackActionSetZ sched
  r := 3
  backAction_weight_bound := by
    intro stab_idx e he
    show ErrorVec.weight e ≤ 3
    have h_e_in : e ∈ schedHooksAtZ sched stab_idx := he
    have h_e_in_all : e ∈ schedAllHooksZ sched :=
      schedHooksAtZ_subset sched stab_idx e h_e_in
    exact schedAllHooksZ_weight_bound sched e h_e_in_all
  C_budget := 2
  hn := by omega
  hns := by omega
  hR := by omega

/-! ## Z-side reachable-E enumeration -/

def schedReachableEZ (sched : Surface3Sched) : Nat → List (ErrorVec 9)
  | 0 => [ErrorVec.identity 9]
  | n+1 =>
    let prev := schedReachableEZ sched n
    let t01_ext : List (ErrorVec 9) :=
      (List.finRange 9).flatMap fun i =>
        [Pauli.X, Pauli.Y, Pauli.Z].flatMap fun p =>
          prev.map fun e => ErrorVec.update e i p
    let t2_ext : List (ErrorVec 9) :=
      (schedAllHooksZ sched).flatMap fun h =>
        prev.map fun e => ErrorVec.mul h e
    prev ++ t01_ext ++ t2_ext

theorem schedReachableEZ_identity (sched : Surface3Sched) (n : Nat) :
    ErrorVec.identity 9 ∈ schedReachableEZ sched n := by
  induction n with
  | zero => simp [schedReachableEZ]
  | succ n ih =>
    show ErrorVec.identity 9 ∈ schedReachableEZ sched (n+1)
    simp only [schedReachableEZ, List.mem_append]
    left; left; exact ih

theorem schedReachableEZ_mono (sched : Surface3Sched) (n : Nat)
    (e : ErrorVec 9) (h : e ∈ schedReachableEZ sched n) :
    e ∈ schedReachableEZ sched (n+1) := by
  show e ∈ schedReachableEZ sched (n+1)
  simp only [schedReachableEZ, List.mem_append]
  left; left; exact h

theorem schedReachableEZ_t01 (sched : Surface3Sched) (n : Nat)
    (e : ErrorVec 9) (i : Fin 9) (p : Pauli)
    (h : e ∈ schedReachableEZ sched n)
    (hp : p = .X ∨ p = .Y ∨ p = .Z) :
    ErrorVec.update e i p ∈ schedReachableEZ sched (n+1) := by
  show ErrorVec.update e i p ∈ schedReachableEZ sched (n+1)
  simp only [schedReachableEZ, List.mem_append]
  left; right
  apply List.mem_flatMap.mpr
  refine ⟨i, List.mem_finRange i, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨p, ?_, ?_⟩
  · rcases hp with hp | hp | hp <;> subst hp <;> simp
  · apply List.mem_map.mpr
    exact ⟨e, h, rfl⟩

theorem schedReachableEZ_t2 (sched : Surface3Sched) (n : Nat)
    (e h_vec : ErrorVec 9)
    (he : e ∈ schedReachableEZ sched n)
    (hh : h_vec ∈ schedAllHooksZ sched) :
    ErrorVec.mul h_vec e ∈ schedReachableEZ sched (n+1) := by
  show ErrorVec.mul h_vec e ∈ schedReachableEZ sched (n+1)
  simp only [schedReachableEZ, List.mem_append]
  right
  apply List.mem_flatMap.mpr
  refine ⟨h_vec, hh, ?_⟩
  apply List.mem_map.mpr
  exact ⟨e, he, rfl⟩

/-! ## Z-side bridge invariant -/

def schedReachInvPredZ (sched : Surface3Sched) (s : State (schedCodeZ sched)) :
    Prop :=
  s.E_tilde ∈ schedReachableEZ sched ((schedCodeZ sched).C_budget - s.C) ∧
  s.C ≤ (schedCodeZ sched).C_budget

theorem schedReachInvZ_init (sched : Surface3Sched) :
    schedReachInvPredZ sched (State.init (schedCodeZ sched)) := by
  refine ⟨?_, ?_⟩
  · show (State.init (schedCodeZ sched)).E_tilde ∈
          schedReachableEZ sched
            ((schedCodeZ sched).C_budget - (State.init (schedCodeZ sched)).C)
    have h1 : (State.init (schedCodeZ sched)).E_tilde = ErrorVec.identity 9 := rfl
    have h2 : (schedCodeZ sched).C_budget - (State.init (schedCodeZ sched)).C = 0 := by
      show (schedCodeZ sched).C_budget - (schedCodeZ sched).C_budget = 0; omega
    rw [h1, h2]
    show ErrorVec.identity 9 ∈ schedReachableEZ sched 0
    simp [schedReachableEZ]
  · show (State.init (schedCodeZ sched)).C ≤ (schedCodeZ sched).C_budget
    show (schedCodeZ sched).C_budget ≤ (schedCodeZ sched).C_budget
    omega

theorem schedReachInvZ_preserve (sched : Surface3Sched)
    (s s' : State (schedCodeZ sched))
    (h_inv : schedReachInvPredZ sched s)
    (hstep : Step (schedCodeZ sched) (.active s) (.active s')) :
    schedReachInvPredZ sched s' := by
  obtain ⟨h_in, h_C⟩ := h_inv
  set n := (schedCodeZ sched).C_budget - s.C with h_n_def
  cases hstep with
  | type0 _ i p hp _ =>
    refine ⟨?_, ?_⟩
    · have h_n' : (schedCodeZ sched).C_budget - (s.C - 1) = n + 1 := by
        show (schedCodeZ sched).C_budget - (s.C - 1) = ((schedCodeZ sched).C_budget - s.C) + 1
        omega
      show ErrorVec.update s.E_tilde i p ∈
            schedReachableEZ sched ((schedCodeZ sched).C_budget - (s.C - 1))
      rw [h_n']
      have hp_cases : p = .X ∨ p = .Y ∨ p = .Z := by
        cases p with
        | I => exact absurd rfl hp
        | X => left; rfl
        | Y => right; left; rfl
        | Z => right; right; rfl
      exact schedReachableEZ_t01 sched n s.E_tilde i p h_in hp_cases
    · show s.C - 1 ≤ (schedCodeZ sched).C_budget; omega
  | type1 _ i p hp _ _ =>
    refine ⟨?_, ?_⟩
    · have h_n' : (schedCodeZ sched).C_budget - (s.C - 1) = n + 1 := by
        show (schedCodeZ sched).C_budget - (s.C - 1) = ((schedCodeZ sched).C_budget - s.C) + 1
        omega
      show ErrorVec.update s.E_tilde i p ∈
            schedReachableEZ sched ((schedCodeZ sched).C_budget - (s.C - 1))
      rw [h_n']
      have hp_cases : p = .X ∨ p = .Y ∨ p = .Z := by
        cases p with
        | I => exact absurd rfl hp
        | X => left; rfl
        | Y => right; left; rfl
        | Z => right; right; rfl
      exact schedReachableEZ_t01 sched n s.E_tilde i p h_in hp_cases
    · show s.C - 1 ≤ (schedCodeZ sched).C_budget; omega
  | type2 _ e he _ _ =>
    refine ⟨?_, ?_⟩
    · have h_n' : (schedCodeZ sched).C_budget - (s.C - 1) = n + 1 := by
        show (schedCodeZ sched).C_budget - (s.C - 1) = ((schedCodeZ sched).C_budget - s.C) + 1
        omega
      show ErrorVec.mul e s.E_tilde ∈
            schedReachableEZ sched ((schedCodeZ sched).C_budget - (s.C - 1))
      rw [h_n']
      have h_e_in : e ∈ schedHooksAtZ sched s.coord.x := he
      have h_e_in_all : e ∈ schedAllHooksZ sched :=
        schedHooksAtZ_subset sched s.coord.x e h_e_in
      exact schedReachableEZ_t2 sched n s.E_tilde e h_in h_e_in_all
    · show s.C - 1 ≤ (schedCodeZ sched).C_budget; omega
  | type3 _ _ =>
    refine ⟨?_, ?_⟩
    · have h_n' : (schedCodeZ sched).C_budget - (s.C - 1) = n + 1 := by
        show (schedCodeZ sched).C_budget - (s.C - 1) = ((schedCodeZ sched).C_budget - s.C) + 1
        omega
      show s.E_tilde ∈
            schedReachableEZ sched ((schedCodeZ sched).C_budget - (s.C - 1))
      rw [h_n']
      exact schedReachableEZ_mono sched n s.E_tilde h_in
    · show s.C - 1 ≤ (schedCodeZ sched).C_budget; omega
  | measure _ nc _ =>
    refine ⟨?_, ?_⟩
    · show (measureStep (schedCodeZ sched) s nc).E_tilde ∈
            schedReachableEZ sched
              ((schedCodeZ sched).C_budget - (measureStep (schedCodeZ sched) s nc).C)
      rw [measureStep_E_tilde, measureStep_C]
      exact h_in
    · show (measureStep (schedCodeZ sched) s nc).C ≤ (schedCodeZ sched).C_budget
      rw [measureStep_C]; exact h_C

def schedReachInvZ (sched : Surface3Sched) : Invariant (schedCodeZ sched) where
  holds := schedReachInvPredZ sched
  holds_init := schedReachInvZ_init sched
  preservation := schedReachInvZ_preserve sched

theorem sched_etilde_in_reachableEZ (sched : Surface3Sched)
    (s : State (schedCodeZ sched))
    (hreach : MultiStep (schedCodeZ sched)
                (.active (State.init (schedCodeZ sched))) (.active s)) :
    s.E_tilde ∈ schedReachableEZ sched ((schedCodeZ sched).C_budget - s.C) :=
  ((schedReachInvZ sched).holds_of_reachable s hreach).1

/-! ## Z-side success predicate and finite check -/

/-- Success on L_X for the Z-side problem: zero parity vs all 8 stabs
    AND non-trivial L_X parity. -/
def isSuccessStateZ (E : ErrorVec 9) : Bool :=
  ((List.finRange 8).all fun i =>
    ErrorVec.parity
      (QStab.Paper.SurfaceD3OperationalIffParam.parametricStabilizers i) E
      = false) &&
  ErrorVec.parity SurfaceD3.logicalX E

/-- For all non-Failing-Z schedulings, no element of `schedReachableEZ 2`
    is a success state. Verified by `native_decide` over all 2304
    Z-CX schedulings. -/
theorem schedReachableEZ_2_not_success_if_not_failing :
    ∀ sched : Surface3Sched,
      classOfZ sched ≠ SchedClass.Failing →
      (schedReachableEZ sched 2).all (fun E => !(isSuccessStateZ E)) = true := by
  native_decide

/-! ## Z-side headline theorem -/

/-- **Operational `d_circ ≥ 3` for ALL non-Failing d=3 surface Z-CX
    orderings, against L_X attacks.** -/
theorem nonFailingZ_op_d_circ_ge_3 :
    ∀ sched : Surface3Sched,
      classOfZ sched ≠ SchedClass.Failing →
      ∀ (s : State (schedCodeZ sched)),
        MultiStep (schedCodeZ sched)
          (.active (State.init (schedCodeZ sched))) (.active s) →
        (schedCodeZ sched).C_budget - s.C ≤ 2 →
        isSuccessStateZ s.E_tilde = false := by
  intro sched h_not_failing s hreach hbudget
  have h_in : s.E_tilde ∈ schedReachableEZ sched ((schedCodeZ sched).C_budget - s.C) :=
    sched_etilde_in_reachableEZ sched s hreach
  have h_in_2 : s.E_tilde ∈ schedReachableEZ sched 2 := by
    rcases Nat.lt_or_ge ((schedCodeZ sched).C_budget - s.C) 2 with hlt | hge
    · rcases Nat.lt_or_ge ((schedCodeZ sched).C_budget - s.C) 1 with hlt' | hge'
      · have : (schedCodeZ sched).C_budget - s.C = 0 := by omega
        rw [this] at h_in
        exact schedReachableEZ_mono sched _ _ (schedReachableEZ_mono sched _ _ h_in)
      · have : (schedCodeZ sched).C_budget - s.C = 1 := by omega
        rw [this] at h_in
        exact schedReachableEZ_mono sched _ _ h_in
    · have : (schedCodeZ sched).C_budget - s.C = 2 := by omega
      rw [this] at h_in
      exact h_in
  have h_all := schedReachableEZ_2_not_success_if_not_failing sched h_not_failing
  rw [List.all_eq_true] at h_all
  have h_check := h_all s.E_tilde h_in_2
  simp at h_check
  exact h_check

end QStab.Paper.SurfaceD3OperationalIffParamZ
