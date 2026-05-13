import QStab.MultiStep
import QStab.Invariant
import QStab.PauliOps

/-!
# Generic reachable-E bridge invariant (distance-parametric)

This file provides a **distance-agnostic** template for proving
operational `d_circ ≥ d` for any QECParams whose back-action set is
contained in a known list of hook errors.

## Idea

Given:
  * `P : QECParams` with `C_budget = d - 1`
  * `allHooks : List (ErrorVec P.n)` such that
    `∀ s, ∀ e ∈ backActionSet P s, e ∈ allHooks`

we define `reachableE allHooks n` = set of `E_tilde` reachable in
≤ n budget-consuming Steps:

  reachableE 0   = {identity}
  reachableE n+1 = reachableE n
                 ∪ {update e i p : e ∈ reachableE n, i : Fin P.n, p ≠ I}
                 ∪ {mul h e : h ∈ allHooks, e ∈ reachableE n}

The bridge invariant holds:
  ∀ s reachable in MultiStep, `s.E_tilde ∈ reachableE (C_budget − s.C)`.

Hence: if no element of `reachableE (d − 1)` is a success state, then
operational `d_circ(P) ≥ d`.

## What this gives

A **single generic theorem** that lifts to ANY distance d, ANY surface-
code-like CSS scheme, ANY scheduling, modulo a per-instance finite check
that "no success state in `reachableE (d − 1)`".

For d=3 we instantiate with `native_decide` over 2304 schedulings —
already done in `Paper/SurfaceD3OperationalIffParam.lean`. For higher d,
the same template applies; only the finite check needs to scale (via
SAT/SMT, sampling + structural argument, or symmetry reduction).

**Zero `sorry`. Standard axioms only.**
-/

namespace QStab.Paper.GenericReachableBridge

open QStab

/-! ## Reachable-E set parameterized by an upper bound on hooks -/

/-- E_tildes reachable in ≤ n budget-consuming Steps, given a list
    `allHooks` that contains every hook in every back-action set. -/
def reachableE {n_qubits : Nat} (allHooks : List (ErrorVec n_qubits)) :
    Nat → List (ErrorVec n_qubits)
  | 0 => [ErrorVec.identity n_qubits]
  | k+1 =>
    let prev := reachableE allHooks k
    let t01_ext : List (ErrorVec n_qubits) :=
      (List.finRange n_qubits).flatMap fun i =>
        [Pauli.X, Pauli.Y, Pauli.Z].flatMap fun p =>
          prev.map fun e => ErrorVec.update e i p
    let t2_ext : List (ErrorVec n_qubits) :=
      allHooks.flatMap fun h => prev.map fun e => ErrorVec.mul h e
    prev ++ t01_ext ++ t2_ext

theorem reachableE_identity {n_qubits : Nat} (allHooks : List (ErrorVec n_qubits))
    (k : Nat) : ErrorVec.identity n_qubits ∈ reachableE allHooks k := by
  induction k with
  | zero => simp [reachableE]
  | succ k ih =>
    show ErrorVec.identity n_qubits ∈ reachableE allHooks (k+1)
    simp only [reachableE, List.mem_append]
    left; left; exact ih

theorem reachableE_mono {n_qubits : Nat} (allHooks : List (ErrorVec n_qubits))
    (k : Nat) (e : ErrorVec n_qubits) (h : e ∈ reachableE allHooks k) :
    e ∈ reachableE allHooks (k+1) := by
  show e ∈ reachableE allHooks (k+1)
  simp only [reachableE, List.mem_append]
  left; left; exact h

theorem reachableE_t01 {n_qubits : Nat} (allHooks : List (ErrorVec n_qubits))
    (k : Nat) (e : ErrorVec n_qubits) (i : Fin n_qubits) (p : Pauli)
    (h : e ∈ reachableE allHooks k)
    (hp : p = .X ∨ p = .Y ∨ p = .Z) :
    ErrorVec.update e i p ∈ reachableE allHooks (k+1) := by
  show ErrorVec.update e i p ∈ reachableE allHooks (k+1)
  simp only [reachableE, List.mem_append]
  left; right
  apply List.mem_flatMap.mpr
  refine ⟨i, List.mem_finRange i, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨p, ?_, ?_⟩
  · rcases hp with hp | hp | hp <;> subst hp <;> simp
  · apply List.mem_map.mpr
    exact ⟨e, h, rfl⟩

theorem reachableE_t2 {n_qubits : Nat} (allHooks : List (ErrorVec n_qubits))
    (k : Nat) (e h_vec : ErrorVec n_qubits)
    (he : e ∈ reachableE allHooks k)
    (hh : h_vec ∈ allHooks) :
    ErrorVec.mul h_vec e ∈ reachableE allHooks (k+1) := by
  show ErrorVec.mul h_vec e ∈ reachableE allHooks (k+1)
  simp only [reachableE, List.mem_append]
  right
  apply List.mem_flatMap.mpr
  refine ⟨h_vec, hh, ?_⟩
  apply List.mem_map.mpr
  exact ⟨e, he, rfl⟩

/-! ## Bridge invariant: any MultiStep-reachable state's E_tilde is in reachableE -/

/-- Hypothesis: every back-action element is in `allHooks`. -/
def hooksUpperBound (P : QECParams) (allHooks : List (ErrorVec P.n)) : Prop :=
  ∀ (s : Fin P.numStab) (e : ErrorVec P.n), e ∈ P.backActionSet s → e ∈ allHooks

/-- The bridge predicate: E_tilde lies in `reachableE` for the matching depth. -/
def reachInvPred (P : QECParams) (allHooks : List (ErrorVec P.n)) (s : State P) : Prop :=
  s.E_tilde ∈ reachableE allHooks (P.C_budget - s.C) ∧ s.C ≤ P.C_budget

theorem reachInv_init (P : QECParams) (allHooks : List (ErrorVec P.n)) :
    reachInvPred P allHooks (State.init P) := by
  refine ⟨?_, ?_⟩
  · show (State.init P).E_tilde ∈ reachableE allHooks (P.C_budget - (State.init P).C)
    have h1 : (State.init P).E_tilde = ErrorVec.identity P.n := rfl
    have h2 : P.C_budget - (State.init P).C = 0 := by
      show P.C_budget - P.C_budget = 0; omega
    rw [h1, h2]
    show ErrorVec.identity P.n ∈ reachableE allHooks 0
    simp [reachableE]
  · show (State.init P).C ≤ P.C_budget
    show P.C_budget ≤ P.C_budget
    omega

theorem reachInv_preserve (P : QECParams) (allHooks : List (ErrorVec P.n))
    (h_bound : hooksUpperBound P allHooks)
    (s s' : State P)
    (h_inv : reachInvPred P allHooks s)
    (hstep : Step P (.active s) (.active s')) :
    reachInvPred P allHooks s' := by
  obtain ⟨h_in, h_C⟩ := h_inv
  set k := P.C_budget - s.C with h_k_def
  cases hstep with
  | type0 _ i p hp _ =>
    refine ⟨?_, ?_⟩
    · have h_n' : P.C_budget - (s.C - 1) = k + 1 := by
        show P.C_budget - (s.C - 1) = (P.C_budget - s.C) + 1; omega
      show ErrorVec.update s.E_tilde i p ∈ reachableE allHooks (P.C_budget - (s.C - 1))
      rw [h_n']
      have hp_cases : p = .X ∨ p = .Y ∨ p = .Z := by
        cases p with
        | I => exact absurd rfl hp
        | X => left; rfl
        | Y => right; left; rfl
        | Z => right; right; rfl
      exact reachableE_t01 allHooks k s.E_tilde i p h_in hp_cases
    · show s.C - 1 ≤ P.C_budget; omega
  | type1 _ i p hp _ _ =>
    refine ⟨?_, ?_⟩
    · have h_n' : P.C_budget - (s.C - 1) = k + 1 := by
        show P.C_budget - (s.C - 1) = (P.C_budget - s.C) + 1; omega
      show ErrorVec.update s.E_tilde i p ∈ reachableE allHooks (P.C_budget - (s.C - 1))
      rw [h_n']
      have hp_cases : p = .X ∨ p = .Y ∨ p = .Z := by
        cases p with
        | I => exact absurd rfl hp
        | X => left; rfl
        | Y => right; left; rfl
        | Z => right; right; rfl
      exact reachableE_t01 allHooks k s.E_tilde i p h_in hp_cases
    · show s.C - 1 ≤ P.C_budget; omega
  | type2 _ e he _ _ =>
    refine ⟨?_, ?_⟩
    · have h_n' : P.C_budget - (s.C - 1) = k + 1 := by
        show P.C_budget - (s.C - 1) = (P.C_budget - s.C) + 1; omega
      show ErrorVec.mul e s.E_tilde ∈ reachableE allHooks (P.C_budget - (s.C - 1))
      rw [h_n']
      have h_e_in_all : e ∈ allHooks := h_bound s.coord.x e he
      exact reachableE_t2 allHooks k s.E_tilde e h_in h_e_in_all
    · show s.C - 1 ≤ P.C_budget; omega
  | type3 _ _ =>
    refine ⟨?_, ?_⟩
    · have h_n' : P.C_budget - (s.C - 1) = k + 1 := by
        show P.C_budget - (s.C - 1) = (P.C_budget - s.C) + 1; omega
      show s.E_tilde ∈ reachableE allHooks (P.C_budget - (s.C - 1))
      rw [h_n']
      exact reachableE_mono allHooks k s.E_tilde h_in
    · show s.C - 1 ≤ P.C_budget; omega
  | measure _ nc _ =>
    refine ⟨?_, ?_⟩
    · show (measureStep P s nc).E_tilde ∈
            reachableE allHooks (P.C_budget - (measureStep P s nc).C)
      rw [measureStep_E_tilde, measureStep_C]
      exact h_in
    · show (measureStep P s nc).C ≤ P.C_budget
      rw [measureStep_C]; exact h_C

def reachInv (P : QECParams) (allHooks : List (ErrorVec P.n))
    (h_bound : hooksUpperBound P allHooks) : Invariant P where
  holds := reachInvPred P allHooks
  holds_init := reachInv_init P allHooks
  preservation := reachInv_preserve P allHooks h_bound

theorem etilde_in_reachableE (P : QECParams) (allHooks : List (ErrorVec P.n))
    (h_bound : hooksUpperBound P allHooks)
    (s : State P)
    (hreach : MultiStep P (.active (State.init P)) (.active s)) :
    s.E_tilde ∈ reachableE allHooks (P.C_budget - s.C) :=
  ((reachInv P allHooks h_bound).holds_of_reachable s hreach).1

/-! ## Generic operational `d_circ ≥ d` theorem

Given:
  * `P` with `C_budget = d − 1`
  * `allHooks` upper-bounding back-action sets
  * `isSuccess : ErrorVec P.n → Bool` (a decidable success check)
  * Hypothesis: no element of `reachableE allHooks (d − 1)` is a success state

we conclude: any MultiStep-reachable state with budget consumed ≤ d − 1
is not a success state. Hence operational `d_circ(P) ≥ d`. -/

/-- Monotonicity of `reachableE` in depth. -/
theorem reachableE_mono_le {n_qubits : Nat} (allHooks : List (ErrorVec n_qubits)) :
    ∀ {p q : Nat}, p ≤ q →
      ∀ e, e ∈ reachableE allHooks p → e ∈ reachableE allHooks q := by
  intro p q hpq
  induction q with
  | zero =>
    intro e he
    have : p = 0 := by omega
    subst this; exact he
  | succ q' ih =>
    intro e he
    rcases Nat.eq_or_lt_of_le hpq with heq | hlt
    · subst heq; exact he
    · have h' : p ≤ q' := Nat.lt_succ_iff.mp hlt
      exact reachableE_mono _ _ _ (ih h' e he)

theorem nonSuccess_op_d_circ_ge_d
    (P : QECParams)
    (allHooks : List (ErrorVec P.n))
    (h_bound : hooksUpperBound P allHooks)
    (isSuccess : ErrorVec P.n → Bool)
    (h_finite_check :
      ∀ E ∈ reachableE allHooks P.C_budget, isSuccess E = false) :
    ∀ s : State P,
      MultiStep P (.active (State.init P)) (.active s) →
      isSuccess s.E_tilde = false := by
  intro s hreach
  have h_in : s.E_tilde ∈ reachableE allHooks (P.C_budget - s.C) :=
    etilde_in_reachableE P allHooks h_bound s hreach
  have h_le : P.C_budget - s.C ≤ P.C_budget := Nat.sub_le _ _
  have h_in_top : s.E_tilde ∈ reachableE allHooks P.C_budget :=
    reachableE_mono_le allHooks h_le s.E_tilde h_in
  exact h_finite_check s.E_tilde h_in_top

end QStab.Paper.GenericReachableBridge
