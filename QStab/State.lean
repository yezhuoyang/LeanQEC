import QStab.Defs

/-! # Program state for the QStab fault-tolerance operational semantics

Defines the 13-field `State` structure matching the paper's σ,
the `ExecState` wrapper (active/done/error), and the initial state.

Note: λ is a Lean keyword, so we use `lam` prefix for error counters
(lam_E for λ_E, cnt0..cnt3 for λ_0..λ_3).
-/

namespace QStab

open QECParams

/-- The active program state σ = (C, RI, x, y, λ_E, Ẽ, I, G, F, λ_0, λ_1, λ_2, λ_3). -/
structure State (P : QECParams) where
  /-- Error budget (decreases on error injection, starts at C_budget) -/
  C : Nat
  /-- Round inconsistency count -/
  RI : Nat
  /-- Current measurement coordinate (x, y) -/
  coord : Coord P
  /-- Total error weight (λ_E in the paper) -/
  lam_E : Nat
  /-- Current error flow Ẽ : n-qubit Pauli vector -/
  E_tilde : ErrorVec P.n
  /-- Inferred syndrome I[T_s] : one Bool per stabilizer -/
  I_syn : Fin P.numStab → Bool
  /-- Classical register G : measurement results indexed by (stabilizer, round) -/
  G : Fin P.numStab → Fin P.R → Bool
  /-- Inconsistency vector F : one Bool per stabilizer -/
  F : Fin P.numStab → Bool
  /-- Type-0 error counter λ_0 (data qubit errors) -/
  cnt0 : Nat
  /-- Type-I error counter λ_1 (errors during measurement) -/
  cnt1 : Nat
  /-- Type-II error counter λ_2 (back-action errors) -/
  cnt2 : Nat
  /-- Type-III error counter λ_3 (measurement bit flips) -/
  cnt3 : Nat

namespace State

/-- The initial state σ_init = (C_budget, 0, I⃗, 0⃗, 0⃗, 0, 0, 0, 0). -/
def init (P : QECParams) : State P where
  C       := P.C_budget
  RI      := 0
  coord   := Coord.first P
  lam_E   := 0
  E_tilde := ErrorVec.identity P.n
  I_syn   := fun _ => false
  G       := fun _ _ => false
  F       := fun _ => false
  cnt0    := 0
  cnt1    := 0
  cnt2    := 0
  cnt3    := 0

/-- Total error count across all types: λ_0 + λ_1 + λ_2 + λ_3. -/
def totalErrors (s : State P) : Nat :=
  s.cnt0 + s.cnt1 + s.cnt2 + s.cnt3

end State

/-- Execution state: wraps active state with done/error termination. -/
inductive ExecState (P : QECParams) where
  /-- Normal execution -/
  | active : State P → ExecState P
  /-- Execution completed: all measurements done -/
  | done   : State P → ExecState P
  /-- Error state: budget exhausted and adversary tried to inject -/
  | error  : State P → ExecState P

namespace ExecState

/-- Extract the underlying state. -/
def state : ExecState P → State P
  | active s => s
  | done s   => s
  | error s  => s

end ExecState

end QStab
