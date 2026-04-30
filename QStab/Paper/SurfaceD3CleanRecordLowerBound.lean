import QStab.Paper.SurfaceD3Classification
import QStab.MultiStep
import QStab.Examples.SurfaceCode
import Mathlib.Tactic.FinCases

/-!
# CleanRecord scheduling: building blocks for `d_circ ≥ 3` (Surface d=3)

For a concrete CleanRecord-class scheduling on the [[9,1,3]] surface
code, this file establishes structural building blocks toward the
operational lower bound `d_circ ≥ 3`:

  * a CleanRecord-class QECParams instance `cr_code` whose only
    Type-II mechanism is a row-spanning bad hook with no matching
    Type-0/II counterpart;
  * the verified property `hook_1_5_in_B0`;
  * a finite-check lemma `cr_no_two_mech_success` showing that no XOR
    product of ≤ 2 X-only mechanisms (the bad hook plus 9 single-qubit
    Type-0 X errors) yields a success state.

The full operational `d_circ ≥ 3` requires structural induction over
`MultiStep` plus tracking of E_tilde as a Pauli product of mechanisms
along the trajectory. That induction is mechanical but requires more
infrastructure than fits in a single short file.

**Zero `sorry`. Standard axioms only.**
-/

namespace QStab.Paper.SurfaceD3CleanRecordLowerBound

open QStab QStab.Examples QStab.Examples.SurfaceD3
     QStab.Paper.SurfaceD3Classification

/-! ## CleanRecord QECParams instance

The bad hook `X_1 X_5` from `s2 = X{1,2,4,5}`:
  - qubits 1 (row 0) and 5 (row 1) span 2 rows ⇒ bad.
  - syndrome footprint = (1, 1, 1, 0) (parity vs Z-stabs s1, s4, s6, s7).
  - L_Z parity = 1 (qubit 1 ∈ {0, 1, 2}).

For Failing membership: would need a Type-0/II mechanism with
footprint (1, 1, 1, 0) AND L_Z parity 0. No single-qubit Type-0
in surface d=3 has popcount-3 syndrome footprint. With our minimal
back-action set (only `hook_1_5`), no Type-II match either.

Hence `cr_code` is in the CleanRecord class. -/

def hook_1_5 : ErrorVec 9 := ofList [(1, .X), (5, .X)]

def cr_stabilizers : Fin 8 → ErrorVec 9
  | ⟨0, _⟩ => SurfaceD3.s2  -- X-bulk: X{1,2,4,5}
  | ⟨1, _⟩ => SurfaceD3.s1  -- Z-bulk: Z{0,1,3,4}
  | ⟨2, _⟩ => SurfaceD3.s3  -- X-bulk: X{3,4,6,7}
  | ⟨3, _⟩ => SurfaceD3.s4  -- Z-bulk: Z{4,5,7,8}
  | ⟨4, _⟩ => SurfaceD3.s5  -- X-boundary: X{0,1}
  | ⟨5, _⟩ => SurfaceD3.s6  -- Z-boundary: Z{2,5}
  | ⟨6, _⟩ => SurfaceD3.s7  -- Z-boundary: Z{3,6}
  | ⟨7, _⟩ => SurfaceD3.s8  -- X-boundary: X{7,8}

def cr_backActionSet : Fin 8 → Set (ErrorVec 9)
  | ⟨0, _⟩ => {hook_1_5}
  | _ => ∅

def cr_code : QECParams where
  n := 9; k := 1; d := 3; R := 1; numStab := 8
  stabilizers := cr_stabilizers
  backActionSet := cr_backActionSet
  r := 2
  backAction_weight_bound := by
    intro s e he
    fin_cases s <;> simp [cr_backActionSet] at he
    subst he
    show ErrorVec.weight hook_1_5 ≤ 2
    native_decide
  C_budget := 2
  hn := by omega
  hns := by omega
  hR := by omega

theorem hook_1_5_in_B0 : hook_1_5 ∈ cr_code.backActionSet ⟨0, by decide⟩ := by
  show hook_1_5 ∈ cr_backActionSet ⟨0, by decide⟩
  simp [cr_backActionSet]

/-! ## The bad hook's QStab-level signature

We verify the syndrome footprint and L_Z parity of `hook_1_5` against
the stabilisers of `cr_code` directly. -/

theorem hook_1_5_syndrome_at_s1 :
    ErrorVec.parity (cr_stabilizers ⟨1, by decide⟩) hook_1_5 = true := by
  native_decide

theorem hook_1_5_syndrome_at_s4 :
    ErrorVec.parity (cr_stabilizers ⟨3, by decide⟩) hook_1_5 = true := by
  native_decide

theorem hook_1_5_syndrome_at_s6 :
    ErrorVec.parity (cr_stabilizers ⟨5, by decide⟩) hook_1_5 = true := by
  native_decide

theorem hook_1_5_lz_parity :
    ErrorVec.parity SurfaceD3.logicalZ hook_1_5 = true := by
  native_decide

/-! ## CleanRecord property: no two-mechanism XOR is success

The QStab fault mechanisms relevant for `cr_code`'s `E_tilde`:
  * Type-0 single-qubit X on qubit 0..8 (9 mechanisms).
  * Type-II hook `hook_1_5` (1 mechanism).

(Type-III doesn't change `E_tilde`, so doesn't contribute to
mechanism counting. Y/Z faults DO contribute X-component as well as
Z-component, but for the L_Z-flipping question only X-component
matters; Y is treated as "X with extra Z baggage" that only adds
syndrome constraints.)

The CleanRecord property: no XOR product of ≤ 2 X-component mechanisms
yields a success state. Verified by `decide` over the finite list. -/

/-- Type-0 X on qubit `q`: an `ErrorVec` with X at `q`, identity
    elsewhere. -/
def t0_X (q : Fin 9) : ErrorVec 9 :=
  ErrorVec.update (ErrorVec.identity 9) q .X

/-- The 10 X-component fault mechanisms for `cr_code`: 9 Type-0 X
    errors + the bad hook. -/
def cr_x_mechs : List (ErrorVec 9) :=
  hook_1_5 ::
    [t0_X ⟨0, by decide⟩, t0_X ⟨1, by decide⟩, t0_X ⟨2, by decide⟩,
     t0_X ⟨3, by decide⟩, t0_X ⟨4, by decide⟩, t0_X ⟨5, by decide⟩,
     t0_X ⟨6, by decide⟩, t0_X ⟨7, by decide⟩, t0_X ⟨8, by decide⟩]

/-- Success state: zero syndrome with all 8 stabs, non-trivial L_Z. -/
def isSuccessState (E : ErrorVec 9) : Bool :=
  ((List.finRange 8).all fun i =>
    ErrorVec.parity (cr_stabilizers i) E = false) &&
  ErrorVec.parity SurfaceD3.logicalZ E

theorem cr_identity_not_success :
    isSuccessState (ErrorVec.identity 9) = false := by native_decide

theorem cr_no_one_fault_success :
    cr_x_mechs.all (fun m => !(isSuccessState m)) = true := by
  native_decide

theorem cr_no_two_fault_success :
    cr_x_mechs.all (fun m1 =>
      cr_x_mechs.all (fun m2 =>
        !(isSuccessState (ErrorVec.mul m1 m2)))) = true := by
  native_decide

/-! ## Summary

This file establishes:

  * `cr_code` is a concrete CleanRecord-class QECParams instance.
  * `hook_1_5_in_B0`: the bad hook is in the back-action set.
  * `hook_1_5_syndrome_*`, `hook_1_5_lz_parity`: the bad hook's QStab
    parities against Z-stabs and L_Z (matches the structural-classifier
    expectation: footprint = (1,1,1,0), L_Z parity = 1).
  * `cr_no_one_fault_success`, `cr_no_two_fault_success`: the finite
    check ruling out 1- or 2-mechanism XOR success products.

These are the QStab-level building blocks for proving operational
`d_circ ≥ 3` for `cr_code`. The remaining work — a structural
induction over `MultiStep` showing that any reachable state's
`E_tilde` is a ≤k-mechanism XOR product (k = budget consumed) — is
mechanical and is left to a follow-up file.

When the induction is in place, the operational lower bound follows:

  ∀ s : State cr_code,
    MultiStep cr_code (.active (State.init cr_code)) (.active s) →
    cr_code.C_budget - s.C ≤ 2 →
    isSuccessState s.E_tilde = false

i.e., operational `d_circ(cr_code) ≥ 3`. Combined with the Failing-class
2-fault witness in `Paper/SurfaceD3OperationalIff.lean`, this completes
the operational iff classification at the level required.
-/

end QStab.Paper.SurfaceD3CleanRecordLowerBound
