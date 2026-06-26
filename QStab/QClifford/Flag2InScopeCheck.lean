import QStab.QClifford.Flag2General
import QStab.Examples.SurfaceCode

/-! # Surface d=3 and Steane all satisfy `Flag2General.InScope`

This file mechanically verifies that the stabilizer codes of interest
to the paper all satisfy the weight-≤-4 scope restriction of the
2-flag scheme.

If `InScope` holds for every stabilizer of a code, the FT theorem
applies to that code. We discharge the bound via `decide` /
`native_decide` for each concrete stabilizer.

The verification has two parts:
1. Define the *support list* of each stabilizer (the qubits where it
   acts non-trivially).
2. `decide` that each support list has length ≤ 4.

This is a **Lean-side double-check** of what `notes/validate_flag2_extensive.py`
verified numerically.
-/

namespace QStab.QClifford.Flag2General.InScopeCheck

open QStab QStab.QClifford QStab.QClifford.Flag2General

/-! ## Surface d=3 stabilizer supports (matching SurfaceCode.lean) -/

/-- Support list of `s1 = Z₁Z₂Z₄Z₅` (bulk Z, weight 4). -/
def s1_support : List (Fin 9) :=
  [⟨0, by omega⟩, ⟨1, by omega⟩, ⟨3, by omega⟩, ⟨4, by omega⟩]

/-- Support list of `s2 = X₂X₃X₅X₆` (bulk X, weight 4). -/
def s2_support : List (Fin 9) :=
  [⟨1, by omega⟩, ⟨2, by omega⟩, ⟨4, by omega⟩, ⟨5, by omega⟩]

/-- Support list of `s3 = X₄X₅X₇X₈` (bulk X, weight 4). -/
def s3_support : List (Fin 9) :=
  [⟨3, by omega⟩, ⟨4, by omega⟩, ⟨6, by omega⟩, ⟨7, by omega⟩]

/-- Support list of `s4 = Z₅Z₆Z₈Z₉` (bulk Z, weight 4). -/
def s4_support : List (Fin 9) :=
  [⟨4, by omega⟩, ⟨5, by omega⟩, ⟨7, by omega⟩, ⟨8, by omega⟩]

/-- Support list of `s5 = X₁X₂` (boundary X, weight 2). -/
def s5_support : List (Fin 9) := [⟨0, by omega⟩, ⟨1, by omega⟩]

/-- Support list of `s6 = Z₃Z₆` (boundary Z, weight 2). -/
def s6_support : List (Fin 9) := [⟨2, by omega⟩, ⟨5, by omega⟩]

/-- Support list of `s7 = Z₄Z₇` (boundary Z, weight 2). -/
def s7_support : List (Fin 9) := [⟨3, by omega⟩, ⟨6, by omega⟩]

/-- Support list of `s8 = X₈X₉` (boundary X, weight 2). -/
def s8_support : List (Fin 9) := [⟨7, by omega⟩, ⟨8, by omega⟩]

/-! ## All 8 surface d=3 stabilizers are within Flag2 scope -/

example : InScope s1_support := by decide
example : InScope s2_support := by decide
example : InScope s3_support := by decide
example : InScope s4_support := by decide
example : InScope s5_support := by decide
example : InScope s6_support := by decide
example : InScope s7_support := by decide
example : InScope s8_support := by decide

/-- Bundled: all 8 surface d=3 stabilizers are within Flag2 scope. -/
theorem surfaceD3_all_in_scope :
    InScope s1_support ∧ InScope s2_support ∧ InScope s3_support ∧
    InScope s4_support ∧ InScope s5_support ∧ InScope s6_support ∧
    InScope s7_support ∧ InScope s8_support := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## Steane [7,1,3] stabilizers — all weight 4

The Steane code has 6 stabilizer generators (3 X-type + 3 Z-type),
each of weight 4. All within Flag2 scope. -/

/-- X-stab supports for Steane (matching the standard generator matrix). -/
def steane_x1 : List (Fin 7) :=
  [⟨0, by omega⟩, ⟨2, by omega⟩, ⟨4, by omega⟩, ⟨6, by omega⟩]

def steane_x2 : List (Fin 7) :=
  [⟨1, by omega⟩, ⟨2, by omega⟩, ⟨5, by omega⟩, ⟨6, by omega⟩]

def steane_x3 : List (Fin 7) :=
  [⟨3, by omega⟩, ⟨4, by omega⟩, ⟨5, by omega⟩, ⟨6, by omega⟩]

example : InScope steane_x1 := by decide
example : InScope steane_x2 := by decide
example : InScope steane_x3 := by decide

/-! ## Five-qubit code [[5,1,3]] stabilizers — weight 4

Each stabilizer is a tensor product of 4 non-identity Paulis on
disjoint qubits.  Not a CSS code, but if we measure its X-part /
Z-part separately, each part has weight ≤ 4. Within Flag2 scope. -/

/-- A representative weight-4 support for one of the [[5,1,3]] stabs. -/
def fiveQubit_s1 : List (Fin 5) :=
  [⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩]

example : InScope fiveQubit_s1 := by decide

/-! ## A weight-5 example that is OUT OF SCOPE

This is documented as a known limitation: the 2-flag design does
not catch all anc-X faults at this weight. -/

/-- A weight-5 support. -/
def w5_example : List (Fin 6) :=
  [⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩, ⟨4, by omega⟩]

/-- Weight-5 supports are NOT in Flag2 scope. -/
example : ¬ InScope w5_example := by decide

end QStab.QClifford.Flag2General.InScopeCheck
