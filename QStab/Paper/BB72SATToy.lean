import Std.Tactic.BVDecide.LRAT

/-!
# Toy LRAT-via-`check_sound` test

Validates the streaming-verifier path before scaling to BB72:

  * `LRAT.check : Array IntAction → CNF Nat → Bool` (verified function)
  * `LRAT.check_sound` proves `check = true → cnf.Unsat`
  * `native_decide` evaluates `check` in compiled code; resulting proof
    term is shallow (= `Decidable.decide ... = .isTrue rfl`), so kernel
    recursion isn't an issue.

This file: 4-clause UNSAT instance from Mathlib's `lrat_proof` example,
imported the new way.
-/

open Std.Sat
open Std.Tactic.BVDecide.LRAT

/-- Toy CNF: `(x ∨ y) ∧ (¬x ∨ y) ∧ (x ∨ ¬y) ∧ (¬x ∨ ¬y)` — clearly UNSAT.

    Note: `CNF.lift` shifts variables by +1 internally, so DIMACS var `i`
    must be encoded as Lean var `i - 1` (= 0-indexed). LRAT IntAction
    literals stay 1-indexed (DIMACS-style). -/
def toy_cnf : CNF Nat :=
  ⟨#[
    [(0, true),  (1, true)],
    [(0, false), (1, true)],
    [(0, true),  (1, false)],
    [(0, false), (1, false)]
  ]⟩

/-- Toy LRAT proof, parsed via the Std parser to ensure faithful format. -/
def toy_lrat_bytes : ByteArray :=
  String.toUTF8 "5 -2 0 4 3 0\n5 d 3 4 0\n6 1 0 5 1 0\n6 d 1 0\n7 0 5 2 6 0\n"

def toy_lrat : Array IntAction :=
  match parseLRATProof toy_lrat_bytes with
  | .ok a => a
  | .error _ => #[]

#eval toy_lrat
#eval check toy_lrat toy_cnf

/-- The toy CNF is unsatisfiable, proven by the verified LRAT checker. -/
theorem toy_unsat : toy_cnf.Unsat := by
  apply check_sound toy_lrat toy_cnf
  native_decide
