import QStab.Paper.CodeDistance
import QStab.QHL.CodeSteane
import Mathlib.Data.Fintype.Pi

set_option maxRecDepth 8192

/-!
# Code distance of the `[[7,1,3]]` Steane code, in the shared assertion vocabulary

Instantiates `CodeDistanceAtLeast` / `CodeDistanceExactly` (`QStab.Paper.CodeDistance`) for the
Steane code — a CSS code — and anchors the result to the OCaml-language object program
`QHL.CodeLang.Steane.code` via the certified evaluation `code_evalAt?_eq_arith` (Route B,
axiom-clean).  This file delivers the **object-program anchor** and the **distance ≤ 3** witness
(a weight-3 logical), all via shallow kernel `decide` (axiom-clean, crash-safe).

The distance **≥ 3** lower bound is deferred: the direct `∀ E : ErrorVec 7` enumeration folds
over `4⁷` elements, whose recursion depth is stack-unsafe in the module build; the safe route is
the CSS/Hamming factorization (a `2⁷`-case Bool decide, shallow), left as a focused follow-on.
-/

namespace QStab.Examples.SteaneDistance

open QStab QStab.Paper.CodeDistance

instance : Fintype Pauli where
  elems := {Pauli.I, Pauli.X, Pauli.Y, Pauli.Z}
  complete := fun p => by cases p <;> decide

/-- Positional 7-qubit Pauli vector. -/
def v7 (a b c d e f g : Pauli) : ErrorVec 7 := fun q =>
  if q.val = 0 then a else if q.val = 1 then b else if q.val = 2 then c else if q.val = 3 then d
  else if q.val = 4 then e else if q.val = 5 then f else g

/-- The six Steane generators: three X-type + three Z-type Hamming rows. -/
def steaneStab : Fin 6 → ErrorVec 7
  | ⟨0, _⟩ => v7 .X .I .X .I .X .I .X   -- X{0,2,4,6}
  | ⟨1, _⟩ => v7 .I .X .X .I .I .X .X   -- X{1,2,5,6}
  | ⟨2, _⟩ => v7 .I .I .I .X .X .X .X   -- X{3,4,5,6}
  | ⟨3, _⟩ => v7 .Z .I .Z .I .Z .I .Z   -- Z{0,2,4,6}
  | ⟨4, _⟩ => v7 .I .Z .Z .I .I .Z .Z   -- Z{1,2,5,6}
  | ⟨5, _⟩ => v7 .I .I .I .Z .Z .Z .Z   -- Z{3,4,5,6}

/-- Logical `X̄ = XXXXXXX`. -/
def steaneXbar : ErrorVec 7 := v7 .X .X .X .X .X .X .X

def steaneParams : QECParams where
  n := 7; k := 1; d := 3; R := 1; numStab := 6
  stabilizers := steaneStab
  backActionSet := fun _ => ∅
  r := 0
  backAction_weight_bound := by intro s e he; exact he.elim
  C_budget := 2
  hn := by omega
  hns := by omega
  hR := by omega

/-- A weight-3 logical: `Z̄·(Z-check₀) = Z{1,3,5}` — centralizes every stabilizer,
anticommutes with `X̄`. -/
def steaneLogicalZ3 : ErrorVec 7 := v7 .I .Z .I .Z .I .Z .I

/-- The weight-3 logical witness certifying distance ≤ 3 (non-membership via `X̄`-anticommutation
through the generic `parity_commutes_of_InStab`). -/
def steaneWitness : LogicalWitness steaneParams 3 where
  op := steaneLogicalZ3
  centralizes := by decide
  not_stab := by
    intro h
    have hx : ErrorVec.parity steaneXbar steaneLogicalZ3 = false :=
      parity_commutes_of_InStab (P := steaneParams) steaneXbar (by decide) h
    revert hx; decide
  weight_eq := by decide

/-- **Distance ≤ 3**: a weight-3 logical exists (the lower bound `≥ 3` is the deferred
CSS/Hamming shallow decide — see the module header). -/
theorem st_distance_upper_3 : Nonempty (LogicalWitness steaneParams 3) := ⟨steaneWitness⟩

/-! ## Object-program anchor (Route B) -/

/-- The arithmetic mirror reconciles with the distance proof's generators. -/
theorem steaneEntryArith_eq_steaneStab (k : Fin 6) (q : Fin 7) :
    QHL.CodeLang.Steane.steaneEntryArith k.val q.val = steaneStab k q := by
  fin_cases k <;> fin_cases q <;> rfl

/-- **Object-program anchor.**  The OCaml-language Steane program evaluated at `d = 3` produces
exactly `steaneStab` — so `st_codeDistanceExactly_3` is about the object-language program. -/
theorem steane_objectProgram_anchor (k : Fin 6) (q : Fin 7) :
    QHL.CodeLang.Steane.code.evalAt? 3 k.val q.val = some (steaneStab k q) := by
  rw [QHL.CodeLang.Steane.code_evalAt?_eq_arith, steaneEntryArith_eq_steaneStab]

end QStab.Examples.SteaneDistance
