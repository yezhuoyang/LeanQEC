import QStab.Paper.CodeDistance
import QStab.QHL.CodeFiveQubit
import Mathlib.Data.Fintype.Pi

set_option maxRecDepth 8192

/-!
# Code distance of the `[[5,1,3]]` five-qubit code, in the shared assertion vocabulary

A self-contained instantiation of the code-agnostic `CodeDistanceAtLeast` / `CodeDistanceExactly`
predicates (`QStab.Paper.CodeDistance`) for the canonical five-qubit code — a genuinely
**non-CSS** code, distinct in structure from the surface/HGP CSS codes.  The lower bound is the
finite normalizer check (no weight-≤2 undetected operator is nontrivial); the upper bound is a
weight-3 logical `X̄` representative.  Together: distance `= 3` exactly, stated in the same
predicate the parametric codes use — evidence that the distance argument is code-agnostic.

The generators are re-stated as explicit `v5` vectors (the older `FiveQubitCode.lean` carries
unrelated circuit-level bit-rot), and `fq_objectProgram_anchor` certifies they are exactly the
evaluation of the OCaml-language `code` — so the result is about the object program.
-/

namespace QStab.Examples.FiveQubitDistance

open QStab QStab.Paper.CodeDistance

/-- Local `Fintype Pauli` (four elements) — enables the finite `decide` checks. -/
instance : Fintype Pauli where
  elems := {Pauli.I, Pauli.X, Pauli.Y, Pauli.Z}
  complete := fun p => by cases p <;> decide

/-- Positional 5-qubit Pauli vector helper. -/
def v5 (a b c d e : Pauli) : ErrorVec 5 := fun q =>
  if q.val = 0 then a else if q.val = 1 then b else if q.val = 2 then c
  else if q.val = 3 then d else e

/-- The four five-qubit stabilizer generators (cyclic `XZZXI` family). -/
def fqStab : Fin 4 → ErrorVec 5
  | ⟨0, _⟩ => v5 .X .Z .Z .X .I  -- XZZXI
  | ⟨1, _⟩ => v5 .I .X .Z .Z .X  -- IXZZX
  | ⟨2, _⟩ => v5 .X .I .X .Z .Z  -- XIXZZ
  | ⟨3, _⟩ => v5 .Z .X .I .X .Z  -- ZXIXZ

/-- Logical `Z̄ = ZZZZZ`. -/
def fqLogicalZ : ErrorVec 5 := v5 .Z .Z .Z .Z .Z

/-- The five-qubit code as `QECParams` (only the distance-relevant fields matter here;
`backActionSet := ∅` since code distance is a purely combinatorial property). -/
def fqParams : QECParams where
  n := 5; k := 1; d := 3; R := 1; numStab := 4
  stabilizers := fqStab
  backActionSet := fun _ => ∅
  r := 0
  backAction_weight_bound := by intro s e he; exact he.elim
  C_budget := 2
  hn := by omega
  hns := by omega
  hR := by omega

/-- The finite normalizer fact: every weight-≤2 operator is detected or the identity
(`d = 3`).  Kernel-checked over the `4⁵` operators — the combinatorial core. -/
theorem fq_no_weight2 : ∀ (E : ErrorVec 5), ErrorVec.weight E ≤ 2 →
    (∃ i : Fin 4, ErrorVec.parity (fqStab i) E = true) ∨ E = ErrorVec.identity 5 := by
  decide

/-- **Code distance ≥ 3**, in the shared `CodeDistanceAtLeast` vocabulary. -/
theorem fq_codeDistanceAtLeast_3 : CodeDistanceAtLeast fqParams 3 := by
  intro E hcent hnot
  by_contra hlt
  have hw : ErrorVec.weight E ≤ 2 := by omega
  rcases fq_no_weight2 E hw with ⟨i, hi⟩ | hid
  · have hc : ErrorVec.parity (fqStab i) E = false := hcent i
    rw [hc] at hi; exact absurd hi (by decide)
  · exact hnot (by rw [hid]; exact InStab.identity)

/-- A weight-3 logical `X̄` representative: `X̄·s₀ = I Y Y I X` (the all-`X` logical times
generator `s₀`), weight exactly 3, anticommuting with `Z̄`. -/
def fqLogicalX3 : ErrorVec 5 := v5 .I .Y .Y .I .X

/-- The weight-3 logical witness certifying distance ≤ 3. -/
def fqWitness : LogicalWitness fqParams 3 where
  op := fqLogicalX3
  centralizes := by decide
  not_stab := by
    intro h
    have hz : ErrorVec.parity fqLogicalZ fqLogicalX3 = false :=
      parity_commutes_of_InStab (P := fqParams) fqLogicalZ (by decide) h
    revert hz; decide
  weight_eq := by decide

/-- **Five-qubit code distance = 3, exactly** — the shared predicate, on a non-CSS code:
lower bound from the coset/weight argument, upper bound from a weight-3 logical witness. -/
theorem fq_codeDistanceExactly_3 : CodeDistanceExactly fqParams 3 :=
  codeDistanceExactly_intro fq_codeDistanceAtLeast_3 fqWitness

/-! ## Object-program anchor (Route B: certified evaluation, axiom-clean) -/

/-- The arithmetic mirror of the object program reconciles with the distance proof's
generators `fqStab` (pure `Nat` casework — no interpreter). -/
theorem fqEntryArith_eq_fqStab (k : Fin 4) (q : Fin 5) :
    QHL.CodeLang.FiveQubit.fqEntryArith k.val q.val = fqStab k q := by
  fin_cases k <;> fin_cases q <;> rfl

/-- **Object-program anchor.**  The OCaml-style object program
`QHL.CodeLang.FiveQubit.code`, evaluated at `d = 3`, produces *exactly* the generators
`fqStab` whose code distance we proved — composing the certified evaluation
`code_evalAt?_eq_arith` (axiom-clean, no `native_decide`) with the arithmetic bridge.
So `fq_codeDistanceExactly_3` is provably a statement about the object-language program. -/
theorem fq_objectProgram_anchor (k : Fin 4) (q : Fin 5) :
    QHL.CodeLang.FiveQubit.code.evalAt? 3 k.val q.val = some (fqStab k q) := by
  rw [QHL.CodeLang.FiveQubit.code_evalAt?_eq_arith, fqEntryArith_eq_fqStab]

end QStab.Examples.FiveQubitDistance
