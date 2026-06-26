import QStab.QClifford.Gate

/-! # `QStab.QClifford.PropagateLemmas` — reusable Pauli-propagation facts

Extracted from `QStab.Compiler.LiftInvariant` (now legacy) on the legacy
retirement pass. Contains four genuinely reusable lemmas that other
parts of the codebase consume:

* `propagateCircuit_append_singleton` — `++ [g]` distributes through
  `propagateCircuit`.
* `propagateGate_paulis_all_I` — every gate preserves the "all Paulis
  are I" invariant.
* `propagateCircuit_paulis_all_I` — generalisation to a whole circuit.
* `propagateCircuit_clean_paulis` — the clean state's Paulis remain `I`
  after propagating any circuit.

The lemmas live in the namespace `QStab.QClifford` so consumers can
open it alongside other gate-level utilities. The namespace alias
`QStab.Compiler` (where they previously lived) is preserved at the end
of the file so any leftover paper/doc references to
`QStab.Compiler.propagateCircuit_clean_paulis` etc. still resolve via
`export` — there is no semantic change to call sites.
-/

namespace QStab.QClifford

open QStab.QClifford

/-- `propagateCircuit` distributes over `++` from the right: appending
    a single gate to the gate-list equals applying that gate to the
    result of the prefix. -/
theorem propagateCircuit_append_singleton {nq : Nat}
    (gs : Circuit nq) (g : Gate nq) (es : ErrorState nq) :
    propagateCircuit (gs ++ [g]) es = propagateGate g (propagateCircuit gs es) := by
  induction gs generalizing es with
  | nil => simp [propagateCircuit]
  | cons g' rest ih =>
    simp [propagateCircuit, List.cons_append, ih]

/-- The invariant "all paulis are I" is preserved by every gate. -/
theorem propagateGate_paulis_all_I {nq : Nat} (g : Gate nq)
    (es : ErrorState nq) (h : ∀ q, es.paulis q = Pauli.I) (q : Fin nq) :
    (propagateGate g es).paulis q = Pauli.I := by
  cases g <;> simp [propagateGate, h, xPart, zPart, pauliMul, hadamardAction]

/-- Generalized: any propagateCircuit preserves "all paulis are I". -/
theorem propagateCircuit_paulis_all_I {nq : Nat} (gs : Circuit nq) (es : ErrorState nq)
    (h : ∀ q, es.paulis q = Pauli.I) (q : Fin nq) :
    (propagateCircuit gs es).paulis q = Pauli.I := by
  induction gs generalizing es with
  | nil => simp [propagateCircuit]; exact h q
  | cons g rest ih =>
    simp only [propagateCircuit]
    apply ih
    intro q'
    exact propagateGate_paulis_all_I g es h q'

/-- Clean state's paulis are preserved by any propagateCircuit. -/
theorem propagateCircuit_clean_paulis {nq : Nat} (gs : Circuit nq) (q : Fin nq) :
    (propagateCircuit gs (ErrorState.clean nq)).paulis q = Pauli.I := by
  apply propagateCircuit_paulis_all_I
  intro q'
  simp [ErrorState.clean]

end QStab.QClifford

/-! ## Back-compat namespace aliases

The lemmas originally lived in `namespace QStab.Compiler` (inside
`QStab/Compiler/LiftInvariant.lean`). We re-export them under that
namespace so that any straggling reference — including ones inside
quarantined `QStab/Compiler/Legacy/LiftInvariant.lean` — continues to
resolve. New code should prefer the `QStab.QClifford.*` names. -/

namespace QStab.Compiler

export QStab.QClifford
  (propagateCircuit_append_singleton
   propagateGate_paulis_all_I
   propagateCircuit_paulis_all_I
   propagateCircuit_clean_paulis)

end QStab.Compiler
