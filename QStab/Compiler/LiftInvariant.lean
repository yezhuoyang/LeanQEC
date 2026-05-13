import QStab.QClifford.Gate
import QStab.State

/-! # `QStab.Compiler.LiftInvariant` — bridges QStab invariants to QClifford

Phase B (session 2, iter 8) entry point. Provides:

* `compatible es s` — pointwise equality between the QClifford
  `ErrorState`'s data Paulis and the QStab `State`'s abstract error
  flow `E_tilde`. The ancilla qubit (`Fin (P.n+1)` index `P.n`) is
  unconstrained — QStab abstracts it away.
* `liftReach c es` — `es` is reachable from `ErrorState.clean` by
  propagating *some* sequence of gates drawn from `c` (the bundle's
  circuit). This is the QClifford analog of MultiStep-reachability.
* `liftReach_clean` — clean state satisfies `liftReach` (empty gs).
* `liftReach_preserve` — extending by any gate `g ∈ c` preserves
  `liftReach`; matches the weakened `QCliffordFTBundle.preservation`
  field signature from iter 7.

The connection to source-side `Invariant P` and to `qstab_sound` is
built in iter 9 (SchemeCorrect for xCircuit) and iter 10 (per-gadget
liftInvariant transfer). This file is the structural foundation.
-/

namespace QStab.Compiler

open QStab QStab.QClifford

/-! ## Compatibility predicate -/

/-- Data-qubit-level compatibility: the QClifford error state's
    data-qubit Paulis (indices `0..P.n-1` of `Fin (P.n+1)`) equal the
    QStab state's abstract error vector `E_tilde`. -/
def compatible {P : QECParams} (es : ErrorState (P.n + 1)) (s : State P) : Prop :=
  ∀ i : Fin P.n, es.paulis ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ = s.E_tilde i

/-- Clean QClifford state is compatible with the initial QStab state. -/
theorem compatible_clean (P : QECParams) :
    compatible (P := P) (ErrorState.clean (P.n + 1)) (State.init P) := by
  intro i
  simp [ErrorState.clean, State.init, ErrorVec.identity]

/-! ## Circuit-gate-set reachability -/

/-- `liftReach c es` says `es` is reachable from `ErrorState.clean` by
    propagating some sequence of gates ALL drawn from `c`. The order
    of gates need not match `c`; only the membership constraint
    matters. This is what makes the predicate preserved by every
    `g ∈ c` in the bundle's `preservation` field. -/
def liftReach (c : Circuit nq) (es : ErrorState nq) : Prop :=
  ∃ gs : Circuit nq, (∀ g ∈ gs, g ∈ c) ∧
    es = propagateCircuit gs (ErrorState.clean nq)

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

/-- Clean state always satisfies `liftReach` (witness: empty gate
    sequence). -/
theorem liftReach_clean {nq : Nat} (c : Circuit nq) :
    liftReach c (ErrorState.clean nq) :=
  ⟨[], fun _ h => (List.not_mem_nil h).elim, rfl⟩

/-- **The load-bearing preservation lemma**: applying any gate `g ∈ c`
    to a `liftReach`-state gives another `liftReach`-state. Body:
    extend the witness `gs` by appending `g`. -/
theorem liftReach_preserve {nq : Nat} (c : Circuit nq) (g : Gate nq) (hg : g ∈ c)
    (es : ErrorState nq) (h : liftReach c es) :
    liftReach c (propagateGate g es) := by
  obtain ⟨gs, hsub, hes⟩ := h
  refine ⟨gs ++ [g], ?_, ?_⟩
  · intro g' hmem
    rcases List.mem_append.mp hmem with h1 | h1
    · exact hsub g' h1
    · rcases List.mem_singleton.mp h1 with rfl
      exact hg
  · rw [propagateCircuit_append_singleton, hes]

end QStab.Compiler
