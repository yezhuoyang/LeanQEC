import QStab.QClifford.Gate
import QStab.QClifford.PropagateLemmas
import QStab.State
import QStab.Invariant
import QStab.Paper.Soundness

/-!
**LEGACY (quarantined 2026-06-15).** Per audit memo
`audit_compile_qstab_qclifford`, the `liftReach` machinery is consumed
only by the legacy `compileCertificate`, whose joint
`invHolds := liftReach …` / `failure := ∃ i < n, paulis i ≠ I`
predicates are unsatisfiable (every `liftReach` state is paulis-clean).

The four genuinely reusable Pauli-propagation lemmas previously living
in this file (`propagateCircuit_append_singleton`,
`propagateGate_paulis_all_I`, `propagateCircuit_paulis_all_I`,
`propagateCircuit_clean_paulis`) have been extracted to
`QStab/QClifford/PropagateLemmas.lean` and are re-imported here so the
file's `compatible_clean` / `compatible_of_noBackAction` (which
incidentally consume `propagateCircuit_paulis_all_I` via
`liftReach_paulis_clean`) continue to typecheck.

# `QStab.Compiler.LiftInvariant` — bridges QStab invariants to QClifford

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
  `liftReach`; matches the weakened `QCliffordFTCertificate.preservation`
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

-- `propagateCircuit_append_singleton` — extracted to
-- `QStab/QClifford/PropagateLemmas.lean`; re-exported as
-- `QStab.Compiler.propagateCircuit_append_singleton`.

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

/-! ## `liftInvariant`: the existential predicate on `ErrorState`

The bridge from per-fault QStab semantics to per-gate QClifford
states. `liftInvariant P inv es` says "there exists a QStab state
`qs` satisfying `inv.holds` and consistent with `es`'s data Paulis".
This is the predicate the compiled bundle's `invHolds` field will
use. -/

open QStab.Paper.Soundness

/-- The lifted invariant: `es` is consistent with some QStab state
    that satisfies `inv.holds`. -/
def liftInvariant {P : QECParams} (inv : Invariant P)
    (es : ErrorState (P.n + 1)) : Prop :=
  ∃ qs : State P, inv.holds qs ∧ compatible es qs

/-- Initial state condition: the clean QClifford state satisfies
    `liftInvariant` (witness: `State.init P`). -/
theorem liftInvariant_clean {P : QECParams} (inv : Invariant P) :
    liftInvariant inv (ErrorState.clean (P.n + 1)) :=
  ⟨State.init P, inv.holds_init, compatible_clean P⟩

/-! ## Clean-gadget transfer (fault-free case)

For a fault-free gadget Γ with `noBackAction`, propagating `Γ` from
an `initialFromData E` state keeps the data part equal to `E`. So
the QClifford state's data Paulis match the QStab state's `E_tilde`
throughout — `compatible` is preserved (with the QStab state unchanged
or only updated by a `measure` Step that leaves `E_tilde` alone).

Stated for `initialFromData E` inputs only. Multi-gadget composition
will require either a stronger noBackAction or per-gadget reset. -/

/-- Bridge from `noBackAction` (data is preserved) to `compatible`
    preservation after one fault-free gadget run. Applies when the
    input is `initialFromData E` (the stating shape of `noBackAction`). -/
theorem compatible_of_noBackAction
    {P : QECParams} (Γ : Circuit (P.n + 1)) (h_noBA : noBackAction Γ)
    {qs : State P} (h_qs_E : qs.E_tilde = qs.E_tilde) :
    -- For any QStab state qs, the QClifford state propagateCircuit Γ
    -- (initialFromData qs.E_tilde) is compatible with qs.
    compatible (propagateCircuit Γ (initialFromData qs.E_tilde)) qs := by
  intro i
  have := h_noBA qs.E_tilde i
  -- this : dataPauli (runClean Γ qs.E_tilde) i = qs.E_tilde i
  -- runClean Γ E = propagateCircuit Γ (initialFromData E)
  -- dataPauli es i = es.paulis ⟨i.val, ...⟩
  show (propagateCircuit Γ (initialFromData qs.E_tilde)).paulis ⟨i.val, _⟩ = qs.E_tilde i
  exact this

/-! ## Clean-propagation structural fact

Since every individual gate is a no-op on clean paulis (the all-`I`
vector), `liftReach c` states are paulis-clean for any circuit `c`.
This is the structural lemma that makes the bundle's `bridge` field
trivial under the placeholder `failure := fun _ => False`. -/

-- `propagateGate_paulis_all_I`, `propagateCircuit_paulis_all_I`, and
-- `propagateCircuit_clean_paulis` — extracted to
-- `QStab/QClifford/PropagateLemmas.lean`; re-exported under the
-- `QStab.Compiler` namespace so consumers keep their original names.

/-- **`liftReach` corollary**: every state in `liftReach c` has paulis
    all `I`. This is the structural fact making the bundle's bridge
    trivial under the placeholder `failure := fun _ => False` — and
    it's the foundation for the eventual real failure-lift design. -/
theorem liftReach_paulis_clean {nq : Nat} (c : Circuit nq) (es : ErrorState nq)
    (h : liftReach c es) (q : Fin nq) :
    es.paulis q = Pauli.I := by
  obtain ⟨gs, _, hes⟩ := h
  rw [hes]
  exact propagateCircuit_clean_paulis gs q

end QStab.Compiler
