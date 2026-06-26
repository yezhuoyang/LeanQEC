import QStab.QClifford.Gate

/-! # QClifford non-deterministic fault semantics

The deterministic core (`Gate`, `propagateGate` in `QClifford/Gate.lean`,
and `cevalC` in `QHL/Target/CEval.lean`) models only the **fault-free**
gate circuit. This file adds the fault model the gate level was missing:
explicit single-qubit Pauli **error locations** as first-class
instructions, together with a **non-deterministic injection transition**
and an **error count**.

## Contrast with QStab

QStab's `Step` (see `QStab/Step.lean`) is non-deterministic over the
*abstract* error location: `Step.type0 s i p` injects a Pauli `p` at an
arbitrary data index `i`, with no commitment to where in a gate circuit
that fault physically sits.

At QClifford the error locations are **fixed in the circuit**. An
`FInstr.errLoc q` instruction marks a concrete fault site on a concrete
qubit `q`. The only non-determinism left at such a site is *whether* a
fault occurs and *which* single-qubit Pauli `p ≠ I` is injected —
mirroring QStab's `(p, hp : p ≠ I)`, but with the location now
syntactically pinned.

Unlike QStab, QClifford carries **no effect-type annotation** on a fault.
The four-effect classification (Type-0/I/II/III) is a *QStab abstraction*
that exists precisely to avoid enumerating concrete locations; once the
location is fixed in the circuit there is nothing to classify at this
layer. We therefore track only a raw **error count** (the number of
injected single-qubit Paulis), via the weight index `w` of `fcevalW`.

## Conservative extension

`eraseFaults` drops the error locations and recovers the underlying gate
circuit; taking the no-fault (`idle`) choice at every site reproduces the
deterministic `propagateCircuit` trajectory with error count `0`
(`fcevalW_faultFree`, `fceval_faultFree`). So the existing deterministic
semantics is the count-`0` slice of the new relation, and nothing in the
fault-free development changes.
-/

namespace QStab.QClifford

/-- A **faulty instruction**: either a Clifford gate, or an error
    location on qubit `q`. An error location carries no effect type —
    only its position (its index in the list) and qubit are fixed; the
    injected Pauli is chosen non-deterministically by the semantics. -/
inductive FInstr (nq : Nat) where
  | gate   (g : Gate nq)
  | errLoc (q : Fin nq)

/-- A **faulty circuit**: a gate circuit interspersed with error
    locations at fixed positions. -/
abbrev FCircuit (nq : Nat) := List (FInstr nq)

/-- Erase the error locations, recovering the underlying fault-free gate
    circuit. The image is exactly an ordinary `Circuit`. -/
def eraseFaults {nq : Nat} : FCircuit nq → Circuit nq
  | []                 => []
  | .gate g   :: rest  => g :: eraseFaults rest
  | .errLoc _ :: rest  => eraseFaults rest

@[simp] theorem eraseFaults_nil {nq : Nat} :
    eraseFaults ([] : FCircuit nq) = [] := rfl

@[simp] theorem eraseFaults_gate {nq : Nat} (g : Gate nq) (rest : FCircuit nq) :
    eraseFaults (.gate g :: rest) = g :: eraseFaults rest := rfl

@[simp] theorem eraseFaults_errLoc {nq : Nat} (q : Fin nq) (rest : FCircuit nq) :
    eraseFaults (.errLoc q :: rest) = eraseFaults rest := rfl

/-- **Single-instruction transition** (non-deterministic).

    * `step_gate`   — a gate propagates deterministically via
      `propagateGate`.
    * `step_idle`   — an error location may inject *nothing* (the fault
      does not occur).
    * `step_inject` — an error location may inject *one* single-qubit
      Pauli `p ≠ I` on its qubit `q`.

    The choice between `step_idle` and `step_inject`, and the choice of
    `p`, is the entire non-determinism of the QClifford fault model. -/
inductive fstep {nq : Nat} : FInstr nq → ErrorState nq → ErrorState nq → Prop where
  | step_gate (g : Gate nq) (es : ErrorState nq) :
      fstep (.gate g) es (propagateGate g es)
  | step_idle (q : Fin nq) (es : ErrorState nq) :
      fstep (.errLoc q) es es
  | step_inject (q : Fin nq) (es : ErrorState nq)
      (p : Pauli) (hp : p ≠ Pauli.I) :
      fstep (.errLoc q) es (es.inject q p)

/-- **Multi-instruction execution** (non-deterministic), the QClifford
    analog of QStab `MultiStep`: run the instruction list left-to-right,
    resolving the non-determinism of every error location independently. -/
inductive fceval {nq : Nat} : FCircuit nq → ErrorState nq → ErrorState nq → Prop where
  | nil (es : ErrorState nq) : fceval [] es es
  | cons (i : FInstr nq) (is : FCircuit nq) (es esm es' : ErrorState nq) :
      fstep i es esm → fceval is esm es' → fceval (i :: is) es es'

/-- **Error-count-indexed execution**: `fcevalW w fc es es'` says `es'`
    is reachable from `es` by running `fc` with *exactly* `w` single-qubit
    Pauli injections. The count `w` is the number of error locations that
    fired (`inject`); idle locations and gates do not contribute. This is
    the measure a "tolerates `t` faults" definition will bound. -/
inductive fcevalW {nq : Nat} : Nat → FCircuit nq → ErrorState nq → ErrorState nq → Prop where
  | nil (es : ErrorState nq) : fcevalW 0 [] es es
  | gate (g : Gate nq) (is : FCircuit nq) (es es' : ErrorState nq) (w : Nat) :
      fcevalW w is (propagateGate g es) es' →
      fcevalW w (.gate g :: is) es es'
  | idle (q : Fin nq) (is : FCircuit nq) (es es' : ErrorState nq) (w : Nat) :
      fcevalW w is es es' →
      fcevalW w (.errLoc q :: is) es es'
  | inject (q : Fin nq) (is : FCircuit nq) (es es' : ErrorState nq)
      (p : Pauli) (hp : p ≠ Pauli.I) (w : Nat) :
      fcevalW w is (es.inject q p) es' →
      fcevalW (w + 1) (.errLoc q :: is) es es'

/-- The count-indexed relation refines the plain one: forgetting the
    count yields an `fceval` execution. -/
theorem fceval_of_fcevalW {nq : Nat} {w : Nat} {fc : FCircuit nq}
    {es es' : ErrorState nq} (h : fcevalW w fc es es') : fceval fc es es' := by
  induction h with
  | nil es => exact fceval.nil es
  | gate g is es esf w _ ih =>
      exact fceval.cons _ is es _ esf (fstep.step_gate g es) ih
  | idle q is es esf w _ ih =>
      exact fceval.cons _ is es _ esf (fstep.step_idle q es) ih
  | inject q is es esf p hp w _ ih =>
      exact fceval.cons _ is es _ esf (fstep.step_inject q es p hp) ih

/-- Conversely, every `fceval` execution has *some* error count. -/
theorem exists_count {nq : Nat} {fc : FCircuit nq} {es es' : ErrorState nq}
    (h : fceval fc es es') : ∃ w, fcevalW w fc es es' := by
  induction h with
  | nil es => exact ⟨0, fcevalW.nil es⟩
  | cons i is es esm esf hstep _ ih =>
      obtain ⟨w, hw⟩ := ih
      cases hstep with
      | step_gate g => exact ⟨w, fcevalW.gate g is es esf w hw⟩
      | step_idle q => exact ⟨w, fcevalW.idle q is es esf w hw⟩
      | step_inject q _es p hp => exact ⟨w + 1, fcevalW.inject q is es esf p hp w hw⟩

/-- **Conservative extension (counted form).** Taking the no-fault choice
    at every error location reproduces the deterministic
    `propagateCircuit` trajectory on the erased circuit, with error count
    `0`. -/
theorem fcevalW_faultFree {nq : Nat} (fc : FCircuit nq) (es : ErrorState nq) :
    fcevalW 0 fc es (propagateCircuit (eraseFaults fc) es) := by
  induction fc generalizing es with
  | nil => simpa using fcevalW.nil es
  | cons i rest ih =>
      cases i with
      | gate g =>
          have h := fcevalW.gate g rest es
            (propagateCircuit (eraseFaults rest) (propagateGate g es)) 0 (ih (propagateGate g es))
          simpa [eraseFaults, propagateCircuit] using h
      | errLoc q =>
          have h := fcevalW.idle q rest es
            (propagateCircuit (eraseFaults rest) es) 0 (ih es)
          simpa [eraseFaults] using h

/-- **Conservative extension (plain form).** The deterministic fault-free
    run is one of the non-deterministic executions. -/
theorem fceval_faultFree {nq : Nat} (fc : FCircuit nq) (es : ErrorState nq) :
    fceval fc es (propagateCircuit (eraseFaults fc) es) :=
  fceval_of_fcevalW (fcevalW_faultFree fc es)

end QStab.QClifford
