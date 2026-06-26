import QStab.QClifford.FaultSemantics

/-! # QClifford assertion atoms, fault-tolerance condition, and barrier descent

This file collects the **non-Hoare-logic** semantic foundation for QClifford
fault tolerance:

1. **Assertion atoms** (`§ atoms`). A fixed, checkable vocabulary of
   atomic predicates over an `ErrorState`. The gate-level analog of QStab's
   `L_stab` atom table. Every QClifford assertion in the paper is a
   Boolean combination of these atoms.

2. **Fault-tolerance condition** (`ToleratesFaults`). The indexed form
   used by the barrier-descent FT proof: running the instrumented
   circuit `fc` from the clean state with at most `t` injected
   single-qubit Pauli faults never reaches a `failure` state. The bound
   on faults is the **error count** `w` of `fcevalW`.

3. **Barrier descent** (`barrier_tolerates`). The semantic meta-lemma
   that converts a barrier function (with init, alignment, floor
   conditions) into a `ToleratesFaults` fact. This is the engine
   underneath `FTDeriv.BarrierDist`.

The Hoare logic itself (on `QCState` with the λ-aware `F-ErrLoc` rule)
lives in `FaultHoare.lean`. This file is the dependency floor that
both the Hoare logic and the barrier-cert framework rest on.

## Background

The pre-2026-06-13 `FaultHoare.lean` mixed all of this with an UNSOUND
F-Hoare calculus (lacking the λ-bump in F-ErrLoc). That unsound version
has been **deleted** along with its only consumer (a dead compiler).
This file extracts the load-bearing semantic content; the canonical
`FaultHoare.lean` is the λ-aware sound Hoare logic.
-/

namespace QStab.QClifford

/-! ## § atoms — the QClifford assertion vocabulary

Assertions are predicates on `ErrorState nq` (for λ-agnostic predicates)
or `QCState nq` (for λ-mentioning predicates; see `FaultHoare.lean`).
The atoms below are the λ-agnostic vocabulary; the λ atom is added at
the QCState level. Every assertion used is a Boolean/quantifier
combination of these atoms. They are decidable on a concrete state. -/

/-- Single-qubit anticommutation of Paulis: `true` iff the two Paulis
    anticommute. Used to define the symplectic parity atom. -/
def anticommute : Pauli → Pauli → Bool
  | .I, _ => false
  | _, .I => false
  | .X, .X => false
  | .X, .Y => true
  | .X, .Z => true
  | .Y, .X => true
  | .Y, .Y => false
  | .Y, .Z => true
  | .Z, .X => true
  | .Z, .Y => true
  | .Z, .Z => false

/-- **Atom `Pauli@`**: the single-qubit Pauli at data qubit `q` is `p`. -/
def PauliAt {nq : Nat} (es : ErrorState nq) (q : Fin nq) (p : Pauli) : Prop :=
  es.paulis q = p

/-- **Atom `Flip@`**: the measurement-flip bit at qubit `q` is `b`. -/
def FlipAt {nq : Nat} (es : ErrorState nq) (q : Fin nq) (b : Bool) : Prop :=
  es.measFlips q = b

/-- **Atom `Weight`**: the Pauli weight of the error state (number of
    non-identity qubits). The gate-level analog of QStab's `|Ẽ|`. -/
def weightC {nq : Nat} (es : ErrorState nq) : Nat :=
  (Finset.univ.filter (fun q => es.paulis q ≠ Pauli.I)).card

/-- **Atom `Parity`**: the symplectic inner product (mod 2) of a Pauli
    vector `T` (e.g. a stabilizer generator) with the error state. -/
def parityC {nq : Nat} (T : Fin nq → Pauli) (es : ErrorState nq) : Bool :=
  (Finset.univ.filter (fun q => anticommute (T q) (es.paulis q) = true)).card % 2 == 1

/-- **Atom `∈ G`**: membership of the error state's Pauli vector in a
    Pauli set `G` (instantiated to the stabilizer group `S`, its
    normaliser `N(S)`, or a logical coset `L` per code spec). -/
def InGroup {nq : Nat} (G : (Fin nq → Pauli) → Prop) (es : ErrorState nq) : Prop :=
  G es.paulis

/-- **Logical failure**: the residual Pauli is a *nontrivial logical
    operator* — in the normaliser `N(S)` but not in the stabilizer group
    `S`. This is the gate-level image of the QStab logical-coset notion
    that defines `d^circ`.

    NOTE: this is a *reference template* for the failure predicate `fail`
    in `ToleratesFaults`. Concrete Lean instantiations (e.g. for surface
    d=3) use scheme-specific predicates such as `failureIn LogicalClass`
    that wrap this abstract condition in a decidability-friendly form.
    See `QHL/Compile/CompileFT.lean` for the concrete instantiator. -/
def logicalFailure {nq : Nat} (Stab Norm : (Fin nq → Pauli) → Prop)
    (es : ErrorState nq) : Prop :=
  Norm es.paulis ∧ ¬ Stab es.paulis

/-! ## Fault-tolerance condition (indexed form) -/

/-- **The QClifford fault-tolerance condition (indexed form).** Running
    the instrumented circuit `fc` from the clean state with at most `t`
    injected single-qubit Pauli faults never reaches a `failure` state.
    The fault budget `t` bounds the **error count** `w` of `fcevalW`;
    this is the gate-level, location-explicit analog of QStab's
    `d^circ ≥ t+1`.

    The state-resident λ form `ToleratesFaultsΛ` (in `StatefulFault.lean`)
    is provably equivalent (see `tolerates_iff_lambda`). The Hoare-triple
    form (in `FaultHoare.lean`) is also provably equivalent. We retain
    this indexed form because the barrier-descent proof
    (`barrier_tolerates` below) is structurally cleanest in this form
    (induction on `fcevalW`'s error count). -/
def ToleratesFaults {nq : Nat} (fc : FCircuit nq)
    (failure : ErrorState nq → Prop) (t : Nat) : Prop :=
  ∀ (w : Nat) (es' : ErrorState nq),
    w ≤ t → fcevalW w fc (ErrorState.clean nq) es' → ¬ failure es'

/-! ## Barrier descent: from a barrier function to a `ToleratesFaults` fact

A `barrier` `β` measures distance to a logical failure; gates preserve
it, each injection lowers it by at most `1`, and a failure has `β = 0`.
Then with fewer than `d` faults the barrier stays positive, so no
failure occurs. This is the QClifford analog of QStab's barrier
invariant; it is also the engine underneath `FTDeriv.BarrierDist`.
-/

/-- `.gate g ∈ fc` implies `g` survives erasure into the gate circuit. -/
theorem eraseFaults_mem_gate {nq : Nat} {g : Gate nq} {fc : FCircuit nq}
    (h : FInstr.gate g ∈ fc) : g ∈ eraseFaults fc := by
  induction fc with
  | nil => simp at h
  | cons a rest ih =>
      rcases List.mem_cons.mp h with h1 | h1
      · subst h1; exact List.mem_cons_self
      · cases a with
        | gate g' => exact List.mem_cons_of_mem _ (ih h1)
        | errLoc q => simpa [eraseFaults] using ih h1

/-- **Barrier count bound.** If `β` is preserved by every gate of `fc`
    and drops by at most `1` per single-qubit injection, then along any
    weight-`w` execution the barrier drops by at most `w`. -/
theorem barrier_count_bound {nq : Nat} (β : ErrorState nq → Nat)
    (Gates : Gate nq → Prop)
    (gate_inv : ∀ g, Gates g → ∀ es, β (propagateGate g es) = β es)
    (inject_dec : ∀ (q : Fin nq) (es : ErrorState nq) (p : Pauli),
        p ≠ Pauli.I → β es ≤ β (es.inject q p) + 1)
    {w : Nat} {sub : FCircuit nq} {es es' : ErrorState nq}
    (hev : fcevalW w sub es es') :
    (∀ g, FInstr.gate g ∈ sub → Gates g) → β es ≤ β es' + w := by
  induction hev with
  | nil es => intro _; simp
  | gate g is es esf w _ ih =>
      intro hmem
      have hg : Gates g := hmem g List.mem_cons_self
      have hmem' : ∀ g', FInstr.gate g' ∈ is → Gates g' :=
        fun g' h => hmem g' (List.mem_cons_of_mem _ h)
      have hih := ih hmem'
      rw [gate_inv g hg es] at hih
      exact hih
  | idle q is es esf w _ ih =>
      intro hmem
      exact ih (fun g' h => hmem g' (List.mem_cons_of_mem _ h))
  | inject q is es esf p hp w _ ih =>
      intro hmem
      have hih := ih (fun g' h => hmem g' (List.mem_cons_of_mem _ h))
      have hdec := inject_dec q es p hp
      omega

/-- **Barrier ⇒ fault-tolerance (in principle).** A barrier `β` with
    margin `d` at the clean state, preserved by the circuit's gates,
    decreasing by at most `1` per injection, and vanishing on failures,
    proves the circuit tolerates any `t < d` faults. This is the
    gate-level analog of QStab's `Barrier-Intro`/fault-tolerance theorem;
    constructing a concrete `β` for a given code is the engineering step. -/
theorem barrier_tolerates {nq : Nat} (β : ErrorState nq → Nat)
    (fc : FCircuit nq) (failure : ErrorState nq → Prop) (d : Nat)
    (gate_inv : ∀ g ∈ eraseFaults fc, ∀ es, β (propagateGate g es) = β es)
    (inject_dec : ∀ (q : Fin nq) (es : ErrorState nq) (p : Pauli),
        p ≠ Pauli.I → β es ≤ β (es.inject q p) + 1)
    (init : d ≤ β (ErrorState.clean nq))
    (fail_zero : ∀ es, failure es → β es = 0)
    (t : Nat) (ht : t < d) :
    ToleratesFaults fc failure t := by
  intro w es' hw hev hfail
  have hbound : β (ErrorState.clean nq) ≤ β es' + w :=
    barrier_count_bound β (fun g => g ∈ eraseFaults fc)
      (fun g hg es => gate_inv g hg es) inject_dec hev
      (fun g hg => eraseFaults_mem_gate hg)
  have h0 : β es' = 0 := fail_zero es' hfail
  omega

end QStab.QClifford
