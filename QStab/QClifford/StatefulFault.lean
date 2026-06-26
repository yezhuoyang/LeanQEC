import QStab.QClifford.ToleratesFaults

/-! # State-resident fault counter `λ` for QClifford

The existing development (`FaultSemantics.lean`, `FaultHoare.lean`) keeps
the injection count `w` as an **index of the execution relation**
(`fcevalW w fc es es'`), and defines `ToleratesFaults` by ranging over
`w ≤ t`. That works, but is operationally inconvenient when stating
Hoare-style assertions: the count is not visible in the state, so one
cannot write a precondition like `λ = 0` or a postcondition like
`λ ≤ t → ¬failure`.

This file makes the count **first-class in the state**, mirroring QStab
(`Defs.QStabState` carries `λ₀, λ₁, λ₂, λ₃, λ_E` as fields of `σ`). The
construction is purely additive: nothing in the existing
`ErrorState`/`fstep`/`fcevalW` development is touched.

* `QCState` wraps an `ErrorState` with a `Nat` field `lambda`.
* `qcstep` is the non-deterministic single-instruction transition on
  `QCState`. `step_idle` leaves `λ` unchanged; `step_inject` bumps
  `λ ↦ λ + 1`.
* `qceval` is the reflexive-transitive closure.
* `ToleratesFaultsΛ` defines fault tolerance in terms of the
  `QCState.lambda` field instead of an external index.
* `tolerates_iff_lambda` proves the two formulations agree.

## Why this matters for the paper

With `λ` resident in the state, the QClifford fault-tolerance condition
reads cleanly as a Hoare triple over `qceval`:

  `⟨clean, λ = 0⟩  fc  ⟨λ ≤ t → ¬failure⟩`

This is the gate-level analog of QStab's
`(C_budget − C) ≤ t → invariant`, and is what the paper (§3) advertises
as "fault tolerance at QClifford".
-/

namespace QStab.QClifford

/-! ## The state -/

/-- A **QClifford program state** with a state-resident fault counter.
    `paulis` and `measFlips` are the existing `ErrorState` fields;
    `lambda` is the number of single-qubit Pauli faults injected so far.
    This mirrors QStab's `σ` carrying per-type counters `λ₀, …, λ_E`. -/
structure QCState (nq : Nat) where
  /-- Underlying gate-level error state. -/
  es : ErrorState nq
  /-- Number of single-qubit Pauli injections that have fired. -/
  lambda : Nat

/-- The clean state: no errors, no flips, no injections. -/
def QCState.clean (nq : Nat) : QCState nq where
  es := ErrorState.clean nq
  lambda := 0

@[simp] theorem QCState.clean_lambda (nq : Nat) :
    (QCState.clean nq).lambda = 0 := rfl

@[simp] theorem QCState.clean_es (nq : Nat) :
    (QCState.clean nq).es = ErrorState.clean nq := rfl

/-! ## Single-instruction transition -/

/-- **Non-deterministic single-instruction transition** with
    state-resident `λ`. The three rules mirror `fstep`:

    * `step_gate`   — a gate propagates via `propagateGate`; `λ` is
      preserved (no fault was injected).
    * `step_idle`   — an error location may inject *nothing*; `λ` is
      preserved.
    * `step_inject` — an error location may inject one Pauli `p ≠ I` on
      its qubit `q`; `λ ↦ λ + 1`.

    The choice between `step_idle` and `step_inject`, and the choice of
    `p`, is the full non-determinism of the fault model. The `λ`-bump
    on `step_inject` is the only operational change vs. `fstep`. -/
inductive qcstep {nq : Nat} : FInstr nq → QCState nq → QCState nq → Prop where
  | step_gate (g : Gate nq) (σ : QCState nq) :
      qcstep (.gate g) σ ⟨propagateGate g σ.es, σ.lambda⟩
  | step_idle (q : Fin nq) (σ : QCState nq) :
      qcstep (.errLoc q) σ σ
  | step_inject (q : Fin nq) (σ : QCState nq)
      (p : Pauli) (hp : p ≠ Pauli.I) :
      qcstep (.errLoc q) σ ⟨σ.es.inject q p, σ.lambda + 1⟩

/-! ## Multi-instruction execution -/

/-- **Multi-instruction execution** with state-resident `λ`. Concatenates
    `qcstep` over the instruction list; each `step_inject` bumps `λ`. -/
inductive qceval {nq : Nat} : FCircuit nq → QCState nq → QCState nq → Prop where
  | nil (σ : QCState nq) : qceval [] σ σ
  | cons (i : FInstr nq) (is : FCircuit nq) (σ σm σ' : QCState nq) :
      qcstep i σ σm → qceval is σm σ' → qceval (i :: is) σ σ'

/-! ## Fault tolerance via the state-resident counter -/

/-- **QClifford fault tolerance (state-resident form).** Running the
    instrumented circuit `fc` from the clean state, every reachable
    QCState whose `λ` is at most `t` is non-failing.

    This is the form the paper's §3 advertises: a single quantification
    over reachable QCStates, with the fault budget read off the state
    itself. -/
def ToleratesFaultsΛ {nq : Nat} (fc : FCircuit nq)
    (failure : ErrorState nq → Prop) (t : Nat) : Prop :=
  ∀ σ' : QCState nq,
    qceval fc (QCState.clean nq) σ' → σ'.lambda ≤ t → ¬ failure σ'.es

/-! ## Equivalence with the indexed form

The state-resident form `ToleratesFaultsΛ` is **provably equivalent** to
the original index-based `ToleratesFaults`. The bridge is a count-tracking
isomorphism between `fcevalW` and `qceval`: a run of `fcevalW w fc es es'`
corresponds to a `qceval fc ⟨es, k⟩ ⟨es', k + w⟩` run for every starting
offset `k`. We instantiate at `k = 0` and `es = clean`.
-/

/-- Forward direction of the count-tracking iso: an indexed run lifts to
    a stateful run that bumps `λ` by `w`. -/
theorem qceval_of_fcevalW {nq : Nat} {w : Nat} {fc : FCircuit nq}
    {es es' : ErrorState nq} (k : Nat)
    (h : fcevalW w fc es es') :
    qceval fc ⟨es, k⟩ ⟨es', k + w⟩ := by
  induction h generalizing k with
  | nil es =>
      simpa [Nat.add_zero] using (qceval.nil (nq := nq) ⟨es, k⟩)
  | gate g is es esf w _ ih =>
      exact qceval.cons _ is ⟨es, k⟩ ⟨propagateGate g es, k⟩ ⟨esf, k + w⟩
        (qcstep.step_gate g ⟨es, k⟩) (ih k)
  | idle q is es esf w _ ih =>
      exact qceval.cons _ is ⟨es, k⟩ ⟨es, k⟩ ⟨esf, k + w⟩
        (qcstep.step_idle q ⟨es, k⟩) (ih k)
  | inject q is es esf p hp w _ ih =>
      -- inject bumps λ by 1, then the IH runs from offset k+1
      have hstep : qcstep (.errLoc q) ⟨es, k⟩ ⟨es.inject q p, k + 1⟩ :=
        qcstep.step_inject q ⟨es, k⟩ p hp
      have hrec : qceval is ⟨es.inject q p, k + 1⟩ ⟨esf, (k + 1) + w⟩ := ih (k + 1)
      have heq : (k + 1) + w = k + (w + 1) := by omega
      rw [heq] at hrec
      exact qceval.cons _ is ⟨es, k⟩ ⟨es.inject q p, k + 1⟩ ⟨esf, k + (w + 1)⟩
        hstep hrec

/-- Backward direction: a stateful run from `⟨es, k⟩` to `⟨es', k'⟩` is
    an indexed run with `w = k' − k` (and `k ≤ k'`). -/
theorem fcevalW_of_qceval {nq : Nat} {fc : FCircuit nq}
    {σ σ' : QCState nq} (h : qceval fc σ σ') :
    σ.lambda ≤ σ'.lambda ∧ fcevalW (σ'.lambda - σ.lambda) fc σ.es σ'.es := by
  induction h with
  | nil σ =>
      refine ⟨Nat.le_refl _, ?_⟩
      simpa [Nat.sub_self] using fcevalW.nil σ.es
  | cons i is σ σm σ' hstep _ ih =>
      obtain ⟨hle_m, hindex⟩ := ih
      cases hstep with
      | step_gate g =>
          -- λ unchanged across step_gate; σm = ⟨propagateGate g σ.es, σ.lambda⟩
          refine ⟨hle_m, ?_⟩
          have : fcevalW (σ'.lambda - σ.lambda) (.gate g :: is) σ.es σ'.es :=
            fcevalW.gate g is σ.es σ'.es (σ'.lambda - σ.lambda) hindex
          exact this
      | step_idle q =>
          -- λ unchanged across step_idle; σm = σ
          refine ⟨hle_m, ?_⟩
          have : fcevalW (σ'.lambda - σ.lambda) (.errLoc q :: is) σ.es σ'.es :=
            fcevalW.idle q is σ.es σ'.es (σ'.lambda - σ.lambda) hindex
          exact this
      | step_inject q _σ p hp =>
          -- σm = ⟨σ.es.inject q p, σ.lambda + 1⟩
          have hle : σ.lambda ≤ σ'.lambda := Nat.le_trans (Nat.le_succ _) hle_m
          refine ⟨hle, ?_⟩
          have hdiff : σ'.lambda - σ.lambda = (σ'.lambda - (σ.lambda + 1)) + 1 := by
            have h1 : σ.lambda + 1 ≤ σ'.lambda := hle_m
            omega
          rw [hdiff]
          exact fcevalW.inject q is σ.es σ'.es p hp (σ'.lambda - (σ.lambda + 1)) hindex

/-- **Equivalence between the two FT formulations.** -/
theorem tolerates_iff_lambda {nq : Nat} (fc : FCircuit nq)
    (failure : ErrorState nq → Prop) (t : Nat) :
    ToleratesFaults fc failure t ↔ ToleratesFaultsΛ fc failure t := by
  constructor
  · -- (→) indexed ⇒ state-resident
    intro hTol σ' hev hbound
    obtain ⟨hle, hindex⟩ := fcevalW_of_qceval hev
    -- σ'.lambda - 0 = σ'.lambda
    have hindex' : fcevalW σ'.lambda fc (ErrorState.clean nq) σ'.es := by
      have : σ'.lambda - (QCState.clean nq).lambda = σ'.lambda := by
        simp [QCState.clean]
      rw [this] at hindex
      simpa [QCState.clean] using hindex
    exact hTol σ'.lambda σ'.es hbound hindex'
  · -- (←) state-resident ⇒ indexed
    intro hTolΛ w es' hbound hindex
    have hev : qceval fc ⟨ErrorState.clean nq, 0⟩ ⟨es', 0 + w⟩ :=
      qceval_of_fcevalW (k := 0) hindex
    have hev' : qceval fc (QCState.clean nq) ⟨es', w⟩ := by
      simpa [QCState.clean] using hev
    have hlambda : (⟨es', w⟩ : QCState nq).lambda ≤ t := hbound
    exact hTolΛ ⟨es', w⟩ hev' hlambda

end QStab.QClifford
