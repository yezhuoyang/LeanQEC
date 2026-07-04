import QStab.QClifford.Compile.ETildeCSimulation

/-!
# Generic post-selection QStab→QClifford preservation (the reusable reduction)

The unconditional bridge `hFold_of_valid` (ETildeCSimulation) maps *every* compiled
run to an abstract reachable `State`, requiring every fault's data residual to be
weight-`≤ 1` or in the abstract back-action set `P.backActionSet`.  Schemes with
**post-selection** (Shor / Flag) produce faults whose residual is neither — but
those faults are *detected* (they flip a verifier flag), and the abstract `State`
**already carries the detector field `F`** (XOR-updated by each back-action's
stabilizer parity in the `errII` step).  So post-selection is expressible at the
QStab layer as `F = 0` (accepted), and the whole distance argument stays abstract.

`postselect_barZ_reduction` is the generic reduction: it reuses `faults_to_reachable`
verbatim (so, over a spec whose `backActionSet` is *enlarged* to admit the detected
residuals, the per-fault obligation holds for **every** fault), then closes the
post-selection bar-Z floor from two supplied facts:

* `accepted_barrier` — the **abstract accepted barrier** (Component B): for reachable
  states with `F = 0` and logical `E_tilde`, `C_budget - C ≥ d`.  This is the
  `F`-aware generalization of `aligned_distance_ge_d`; it is proved **once**,
  scheme-independently, and is the sole nontrivial obligation.
* `flag_correspondence` — the detector correspondence: an accepted compiled run
  (`allFlagsZero spec`) maps to an abstract state with `F = 0`.  This threads the
  QClifford post-selection condition into the QStab `F` field.

Everything else — the per-scheme back-action + detection facts — is discharged by
the scheme's compilation (Component D), with no barrier reasoning.
-/

namespace QStab.QClifford.Compile

open QStab QStab.QClifford QStab.QClifford.PCC

/-- **The generic post-selection bar-Z reduction.**  Reusing the abstract
`faults_to_reachable` simulation, an accepted (`allFlagsZero`) clean-start run of a
compiled circuit whose data residual is a nontrivial bar-Z logical fired at least
`d` faults — given the abstract accepted barrier and the detector correspondence.
No scheme knowledge; the back-action set is a parameter (instantiated to the
*enlarged*, post-selection-closed set for Shor/Flag). -/
theorem postselect_barZ_reduction {P : QECParams} {prog : QStabProgram P} {k : Nat}
    {fc : FCircuit (P.n + k)} {spec : CodeSpec (P.n + k)} {d : Nat}
    (logicalZ : ErrorVec P.n)
    (hvalid : ∀ f : FiredFaultWithContext (P.n + k),
      f.site ∈ QStab.QClifford.PCC.errLocsWithContextAux
        (QCState.clean (P.n + k)).es.detectorCursor fc →
      ErrorVec.weight (targetFaultDataResidual P f) ≤ 1 ∨
        ∀ st' : State P, targetFaultDataResidual P f ∈ P.backActionSet (currentStab prog st'))
    (flag_correspondence : ∀ (σ : QCState (P.n + k)) (s : State P),
      qceval fc (QCState.clean (P.n + k)) σ →
      MultiStep prog (.active (State.init P)) (.active s) →
      s.E_tilde = dataErrorOfQCState P k σ → s.C = P.C_budget - σ.lambda →
      allFlagsZero spec σ.es → ∀ j : Fin P.numStab, s.F j = false)
    (accepted_barrier : ∀ s : State P,
      MultiStep prog (.active (State.init P)) (.active s) →
      (∀ j : Fin P.numStab, s.F j = false) →
      (∀ i : Fin P.numStab, ErrorVec.parity (P.stabilizers i) s.E_tilde = false) →
      ErrorVec.parity logicalZ s.E_tilde = true →
      P.C_budget - s.C ≥ d) :
    ∀ σ : QCState (P.n + k),
      qceval fc (QCState.clean (P.n + k)) σ → σ.lambda ≤ P.C_budget →
      allFlagsZero spec σ.es →
      (∀ i : Fin P.numStab,
        ErrorVec.parity (P.stabilizers i) (dataErrorOfQCState P k σ) = false) →
      ErrorVec.parity logicalZ (dataErrorOfQCState P k σ) = true →
      d ≤ σ.lambda := by
  intro σ hrun hbudget hAccepted hSyn hLog
  obtain ⟨faults, hlen, hmem, hprod⟩ := hproduct_of_qceval hrun
  obtain ⟨s, hreach, hE, hC⟩ :=
    faults_to_reachable σ faults hlen hbudget (fun f hf => hvalid f (hmem f hf)) hprod
  have hFzero : ∀ j : Fin P.numStab, s.F j = false :=
    flag_correspondence σ s hrun hreach hE hC hAccepted
  have hSyn' : ∀ i : Fin P.numStab, ErrorVec.parity (P.stabilizers i) s.E_tilde = false := by
    intro i; rw [hE]; exact hSyn i
  have hLog' : ErrorVec.parity logicalZ s.E_tilde = true := by rw [hE]; exact hLog
  have hbar : P.C_budget - s.C ≥ d := accepted_barrier s hreach hFzero hSyn' hLog'
  rw [hC] at hbar
  omega

/-- info: 'QStab.QClifford.Compile.postselect_barZ_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms postselect_barZ_reduction

end QStab.QClifford.Compile
