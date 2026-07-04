import QStab.QClifford.PCC.VCGen

/-!
# No-go soundness — the verifier's "stop trying" rule

The dual of `vcgen_sound`.  `vcgen_sound` says: a discharged certificate implies the circuit is
`Safe`.  Here we prove the contrapositive engine: a **real dangerous run** — a `qceval` execution
of the (honestly compiled) circuit with at most `d-1` faults that is nonetheless a `failure` —
makes `Safe` impossible, and therefore **no VCGen certificate can pass** for that circuit at
distance `d`.

This is exactly the semantics a *no-go* proof-carrying certificate needs.  The message to the
verifier is not "here is why your circuit is safe" but "here is a sub-`d`-fault logical error;
no proof of distance `d` can exist — stop trying."  Crucially the verifier still knows nothing
about scheduling: it is handed one compiled circuit `C` and a dangerous run for it.  Quantifying
the dangerous run over *all* schedules (with `C := compileProgram (standardProgram order)`) is a
meta-statement that lives above the verifier.
-/

namespace QStab.QClifford.PCC

open QStab.QClifford

/-- **A real dangerous run refutes `Safe`.**  A `qceval` execution reaching a state with at most
`spec.d - 1` faults that is a `failure` contradicts the `ToleratesFaultsΛ (spec.d - 1)` conjunct
of `Safe`.  This is the real-semantics dual of the `reach` slot — a reach witness *below* the
claimed distance. -/
theorem real_dangerous_sound {nq : Nat} (C : FCircuit nq) (spec : CodeSpec nq)
    (σ : QCState nq) (hrun : qceval C (QCState.clean nq) σ)
    (hlam : σ.lambda ≤ spec.d - 1) (hfail : failure spec σ.es) :
    ¬ Safe C spec := by
  intro hSafe
  exact hSafe.2.2.2.1 σ hrun hlam hfail

/-- **No VCGen certificate can pass** for a circuit that admits a dangerous run — the no-go
analogue of `vcgen_sound`.  Any certificate would, by `vcgen_sound`, force `Safe`, which the
dangerous run refutes.  So the verifier can *soundly* reject every candidate proof. -/
theorem no_vcgen_cert {nq : Nat} (input : VCInput nq)
    (σ : QCState nq) (hrun : qceval input.program (QCState.clean nq) σ)
    (hlam : σ.lambda ≤ input.toCodeSpec.d - 1) (hfail : failure input.toCodeSpec σ.es) :
    IsEmpty (VCGen input) := by
  constructor
  intro cert
  exact real_dangerous_sound input.program input.toCodeSpec σ hrun hlam hfail (vcgen_sound cert)

end QStab.QClifford.PCC
