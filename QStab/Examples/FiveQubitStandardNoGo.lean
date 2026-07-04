import QStab.QClifford.PCC.NoGoSoundness
import QStab.QClifford.Compile.Calculus

/-!
# The `[[5,1,3]]` code under the Standard scheme: the compiled-circuit no-go

The no-go theorem, stated at the level you actually want: quantified over **every** high-level
stabilizer-measurement schedule, after **honest compilation** with the fixed compilation rule, no
proof can pass VCGen at distance `3`.

```
∀ order, ¬ Safe (compileProgram (fiveQubitStandardProgram order)) spec₃
       ⇒ ∀ order, IsEmpty (VCGen (input order))     -- no VCGen certificate can pass
```

VCGen stays scheduling-blind — it is handed one compiled circuit.  The `∀ order` and the
`compileProgram` sit *above* the verifier.  The proof engine is `real_dangerous_sound`
(`NoGoSoundness.lean`): a real sub-`d`-fault `failure` run refutes `Safe`.

**Status.**  The *reduction* is proved here and is axiom-clean: the no-go follows, for every
schedule, from a `DangerousRun` — a genuine `qceval` execution of the compiled circuit with `≤ 2`
faults that is a `failure`.  The *remaining obligation* is to discharge `DangerousRun` for every
schedule (the parametric fault-propagation adequacy: an ancilla fault mid-CNOT-ladder deposits the
weight-2 suffix hook, which `nogo_core` completes to a logical failure).  That obligation is stated
explicitly below and is **not** assumed away — it is the next step of the campaign, not a `sorry`.
-/

namespace QStab.Examples.FiveQubitStandardNoGo

open QStab.QClifford QStab.QClifford.PCC QStab.QClifford.Compile

/-- **The schedule-parametrized five-qubit Standard program.**  Measure each of the four
`[[5,1,3]]` stabilizers in the CNOT order given by `order i`, under the NZ (unflagged) scheme.
Built by the same code-agnostic `fold (.meas .NZ (order i))` the surface program uses. -/
def fiveQubitStandardProgram (order : Fin 4 → RuleSchedule 5) : XZProgram 5 :=
  (List.finRange 4).foldr (fun i acc => .seq (.meas .NZ (order i)) acc) .skip

/-- The honestly-compiled QClifford circuit for schedule `order`. -/
def fiveQubitStandardCircuit (order : Fin 4 → RuleSchedule 5) :
    FCircuit (5 + programHelperCount (fiveQubitStandardProgram order)) :=
  compileProgram (fiveQubitStandardProgram order)

/-- **The remaining obligation (parametric adequacy).**  For schedule `order` and a code spec, a
real `qceval` run of the compiled circuit reaching a state with `≤ spec.d - 1` faults that is a
`failure`.  Discharging this for *every* `order` is the fault-propagation campaign — the honest
circuit-semantics content of the no-go. -/
def DangerousRun (order : Fin 4 → RuleSchedule 5)
    (spec : CodeSpec (5 + programHelperCount (fiveQubitStandardProgram order))) : Prop :=
  ∃ σ, qceval (fiveQubitStandardCircuit order) (QCState.clean _) σ ∧
    σ.lambda ≤ spec.d - 1 ∧ failure spec σ.es

/-- **The no-go reduction (axiom-clean).**  For every schedule, a dangerous run refutes `Safe` of
the honestly compiled circuit. -/
theorem fiveQubit_standard_nogo (order : Fin 4 → RuleSchedule 5)
    (spec : CodeSpec (5 + programHelperCount (fiveQubitStandardProgram order)))
    (h : DangerousRun order spec) :
    ¬ Safe (fiveQubitStandardCircuit order) spec := by
  obtain ⟨σ, hrun, hlam, hfail⟩ := h
  exact real_dangerous_sound _ spec σ hrun hlam hfail

/-- **No VCGen certificate can pass (axiom-clean).**  For every schedule, given a dangerous run,
the verifier's proof obligation for the compiled circuit is unsatisfiable — no certificate exists.
This is the exact "stop trying" statement, with the `∀ order` and honest `compileProgram` above a
scheduling-blind VCGen. -/
theorem fiveQubit_standard_no_vcgen_cert (order : Fin 4 → RuleSchedule 5)
    (hnq : 0 < 5 + programHelperCount (fiveQubitStandardProgram order))
    (spec : CodeSpec (5 + programHelperCount (fiveQubitStandardProgram order)))
    (hnumStab : 0 < spec.numStab)
    (h : DangerousRun order spec) :
    IsEmpty (VCGen (VCInput.ofPCC (fiveQubitStandardCircuit order) spec .unconditional hnq hnumStab)) := by
  obtain ⟨σ, hrun, hlam, hfail⟩ := h
  refine no_vcgen_cert _ σ ?_ ?_ ?_
  · simpa using hrun
  · simpa using hlam
  · simpa using hfail

end QStab.Examples.FiveQubitStandardNoGo
