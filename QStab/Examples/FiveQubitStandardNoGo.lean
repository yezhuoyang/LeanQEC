import QStab.QClifford.PCC.NoGoSoundness
import QStab.QClifford.Compile.Calculus
import QStab.Examples.FiveQubitNoGo

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

/-! ## Sound quantification over ALL Standard scheduling orders

The soundness of "for all possible scheduling" is not negotiable: `order` must range over exactly
the *valid* Standard schedules of the `[[5,1,3]]` code — every CNOT ordering of the correct
measurement, and nothing else.  An unconstrained `Fin 4 → RuleSchedule 5` also contains garbage
(wrong qubits, wrong Paulis, repeats, empty), for which `¬Safe` would hold for a trivial,
non-hook reason.  The predicate below excludes all of that. -/

/-- The X/Z label of a stabilizer entry.  The five-qubit generators use only `X` and `Z`. -/
def kindOf (p : Pauli) : XZPauli := if p = Pauli.X then XZPauli.X else XZPauli.Z

/-- The canonical measurement slots of stabilizer `i`: one slot per **support** qubit, its kind
the stabilizer's Pauli there.  These are the CNOTs a correct Standard measurement of `T_i` must
perform; a schedule chooses only their order. -/
def canonicalSlots (i : Fin 4) : List (ScheduledPauli 5) :=
  (List.finRange 5).filterMap fun q =>
    if FiveQubitNoGo.fqStab i q = Pauli.I then none
    else some { kind := kindOf (FiveQubitNoGo.fqStab i q), qubit := q }

/-- **A sound and complete "for all scheduling orders" predicate.**  `order` is a valid Standard
schedule iff, for every stabilizer `i`, its slot list is a **permutation** of the canonical
measurement slots — exactly the correct support qubits with the correct `X`/`Z` kinds, in *any*
CNOT order.  `List.Perm` admits every ordering (the entire Standard scheduling freedom) and no
invalid schedule (missing/extra/wrong qubit, wrong Pauli, or a repeat), because a permutation
preserves the multiset of `(kind, qubit)` slots exactly. -/
def ValidStandardSchedule (order : Fin 4 → RuleSchedule 5) : Prop :=
  ∀ i, List.Perm (order i).slots (canonicalSlots i)

/-- Sanity check: the identity ordering (canonical slots as written) is a valid schedule — the
predicate is inhabited, so `∀ valid order, …` is not vacuous. -/
theorem canonicalOrder_valid :
    ValidStandardSchedule (fun i => ⟨canonicalSlots i⟩) :=
  fun _ => List.Perm.refl _

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

/-! ## The no-go over exactly the valid schedules

Every valid NZ schedule compiles to a `FCircuit 9` (5 data + 4 ancillas — `helperCount .NZ = 1`),
so the spec type is uniform. -/

/-- **The remaining adequacy obligation, over valid schedules.**  Every valid Standard schedule
admits a dangerous run — a real ≤`(d-1)`-fault `qceval` `failure` of the compiled circuit.
Discharging this is the fault-propagation campaign; it is the honest circuit-semantics content of
the no-go, stated explicitly here rather than assumed inside a "finished" theorem. -/
def StandardAdequacy (spec : CodeSpec 9) : Prop :=
  ∀ order, ValidStandardSchedule order → DangerousRun order spec

/-- **The five-qubit Standard no-go, over exactly the valid schedules, modulo adequacy.**  For
every valid CNOT ordering of the correct `[[5,1,3]]` measurement, honestly compiled, no proof
passes VCGen at distance `spec.d`.  The `∀ order` (ranging over *precisely* the valid schedules,
by `ValidStandardSchedule`) and the honest `compileProgram` sit above a scheduling-blind VCGen;
the sole open lemma is the circuit-semantics `StandardAdequacy`. -/
theorem fiveQubit_standard_full_nogo (spec : CodeSpec 9) (adeq : StandardAdequacy spec) :
    ∀ order, ValidStandardSchedule order → ¬ Safe (fiveQubitStandardCircuit order) spec :=
  fun order hv => fiveQubit_standard_nogo order spec (adeq order hv)

end QStab.Examples.FiveQubitStandardNoGo
