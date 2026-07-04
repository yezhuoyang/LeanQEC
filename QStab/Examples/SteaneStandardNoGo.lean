import QStab.QClifford.PCC.NoGoSoundness
import QStab.QClifford.Compile.Calculus
import QStab.Paper.CodeDistance

/-!
# The `[[7,1,3]]` Steane code under the Standard scheme: the compiled-circuit no-go

The Steane no-go, stated at the level you actually want: quantified over **every** high-level
stabilizer-measurement schedule, after **honest compilation** with the fixed compilation rule, no
proof can pass VCGen at distance `3`.  Because Steane is CSS, the completing-fault wall that
blocks the (non-CSS) five-qubit campaign dissolves: order the program with all three X-stabilizer
gadgets first and all three Z-stabilizer gadgets last, and run a **pure-Z** attack.  Then every
detector is structurally quiet:

* X-detectors run first on clean data (the Z-faults are injected later) — they measure `0`;
* Z-detectors: a `Z` on a data qubit commutes with a Z-gadget's `CX(data, anc)` (`Z` on the
  control stays on the control, never reaches the ancilla) — so it never flips a Z-measurement.

This file mirrors `FiveQubitStandardNoGo.lean`: the schedule-parametrized program, the honest
compilation, the faithful `CodeSpec`, the sound `ValidStandardSchedule` predicate, the no-go
reduction (`steane_standard_nogo`, via `real_dangerous_sound`), the adequacy obligation
(`StandardAdequacy`), and the packaged full no-go (`steane_standard_full_nogo`).

Everything here is axiom-clean: `[propext, Classical.choice, Quot.sound]`, no `native_decide`.
-/

set_option maxRecDepth 8192

namespace QStab.Examples.SteaneStandardNoGo

open QStab QStab.QClifford QStab.QClifford.PCC QStab.QClifford.Compile

/-! ## Steane stabilizer data (X-first, Z-last) -/

/-- Positional 7-qubit Pauli vector. -/
def v7 (a b c d e f g : Pauli) : ErrorVec 7 := fun q =>
  if q.val = 0 then a else if q.val = 1 then b else if q.val = 2 then c else if q.val = 3 then d
  else if q.val = 4 then e else if q.val = 5 then f else g

/-- The six Steane generators, ordered **X-first then Z-last** (indices `0..5`).  Three X-type
Hamming rows then three Z-type Hamming rows on the 7 data qubits. -/
def steaneStabVec : Fin 6 → ErrorVec 7
  | ⟨0, _⟩ => v7 .X .I .X .I .X .I .X   -- X{0,2,4,6}
  | ⟨1, _⟩ => v7 .I .X .X .I .I .X .X   -- X{1,2,5,6}
  | ⟨2, _⟩ => v7 .I .I .I .X .X .X .X   -- X{3,4,5,6}
  | ⟨3, _⟩ => v7 .Z .I .Z .I .Z .I .Z   -- Z{0,2,4,6}
  | ⟨4, _⟩ => v7 .I .Z .Z .I .I .Z .Z   -- Z{1,2,5,6}
  | ⟨5, _⟩ => v7 .I .I .I .Z .Z .Z .Z   -- Z{3,4,5,6}

/-- Logical `X̄ = XXXXXXX` and `Z̄ = ZZZZZZZ`. -/
def steaneLogicalX : ErrorVec 7 := v7 .X .X .X .X .X .X .X
def steaneLogicalZ : ErrorVec 7 := v7 .Z .Z .Z .Z .Z .Z .Z

/-- The Steane code as `QECParams` (combinatorial fields; `backActionSet` is irrelevant to the
no-go, which quantifies over schedules explicitly). -/
def steaneParams : QECParams where
  n := 7; k := 1; d := 3; R := 1; numStab := 6
  stabilizers := steaneStabVec
  backActionSet := fun _ => ∅
  r := 0
  backAction_weight_bound := by intro s e he; exact he.elim
  C_budget := 2
  hn := by omega
  hns := by omega
  hR := by omega

/-! ## The schedule-parametrized Steane Standard program -/

/-- **The schedule-parametrized Steane Standard program.**  Measure each of the six Steane
stabilizers in the CNOT order given by `order i`, under the NZ (unflagged) scheme.  Built by the
same code-agnostic `fold (.meas .NZ (order i))` the surface program uses.  The `finRange 6` order
gives the X-gadgets (0,1,2) first, the Z-gadgets (3,4,5) last. -/
def steaneStandardProgram (order : Fin 6 → RuleSchedule 7) : XZProgram 7 :=
  (List.finRange 6).foldr (fun i acc => .seq (.meas .NZ (order i)) acc) .skip

/-- The honestly-compiled QClifford circuit for schedule `order`. -/
def steaneStandardCircuit (order : Fin 6 → RuleSchedule 7) :
    FCircuit (7 + programHelperCount (steaneStandardProgram order)) :=
  compileProgram (steaneStandardProgram order)

/-! ## Sound quantification over ALL Standard scheduling orders -/

/-- The X/Z label of a Pauli.  The Steane generators use only `X` and `Z`. -/
def kindOf (p : Pauli) : XZPauli := if p = Pauli.X then XZPauli.X else XZPauli.Z

/-- The canonical measurement slots of stabilizer `i`: one slot per **support** qubit, its kind
the stabilizer's Pauli there.  These are the CNOTs a correct Standard measurement of `T_i` must
perform; a schedule chooses only their order. -/
def canonicalSlots (i : Fin 6) : List (ScheduledPauli 7) :=
  (List.finRange 7).filterMap fun q =>
    if steaneStabVec i q = Pauli.I then none
    else some { kind := kindOf (steaneStabVec i q), qubit := q }

/-- **A sound and complete "for all scheduling orders" predicate.**  `order` is a valid Standard
schedule iff, for every stabilizer `i`, its slot list is a **permutation** of the canonical
measurement slots — exactly the correct support qubits with the correct `X`/`Z` kinds, in *any*
CNOT order.  `List.Perm` admits every ordering (the entire Standard scheduling freedom) and no
invalid schedule. -/
def ValidStandardSchedule (order : Fin 6 → RuleSchedule 7) : Prop :=
  ∀ i, List.Perm (order i).slots (canonicalSlots i)

/-- The canonical schedule: measure each stabilizer's support in index order. -/
def canonicalOrder : Fin 6 → RuleSchedule 7 := fun i => ⟨canonicalSlots i⟩

/-- Sanity check: the canonical ordering is a valid schedule — the predicate is inhabited, so
`∀ valid order, …` is not vacuous. -/
theorem canonicalOrder_valid : ValidStandardSchedule canonicalOrder :=
  fun _ => List.Perm.refl _

/-! ## The faithful Steane code spec (on the 13 = 7 data + 6 ancilla qubits) -/

/-- The Steane stabilizers embedded on the 13 compiled qubits (data on `0..6`, `I` on the six
ancillas `7..12`). -/
def steaneEmb (i : Fin 6) : Fin 13 → Pauli :=
  fun q => if h : q.val < 7 then steaneStabVec i ⟨q.val, h⟩ else Pauli.I

/-- The faithful `CodeSpec` the verifier checks against: the Steane stabilizers, data on `0..6`,
each stabilizer reading its own ancilla-measurement detector, distance `3`. -/
def steaneSpec : CodeSpec 13 where
  numStab := 6
  numFlags := 6
  isData := fun q => decide (q.val < 7)
  stabilizer := steaneEmb
  stabilizerReadout := fun i => [⟨i.val, i.isLt⟩]
  postselectFlag := fun _ => false
  flagSlot := fun i => i.val
  flagSlot_injective := by intro a b h; exact Fin.ext h
  flagSlot_ordered := by intro i; rfl
  readout_disjoint := by
    intro i j hij s hs_i hs_j
    simp only [List.mem_singleton] at hs_i hs_j
    apply hij; apply Fin.ext
    have e1 : s.val = i.val := congrArg Fin.val hs_i
    have e2 : s.val = j.val := congrArg Fin.val hs_j
    omega
  gadgetDetectorStart := fun i => i.val
  gadget := fun _ => []
  expectedProgram := []
  d := 3
  d_pos := by decide

/-! ## The no-go reduction (axiom-clean) -/

/-- **The remaining obligation (parametric adequacy).**  For schedule `order` and a code spec, a
real `qceval` run of the compiled circuit reaching a state with `≤ spec.d - 1` faults that is a
`failure`.  Discharging this for *every* `order` is the fault-propagation campaign. -/
def DangerousRun (order : Fin 6 → RuleSchedule 7)
    (spec : CodeSpec (7 + programHelperCount (steaneStandardProgram order))) : Prop :=
  ∃ σ, qceval (steaneStandardCircuit order) (QCState.clean _) σ ∧
    σ.lambda ≤ spec.d - 1 ∧ failure spec σ.es

/-- **The no-go reduction (axiom-clean).**  For every schedule, a dangerous run refutes `Safe` of
the honestly compiled circuit. -/
theorem steane_standard_nogo (order : Fin 6 → RuleSchedule 7)
    (spec : CodeSpec (7 + programHelperCount (steaneStandardProgram order)))
    (h : DangerousRun order spec) :
    ¬ Safe (steaneStandardCircuit order) spec := by
  obtain ⟨σ, hrun, hlam, hfail⟩ := h
  exact real_dangerous_sound _ spec σ hrun hlam hfail

/-- **No VCGen certificate can pass (axiom-clean).**  For every schedule, given a dangerous run,
the verifier's proof obligation for the compiled circuit is unsatisfiable — no certificate exists. -/
theorem steane_standard_no_vcgen_cert (order : Fin 6 → RuleSchedule 7)
    (hnq : 0 < 7 + programHelperCount (steaneStandardProgram order))
    (spec : CodeSpec (7 + programHelperCount (steaneStandardProgram order)))
    (hnumStab : 0 < spec.numStab)
    (h : DangerousRun order spec) :
    IsEmpty (VCGen (VCInput.ofPCC (steaneStandardCircuit order) spec .unconditional hnq hnumStab)) := by
  obtain ⟨σ, hrun, hlam, hfail⟩ := h
  refine no_vcgen_cert _ σ ?_ ?_ ?_
  · simpa using hrun
  · simpa using hlam
  · simpa using hfail

/-! ## The no-go over exactly the valid schedules

Every valid NZ schedule of the six Steane stabilizers compiles to an `FCircuit 13` (7 data +
6 ancillas — `helperCount .NZ = 1` per gadget, and `7 + 6 = 13` reduces definitionally), so the
spec type is uniform. -/

/-- **The adequacy obligation, over valid schedules.**  Every valid Standard schedule admits a
dangerous run — a real ≤`(d-1)`-fault `qceval` `failure` of the compiled circuit.  (`CodeSpec 13`
type-checks against the compiled `FCircuit (7 + programHelperCount …)` because that index reduces
to `13` definitionally.) -/
def StandardAdequacy (spec : CodeSpec 13) : Prop :=
  ∀ order, ValidStandardSchedule order → DangerousRun order spec

/-- **The Steane Standard no-go, over exactly the valid schedules, modulo adequacy.**  For every
valid CNOT ordering of the correct Steane measurement, honestly compiled, no proof passes VCGen
at distance `spec.d`. -/
theorem steane_standard_full_nogo (spec : CodeSpec 13) (adeq : StandardAdequacy spec) :
    ∀ order, ValidStandardSchedule order → ¬ Safe (steaneStandardCircuit order) spec :=
  fun order hv => steane_standard_nogo order spec (adeq order hv)

/-! ## A concrete circuit-level witness (a real fcevalW dangerous run)

For the canonical schedule, an explicit **pure-Z** 2-fault script (`Z` at error-locations 2 and 29)
drives the honestly-compiled circuit — through the real `runFScript`/detector semantics — to a
genuine `failure`: an undetected logical error with only 2 < d = 3 faults.  Everything is kernel
`decide` (no `native_decide`).  This confirms `steaneSpec` + kernel `decide` on the 13-qubit
circuit is feasible, and that the CSS pure-Z attack lands. -/

/-- The concrete 2-fault (pure-`Z`) attack script on the canonical compiled circuit. -/
def canonAttackScript : List (Option Pauli) :=
  (List.range 84).map fun k => if k = 2 ∨ k = 29 then some Pauli.Z else none

/-- **A real dangerous run of the honestly-compiled circuit** for the canonical schedule: a
2-fault `qceval` execution that is a `failure`.  Built from the concrete script via
`runFScript_sound` + `qceval_of_fcevalW`, with `failure` discharged by kernel `decide`. -/
theorem steaneSpec_canonical_dangerousRun : DangerousRun canonicalOrder steaneSpec :=
  ⟨_, qceval_of_fcevalW (k := 0)
        (runFScript_sound (steaneStandardCircuit canonicalOrder) canonAttackScript
          (ErrorState.clean 13)),
   by decide, by decide⟩

/-- **The honestly-compiled circuit for the canonical schedule is not `Safe`** — a concrete,
axiom-clean instance of the no-go at the real circuit level (one valid schedule; the universal
statement is the parametric adequacy in `SteaneStandardNoGoAdequacy.lean`). -/
theorem canonical_not_safe :
    ¬ Safe (steaneStandardCircuit canonicalOrder) steaneSpec :=
  steane_standard_nogo canonicalOrder steaneSpec steaneSpec_canonical_dangerousRun

end QStab.Examples.SteaneStandardNoGo
