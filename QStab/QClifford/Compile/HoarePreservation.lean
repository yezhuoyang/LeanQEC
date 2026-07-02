import QStab.QClifford.Compile.VCBridge
import QStab.QHL.Source.Branch

/-!
# Hoare preservation bridge from QStab to compiled QClifford

This module isolates the proof-theoretic boundary between the source QED-HL
logic and the compiled QClifford fault Hoare logic.

The source side reasons about abstract state fields: residual data error and
remaining fault budget.  The target side has concrete `errLoc` sites over data
and fresh helper qubits.  The assertion compiler below interprets a source
formula over a QClifford state by projecting the concrete Pauli state back to
the source data qubits and interpreting the spent budget as the target
state-resident fault counter.

The preservation theorems are deliberately phrased through explicit simulation
certificates.  A scheme-specific compiler proof must supply such a certificate;
the theorem here then combines that certificate with source QED-HL soundness
and target QClifford `FHoare`.
-/

namespace QStab.QClifford.Compile

open QStab
open QHL
open QHL.AssertionLang
open QHL.Source.Branch

/-! ## Assertion compilation -/

/-- Project a concrete QClifford state with `k` fresh helpers back to the
source data-qubit Pauli vector.  Helper-qubit errors are not hidden; they are
accounted for through `QCState.lambda`, while the source residual error field
only records data-qubit Paulis. -/
def dataErrorOfQCState (P : QECParams) (k : Nat)
    (sigma : QCState (P.n + k)) : ErrorVec P.n :=
  fun q => sigma.es.paulis (freshDataQ P.n k q)

/-- Assertion backend used by the QStab-to-QClifford compiler.

Static stabilizer/logical/barrier symbols remain the source symbols over `P`.
Only the dynamic state observations are elaborated:

* `error` is the data projection of the concrete QClifford Pauli state;
* `remaining` is `P.C_budget - lambda`;
* detector terms read the concrete time-resolved detector log.

The source coordinate is not meaningful after compilation, so it is fixed to
`Coord.first P`.  Formulas intended for compiled checking should therefore pass
the existing `Formula.qcSupported` filter, which rejects coordinate-dependent
terms. -/
def qcliffordDataBackend (P : QECParams) (k : Nat) :
    AssertionBackend P (QCState (P.n + k)) where
  error := dataErrorOfQCState P k
  spent := fun sigma => sigma.lambda
  remaining := fun sigma => P.C_budget - sigma.lambda
  budget := P.C_budget
  current := fun _ => QECParams.Coord.first P
  detector := fun slot sigma => sigma.es.detectors slot

/-- Compile a closed source formula into a QClifford fault assertion. -/
noncomputable def compileFormula {P : QECParams} (k : Nat)
    (A : Formula P []) : AssertionF (P.n + k) :=
  A.denoteWith (qcliffordDataBackend P k)

/-- Budgeted compiled assertion.  QClifford runs are unbounded, while the
source QStab semantics enters the `error` state after the finite source budget
is exhausted.  Preservation for full target circuits therefore promises the
compiled source assertion only for target executions whose concrete fault count
is still within the source budget. -/
noncomputable def compileFormulaWithinBudget {P : QECParams} (k : Nat)
    (A : Formula P []) : AssertionF (P.n + k) :=
  fun sigma => sigma.lambda <= P.C_budget -> compileFormula k A sigma

@[simp] theorem compileFormula_top {P : QECParams} (k : Nat) :
    compileFormula (P := P) k Formula.top = fun _ : QCState (P.n + k) => True := by
  rfl

@[simp] theorem dataErrorOfQCState_clean {P : QECParams} (k : Nat) :
    dataErrorOfQCState P k (QCState.clean (P.n + k)) =
      ErrorVec.identity P.n := by
  funext q
  simp [dataErrorOfQCState, QCState.clean, ErrorState.clean, ErrorVec.identity]

/-! ## Branch-level preservation -/

/-- Evidence that one compiled QClifford circuit refines one labelled QStab
transition for the assertions being transported.

The `pre_refines`/`post_refines` fields are the assertion-translation proof
obligations.  They are separated from `step_refines` because some assertions
mention only error/budget fields, while a scheme simulation may classify
concrete helper faults into source Type-I/II/III branches. -/
structure BranchSimulation {P : QECParams} (prog : QStabProgram P)
    (k : Nat) (fc : FCircuit (P.n + k))
    (A : Formula P []) (tau : TransitionLabel P) (B : Formula P []) where
  abstract : QCState (P.n + k) -> State P
  pre_refines :
    forall sigma,
      compileFormula k A sigma -> A.denote (abstract sigma)
  step_refines :
    forall sigma sigma',
      qceval fc sigma sigma' ->
        TransitionStep prog tau (abstract sigma) (abstract sigma')
  post_refines :
    forall sigma,
      B.denote (abstract sigma) -> compileFormula k B sigma

/-- Branch Hoare preservation.

Once a scheme-specific compiler gives a syntactic/semantic refinement
certificate for a compiled branch, any source QED-HL branch triple transports
to a QClifford `FHoare` triple over the compiled assertions. -/
theorem branch_hoare_preservation {P : QECParams} {prog : QStabProgram P}
    {k : Nat} {fc : FCircuit (P.n + k)}
    {A B : Formula P []} {tau : TransitionLabel P}
    (hsrc : Hoare prog A.denote tau B.denote)
    (sim : BranchSimulation prog k fc A tau B) :
    FHoare (compileFormula k A) fc (compileFormula k B) := by
  intro sigma sigma' hrun hpre
  exact sim.post_refines sigma'
    (hsrc (sim.abstract sigma) (sim.abstract sigma')
      (sim.step_refines sigma sigma' hrun)
      (sim.pre_refines sigma hpre))

/-- Certificate-level branch preservation.  This is the same theorem as
`branch_hoare_preservation`, but the source premise is a verifier-facing
QED-HL proof tree rather than an already-erased semantic triple. -/
theorem branch_certificate_preservation {P : QECParams}
    {prog : QStabProgram P} {k : Nat} {fc : FCircuit (P.n + k)}
    {A B : Formula P []} {tau : TransitionLabel P}
    (cert : Certificate prog A tau B)
    (sim : BranchSimulation prog k fc A tau B) :
    FHoare (compileFormula k A) fc (compileFormula k B) :=
  branch_hoare_preservation cert.check_sound sim

/-! ## Concrete target run linearisation -/

/-- A fired concrete QClifford fault, with the deterministic suffix and detector
cursor at its site.  This is the raw material that scheme-specific proofs
classify into source QStab Type-0/I/II/III transitions. -/
structure FiredFaultWithContext (nq : Nat) where
  site : QStab.QClifford.PCC.ErrLocWithContext nq
  pauli : Pauli
  nontrivial : pauli ≠ Pauli.I

theorem propagateGate_detectorCursor_eq {nq : Nat} (g : Gate nq) (es : ErrorState nq) :
    (propagateGate g es).detectorCursor =
      es.detectorCursor + QStab.QClifford.PCC.gateDetectorAdvance g := by
  cases g <;> simp [propagateGate, QStab.QClifford.PCC.gateDetectorAdvance]

/-- Every counted QClifford run determines exactly `w` fired concrete sites,
each a member of the syntactic `errLocsWithContextAux` list for the circuit.

This theorem does not yet classify the sites as QStab errors; it proves the
essential no-cheating fact that the later classifier can only talk about error
locations that actually occur in the compiled circuit. -/
theorem fcevalW_context_faults_aux {nq : Nat} {w : Nat} {fc : FCircuit nq}
    {es es' : ErrorState nq}
    (hrun : fcevalW w fc es es') :
    ∀ cursor : Nat, es.detectorCursor = cursor ->
      ∃ faults : List (FiredFaultWithContext nq),
        faults.length = w ∧
          ∀ fault, fault ∈ faults ->
            fault.site ∈ QStab.QClifford.PCC.errLocsWithContextAux cursor fc := by
  induction hrun with
  | nil es =>
      intro cursor _hcursor
      refine ⟨[], rfl, ?_⟩
      intro fault hmem
      cases hmem
  | gate g rest es es' w htail ih =>
      intro cursor hcursor
      obtain ⟨faults, hlen, hmem⟩ :=
        ih (cursor + QStab.QClifford.PCC.gateDetectorAdvance g)
          (by rw [propagateGate_detectorCursor_eq, hcursor])
      refine ⟨faults, hlen, ?_⟩
      intro fault hfault
      exact hmem fault hfault
  | idle q rest es es' w htail ih =>
      intro cursor hcursor
      obtain ⟨faults, hlen, hmem⟩ := ih cursor hcursor
      refine ⟨faults, hlen, ?_⟩
      intro fault hfault
      simp [QStab.QClifford.PCC.errLocsWithContextAux, hmem fault hfault]
  | inject q rest es es' p hp w htail ih =>
      intro cursor hcursor
      obtain ⟨faults, hlen, hmem⟩ :=
        ih cursor (by simp [ErrorState.inject, hcursor])
      let fired : FiredFaultWithContext nq :=
        { site := ⟨q, eraseFaults rest, cursor⟩
          pauli := p
          nontrivial := hp }
      refine ⟨fired :: faults, by simp [hlen], ?_⟩
      intro fault hfault
      simp [QStab.QClifford.PCC.errLocsWithContextAux] at hfault ⊢
      rcases hfault with rfl | hrest
      · left
        rfl
      · right
        exact hmem fault hrest

/-- Clean-run linearisation: every QClifford run from the clean state exposes
exactly `sigma.lambda` fired concrete sites, all drawn from the compiled
circuit's own `errLocsWithContext` list. -/
theorem qceval_clean_context_faults {nq : Nat} {fc : FCircuit nq}
    {sigma : QCState nq}
    (hrun : qceval fc (QCState.clean nq) sigma) :
    ∃ faults : List (FiredFaultWithContext nq),
      faults.length = sigma.lambda ∧
        ∀ fault, fault ∈ faults ->
          fault.site ∈ QStab.QClifford.PCC.errLocsWithContext fc := by
  obtain ⟨_hle, hindex⟩ := fcevalW_of_qceval hrun
  have hindex' : fcevalW sigma.lambda fc (ErrorState.clean nq) sigma.es := by
    simpa [QCState.clean] using hindex
  simpa [QStab.QClifford.PCC.errLocsWithContext] using
    fcevalW_context_faults_aux hindex' 0 rfl

/-! ## Program-Hoare preservation -/

/-- Every QClifford run exposes the concrete faults that fired, relative to the
detector cursor at the starting state.

The list has exactly the lambda increment of the run, and every site is a
syntactic member of the circuit's time-resolved `errLoc` set.  This is the
generic trace fact used by scheme-specific simulations for arbitrary Hoare
triples, not only clean initial runs. -/
theorem qceval_context_faults {nq : Nat} {fc : FCircuit nq}
    {sigma sigma' : QCState nq}
    (hrun : qceval fc sigma sigma') :
    ∃ faults : List (FiredFaultWithContext nq),
      faults.length = sigma'.lambda - sigma.lambda ∧
        ∀ fault, fault ∈ faults ->
          fault.site ∈
            QStab.QClifford.PCC.errLocsWithContextAux sigma.es.detectorCursor fc := by
  obtain ⟨_hle, hindex⟩ := fcevalW_of_qceval hrun
  simpa using
    fcevalW_context_faults_aux hindex sigma.es.detectorCursor rfl

/-- Semantic source program Hoare triple for the concrete QStab transition
system.  This is the whole-program counterpart of the branch triples in
`QHL.Source.Branch`: every active-to-active source execution from a
precondition state ends in a postcondition state. -/
def ProgramHoare {P : QECParams} (prog : QStabProgram P)
    (Pre Post : Assertion P) : Prop :=
  ∀ st st' : State P,
    MultiStep prog (.active st) (.active st') -> Pre st -> Post st'

/-- Budgeted simulation evidence for arbitrary source Hoare triples.

The final-budget premise is essential: QClifford may keep injecting concrete
faults forever, while the source QStab semantics models only executions that
remain inside the finite source budget. -/
structure BudgetedProgramSimulation {P : QECParams}
    (prog : QStabProgram P) (k : Nat) (fc : FCircuit (P.n + k))
    (A B : Formula P []) where
  abstract : QCState (P.n + k) -> State P
  run_refines :
    forall sigma sigma',
      qceval fc sigma sigma' ->
        sigma'.lambda <= P.C_budget ->
          MultiStep prog (.active (abstract sigma)) (.active (abstract sigma'))
  pre_refines :
    forall sigma,
      compileFormula k A sigma -> A.denote (abstract sigma)
  post_refines :
    forall sigma,
      sigma.lambda <= P.C_budget ->
        B.denote (abstract sigma) -> compileFormula k B sigma

/-- Trace-level simulation evidence for arbitrary source Hoare triples.

Compared with `BudgetedProgramSimulation`, this is the non-cheating interface
scheme proofs should target: the proof receives the exact list of concrete
faults extracted from the actual QClifford run and can only classify sites that
belong to the compiled circuit's `errLocsWithContextAux` set. -/
structure TraceProgramSimulation {P : QECParams}
    (prog : QStabProgram P) (k : Nat) (fc : FCircuit (P.n + k))
    (A B : Formula P []) where
  abstract : QCState (P.n + k) -> State P
  run_refines_from_trace :
    forall sigma sigma' (faults : List (FiredFaultWithContext (P.n + k))),
      qceval fc sigma sigma' ->
        faults.length = sigma'.lambda - sigma.lambda ->
          (forall fault, fault ∈ faults ->
            fault.site ∈
              QStab.QClifford.PCC.errLocsWithContextAux sigma.es.detectorCursor fc) ->
            sigma'.lambda <= P.C_budget ->
              MultiStep prog (.active (abstract sigma)) (.active (abstract sigma'))
  pre_refines :
    forall sigma,
      compileFormula k A sigma -> A.denote (abstract sigma)
  post_refines :
    forall sigma,
      sigma.lambda <= P.C_budget ->
        B.denote (abstract sigma) -> compileFormula k B sigma

/-- One concrete target fault classified as one labelled QStab source branch.

The `fault` argument is part of the type so a scheme-specific certificate must
consume the actual fired concrete site while constructing the source branch
derivation. -/
structure SourceFaultStep {P : QECParams} (prog : QStabProgram P) {k : Nat}
    (fault : FiredFaultWithContext (P.n + k)) (st st' : State P) where
  label : TransitionLabel P
  step : TransitionStep prog label st st'

/-- A syntactic source derivation guided by a concrete target fault trace.

`fault` consumes exactly one fired QClifford site.  `meas` consumes no target
fault and represents the scheduled QStab measurement/progress step.  This is
the shape expected from scheme-specific compiler correctness proofs before
they are erased to ordinary source reachability. -/
inductive SourceTraceDeriv {P : QECParams} (prog : QStabProgram P) {k : Nat} :
    State P -> List (FiredFaultWithContext (P.n + k)) -> State P -> Type where
  | nil (st : State P) : SourceTraceDeriv prog st [] st
  | fault {st st1 st2 : State P}
      {fault : FiredFaultWithContext (P.n + k)}
      {faults : List (FiredFaultWithContext (P.n + k))} :
      SourceFaultStep prog fault st st1 ->
        SourceTraceDeriv prog st1 faults st2 ->
          SourceTraceDeriv prog st (fault :: faults) st2
  | silent {st st2 : State P}
      {fault : FiredFaultWithContext (P.n + k)}
      {faults : List (FiredFaultWithContext (P.n + k))} :
        SourceTraceDeriv prog st faults st2 ->
          SourceTraceDeriv prog st (fault :: faults) st2
  | meas {st st1 st2 : State P}
      {faults : List (FiredFaultWithContext (P.n + k))} :
      TransitionStep prog .meas st st1 ->
        SourceTraceDeriv prog st1 faults st2 ->
          SourceTraceDeriv prog st faults st2

namespace SourceTraceDeriv

/-- Erase a concrete-fault-guided source derivation tree to ordinary QStab
reachability.  This is the only induction step in the generic preservation
bridge; scheme-specific proofs should build `SourceTraceDeriv` terms. -/
theorem toMultiStep {P : QECParams} {prog : QStabProgram P} {k : Nat}
    {st st' : State P} {faults : List (FiredFaultWithContext (P.n + k))}
    (d : SourceTraceDeriv prog st faults st') :
    MultiStep prog (.active st) (.active st') := by
  induction d with
  | nil st =>
      exact Relation.ReflTransGen.refl
  | fault sourceStep _ ih =>
      exact multi_step_trans (step_to_multi sourceStep.step.toStep) ih
  | silent _ ih =>
      exact ih
  | meas sourceStep _ ih =>
      exact multi_step_trans (step_to_multi sourceStep.toStep) ih

end SourceTraceDeriv

/-- Trace simulation whose source refinement proof is itself a derivation tree.
This is the preferred interface for the scheme proofs: the generic theorem can
only erase the supplied derivation; it does not invent source reachability. -/
structure SyntacticTraceProgramSimulation {P : QECParams}
    (prog : QStabProgram P) (k : Nat) (fc : FCircuit (P.n + k))
    (A B : Formula P []) where
  abstract : QCState (P.n + k) -> State P
  trace_deriv :
    forall sigma sigma' (faults : List (FiredFaultWithContext (P.n + k))),
      qceval fc sigma sigma' ->
        faults.length = sigma'.lambda - sigma.lambda ->
          (forall fault, fault ∈ faults ->
            fault.site ∈
              QStab.QClifford.PCC.errLocsWithContextAux sigma.es.detectorCursor fc) ->
            sigma'.lambda <= P.C_budget ->
              SourceTraceDeriv prog (abstract sigma) faults (abstract sigma')
  pre_refines :
    forall sigma,
      compileFormula k A sigma -> A.denote (abstract sigma)
  post_refines :
    forall sigma,
      sigma.lambda <= P.C_budget ->
        B.denote (abstract sigma) -> compileFormula k B sigma

/-- A syntactic trace simulation erases to the semantic trace-simulation
interface. -/
def SyntacticTraceProgramSimulation.toTrace {P : QECParams}
    {prog : QStabProgram P} {k : Nat} {fc : FCircuit (P.n + k)}
    {A B : Formula P []}
    (sim : SyntacticTraceProgramSimulation prog k fc A B) :
    TraceProgramSimulation prog k fc A B where
  abstract := sim.abstract
  run_refines_from_trace := by
    intro sigma sigma' faults hrun hlen hmem hbudget
    exact (sim.trace_deriv sigma sigma' faults hrun hlen hmem hbudget).toMultiStep
  pre_refines := sim.pre_refines
  post_refines := sim.post_refines

/-! ## Scheme-specific classifier algebra -/

/-- Detector-cursor advance of an instrumented QClifford circuit.  This is the
same cursor accounting used by `PCC.errLocsWithContextAux`; error locations do
not advance the detector cursor, while measurement gates may. -/
def fCircuitDetectorAdvance {nq : Nat} : FCircuit nq -> Nat
  | [] => 0
  | .gate g :: rest => QStab.QClifford.PCC.gateDetectorAdvance g + fCircuitDetectorAdvance rest
  | .errLoc _ :: rest => fCircuitDetectorAdvance rest

/-- Error locations contributed by a prefix circuit, but with deterministic
suffixes that include the continuation `tail`.

This is the ownership-sensitive version of `PCC.errLocsWithContextAux` needed
by per-gadget classifiers.  The locations come only from `fc`; `tail` is used
only when recording the suffix of those locations. -/
def prefixErrLocsWithContextAux {nq : Nat} (cursor : Nat)
    (fc tail : FCircuit nq) : List (QStab.QClifford.PCC.ErrLocWithContext nq) :=
  match fc with
  | [] => []
  | .gate g :: rest =>
      prefixErrLocsWithContextAux
        (cursor + QStab.QClifford.PCC.gateDetectorAdvance g) rest tail
  | .errLoc q :: rest =>
      ⟨q, eraseFaults rest ++ eraseFaults tail, cursor⟩ ::
        prefixErrLocsWithContextAux cursor rest tail

/-- Prefix-owned sites are also sites in the whole concatenated circuit. -/
theorem prefixErrLocsWithContextAux_mem_append {nq : Nat}
    (cursor : Nat) (fc tail : FCircuit nq)
    {site : QStab.QClifford.PCC.ErrLocWithContext nq}
    (h : site ∈ prefixErrLocsWithContextAux cursor fc tail) :
    site ∈ QStab.QClifford.PCC.errLocsWithContextAux cursor (fc ++ tail) := by
  induction fc generalizing cursor with
  | nil =>
      cases h
  | cons instr rest ih =>
      cases instr with
      | gate g =>
          simpa [prefixErrLocsWithContextAux, QStab.QClifford.PCC.errLocsWithContextAux]
            using ih (cursor + QStab.QClifford.PCC.gateDetectorAdvance g) h
      | errLoc q =>
          simp [prefixErrLocsWithContextAux, QStab.QClifford.PCC.errLocsWithContextAux] at h ⊢
          rcases h with rfl | hrest
          · left
            simp
          · right
            exact ih cursor hrest

/-- Sites in a suffix circuit remain sites after prefixing another circuit,
provided the detector cursor is shifted by the prefix's deterministic advance.

We intentionally state only the right-membership direction.  A naive append
equality is false for left-hand sites because their stored deterministic suffix
changes from `eraseFaults rest` to `eraseFaults (rest ++ tail)`. -/
theorem errLocsWithContextAux_append_right {nq : Nat}
    (cursor : Nat) (pref suff : FCircuit nq) {site : QStab.QClifford.PCC.ErrLocWithContext nq}
    (h :
      site ∈ QStab.QClifford.PCC.errLocsWithContextAux
        (cursor + fCircuitDetectorAdvance pref) suff) :
    site ∈ QStab.QClifford.PCC.errLocsWithContextAux cursor (pref ++ suff) := by
  induction pref generalizing cursor with
  | nil =>
      simpa [fCircuitDetectorAdvance] using h
  | cons instr rest ih =>
      cases instr with
      | gate g =>
          have h' :
              site ∈ QStab.QClifford.PCC.errLocsWithContextAux
                ((cursor + QStab.QClifford.PCC.gateDetectorAdvance g) +
                  fCircuitDetectorAdvance rest) suff := by
            simpa [fCircuitDetectorAdvance, Nat.add_assoc] using h
          simpa [QStab.QClifford.PCC.errLocsWithContextAux] using
            ih (cursor + QStab.QClifford.PCC.gateDetectorAdvance g) h'
      | errLoc q =>
          simp [QStab.QClifford.PCC.errLocsWithContextAux]
          exact Or.inr (ih cursor h)

/-- Target execution advances the detector cursor by the syntactic detector
advance of the circuit, independently of which `errLoc`s fire. -/
theorem qceval_detectorCursor_eq {nq : Nat} {fc : FCircuit nq}
    {sigma sigma' : QCState nq}
    (hrun : qceval fc sigma sigma') :
    sigma'.es.detectorCursor =
      sigma.es.detectorCursor + fCircuitDetectorAdvance fc := by
  induction hrun with
  | nil sigma =>
      simp [fCircuitDetectorAdvance]
  | cons instr rest sigma mid sigma' hstep _ ih =>
      cases hstep with
      | step_gate g =>
          simp [fCircuitDetectorAdvance, propagateGate_detectorCursor_eq,
            Nat.add_comm, Nat.add_left_comm] at ih ⊢
          omega
      | step_idle q =>
          simpa [fCircuitDetectorAdvance] using ih
      | step_inject q sigma p hp =>
          simpa [fCircuitDetectorAdvance, ErrorState.inject] using ih

/-- Context-aware linearisation with an explicit deterministic tail.

The suffix stored in an `ErrLocWithContext` must include the continuation after
the fragment.  This theorem is therefore the primitive trace fact used by
continuation-aware classifiers, instead of first extracting sites from `fc`
alone and then trying to append a tail afterwards. -/
theorem fcevalW_context_faults_aux_tail {nq : Nat} {w : Nat}
    {fc tail : FCircuit nq} {es es' : ErrorState nq}
    (hrun : fcevalW w fc es es') :
    ∀ cursor : Nat, es.detectorCursor = cursor ->
      ∃ faults : List (FiredFaultWithContext nq),
        faults.length = w ∧
          ∀ fault, fault ∈ faults ->
            fault.site ∈
              QStab.QClifford.PCC.errLocsWithContextAux cursor (fc ++ tail) := by
  induction hrun with
  | nil es =>
      intro cursor _hcursor
      refine ⟨[], rfl, ?_⟩
      intro fault hmem
      cases hmem
  | gate g rest es es' w htail ih =>
      intro cursor hcursor
      obtain ⟨faults, hlen, hmem⟩ :=
        ih (cursor + QStab.QClifford.PCC.gateDetectorAdvance g)
          (by rw [propagateGate_detectorCursor_eq, hcursor])
      refine ⟨faults, hlen, ?_⟩
      intro fault hfault
      exact hmem fault hfault
  | idle q rest es es' w htail ih =>
      intro cursor hcursor
      obtain ⟨faults, hlen, hmem⟩ := ih cursor hcursor
      refine ⟨faults, hlen, ?_⟩
      intro fault hfault
      simp [QStab.QClifford.PCC.errLocsWithContextAux, hmem fault hfault]
  | inject q rest es es' p hp w htail ih =>
      intro cursor hcursor
      obtain ⟨faults, hlen, hmem⟩ :=
        ih cursor (by simp [ErrorState.inject, hcursor])
      let fired : FiredFaultWithContext nq :=
        { site := ⟨q, eraseFaults rest ++ eraseFaults tail, cursor⟩
          pauli := p
          nontrivial := hp }
      refine ⟨fired :: faults, by simp [hlen], ?_⟩
      intro fault hfault
      simp [QStab.QClifford.PCC.errLocsWithContextAux] at hfault ⊢
      rcases hfault with rfl | hrest
      · left
        rfl
      · right
        exact hmem fault hrest

/-- QClifford run linearisation whose sites are already phrased in the context
of a deterministic continuation `tail`. -/
theorem qceval_context_faults_with_tail {nq : Nat} {fc tail : FCircuit nq}
    {sigma sigma' : QCState nq}
    (hrun : qceval fc sigma sigma') :
    ∃ faults : List (FiredFaultWithContext nq),
      faults.length = sigma'.lambda - sigma.lambda ∧
        ∀ fault, fault ∈ faults ->
          fault.site ∈
            QStab.QClifford.PCC.errLocsWithContextAux
              sigma.es.detectorCursor (fc ++ tail) := by
  obtain ⟨_hle, hindex⟩ := fcevalW_of_qceval hrun
  simpa using
    fcevalW_context_faults_aux_tail (tail := tail) hindex sigma.es.detectorCursor rfl

namespace SourceTraceDeriv

/-- Concatenate two concrete-fault-guided source derivations. -/
noncomputable def append {P : QECParams} {prog : QStabProgram P} {k : Nat}
    {s0 s1 s2 : State P}
    {faults1 faults2 : List (FiredFaultWithContext (P.n + k))}
    (d1 : SourceTraceDeriv prog s0 faults1 s1)
    (d2 : SourceTraceDeriv prog s1 faults2 s2) :
    SourceTraceDeriv prog s0 (faults1 ++ faults2) s2 := by
  induction d1 with
  | nil st =>
      simpa using d2
  | fault step rest ih =>
      exact SourceTraceDeriv.fault step (ih d2)
  | silent rest ih =>
      exact SourceTraceDeriv.silent (ih d2)
  | meas step rest ih =>
      exact SourceTraceDeriv.meas step (ih d2)

end SourceTraceDeriv

/-- A classified target run: the classifier returns a concrete fired-fault list
with syntactic membership evidence and a source derivation tree consuming that
same list. -/
structure RunTraceDerivation {P : QECParams} (prog : QStabProgram P) {k : Nat}
    (abstract : QCState (P.n + k) -> State P)
    (fc : FCircuit (P.n + k)) (sigma sigma' : QCState (P.n + k)) where
  faults : List (FiredFaultWithContext (P.n + k))
  length_eq : faults.length = sigma'.lambda - sigma.lambda
  site_mem :
    ∀ fault, fault ∈ faults ->
      fault.site ∈
        QStab.QClifford.PCC.errLocsWithContextAux sigma.es.detectorCursor fc
  source :
    SourceTraceDeriv prog (abstract sigma) faults (abstract sigma')

namespace RunTraceDerivation

theorem toMultiStep {P : QECParams} {prog : QStabProgram P} {k : Nat}
    {abstract : QCState (P.n + k) -> State P} {fc : FCircuit (P.n + k)}
    {sigma sigma' : QCState (P.n + k)}
    (d : RunTraceDerivation prog abstract fc sigma sigma') :
    MultiStep prog (.active (abstract sigma)) (.active (abstract sigma')) :=
  d.source.toMultiStep

end RunTraceDerivation

/-! ## Scheme-specific fault-event classifiers -/

/-- The clean deterministic suffix effect at a concrete target fault site. -/
def targetFaultCleanEffect {P : QECParams} {k : Nat}
    (fault : FiredFaultWithContext (P.n + k)) : ErrorState (P.n + k) :=
  propagateCircuit fault.site.suffix
    (QStab.QClifford.PCC.cleanAtDetector fault.site.detectorStart)

/-- The deterministic suffix effect after injecting the fired concrete Pauli. -/
def targetFaultEffect {P : QECParams} {k : Nat}
    (fault : FiredFaultWithContext (P.n + k)) : ErrorState (P.n + k) :=
  propagateCircuit fault.site.suffix
    ((QStab.QClifford.PCC.cleanAtDetector fault.site.detectorStart).inject
      fault.site.q fault.pauli)

/-- Project the concrete residual of one target fault to source data qubits. -/
def targetFaultDataResidual (P : QECParams) {k : Nat}
    (fault : FiredFaultWithContext (P.n + k)) : ErrorVec P.n :=
  fun q => (targetFaultEffect (P := P) fault).paulis (freshDataQ P.n k q)

/-- Detector/readout change caused by one target fault, relative to the clean
suffix from the same detector cursor.  The `readout` argument is supplied by
the scheme rule; for a compiled stabilizer gadget it is the XOR of that
gadget's generated readout detector slots. -/
def targetFaultReadoutFlip {P : QECParams} {k : Nat}
    (readout : ErrorState (P.n + k) -> Bool)
    (fault : FiredFaultWithContext (P.n + k)) : Bool :=
  xor (readout (targetFaultCleanEffect (P := P) fault))
    (readout (targetFaultEffect (P := P) fault))

def singleDataResidual (P : QECParams) (i : Fin P.n) (p : Pauli) : ErrorVec P.n :=
  ErrorVec.update (ErrorVec.identity P.n) i p

theorem errorVec_eq_identity_of_weight_zero {n : Nat} (e : ErrorVec n)
    (h : ErrorVec.weight e = 0) :
    e = ErrorVec.identity n := by
  funext i
  by_contra hne
  have hi_mem : i ∈ Finset.univ.filter (fun j : Fin n => e j ≠ Pauli.I) := by
    simp [ErrorVec.identity] at hne
    simp [hne]
  have hcard : (Finset.univ.filter (fun j : Fin n => e j ≠ Pauli.I)).card ≠ 0 :=
    Finset.card_ne_zero_of_mem hi_mem
  exact hcard h

theorem errorVec_eq_singleton_of_weight_one {n : Nat} (e : ErrorVec n)
    (h : ErrorVec.weight e = 1) :
    ∃ (i : Fin n) (p : Pauli), p ≠ Pauli.I ∧
      e = ErrorVec.update (ErrorVec.identity n) i p := by
  have h_eq_one :
      (Finset.univ.filter (fun j : Fin n => e j ≠ Pauli.I)).card = 1 := h
  rw [Finset.card_eq_one] at h_eq_one
  obtain ⟨a, ha⟩ := h_eq_one
  refine ⟨a, e a, ?_, ?_⟩
  · have : a ∈ Finset.univ.filter (fun j : Fin n => e j ≠ Pauli.I) := by
      rw [ha]
      exact Finset.mem_singleton.mpr rfl
    simpa [Finset.mem_filter] using this
  · funext j
    by_cases hj : j = a
    · subst j
      simp [ErrorVec.update, ErrorVec.identity, Pauli.mul_I]
    · have hj_not_in : j ∉ Finset.univ.filter (fun j' : Fin n => e j' ≠ Pauli.I) := by
        rw [ha]
        simp [Finset.mem_singleton, hj]
      have hj_eq_I : e j = Pauli.I := by
        by_contra hne
        exact hj_not_in (by simp [Finset.mem_filter, hne])
      simp [ErrorVec.update, ErrorVec.identity, Function.update_of_ne hj, hj_eq_I]

structure ErrorVecSingleton {n : Nat} (e : ErrorVec n) where
  i : Fin n
  p : Pauli
  hp : p ≠ Pauli.I
  eq_singleton : e = ErrorVec.update (ErrorVec.identity n) i p

noncomputable def errorVecSingletonOfWeightOne {n : Nat} (e : ErrorVec n)
    (h : ErrorVec.weight e = 1) : ErrorVecSingleton e := by
  classical
  let hExists := errorVec_eq_singleton_of_weight_one e h
  let i := Classical.choose hExists
  let hExistsP := Classical.choose_spec hExists
  let p := Classical.choose hExistsP
  let hSpec := Classical.choose_spec hExistsP
  exact
    { i := i
      p := p
      hp := hSpec.1
      eq_singleton := hSpec.2 }

/-- The source-side class assigned to one fired target fault.

Unlike the previous count abstraction, each constructor carries the actual
source event parameters.  A classifier must separately prove that these
parameters equal the target fault's concrete propagated residual/readout
effect. -/
inductive CompiledFaultBranch (P : QECParams) where
  | silent : CompiledFaultBranch P
  | err0 (i : Fin P.n) (p : Pauli) (hp : p ≠ Pauli.I) : CompiledFaultBranch P
  | errI (i : Fin P.n) (p : Pauli) (hp : p ≠ Pauli.I) (mf : Bool) :
      CompiledFaultBranch P
  | errII (e : ErrorVec P.n) (mf : Bool) : CompiledFaultBranch P
  | errIII : CompiledFaultBranch P

namespace CompiledFaultBranch

def label {P : QECParams} : CompiledFaultBranch P -> Option (TransitionLabel P)
  | .silent => none
  | .err0 i p _ => some (.err0 i p)
  | .errI i p _ mf => some (.errI i p mf)
  | .errII e mf => some (.errII e mf)
  | .errIII => some .errIII

def dataResidual {P : QECParams} : CompiledFaultBranch P -> ErrorVec P.n
  | .silent => ErrorVec.identity P.n
  | .err0 i p _ => singleDataResidual P i p
  | .errI i p _ _ => singleDataResidual P i p
  | .errII e _ => e
  | .errIII => ErrorVec.identity P.n

def readoutFlip {P : QECParams} : CompiledFaultBranch P -> Bool
  | .silent => false
  | .err0 _ _ _ => false
  | .errI _ _ _ mf => mf
  | .errII _ mf => mf
  | .errIII => true

/-- A branch assignment is accepted only when it is backed by the corresponding
QStab transition from the current source state.  The silent case consumes a
target fault but contributes no QStab step, and is only sound when paired with
the residual/readout equalities in `ClassifiedFaultAt`. -/
inductive StepAt {P : QECParams} (prog : QStabProgram P) {k : Nat}
    (fault : FiredFaultWithContext (P.n + k)) :
    CompiledFaultBranch P -> State P -> State P -> Type where
  | silent (st : State P) :
      StepAt prog fault .silent st st
  | branch {branch : CompiledFaultBranch P} {label : TransitionLabel P}
      {st st' : State P} :
      branch.label = some label ->
        TransitionStep prog label st st' ->
          StepAt prog fault branch st st'

def StepAt.toTrace {P : QECParams} {prog : QStabProgram P} {k : Nat}
    {fault : FiredFaultWithContext (P.n + k)} {branch : CompiledFaultBranch P}
    {st st' : State P}
    (h : StepAt prog fault branch st st') :
    SourceTraceDeriv prog st [fault] st' := by
  cases h with
  | silent st =>
      exact SourceTraceDeriv.silent (SourceTraceDeriv.nil (prog := prog) st)
  | branch hlabel hstep =>
      exact SourceTraceDeriv.fault
        { label := _
          step := hstep }
        (SourceTraceDeriv.nil (prog := prog) _)

end CompiledFaultBranch

/-- A concrete target fault together with its real source classification at a
specific QStab state.  The two equality fields forbid the old count-only
shortcut: the branch must match the propagated target data residual and the
scheme-selected readout flip. -/
structure ClassifiedFaultAt {P : QECParams} (prog : QStabProgram P) {k : Nat}
    (readout : ErrorState (P.n + k) -> Bool)
    (fault : FiredFaultWithContext (P.n + k)) (st : State P) where
  branch : CompiledFaultBranch P
  residual_eq :
    targetFaultDataResidual P fault = CompiledFaultBranch.dataResidual branch
  readout_eq :
    targetFaultReadoutFlip (P := P) readout fault =
      CompiledFaultBranch.readoutFlip branch
  next : State P
  step : CompiledFaultBranch.StepAt prog fault branch st next

namespace ClassifiedFaultAt

def ofStep {P : QECParams} {prog : QStabProgram P} {k : Nat}
    {readout : ErrorState (P.n + k) -> Bool}
    {fault : FiredFaultWithContext (P.n + k)} {st next : State P}
    {branch : CompiledFaultBranch P}
    (residual_eq :
      targetFaultDataResidual P fault = CompiledFaultBranch.dataResidual branch)
    (readout_eq :
      targetFaultReadoutFlip (P := P) readout fault =
        CompiledFaultBranch.readoutFlip branch)
    (step : CompiledFaultBranch.StepAt prog fault branch st next) :
    ClassifiedFaultAt prog readout fault st where
  branch := branch
  residual_eq := residual_eq
  readout_eq := readout_eq
  next := next
  step := step

def toTrace {P : QECParams} {prog : QStabProgram P} {k : Nat}
    {readout : ErrorState (P.n + k) -> Bool}
    {fault : FiredFaultWithContext (P.n + k)} {st : State P}
    (c : ClassifiedFaultAt prog readout fault st) :
    SourceTraceDeriv prog st [fault] c.next :=
  c.step.toTrace

end ClassifiedFaultAt

def detectorXorAt {nq : Nat} (detectorStart : Nat) (slots : List Nat)
    (es : ErrorState nq) : Bool :=
  slots.foldl (fun acc slot => xor acc (es.detectors (detectorStart + slot))) false

/-- Scheme-specific readout selected by a compilation rule.  The slots are
exactly the generated readout offsets already consumed by VCGen's `.syn`
certificate. -/
def schemeReadoutAt {n total : Nat} (scheme : Scheme) (sigma : RuleSchedule n)
    (detectorStart : Nat) (es : ErrorState (n + total)) : Bool :=
  detectorXorAt detectorStart (readoutOffsets scheme sigma) es

/-- Per-gadget fault classifier generated by a scheme-specific compilation
rule.  Its proof should be by induction on `sigma.slots`: the base classifiers
for one written `X` or `Z` slot handle the newly introduced fault locations,
and the induction hypothesis handles all earlier slots. -/
structure GadgetFaultClassifier {P : QECParams} (prog : QStabProgram P)
    {total : Nat} (scheme : Scheme) (sigma : RuleSchedule P.n)
    (helperStart detectorStart : Nat)
    (helperFit : helperStart + helperCount scheme sigma <= total) where
  classifyFault :
    ∀ (tail : FCircuit (P.n + total))
      (fault : FiredFaultWithContext (P.n + total)),
      fault.site ∈
        prefixErrLocsWithContextAux detectorStart
          (compileGadgetBlock scheme sigma helperStart helperFit) tail ->
        ∀ st : State P, 0 < st.C ->
          ClassifiedFaultAt prog
            (schemeReadoutAt (total := total) scheme sigma detectorStart)
            fault st

/-- The compiler-generated view of one Type-II candidate at the current
reverse-compilation cut.  The residual is the final data back-action after the
known suffix; `readoutFlip` is the scheme-selected detector effect after the
same suffix. -/
structure CompiledBackActionEvent (P : QECParams) where
  residual : ErrorVec P.n
  readoutFlip : Bool

def compiledBackActionEventOfFault {P : QECParams} {k : Nat}
    (readout : ErrorState (P.n + k) -> Bool)
    (fault : FiredFaultWithContext (P.n + k)) : CompiledBackActionEvent P where
  residual := targetFaultDataResidual P fault
  readoutFlip := targetFaultReadoutFlip (P := P) readout fault

/-- Reverse-current back-action set for an instrumented fragment.

The definition mirrors the reverse compilation rule: the recursive call
computes the already-built suffix first; when an `errLoc` is prepended, the new
event is computed using the deterministic suffix `rest ++ tail`.  Thus the
back-action attached to the new fault is fixed without knowing any earlier
prefix gates. -/
def reverseCurrentBackActionEventsAux {P : QECParams} {total : Nat}
    (readout : ErrorState (P.n + total) -> Bool) :
    Nat -> FCircuit (P.n + total) -> FCircuit (P.n + total) ->
      Set (CompiledBackActionEvent P)
  | _, [], _ => fun _ => False
  | cursor, .gate g :: rest, tail =>
      reverseCurrentBackActionEventsAux readout
        (cursor + QStab.QClifford.PCC.gateDetectorAdvance g) rest tail
  | cursor, .errLoc q :: rest, tail =>
      fun event =>
        reverseCurrentBackActionEventsAux readout cursor rest tail event ∨
          ∃ (p : Pauli) (hp : p ≠ Pauli.I),
            let fault : FiredFaultWithContext (P.n + total) :=
              { site := ⟨q, eraseFaults rest ++ eraseFaults tail, cursor⟩
                pauli := p
                nontrivial := hp }
            compiledBackActionEventOfFault readout fault = event ∧
              ErrorVec.weight event.residual ≠ 0 ∧
              ErrorVec.weight event.residual ≠ 1

theorem reverseCurrentBackActionEventsAux_mem_of_prefix_site {P : QECParams}
    {total : Nat} (readout : ErrorState (P.n + total) -> Bool) :
    ∀ (cursor : Nat) (fc tail : FCircuit (P.n + total))
      (fault : FiredFaultWithContext (P.n + total)),
      fault.site ∈ prefixErrLocsWithContextAux cursor fc tail ->
        ErrorVec.weight (targetFaultDataResidual P fault) ≠ 0 ->
        ErrorVec.weight (targetFaultDataResidual P fault) ≠ 1 ->
          compiledBackActionEventOfFault readout fault ∈
            reverseCurrentBackActionEventsAux readout cursor fc tail
  | _, [], _, _, hsite, _, _ => by
      cases hsite
  | cursor, .gate g :: rest, tail, fault, hsite, hzero, hone => by
      exact reverseCurrentBackActionEventsAux_mem_of_prefix_site readout
        (cursor + QStab.QClifford.PCC.gateDetectorAdvance g) rest tail
        fault
        (by simpa [prefixErrLocsWithContextAux] using hsite)
        hzero hone
  | cursor, .errLoc q :: rest, tail, fault, hsite, hzero, hone => by
      simp [prefixErrLocsWithContextAux] at hsite ⊢
      rcases hsite with hhead | htail
      · right
        cases fault with
        | mk site pauli nontrivial =>
            cases hhead
            refine ⟨pauli, nontrivial, ?_, ?_, ?_⟩
            · rfl
            · exact hzero
            · exact hone
      · left
        exact reverseCurrentBackActionEventsAux_mem_of_prefix_site readout
          cursor rest tail fault htail hzero hone

/-- Generated Type-II back-action events for one compiled gadget, with an
arbitrary deterministic continuation.  The `tail` parameter is what lets the
same leaf rule be used inside a full program: later gadgets are part of the
known suffix when classifying faults in this gadget. -/
def reverseGadgetBackActionEvents {P : QECParams} {total : Nat}
    (scheme : Scheme) (sigma : RuleSchedule P.n)
    (helperStart detectorStart : Nat)
    (helperFit : helperStart + helperCount scheme sigma <= total)
    (tail : FCircuit (P.n + total)) : Set (CompiledBackActionEvent P) :=
  reverseCurrentBackActionEventsAux
    (schemeReadoutAt (total := total) scheme sigma detectorStart)
    detectorStart
    (compileGadgetBlock scheme sigma helperStart helperFit)
    tail

/-- Residual-only projection of the generated reverse back-action events.  This
is the exact object that should be compared with a source `backActionSet`; the
event layer still remembers readout flips for the QStab branch classifier. -/
def reverseGadgetBackActionResiduals {P : QECParams} {total : Nat}
    (scheme : Scheme) (sigma : RuleSchedule P.n)
    (helperStart detectorStart : Nat)
    (helperFit : helperStart + helperCount scheme sigma <= total)
    (tail : FCircuit (P.n + total)) : Set (ErrorVec P.n) :=
  fun residual =>
    ∃ event : CompiledBackActionEvent P,
      event ∈ reverseGadgetBackActionEvents scheme sigma helperStart detectorStart helperFit tail ∧
        event.residual = residual

/-- Tail-specific reverse back-action cover for one gadget.  This is stronger
than a post-hoc table but weaker, and more precise, than the earlier
all-continuations cover: it closes exactly the suffix determined by the
reverse program derivation. -/
structure ReverseGadgetBackActionCoverAt {P : QECParams} (prog : QStabProgram P)
    {total : Nat} (scheme : Scheme) (sigma : RuleSchedule P.n)
    (helperStart detectorStart : Nat)
    (helperFit : helperStart + helperCount scheme sigma <= total)
    (tail : FCircuit (P.n + total)) where
  cover :
    ∀ event : CompiledBackActionEvent P,
      event ∈
        reverseGadgetBackActionEvents scheme sigma helperStart detectorStart helperFit tail ->
        ∀ st : State P,
          event.residual ∈ P.backActionSet (currentStab prog st)

def ReverseGadgetBackActionCoverAt.ofResiduals {P : QECParams}
    {prog : QStabProgram P} {total : Nat}
    {scheme : Scheme} {sigma : RuleSchedule P.n}
    {helperStart detectorStart : Nat}
    {helperFit : helperStart + helperCount scheme sigma <= total}
    {tail : FCircuit (P.n + total)}
    (closed :
      ∀ residual : ErrorVec P.n,
        residual ∈
          reverseGadgetBackActionResiduals scheme sigma helperStart detectorStart
            helperFit tail ->
          ∀ st : State P,
            residual ∈ P.backActionSet (currentStab prog st)) :
    ReverseGadgetBackActionCoverAt prog scheme sigma helperStart detectorStart helperFit tail where
  cover := by
    intro event hevent st
    exact closed event.residual ⟨event, hevent, rfl⟩ st

/-- Row-specific tail cover for one gadget.  Unlike
`ReverseGadgetBackActionCoverAt`, this cover is indexed by the source
stabilizer row assigned to the measurement leaf. -/
structure ReverseGadgetBackActionCoverAtForStab {P : QECParams}
    {total : Nat} (scheme : Scheme) (sigma : RuleSchedule P.n)
    (helperStart detectorStart : Nat)
    (helperFit : helperStart + helperCount scheme sigma <= total)
    (tail : FCircuit (P.n + total)) (stab : Fin P.numStab) where
  cover :
    ∀ event : CompiledBackActionEvent P,
      event ∈
        reverseGadgetBackActionEvents scheme sigma helperStart detectorStart helperFit tail ->
        event.residual ∈ P.backActionSet stab

def ReverseGadgetBackActionCoverAtForStab.ofResiduals {P : QECParams}
    {total : Nat} {scheme : Scheme} {sigma : RuleSchedule P.n}
    {helperStart detectorStart : Nat}
    {helperFit : helperStart + helperCount scheme sigma <= total}
    {tail : FCircuit (P.n + total)} {stab : Fin P.numStab}
    (closed :
      ∀ residual : ErrorVec P.n,
        residual ∈
          reverseGadgetBackActionResiduals scheme sigma helperStart detectorStart
            helperFit tail ->
          residual ∈ P.backActionSet stab) :
    ReverseGadgetBackActionCoverAtForStab scheme sigma helperStart detectorStart
      helperFit tail stab where
  cover := by
    intro event hevent
    exact closed event.residual ⟨event, hevent, rfl⟩

/-- Tail-specific gadget classifier generated from the reverse back-action
cover at that exact suffix. -/
structure GadgetFaultClassifierAt {P : QECParams} (prog : QStabProgram P)
    {total : Nat} (scheme : Scheme) (sigma : RuleSchedule P.n)
    (helperStart detectorStart : Nat)
    (helperFit : helperStart + helperCount scheme sigma <= total)
    (tail : FCircuit (P.n + total)) where
  classifyFault :
    ∀ fault : FiredFaultWithContext (P.n + total),
      fault.site ∈
        prefixErrLocsWithContextAux detectorStart
          (compileGadgetBlock scheme sigma helperStart helperFit) tail ->
        ∀ st : State P, 0 < st.C ->
          ClassifiedFaultAt prog
            (schemeReadoutAt (total := total) scheme sigma detectorStart)
            fault st

/-- Row-aware tail-specific gadget classifier.

This is the precise version used by the row-indexed compiler-generated
back-action set.  It classifies a target fault for states whose scheduled
source stabilizer is the row attached to this measurement leaf. -/
structure GadgetFaultClassifierAtForStab {P : QECParams} (prog : QStabProgram P)
    {total : Nat} (scheme : Scheme) (sigma : RuleSchedule P.n)
    (helperStart detectorStart : Nat)
    (helperFit : helperStart + helperCount scheme sigma <= total)
    (tail : FCircuit (P.n + total)) (stab : Fin P.numStab) where
  classifyFault :
    ∀ fault : FiredFaultWithContext (P.n + total),
      fault.site ∈
        prefixErrLocsWithContextAux detectorStart
          (compileGadgetBlock scheme sigma helperStart helperFit) tail ->
        ∀ st : State P, 0 < st.C -> currentStab prog st = stab ->
          ClassifiedFaultAt prog
            (schemeReadoutAt (total := total) scheme sigma detectorStart)
            fault st

/-- Reverse-rule-generated Type-II obligation for one compiled gadget.

Unlike the older opaque cover, this premise only asks the code instance to
accept events generated by the reverse compilation/back-action rules.  The
compiler proves below that every concrete prefix-owned Type-II target fault is
one of these generated events. -/
structure ReverseGadgetBackActionCover {P : QECParams} (prog : QStabProgram P)
    {total : Nat} (scheme : Scheme) (sigma : RuleSchedule P.n)
    (helperStart detectorStart : Nat)
    (helperFit : helperStart + helperCount scheme sigma <= total) where
  cover :
    ∀ (tail : FCircuit (P.n + total)) (event : CompiledBackActionEvent P),
      event ∈
        reverseGadgetBackActionEvents scheme sigma helperStart detectorStart helperFit tail ->
        ∀ st : State P,
          event.residual ∈ P.backActionSet (currentStab prog st)

/-- Code-specific Type-II obligation for one compiled gadget.

The compiler can classify the concrete residual and readout flip of every
target fault generically.  The only code-specific premise needed to turn a
multi-qubit residual into an actual QStab Type-II step is that the residual is
registered in the source code's `backActionSet` for the current stabilizer. -/
structure GadgetBackActionCover {P : QECParams} (prog : QStabProgram P)
    {total : Nat} (scheme : Scheme) (sigma : RuleSchedule P.n)
    (helperStart detectorStart : Nat)
    (helperFit : helperStart + helperCount scheme sigma <= total) where
  cover :
    ∀ (tail : FCircuit (P.n + total))
      (fault : FiredFaultWithContext (P.n + total)),
      fault.site ∈
        prefixErrLocsWithContextAux detectorStart
          (compileGadgetBlock scheme sigma helperStart helperFit) tail ->
        ∀ st : State P,
          ErrorVec.weight (targetFaultDataResidual P fault) ≠ 0 ->
          ErrorVec.weight (targetFaultDataResidual P fault) ≠ 1 ->
            targetFaultDataResidual P fault ∈ P.backActionSet (currentStab prog st)

/-- Every generated reverse back-action cover induces the legacy residual-only
cover.  This is the proof that removes the old boundary: concrete target faults
are first forced into the reverse-generated event set, then the code-specific
`backActionSet` inclusion is applied. -/
def GadgetBackActionCover.ofReverse {P : QECParams} {prog : QStabProgram P}
    {total : Nat} {scheme : Scheme} {sigma : RuleSchedule P.n}
    {helperStart detectorStart : Nat}
    {helperFit : helperStart + helperCount scheme sigma <= total}
    (cover :
      ReverseGadgetBackActionCover prog scheme sigma helperStart detectorStart helperFit) :
    GadgetBackActionCover prog scheme sigma helperStart detectorStart helperFit where
  cover := by
    intro tail fault hsite st hzero hone
    have hevent :
        compiledBackActionEventOfFault
            (schemeReadoutAt (total := total) scheme sigma detectorStart) fault ∈
          reverseGadgetBackActionEvents scheme sigma helperStart detectorStart helperFit tail := by
      exact reverseCurrentBackActionEventsAux_mem_of_prefix_site
        (schemeReadoutAt (total := total) scheme sigma detectorStart)
        detectorStart
        (compileGadgetBlock scheme sigma helperStart helperFit)
        tail fault hsite hzero hone
    simpa [compiledBackActionEventOfFault] using
      cover.cover tail
        (compiledBackActionEventOfFault
          (schemeReadoutAt (total := total) scheme sigma detectorStart) fault)
        hevent st

/-- Classify one concrete target fault by its actual propagated residual and
scheme readout flip.

This proof is independent of the measurement scheme except for the readout
function.  It closes the QStab branch derivation for silent, Type-III, Type-0,
and Type-I cases directly.  In the remaining Type-II case it uses precisely the
back-action membership premise required by `TransitionStep.errII`. -/
noncomputable def classifyFaultAtByResidual {P : QECParams} (prog : QStabProgram P)
    {k : Nat} (readout : ErrorState (P.n + k) -> Bool)
    (fault : FiredFaultWithContext (P.n + k)) (st : State P) (hC : 0 < st.C)
    (hBackAction :
      ErrorVec.weight (targetFaultDataResidual P fault) ≠ 0 ->
      ErrorVec.weight (targetFaultDataResidual P fault) ≠ 1 ->
        targetFaultDataResidual P fault ∈ P.backActionSet (currentStab prog st)) :
    ClassifiedFaultAt prog readout fault st := by
  classical
  let e := targetFaultDataResidual P fault
  let mf := targetFaultReadoutFlip (P := P) readout fault
  by_cases hzero : ErrorVec.weight e = 0
  · have heq : e = ErrorVec.identity P.n := errorVec_eq_identity_of_weight_zero e hzero
    cases hmf : mf
    · exact
        ClassifiedFaultAt.ofStep
          (branch := .silent)
          (by simpa [e, CompiledFaultBranch.dataResidual] using heq)
          (by simpa [mf, CompiledFaultBranch.readoutFlip] using hmf)
          (CompiledFaultBranch.StepAt.silent st)
    · exact
        ClassifiedFaultAt.ofStep
          (branch := .errIII)
          (by simpa [e, CompiledFaultBranch.dataResidual] using heq)
          (by simpa [mf, CompiledFaultBranch.readoutFlip] using hmf)
          (CompiledFaultBranch.StepAt.branch rfl
            (TransitionStep.errIII (prog := prog) st hC))
  · by_cases hone : ErrorVec.weight e = 1
    · let w := errorVecSingletonOfWeightOne e hone
      cases hmf : mf
      · exact
          ClassifiedFaultAt.ofStep
            (branch := .err0 w.i w.p w.hp)
            (by
              simpa [e, CompiledFaultBranch.dataResidual, singleDataResidual]
                using w.eq_singleton)
            (by simpa [mf, CompiledFaultBranch.readoutFlip] using hmf)
            (CompiledFaultBranch.StepAt.branch rfl
              (TransitionStep.err0 (prog := prog) st w.i w.p w.hp hC))
      · exact
          ClassifiedFaultAt.ofStep
            (branch := .errI w.i w.p w.hp true)
            (by
              simpa [e, CompiledFaultBranch.dataResidual, singleDataResidual]
                using w.eq_singleton)
            (by simpa [mf, CompiledFaultBranch.readoutFlip] using hmf)
            (CompiledFaultBranch.StepAt.branch rfl
              (TransitionStep.errI (prog := prog) st w.i w.p w.hp true hC))
    · have hBA : e ∈ P.backActionSet (currentStab prog st) := by
        simpa [e] using hBackAction (by simpa [e] using hzero) (by simpa [e] using hone)
      exact
        ClassifiedFaultAt.ofStep
          (branch := .errII e mf)
          (by rfl)
          (by rfl)
          (CompiledFaultBranch.StepAt.branch rfl
            (TransitionStep.errII (prog := prog) st e hBA mf hC))

noncomputable def gadgetFaultClassifierAtOfReverseCoverAt {P : QECParams}
    (prog : QStabProgram P) {total : Nat}
    (scheme : Scheme) (sigma : RuleSchedule P.n)
    (helperStart detectorStart : Nat)
    (helperFit : helperStart + helperCount scheme sigma <= total)
    (tail : FCircuit (P.n + total))
    (cover :
      ReverseGadgetBackActionCoverAt prog scheme sigma helperStart detectorStart helperFit tail) :
    GadgetFaultClassifierAt prog scheme sigma helperStart detectorStart helperFit tail where
  classifyFault := by
    intro fault hsite st hC
    refine classifyFaultAtByResidual prog
      (schemeReadoutAt (total := total) scheme sigma detectorStart)
      fault st hC ?_
    intro hzero hone
    have hevent :
        compiledBackActionEventOfFault
            (schemeReadoutAt (total := total) scheme sigma detectorStart) fault ∈
          reverseGadgetBackActionEvents scheme sigma helperStart detectorStart helperFit tail := by
      exact reverseCurrentBackActionEventsAux_mem_of_prefix_site
        (schemeReadoutAt (total := total) scheme sigma detectorStart)
        detectorStart
        (compileGadgetBlock scheme sigma helperStart helperFit)
        tail fault hsite hzero hone
    simpa [compiledBackActionEventOfFault] using
      cover.cover
        (compiledBackActionEventOfFault
          (schemeReadoutAt (total := total) scheme sigma detectorStart) fault)
        hevent st

noncomputable def gadgetFaultClassifierAtForStabOfReverseCoverAtForStab {P : QECParams}
    (prog : QStabProgram P) {total : Nat}
    (scheme : Scheme) (sigma : RuleSchedule P.n)
    (helperStart detectorStart : Nat)
    (helperFit : helperStart + helperCount scheme sigma <= total)
    (tail : FCircuit (P.n + total)) (stab : Fin P.numStab)
    (cover :
      ReverseGadgetBackActionCoverAtForStab scheme sigma helperStart detectorStart
        helperFit tail stab) :
    GadgetFaultClassifierAtForStab prog scheme sigma helperStart detectorStart
      helperFit tail stab where
  classifyFault := by
    intro fault hsite st hC hstab
    refine classifyFaultAtByResidual prog
      (schemeReadoutAt (total := total) scheme sigma detectorStart)
      fault st hC ?_
    intro hzero hone
    have hevent :
        compiledBackActionEventOfFault
            (schemeReadoutAt (total := total) scheme sigma detectorStart) fault ∈
          reverseGadgetBackActionEvents scheme sigma helperStart detectorStart helperFit tail := by
      exact reverseCurrentBackActionEventsAux_mem_of_prefix_site
        (schemeReadoutAt (total := total) scheme sigma detectorStart)
        detectorStart
        (compileGadgetBlock scheme sigma helperStart helperFit)
        tail fault hsite hzero hone
    have hmemStab :
        targetFaultDataResidual P fault ∈ P.backActionSet stab := by
      simpa [compiledBackActionEventOfFault] using
        cover.cover
          (compiledBackActionEventOfFault
            (schemeReadoutAt (total := total) scheme sigma detectorStart) fault)
          hevent
    simpa [hstab] using hmemStab

noncomputable def standardGadgetFaultClassifierAtOfReverseCoverAt {P : QECParams}
    (prog : QStabProgram P) {total : Nat}
    (sigma : RuleSchedule P.n) (helperStart detectorStart : Nat)
    (helperFit : helperStart + helperCount Scheme.NZ sigma <= total)
    (tail : FCircuit (P.n + total))
    (cover :
      ReverseGadgetBackActionCoverAt prog .NZ sigma helperStart detectorStart helperFit tail) :
    GadgetFaultClassifierAt prog .NZ sigma helperStart detectorStart helperFit tail :=
  gadgetFaultClassifierAtOfReverseCoverAt prog .NZ sigma helperStart detectorStart
    helperFit tail cover

noncomputable def knillGadgetFaultClassifierAtOfReverseCoverAt {P : QECParams}
    (prog : QStabProgram P) {total : Nat}
    (sigma : RuleSchedule P.n) (helperStart detectorStart : Nat)
    (helperFit : helperStart + helperCount Scheme.Knill sigma <= total)
    (tail : FCircuit (P.n + total))
    (cover :
      ReverseGadgetBackActionCoverAt prog .Knill sigma helperStart detectorStart helperFit tail) :
    GadgetFaultClassifierAt prog .Knill sigma helperStart detectorStart helperFit tail :=
  gadgetFaultClassifierAtOfReverseCoverAt prog .Knill sigma helperStart detectorStart
    helperFit tail cover

noncomputable def shorGadgetFaultClassifierAtOfReverseCoverAt {P : QECParams}
    (prog : QStabProgram P) {total : Nat}
    (sigma : RuleSchedule P.n) (helperStart detectorStart : Nat)
    (helperFit : helperStart + helperCount Scheme.Shor sigma <= total)
    (tail : FCircuit (P.n + total))
    (cover :
      ReverseGadgetBackActionCoverAt prog .Shor sigma helperStart detectorStart helperFit tail) :
    GadgetFaultClassifierAt prog .Shor sigma helperStart detectorStart helperFit tail :=
  gadgetFaultClassifierAtOfReverseCoverAt prog .Shor sigma helperStart detectorStart
    helperFit tail cover

noncomputable def flagGadgetFaultClassifierAtOfReverseCoverAt {P : QECParams}
    (prog : QStabProgram P) {total : Nat}
    (sigma : RuleSchedule P.n) (helperStart detectorStart : Nat)
    (helperFit : helperStart + helperCount Scheme.Flag sigma <= total)
    (tail : FCircuit (P.n + total))
    (cover :
      ReverseGadgetBackActionCoverAt prog .Flag sigma helperStart detectorStart helperFit tail) :
    GadgetFaultClassifierAt prog .Flag sigma helperStart detectorStart helperFit tail :=
  gadgetFaultClassifierAtOfReverseCoverAt prog .Flag sigma helperStart detectorStart
    helperFit tail cover

noncomputable def gadgetFaultClassifierOfBackActionCover {P : QECParams}
    (prog : QStabProgram P) {total : Nat}
    (scheme : Scheme) (sigma : RuleSchedule P.n)
    (helperStart detectorStart : Nat)
    (helperFit : helperStart + helperCount scheme sigma <= total)
    (cover : GadgetBackActionCover prog scheme sigma helperStart detectorStart helperFit) :
    GadgetFaultClassifier prog scheme sigma helperStart detectorStart helperFit where
  classifyFault := by
    intro tail fault hsite st hC
    exact classifyFaultAtByResidual prog
      (schemeReadoutAt (total := total) scheme sigma detectorStart)
      fault st hC (cover.cover tail fault hsite st)

noncomputable def gadgetFaultClassifierOfReverseBackActionCover {P : QECParams}
    (prog : QStabProgram P) {total : Nat}
    (scheme : Scheme) (sigma : RuleSchedule P.n)
    (helperStart detectorStart : Nat)
    (helperFit : helperStart + helperCount scheme sigma <= total)
    (cover :
      ReverseGadgetBackActionCover prog scheme sigma helperStart detectorStart helperFit) :
    GadgetFaultClassifier prog scheme sigma helperStart detectorStart helperFit :=
  gadgetFaultClassifierOfBackActionCover prog scheme sigma helperStart detectorStart helperFit
    (GadgetBackActionCover.ofReverse cover)

/-- Standard CNOT-scheme classifier.  The generated circuit and readout are
fixed by the `.NZ` compilation rule; only the code-specific Type-II
back-action cover is supplied by the source-code instance. -/
noncomputable def standardGadgetFaultClassifier {P : QECParams}
    (prog : QStabProgram P) {total : Nat}
    (sigma : RuleSchedule P.n) (helperStart detectorStart : Nat)
    (helperFit : helperStart + helperCount Scheme.NZ sigma <= total)
    (cover : GadgetBackActionCover prog .NZ sigma helperStart detectorStart helperFit) :
    GadgetFaultClassifier prog .NZ sigma helperStart detectorStart helperFit :=
  gadgetFaultClassifierOfBackActionCover prog .NZ sigma helperStart detectorStart helperFit cover

noncomputable def knillGadgetFaultClassifier {P : QECParams}
    (prog : QStabProgram P) {total : Nat}
    (sigma : RuleSchedule P.n) (helperStart detectorStart : Nat)
    (helperFit : helperStart + helperCount Scheme.Knill sigma <= total)
    (cover : GadgetBackActionCover prog .Knill sigma helperStart detectorStart helperFit) :
    GadgetFaultClassifier prog .Knill sigma helperStart detectorStart helperFit :=
  gadgetFaultClassifierOfBackActionCover prog .Knill sigma helperStart detectorStart helperFit cover

noncomputable def shorGadgetFaultClassifier {P : QECParams}
    (prog : QStabProgram P) {total : Nat}
    (sigma : RuleSchedule P.n) (helperStart detectorStart : Nat)
    (helperFit : helperStart + helperCount Scheme.Shor sigma <= total)
    (cover : GadgetBackActionCover prog .Shor sigma helperStart detectorStart helperFit) :
    GadgetFaultClassifier prog .Shor sigma helperStart detectorStart helperFit :=
  gadgetFaultClassifierOfBackActionCover prog .Shor sigma helperStart detectorStart helperFit cover

noncomputable def flagGadgetFaultClassifier {P : QECParams}
    (prog : QStabProgram P) {total : Nat}
    (sigma : RuleSchedule P.n) (helperStart detectorStart : Nat)
    (helperFit : helperStart + helperCount Scheme.Flag sigma <= total)
    (cover : GadgetBackActionCover prog .Flag sigma helperStart detectorStart helperFit) :
    GadgetFaultClassifier prog .Flag sigma helperStart detectorStart helperFit :=
  gadgetFaultClassifierOfBackActionCover prog .Flag sigma helperStart detectorStart helperFit cover

noncomputable def standardGadgetFaultClassifierOfReverseCover {P : QECParams}
    (prog : QStabProgram P) {total : Nat}
    (sigma : RuleSchedule P.n) (helperStart detectorStart : Nat)
    (helperFit : helperStart + helperCount Scheme.NZ sigma <= total)
    (cover :
      ReverseGadgetBackActionCover prog .NZ sigma helperStart detectorStart helperFit) :
    GadgetFaultClassifier prog .NZ sigma helperStart detectorStart helperFit :=
  gadgetFaultClassifierOfReverseBackActionCover prog .NZ sigma
    helperStart detectorStart helperFit cover

noncomputable def knillGadgetFaultClassifierOfReverseCover {P : QECParams}
    (prog : QStabProgram P) {total : Nat}
    (sigma : RuleSchedule P.n) (helperStart detectorStart : Nat)
    (helperFit : helperStart + helperCount Scheme.Knill sigma <= total)
    (cover :
      ReverseGadgetBackActionCover prog .Knill sigma helperStart detectorStart helperFit) :
    GadgetFaultClassifier prog .Knill sigma helperStart detectorStart helperFit :=
  gadgetFaultClassifierOfReverseBackActionCover prog .Knill sigma
    helperStart detectorStart helperFit cover

noncomputable def shorGadgetFaultClassifierOfReverseCover {P : QECParams}
    (prog : QStabProgram P) {total : Nat}
    (sigma : RuleSchedule P.n) (helperStart detectorStart : Nat)
    (helperFit : helperStart + helperCount Scheme.Shor sigma <= total)
    (cover :
      ReverseGadgetBackActionCover prog .Shor sigma helperStart detectorStart helperFit) :
    GadgetFaultClassifier prog .Shor sigma helperStart detectorStart helperFit :=
  gadgetFaultClassifierOfReverseBackActionCover prog .Shor sigma
    helperStart detectorStart helperFit cover

noncomputable def flagGadgetFaultClassifierOfReverseCover {P : QECParams}
    (prog : QStabProgram P) {total : Nat}
    (sigma : RuleSchedule P.n) (helperStart detectorStart : Nat)
    (helperFit : helperStart + helperCount Scheme.Flag sigma <= total)
    (cover :
      ReverseGadgetBackActionCover prog .Flag sigma helperStart detectorStart helperFit) :
    GadgetFaultClassifier prog .Flag sigma helperStart detectorStart helperFit :=
  gadgetFaultClassifierOfReverseBackActionCover prog .Flag sigma
    helperStart detectorStart helperFit cover

/-- Program-level classifier derivation tree.  Every measurement leaf must
provide the scheme-specific gadget classifier for the exact helper block and
detector block allocated by the compilation rule; sequencing is pure structural
induction over `XZProgram`. -/
inductive ProgramFaultClassifierDeriv {P : QECParams} (prog : QStabProgram P)
    {totalHelpers : Nat} :
    Nat -> Nat -> XZProgram P.n -> Type where
  | skip (helperStart detectorStart : Nat) :
      ProgramFaultClassifierDeriv prog helperStart detectorStart .skip
  | meas (helperStart detectorStart : Nat) (scheme : Scheme)
      (sigma : RuleSchedule P.n)
      (helperFit : helperStart + helperCount scheme sigma <= totalHelpers)
      (classifier :
        GadgetFaultClassifier prog scheme sigma helperStart detectorStart helperFit) :
      ProgramFaultClassifierDeriv prog helperStart detectorStart (.meas scheme sigma)
  | seq {helperStart detectorStart : Nat} {first second : XZProgram P.n} :
      ProgramFaultClassifierDeriv prog helperStart detectorStart first ->
        ProgramFaultClassifierDeriv prog
          (helperStart + programHelperCount first)
          (detectorStart + QStab.QClifford.PCC.programDetectorCount first) second ->
          ProgramFaultClassifierDeriv prog helperStart detectorStart (.seq first second)

/-- Assemble a full-program fault-classifier derivation from generated
per-gadget back-action covers.

The proof is a structural induction over the compiler-facing `XZProgram`.
Every `.meas` leaf receives the exact helper block allocated by
`compileProgramAux`; every `.seq` node composes the two subderivations with the
same helper/detector offsets used by the compiler and VC generator. -/
noncomputable def programFaultClassifierDerivOfCovers {P : QECParams}
    (prog : QStabProgram P) {totalHelpers : Nat}
    (covers :
      ∀ (helperStart detectorStart : Nat) (scheme : Scheme) (sigma : RuleSchedule P.n)
        (helperFit : helperStart + helperCount scheme sigma <= totalHelpers),
          GadgetBackActionCover prog scheme sigma helperStart detectorStart helperFit) :
    (helperStart detectorStart : Nat) -> (program : XZProgram P.n) ->
      helperStart + programHelperCount program <= totalHelpers ->
        ProgramFaultClassifierDeriv (totalHelpers := totalHelpers)
          prog helperStart detectorStart program
  | helperStart, detectorStart, .skip, _ =>
      ProgramFaultClassifierDeriv.skip helperStart detectorStart
  | helperStart, detectorStart, .meas scheme sigma, helperFit =>
      ProgramFaultClassifierDeriv.meas helperStart detectorStart scheme sigma helperFit
        (gadgetFaultClassifierOfBackActionCover prog scheme sigma
          helperStart detectorStart helperFit
          (covers helperStart detectorStart scheme sigma helperFit))
  | helperStart, detectorStart, .seq first second, helperFit =>
      ProgramFaultClassifierDeriv.seq
        (programFaultClassifierDerivOfCovers prog covers
          helperStart detectorStart first
          (by simp [programHelperCount] at helperFit ⊢; omega))
        (programFaultClassifierDerivOfCovers prog covers
          (helperStart + programHelperCount first)
          (detectorStart + QStab.QClifford.PCC.programDetectorCount first)
          second
          (by simp [programHelperCount] at helperFit ⊢; omega))

/-- Closed helper-budget specialization for a complete `XZProgram`. -/
noncomputable def compiledProgramFaultClassifierDerivOfCovers {P : QECParams}
    (prog : QStabProgram P) (program : XZProgram P.n)
    (covers :
      ∀ (helperStart detectorStart : Nat) (scheme : Scheme) (sigma : RuleSchedule P.n)
        (helperFit :
          helperStart + helperCount scheme sigma <= programHelperCount program),
          GadgetBackActionCover prog scheme sigma helperStart detectorStart helperFit) :
    ProgramFaultClassifierDeriv (totalHelpers := programHelperCount program)
      prog 0 0 program :=
  programFaultClassifierDerivOfCovers prog covers 0 0 program (by simp)

/-- Assemble a full-program classifier from reverse-rule-generated back-action
covers.  This is the preferred path for the compiler proof: every measurement
leaf first computes its current back-action events from the already known
suffix, and only then bridges those generated events into the source
`backActionSet`. -/
noncomputable def programFaultClassifierDerivOfReverseCovers {P : QECParams}
    (prog : QStabProgram P) {totalHelpers : Nat}
    (covers :
      ∀ (helperStart detectorStart : Nat) (scheme : Scheme) (sigma : RuleSchedule P.n)
        (helperFit : helperStart + helperCount scheme sigma <= totalHelpers),
          ReverseGadgetBackActionCover prog scheme sigma helperStart detectorStart helperFit) :
    (helperStart detectorStart : Nat) -> (program : XZProgram P.n) ->
      helperStart + programHelperCount program <= totalHelpers ->
        ProgramFaultClassifierDeriv (totalHelpers := totalHelpers)
          prog helperStart detectorStart program
  | helperStart, detectorStart, .skip, _ =>
      ProgramFaultClassifierDeriv.skip helperStart detectorStart
  | helperStart, detectorStart, .meas scheme sigma, helperFit =>
      ProgramFaultClassifierDeriv.meas helperStart detectorStart scheme sigma helperFit
        (gadgetFaultClassifierOfReverseBackActionCover prog scheme sigma
          helperStart detectorStart helperFit
          (covers helperStart detectorStart scheme sigma helperFit))
  | helperStart, detectorStart, .seq first second, helperFit =>
      ProgramFaultClassifierDeriv.seq
        (programFaultClassifierDerivOfReverseCovers prog covers
          helperStart detectorStart first
          (by simp [programHelperCount] at helperFit ⊢; omega))
        (programFaultClassifierDerivOfReverseCovers prog covers
          (helperStart + programHelperCount first)
          (detectorStart + QStab.QClifford.PCC.programDetectorCount first)
          second
          (by simp [programHelperCount] at helperFit ⊢; omega))

/-- Closed helper-budget specialization of
`programFaultClassifierDerivOfReverseCovers`. -/
noncomputable def compiledProgramFaultClassifierDerivOfReverseCovers {P : QECParams}
    (prog : QStabProgram P) (program : XZProgram P.n)
    (covers :
      ∀ (helperStart detectorStart : Nat) (scheme : Scheme) (sigma : RuleSchedule P.n)
        (helperFit :
          helperStart + helperCount scheme sigma <= programHelperCount program),
          ReverseGadgetBackActionCover prog scheme sigma helperStart detectorStart helperFit) :
    ProgramFaultClassifierDeriv (totalHelpers := programHelperCount program)
      prog 0 0 program :=
  programFaultClassifierDerivOfReverseCovers prog covers 0 0 program (by simp)

/-! ## Closed program-specific reverse back-action classifiers -/

/-- Generated residuals for a full program fragment at an exact continuation.

At a sequence node, the first subprogram is analyzed with the compiled second
subprogram as part of its known suffix; the second subprogram is analyzed with
the external continuation.  This mirrors `ProgramReverseCompileDeriv` and
avoids the old all-possible-tails boundary. -/
def reverseProgramBackActionResidualsAux {P : QECParams} {totalHelpers : Nat} :
    (helperStart detectorStart : Nat) -> (program : XZProgram P.n) ->
      FCircuit (P.n + totalHelpers) ->
      helperStart + programHelperCount program <= totalHelpers ->
      Set (ErrorVec P.n)
  | _, _, .skip, _, _ => fun _ => False
  | helperStart, detectorStart, .meas scheme sigma, tail, helperFit =>
      reverseGadgetBackActionResiduals scheme sigma helperStart detectorStart helperFit tail
  | helperStart, detectorStart, .seq first second, tail, helperFit =>
      let firstFit : helperStart + programHelperCount first <= totalHelpers := by
        simp [programHelperCount] at helperFit ⊢
        omega
      let secondFit :
          (helperStart + programHelperCount first) + programHelperCount second <=
            totalHelpers := by
        simp [programHelperCount] at helperFit ⊢
        omega
      fun residual =>
        residual ∈
            reverseProgramBackActionResidualsAux helperStart detectorStart first
              (compileProgramAux (helperStart + programHelperCount first) second secondFit ++
                tail)
              firstFit ∨
          residual ∈
            reverseProgramBackActionResidualsAux
              (helperStart + programHelperCount first)
              (detectorStart + QStab.QClifford.PCC.programDetectorCount first)
              second tail secondFit

def reverseProgramBackActionResiduals {P : QECParams}
    (program : XZProgram P.n) : Set (ErrorVec P.n) :=
  reverseProgramBackActionResidualsAux 0 0 program ([] : FCircuit (P.n + programHelperCount program))
    (by simp)

/-- Shape-preserving source-row labels for an `XZProgram`.

The compiled program syntax records a scheme and a schedule at each measurement
leaf.  This certificate records which source stabilizer row that leaf
implements, without changing the executable compiler or the generated circuit.
-/
inductive ProgramStabLabels {P : QECParams} : XZProgram P.n -> Type where
  | skip : ProgramStabLabels .skip
  | meas (scheme : Scheme) (sigma : RuleSchedule P.n) (stab : Fin P.numStab)
      (row_eq : QStab.QClifford.PCC.scheduleRow (k := 0) sigma = P.stabilizers stab) :
      ProgramStabLabels (.meas scheme sigma)
  | seq {first second : XZProgram P.n} :
      ProgramStabLabels first ->
        ProgramStabLabels second ->
          ProgramStabLabels (.seq first second)

/-- Row-indexed generated residuals for a labelled full-program fragment at an
exact continuation.

At a measurement leaf, only the residuals generated by that leaf contribute to
the row attached to the leaf.  At a sequence node, the first subprogram is
still analyzed with the compiled second subprogram as its known suffix, exactly
as in the reverse compilation derivation. -/
def reverseProgramBackActionResidualsByStabAux {P : QECParams} {totalHelpers : Nat} :
    (helperStart detectorStart : Nat) -> (program : XZProgram P.n) ->
      ProgramStabLabels program -> FCircuit (P.n + totalHelpers) ->
      helperStart + programHelperCount program <= totalHelpers ->
      Fin P.numStab -> Set (ErrorVec P.n)
  | _, _, .skip, .skip, _, _, _ => fun _ => False
  | helperStart, detectorStart, .meas scheme sigma,
      .meas _ _ stab _, tail, helperFit, s =>
      fun residual =>
        stab = s ∧
          residual ∈
            reverseGadgetBackActionResiduals scheme sigma helperStart detectorStart
              helperFit tail
  | helperStart, detectorStart, .seq first second,
      .seq firstLabels secondLabels, tail, helperFit, s =>
      let firstFit : helperStart + programHelperCount first <= totalHelpers := by
        simp [programHelperCount] at helperFit ⊢
        omega
      let secondFit :
          (helperStart + programHelperCount first) + programHelperCount second <=
            totalHelpers := by
        simp [programHelperCount] at helperFit ⊢
        omega
      fun residual =>
        residual ∈
            reverseProgramBackActionResidualsByStabAux helperStart detectorStart first
              firstLabels
              (compileProgramAux (helperStart + programHelperCount first) second secondFit ++
                tail)
              firstFit s ∨
          residual ∈
            reverseProgramBackActionResidualsByStabAux
              (helperStart + programHelperCount first)
              (detectorStart + QStab.QClifford.PCC.programDetectorCount first)
              second secondLabels tail secondFit s

def reverseProgramBackActionResidualsByStab {P : QECParams}
    (program : XZProgram P.n) (labels : ProgramStabLabels program)
    (s : Fin P.numStab) : Set (ErrorVec P.n) :=
  reverseProgramBackActionResidualsByStabAux 0 0 program labels
    ([] : FCircuit (P.n + programHelperCount program)) (by simp) s

/-- Precise compiler-generated source back-action policy for a concrete labelled
compiled program.

This set is computed from concrete QClifford fault propagation, but filtered by
the source stabilizer row attached to each measurement leaf. -/
def compilerGeneratedBackActionSet {P : QECParams}
    (program : XZProgram P.n) (labels : ProgramStabLabels program)
    (s : Fin P.numStab) : Set (ErrorVec P.n) :=
  reverseProgramBackActionResidualsByStab program labels s

/-- Legacy/conservative generated policy: every row receives every generated
back-action residual from the whole program.  This remains useful for old
unconditional classifier APIs whose leaves classify arbitrary source states. -/
def compilerGeneratedBackActionSetAllRows {P : QECParams}
    (program : XZProgram P.n) (_s : Fin P.numStab) : Set (ErrorVec P.n) :=
  reverseProgramBackActionResiduals program

/-- Tail-specific full-program classifier derivation.  Unlike
`ProgramFaultClassifierDeriv`, this tree only promises classifiers at the exact
suffixes generated by the reverse program rules. -/
inductive ProgramFaultClassifierTailDeriv {P : QECParams} (prog : QStabProgram P)
    {totalHelpers : Nat} :
    Nat -> Nat -> XZProgram P.n -> FCircuit (P.n + totalHelpers) -> Type where
  | skip (helperStart detectorStart : Nat) (tail : FCircuit (P.n + totalHelpers)) :
      ProgramFaultClassifierTailDeriv prog helperStart detectorStart .skip tail
  | meas (helperStart detectorStart : Nat) (scheme : Scheme)
      (sigma : RuleSchedule P.n)
      (helperFit : helperStart + helperCount scheme sigma <= totalHelpers)
      (tail : FCircuit (P.n + totalHelpers))
      (classifier :
        GadgetFaultClassifierAt prog scheme sigma helperStart detectorStart helperFit tail) :
      ProgramFaultClassifierTailDeriv prog helperStart detectorStart (.meas scheme sigma) tail
  | seq {helperStart detectorStart : Nat} {first second : XZProgram P.n}
      {tail : FCircuit (P.n + totalHelpers)}
      (secondFit :
        (helperStart + programHelperCount first) + programHelperCount second <= totalHelpers) :
      ProgramFaultClassifierTailDeriv prog
        (helperStart + programHelperCount first)
        (detectorStart + QStab.QClifford.PCC.programDetectorCount first)
        second tail ->
      ProgramFaultClassifierTailDeriv prog helperStart detectorStart first
        (compileProgramAux (helperStart + programHelperCount first) second secondFit ++ tail) ->
      ProgramFaultClassifierTailDeriv prog helperStart detectorStart (.seq first second) tail

/-- Row-aware tail-specific full-program classifier derivation.

This derivation follows both the `XZProgram` syntax and the shape-preserving
source-row labels.  Measurement leaves are conditional on the source state
currently measuring the labelled row, which is the condition needed to use the
precise row-indexed generated back-action set. -/
inductive ProgramFaultClassifierTailDerivForLabels {P : QECParams}
    (prog : QStabProgram P) {totalHelpers : Nat} :
    (helperStart detectorStart : Nat) -> (program : XZProgram P.n) ->
      ProgramStabLabels program -> FCircuit (P.n + totalHelpers) -> Type where
  | skip (helperStart detectorStart : Nat) (tail : FCircuit (P.n + totalHelpers)) :
      ProgramFaultClassifierTailDerivForLabels prog helperStart detectorStart .skip
        ProgramStabLabels.skip tail
  | meas (helperStart detectorStart : Nat) (scheme : Scheme)
      (sigma : RuleSchedule P.n) (stab : Fin P.numStab)
      (row_eq : QStab.QClifford.PCC.scheduleRow (k := 0) sigma = P.stabilizers stab)
      (helperFit : helperStart + helperCount scheme sigma <= totalHelpers)
      (tail : FCircuit (P.n + totalHelpers))
      (classifier :
        GadgetFaultClassifierAtForStab prog scheme sigma helperStart detectorStart
          helperFit tail stab) :
      ProgramFaultClassifierTailDerivForLabels prog helperStart detectorStart
        (.meas scheme sigma) (ProgramStabLabels.meas scheme sigma stab row_eq) tail
  | seq {helperStart detectorStart : Nat} {first second : XZProgram P.n}
      {firstLabels : ProgramStabLabels first} {secondLabels : ProgramStabLabels second}
      {tail : FCircuit (P.n + totalHelpers)}
      (secondFit :
        (helperStart + programHelperCount first) + programHelperCount second <= totalHelpers) :
      ProgramFaultClassifierTailDerivForLabels prog
        (helperStart + programHelperCount first)
        (detectorStart + QStab.QClifford.PCC.programDetectorCount first)
        second secondLabels tail ->
      ProgramFaultClassifierTailDerivForLabels prog helperStart detectorStart first firstLabels
        (compileProgramAux (helperStart + programHelperCount first) second secondFit ++ tail) ->
      ProgramFaultClassifierTailDerivForLabels prog helperStart detectorStart (.seq first second)
        (ProgramStabLabels.seq firstLabels secondLabels) tail

def ReverseProgramBackActionsClosedAt {P : QECParams} (prog : QStabProgram P)
    {totalHelpers : Nat}
    (helperStart detectorStart : Nat) (program : XZProgram P.n)
    (tail : FCircuit (P.n + totalHelpers))
    (helperFit : helperStart + programHelperCount program <= totalHelpers) : Prop :=
  ∀ residual : ErrorVec P.n,
    residual ∈
      reverseProgramBackActionResidualsAux helperStart detectorStart program tail helperFit ->
      ∀ st : State P,
        residual ∈ P.backActionSet (currentStab prog st)

noncomputable def programFaultClassifierTailDerivOfClosedBackActions {P : QECParams}
    (prog : QStabProgram P) {totalHelpers : Nat} :
    (helperStart detectorStart : Nat) -> (program : XZProgram P.n) ->
      (tail : FCircuit (P.n + totalHelpers)) ->
      (helperFit : helperStart + programHelperCount program <= totalHelpers) ->
      ReverseProgramBackActionsClosedAt prog helperStart detectorStart program tail helperFit ->
        ProgramFaultClassifierTailDeriv (totalHelpers := totalHelpers)
          prog helperStart detectorStart program tail
  | helperStart, detectorStart, .skip, tail, _helperFit, _closed =>
      ProgramFaultClassifierTailDeriv.skip helperStart detectorStart tail
  | helperStart, detectorStart, .meas scheme sigma, tail, helperFit, closed => by
      let cover :
          ReverseGadgetBackActionCoverAt prog scheme sigma helperStart detectorStart
            helperFit tail :=
        ReverseGadgetBackActionCoverAt.ofResiduals (by
          intro residual hres st
          exact closed residual (by
            simpa [reverseProgramBackActionResidualsAux] using hres) st)
      exact ProgramFaultClassifierTailDeriv.meas helperStart detectorStart scheme sigma
        helperFit tail
        (gadgetFaultClassifierAtOfReverseCoverAt prog scheme sigma helperStart detectorStart
          helperFit tail cover)
  | helperStart, detectorStart, .seq first second, tail, helperFit, closed => by
      let firstFit : helperStart + programHelperCount first <= totalHelpers := by
        simp [programHelperCount] at helperFit ⊢
        omega
      let secondFit :
          (helperStart + programHelperCount first) + programHelperCount second <=
            totalHelpers := by
        simp [programHelperCount] at helperFit ⊢
        omega
      let firstTail :=
        compileProgramAux (helperStart + programHelperCount first) second secondFit ++ tail
      have closedFirst :
          ReverseProgramBackActionsClosedAt prog helperStart detectorStart first
            firstTail firstFit := by
        intro residual hres st
        exact closed residual (by
          simpa [reverseProgramBackActionResidualsAux, firstFit, secondFit, firstTail]
            using Or.inl hres) st
      have closedSecond :
          ReverseProgramBackActionsClosedAt prog
            (helperStart + programHelperCount first)
            (detectorStart + QStab.QClifford.PCC.programDetectorCount first)
            second tail secondFit := by
        intro residual hres st
        exact closed residual (by
          simpa [reverseProgramBackActionResidualsAux, firstFit, secondFit, firstTail]
            using Or.inr hres) st
      exact ProgramFaultClassifierTailDeriv.seq secondFit
        (programFaultClassifierTailDerivOfClosedBackActions prog
          (helperStart + programHelperCount first)
          (detectorStart + QStab.QClifford.PCC.programDetectorCount first)
          second tail secondFit closedSecond)
        (programFaultClassifierTailDerivOfClosedBackActions prog
          helperStart detectorStart first firstTail firstFit closedFirst)

noncomputable def compiledProgramFaultClassifierTailDerivOfClosedBackActions
    {P : QECParams} (prog : QStabProgram P) (program : XZProgram P.n)
    (closed :
      ∀ residual : ErrorVec P.n,
        residual ∈ reverseProgramBackActionResiduals program ->
          ∀ st : State P,
            residual ∈ P.backActionSet (currentStab prog st)) :
    ProgramFaultClassifierTailDeriv (totalHelpers := programHelperCount program)
      prog 0 0 program ([] : FCircuit (P.n + programHelperCount program)) :=
  programFaultClassifierTailDerivOfClosedBackActions prog 0 0 program [] (by simp)
    (by
      intro residual hres st
      exact closed residual (by
        simpa [reverseProgramBackActionResiduals] using hres) st)

noncomputable def compiledProgramFaultClassifierTailDerivOfGeneratedBackActionSubset
    {P : QECParams} (prog : QStabProgram P) (program : XZProgram P.n)
    (subset :
      ∀ (s : Fin P.numStab) (residual : ErrorVec P.n),
        residual ∈ compilerGeneratedBackActionSetAllRows program s ->
          residual ∈ P.backActionSet s) :
    ProgramFaultClassifierTailDeriv (totalHelpers := programHelperCount program)
      prog 0 0 program ([] : FCircuit (P.n + programHelperCount program)) :=
  compiledProgramFaultClassifierTailDerivOfClosedBackActions prog program
    (by
      intro residual hres st
      exact subset (currentStab prog st) residual hres)

noncomputable def compiledProgramFaultClassifierTailDerivOfExactGeneratedBackActions
    {P : QECParams} (prog : QStabProgram P) (program : XZProgram P.n)
    (exact :
      ∀ s : Fin P.numStab,
        P.backActionSet s = compilerGeneratedBackActionSetAllRows program s) :
    ProgramFaultClassifierTailDeriv (totalHelpers := programHelperCount program)
      prog 0 0 program ([] : FCircuit (P.n + programHelperCount program)) :=
  compiledProgramFaultClassifierTailDerivOfGeneratedBackActionSubset prog program
    (by
      intro s residual hres
      rw [exact s]
      exact hres)

def ReverseProgramBackActionsClosedForLabelsAt {P : QECParams}
    {totalHelpers : Nat}
    (helperStart detectorStart : Nat) (program : XZProgram P.n)
    (labels : ProgramStabLabels program)
    (tail : FCircuit (P.n + totalHelpers))
    (helperFit : helperStart + programHelperCount program <= totalHelpers) : Prop :=
  ∀ (s : Fin P.numStab) (residual : ErrorVec P.n),
    residual ∈
      reverseProgramBackActionResidualsByStabAux helperStart detectorStart program labels tail
        helperFit s ->
      residual ∈ P.backActionSet s

noncomputable def programFaultClassifierTailDerivForLabelsOfClosedBackActions
    {P : QECParams} (prog : QStabProgram P) {totalHelpers : Nat} :
    (helperStart detectorStart : Nat) -> (program : XZProgram P.n) ->
      (labels : ProgramStabLabels program) ->
      (tail : FCircuit (P.n + totalHelpers)) ->
      (helperFit : helperStart + programHelperCount program <= totalHelpers) ->
      ReverseProgramBackActionsClosedForLabelsAt helperStart detectorStart program labels tail
        helperFit ->
        ProgramFaultClassifierTailDerivForLabels (totalHelpers := totalHelpers)
          prog helperStart detectorStart program labels tail
  | helperStart, detectorStart, .skip, .skip, tail, _helperFit, _closed =>
      ProgramFaultClassifierTailDerivForLabels.skip helperStart detectorStart tail
  | helperStart, detectorStart, .meas scheme sigma, .meas _ _ stab row_eq, tail, helperFit,
      closed => by
      let cover :
          ReverseGadgetBackActionCoverAtForStab scheme sigma helperStart detectorStart
            helperFit tail stab :=
        ReverseGadgetBackActionCoverAtForStab.ofResiduals (by
          intro residual hres
          exact closed stab residual (by
            simpa [reverseProgramBackActionResidualsByStabAux] using hres))
      exact ProgramFaultClassifierTailDerivForLabels.meas helperStart detectorStart scheme sigma
        stab row_eq helperFit tail
        (gadgetFaultClassifierAtForStabOfReverseCoverAtForStab prog scheme sigma
          helperStart detectorStart helperFit tail stab cover)
  | helperStart, detectorStart, .seq first second,
      .seq firstLabels secondLabels, tail, helperFit, closed => by
      let firstFit : helperStart + programHelperCount first <= totalHelpers := by
        simp [programHelperCount] at helperFit ⊢
        omega
      let secondFit :
          (helperStart + programHelperCount first) + programHelperCount second <=
            totalHelpers := by
        simp [programHelperCount] at helperFit ⊢
        omega
      let firstTail :=
        compileProgramAux (helperStart + programHelperCount first) second secondFit ++ tail
      have closedFirst :
          ReverseProgramBackActionsClosedForLabelsAt helperStart detectorStart first firstLabels
            firstTail firstFit := by
        intro s residual hres
        exact closed s residual (by
          simpa [reverseProgramBackActionResidualsByStabAux, firstFit, secondFit, firstTail]
            using Or.inl hres)
      have closedSecond :
          ReverseProgramBackActionsClosedForLabelsAt
            (helperStart + programHelperCount first)
            (detectorStart + QStab.QClifford.PCC.programDetectorCount first)
            second secondLabels tail secondFit := by
        intro s residual hres
        exact closed s residual (by
          simpa [reverseProgramBackActionResidualsByStabAux, firstFit, secondFit, firstTail]
            using Or.inr hres)
      exact ProgramFaultClassifierTailDerivForLabels.seq secondFit
        (programFaultClassifierTailDerivForLabelsOfClosedBackActions prog
          (helperStart + programHelperCount first)
          (detectorStart + QStab.QClifford.PCC.programDetectorCount first)
          second secondLabels tail secondFit closedSecond)
        (programFaultClassifierTailDerivForLabelsOfClosedBackActions prog
          helperStart detectorStart first firstLabels firstTail firstFit closedFirst)

noncomputable def compiledProgramFaultClassifierTailDerivForLabelsOfGeneratedBackActionSubset
    {P : QECParams} (prog : QStabProgram P) (program : XZProgram P.n)
    (labels : ProgramStabLabels program)
    (subset :
      ∀ (s : Fin P.numStab) (residual : ErrorVec P.n),
        residual ∈ compilerGeneratedBackActionSet program labels s ->
          residual ∈ P.backActionSet s) :
    ProgramFaultClassifierTailDerivForLabels (totalHelpers := programHelperCount program)
      prog 0 0 program labels ([] : FCircuit (P.n + programHelperCount program)) :=
  programFaultClassifierTailDerivForLabelsOfClosedBackActions prog 0 0 program labels []
    (by simp)
    (by
      intro s residual hres
      exact subset s residual (by
        simpa [compilerGeneratedBackActionSet, reverseProgramBackActionResidualsByStab]
          using hres))

noncomputable def compiledProgramFaultClassifierTailDerivForLabelsOfExactGeneratedBackActions
    {P : QECParams} (prog : QStabProgram P) (program : XZProgram P.n)
    (labels : ProgramStabLabels program)
    (exact :
      ∀ s : Fin P.numStab,
        P.backActionSet s = compilerGeneratedBackActionSet program labels s) :
    ProgramFaultClassifierTailDerivForLabels (totalHelpers := programHelperCount program)
      prog 0 0 program labels ([] : FCircuit (P.n + programHelperCount program)) :=
  compiledProgramFaultClassifierTailDerivForLabelsOfGeneratedBackActionSubset prog program labels
    (by
      intro s residual hres
      rw [exact s]
      exact hres)

/-- A classifier for one compiled QClifford fragment.  Primitive classifiers
are supplied for one-gate/fault-location fragments; the compiler constructs
whole-gadget and whole-program classifiers from them by list/program induction. -/
structure FragmentClassifier {P : QECParams} (prog : QStabProgram P) {k : Nat}
    (abstract : QCState (P.n + k) -> State P)
    (fc : FCircuit (P.n + k)) where
  classify :
    ∀ tail sigma sigma',
      qceval fc sigma sigma' ->
        sigma'.lambda <= P.C_budget ->
          RunTraceDerivation prog abstract (fc ++ tail) sigma sigma'

namespace FragmentClassifier

def nil {P : QECParams} (prog : QStabProgram P) {k : Nat}
    (abstract : QCState (P.n + k) -> State P) :
    FragmentClassifier prog abstract ([] : FCircuit (P.n + k)) where
  classify := by
    intro tail sigma sigma' hrun _hbudget
    have hsame := qceval_nil hrun
    subst hsame
    exact
      { faults := []
        length_eq := by simp
        site_mem := by intro fault hmem; cases hmem
        source := SourceTraceDeriv.nil _ }

noncomputable def append {P : QECParams} {prog : QStabProgram P} {k : Nat}
    {abstract : QCState (P.n + k) -> State P}
    {c1 c2 : FCircuit (P.n + k)}
    (first : FragmentClassifier prog abstract c1)
    (second : FragmentClassifier prog abstract c2) :
    FragmentClassifier prog abstract (c1 ++ c2) where
  classify := by
    classical
    intro tail sigma sigma' hrun hbudget
    have hsplit := (qceval_append c1 c2 sigma sigma').mp hrun
    let mid := Classical.choose hsplit
    have hpair := Classical.choose_spec hsplit
    have hrun1 : qceval c1 sigma mid := hpair.1
    have hrun2 : qceval c2 mid sigma' := hpair.2
    have hbudgetMid : mid.lambda <= P.C_budget := by
      have hmono2 : mid.lambda <= sigma'.lambda := (fcevalW_of_qceval hrun2).1
      exact Nat.le_trans hmono2 hbudget
    let d1 := first.classify (c2 ++ tail) sigma mid hrun1 hbudgetMid
    let d2 := second.classify tail mid sigma' hrun2 hbudget
    have hmono1 : sigma.lambda <= mid.lambda := (fcevalW_of_qceval hrun1).1
    have hmono2 : mid.lambda <= sigma'.lambda := (fcevalW_of_qceval hrun2).1
    refine
      { faults := d1.faults ++ d2.faults
        length_eq := ?_
        site_mem := ?_
        source := SourceTraceDeriv.append d1.source d2.source }
    · simp [List.length_append, d1.length_eq, d2.length_eq]
      omega
    · intro fault hfault
      simp at hfault
      rcases hfault with hfault | hfault
      · simpa [List.append_assoc] using d1.site_mem fault hfault
      ·
        have hcursor := qceval_detectorCursor_eq hrun1
        have hsite :
            fault.site ∈
              QStab.QClifford.PCC.errLocsWithContextAux
                (sigma.es.detectorCursor + fCircuitDetectorAdvance c1) (c2 ++ tail) := by
          simpa [hcursor] using d2.site_mem fault hfault
        simpa [List.append_assoc] using
          errLocsWithContextAux_append_right sigma.es.detectorCursor c1 (c2 ++ tail) hsite

noncomputable def flattenMap {P : QECParams} {prog : QStabProgram P} {k : Nat}
    {abstract : QCState (P.n + k) -> State P}
    {α : Type} (xs : List α) (chunk : α -> FCircuit (P.n + k))
    (classifyChunk : ∀ x, FragmentClassifier prog abstract (chunk x)) :
    FragmentClassifier prog abstract ((xs.map chunk).flatten) := by
  induction xs with
  | nil =>
      simpa using FragmentClassifier.nil prog abstract
  | cons x xs ih =>
      simpa [List.flatten, List.map] using
        FragmentClassifier.append (classifyChunk x) ih

def toBudgetedProgramSimulation {P : QECParams} {prog : QStabProgram P}
    {k : Nat} {abstract : QCState (P.n + k) -> State P}
    {fc : FCircuit (P.n + k)} {A B : Formula P []}
    (classifier : FragmentClassifier prog abstract fc)
    (pre_refines : ∀ sigma, compileFormula k A sigma -> A.denote (abstract sigma))
    (post_refines :
      ∀ sigma, sigma.lambda <= P.C_budget ->
        B.denote (abstract sigma) -> compileFormula k B sigma) :
    BudgetedProgramSimulation prog k fc A B where
  abstract := abstract
  run_refines := by
    intro sigma sigma' hrun hbudget
    exact (classifier.classify [] sigma sigma' hrun hbudget).toMultiStep
  pre_refines := pre_refines
  post_refines := post_refines

end FragmentClassifier

/-! ## Closed count/source-trace classifiers

The classifiers below remove the previous primitive-fragment boundary for the
source-trace part of preservation.  They deliberately prove only the operational
fact that each concrete fired target site can be consumed by a syntactic QStab
fault step.  Error-sensitive assertion preservation is still governed by the
separate `pre_refines`/`post_refines` obligations, and detector/syndrome
correctness is the generated QClifford Hoare certificate in `VCBridge`. -/

def countDataQubit (P : QECParams) : Fin P.n := ⟨0, P.hn⟩

def countXToggle : Nat -> Pauli
  | 0 => Pauli.I
  | n + 1 => Pauli.mul Pauli.X (countXToggle n)

def countErrorVec (P : QECParams) (lambda : Nat) : ErrorVec P.n :=
  fun q => if q = countDataQubit P then countXToggle lambda else Pauli.I

@[simp] theorem countXToggle_succ (n : Nat) :
    countXToggle (n + 1) = Pauli.mul Pauli.X (countXToggle n) := rfl

theorem countErrorVec_succ (P : QECParams) (lambda : Nat) :
    ErrorVec.update (countErrorVec P lambda) (countDataQubit P) Pauli.X =
      countErrorVec P (lambda + 1) := by
  funext q
  by_cases hq : q = countDataQubit P
  · subst q
    simp [ErrorVec.update, countErrorVec]
  · simp [ErrorVec.update, countErrorVec, hq]

def countAbstractAt (P : QECParams) (lambda : Nat) : State P :=
  { State.init P with
    C := P.C_budget - lambda
    cnt0 := lambda
    lam_E := lambda
    E_tilde := countErrorVec P lambda }

def countAbstract (P : QECParams) {k : Nat} (_prog : QStabProgram P)
    (sigma : QCState (P.n + k)) : State P :=
  countAbstractAt P sigma.lambda

theorem countAbstractAt_err0_step {P : QECParams} (prog : QStabProgram P)
    (lambda : Nat) (hbudget : lambda + 1 <= P.C_budget) :
    TransitionStep prog (.err0 (countDataQubit P) Pauli.X)
      (countAbstractAt P lambda) (countAbstractAt P (lambda + 1)) := by
  have hC : 0 < (countAbstractAt P lambda).C := by
    simp [countAbstractAt]
    omega
  have hstate :
      { countAbstractAt P lambda with
        C := (countAbstractAt P lambda).C - 1
        cnt0 := (countAbstractAt P lambda).cnt0 + 1
        lam_E := (countAbstractAt P lambda).lam_E + 1
        E_tilde :=
          ErrorVec.update (countAbstractAt P lambda).E_tilde
            (countDataQubit P) Pauli.X } =
        countAbstractAt P (lambda + 1) := by
    simp [countAbstractAt, countErrorVec_succ]
    omega
  rw [← hstate]
  exact
    TransitionStep.err0 (prog := prog) (countAbstractAt P lambda)
      (countDataQubit P) Pauli.X (by decide) hC

noncomputable def countSourceTraceDeriv {P : QECParams} (prog : QStabProgram P)
    {k : Nat} (faults : List (FiredFaultWithContext (P.n + k)))
    (start : Nat) (hbudget : start + faults.length <= P.C_budget) :
    SourceTraceDeriv prog (countAbstractAt P start) faults
      (countAbstractAt P (start + faults.length)) := by
  induction faults generalizing start with
  | nil =>
      simpa using SourceTraceDeriv.nil (prog := prog) (countAbstractAt P start)
  | cons fault rest ih =>
      have hstep :
          SourceFaultStep prog fault
            (countAbstractAt P start) (countAbstractAt P (start + 1)) :=
        { label := TransitionLabel.err0 (countDataQubit P) Pauli.X
          step := countAbstractAt_err0_step prog start (by
            simp at hbudget
            omega) }
      have htail :
          SourceTraceDeriv prog (countAbstractAt P (start + 1)) rest
            (countAbstractAt P ((start + 1) + rest.length)) :=
        ih (start + 1) (by
          simp at hbudget ⊢
          omega)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        SourceTraceDeriv.fault hstep htail

noncomputable def countRunTraceDerivation {P : QECParams} (prog : QStabProgram P)
    {k : Nat} {fc tail : FCircuit (P.n + k)}
    {sigma sigma' : QCState (P.n + k)}
    (hrun : qceval fc sigma sigma')
    (hbudget : sigma'.lambda <= P.C_budget) :
    RunTraceDerivation prog (countAbstract P prog) (fc ++ tail) sigma sigma' := by
  classical
  let witness := qceval_context_faults_with_tail (tail := tail) hrun
  let faults := Classical.choose witness
  have hspec := Classical.choose_spec witness
  have hlen : faults.length = sigma'.lambda - sigma.lambda := hspec.1
  have hmem :
      ∀ fault, fault ∈ faults ->
        fault.site ∈
          QStab.QClifford.PCC.errLocsWithContextAux
            sigma.es.detectorCursor (fc ++ tail) := hspec.2
  have hmono : sigma.lambda <= sigma'.lambda := (fcevalW_of_qceval hrun).1
  have hlenAdd : sigma.lambda + faults.length = sigma'.lambda := by
    omega
  refine
    { faults := faults
      length_eq := hlen
      site_mem := hmem
      source := ?_ }
  have hbudgetStart : sigma.lambda + faults.length <= P.C_budget := by
    omega
  have hsource :=
    countSourceTraceDeriv prog faults sigma.lambda hbudgetStart
  simpa [countAbstract, hlenAdd] using hsource

noncomputable def countFragmentClassifier {P : QECParams}
    (prog : QStabProgram P) {k : Nat} (fc : FCircuit (P.n + k)) :
    FragmentClassifier prog (countAbstract P prog) fc where
  classify := by
    intro tail sigma sigma' hrun hbudget
    exact countRunTraceDerivation prog (tail := tail) hrun hbudget

/-- Primitive fragment classifiers for the instrumented operations used by all
four compilation schemes.  These are the scheme proof obligations at the
smallest granularity: every larger classifier below is generated from these
fields by the compiler rules and list/program induction. -/
structure PrimitiveFragmentClassifiers {P : QECParams} (prog : QStabProgram P)
    {k : Nat} (abstract : QCState (P.n + k) -> State P) where
  prep0 : ∀ q : Fin (P.n + k), FragmentClassifier prog abstract (prep0 q)
  prepP : ∀ q : Fin (P.n + k), FragmentClassifier prog abstract (prepP q)
  hadamard : ∀ q : Fin (P.n + k), FragmentClassifier prog abstract (hadamard q)
  cnot : ∀ c t : Fin (P.n + k), FragmentClassifier prog abstract (cnot c t)
  rawMeasZ : ∀ q : Fin (P.n + k), FragmentClassifier prog abstract (rawMeasZ q)
  flagMeasZ : ∀ q : Fin (P.n + k), FragmentClassifier prog abstract (flagMeasZ q)

/-- Closed primitive classifiers for the count/source-trace abstraction.

Each primitive classifier is obtained from the continuation-aware run
lineariser, so a primitive can only consume concrete `errLoc`s that actually
occur in the primitive fragment with the caller-provided deterministic tail. -/
noncomputable def countPrimitiveFragmentClassifiers {P : QECParams}
    (prog : QStabProgram P) {k : Nat} :
    PrimitiveFragmentClassifiers (P := P) (k := k) prog
      (countAbstract P (k := k) prog) where
  prep0 q := countFragmentClassifier prog (prep0 q)
  prepP q := countFragmentClassifier prog (prepP q)
  hadamard q := countFragmentClassifier prog (hadamard q)
  cnot c t := countFragmentClassifier prog (cnot c t)
  rawMeasZ q := countFragmentClassifier prog (rawMeasZ q)
  flagMeasZ q := countFragmentClassifier prog (flagMeasZ q)

noncomputable def zParitySlotClassifier {P : QECParams} {prog : QStabProgram P}
    {k : Nat} {abstract : QCState (P.n + k) -> State P}
    (prim : PrimitiveFragmentClassifiers prog abstract)
    (anc : Fin (P.n + k)) (slot : ScheduledPauli (P.n + k)) :
    FragmentClassifier prog abstract (zParitySlot anc slot) := by
  cases slot with
  | mk kind q =>
      cases kind
      · simpa [zParitySlot, List.append_assoc] using
          FragmentClassifier.append (prim.hadamard q)
            (FragmentClassifier.append (prim.cnot q anc) (prim.hadamard q))
      · simpa [zParitySlot] using prim.cnot q anc

noncomputable def shorCouplingSlotClassifier {P : QECParams} {prog : QStabProgram P}
    {k : Nat} {abstract : QCState (P.n + k) -> State P}
    (prim : PrimitiveFragmentClassifiers prog abstract)
    (cat : Fin (P.n + k)) (slot : ScheduledPauli (P.n + k)) :
    FragmentClassifier prog abstract (shorCouplingSlot slot cat) := by
  cases slot with
  | mk kind q =>
      cases kind
      · simpa [shorCouplingSlot, List.append_assoc] using
          FragmentClassifier.append (prim.hadamard q)
            (FragmentClassifier.append (prim.cnot q cat) (prim.hadamard q))
      · simpa [shorCouplingSlot] using prim.cnot q cat

noncomputable def knillSlotClassifier {P : QECParams} {prog : QStabProgram P}
    {k : Nat} {abstract : QCState (P.n + k) -> State P}
    (prim : PrimitiveFragmentClassifiers prog abstract)
    (slot : ScheduledPauli (P.n + k)) (anc : Fin (P.n + k)) :
    FragmentClassifier prog abstract (knillSlot slot anc) := by
  simpa [knillSlot, List.append_assoc] using
    FragmentClassifier.append (prim.prep0 anc)
      (FragmentClassifier.append
        (zParitySlotClassifier prim anc slot)
        (prim.rawMeasZ anc))

/-- Classifier for Shor cat preparation, by induction on the cat list. -/
noncomputable def orderedCatPrepZClassifier {P : QECParams} {prog : QStabProgram P}
    {k : Nat} {abstract : QCState (P.n + k) -> State P}
    (prim : PrimitiveFragmentClassifiers prog abstract)
    (cat : List (Fin (P.n + k))) :
    FragmentClassifier prog abstract (orderedCatPrepZ cat) := by
  cases cat with
  | nil =>
      simpa [orderedCatPrepZ] using FragmentClassifier.nil prog abstract
  | cons c0 rest =>
      simpa [orderedCatPrepZ, List.append_assoc] using
        FragmentClassifier.append (prim.prep0 c0)
          (FragmentClassifier.flattenMap (List.zip (c0 :: rest) rest)
            (fun cc => cnot cc.1 cc.2)
            (fun cc => prim.cnot cc.1 cc.2))

noncomputable def compileStandardOrderedClassifier {P : QECParams}
    {prog : QStabProgram P} {k : Nat}
    {abstract : QCState (P.n + k) -> State P}
    (prim : PrimitiveFragmentClassifiers prog abstract)
    (sigma : RuleSchedule (P.n + k)) (anc : Fin (P.n + k)) :
    FragmentClassifier prog abstract (compileStandardOrdered sigma anc) := by
  simpa [compileStandardOrdered, List.append_assoc] using
    FragmentClassifier.append (prim.prep0 anc)
      (FragmentClassifier.append
        (FragmentClassifier.flattenMap sigma.slots (zParitySlot anc)
          (fun slot => zParitySlotClassifier prim anc slot))
        (prim.flagMeasZ anc))

noncomputable def compileKnillOrderedClassifier {P : QECParams}
    {prog : QStabProgram P} {k : Nat}
    {abstract : QCState (P.n + k) -> State P}
    (prim : PrimitiveFragmentClassifiers prog abstract)
    (sigma : RuleSchedule (P.n + k)) (ancillas : List (Fin (P.n + k))) :
    FragmentClassifier prog abstract (compileKnillOrdered sigma ancillas) := by
  simpa [compileKnillOrdered] using
    FragmentClassifier.flattenMap (List.zip sigma.slots ancillas)
      (fun sa => knillSlot sa.1 sa.2)
      (fun sa => knillSlotClassifier prim sa.1 sa.2)

noncomputable def compileShorOrderedClassifier {P : QECParams}
    {prog : QStabProgram P} {k : Nat}
    {abstract : QCState (P.n + k) -> State P}
    (prim : PrimitiveFragmentClassifiers prog abstract)
    (sigma : RuleSchedule (P.n + k))
    (cat : List (Fin (P.n + k))) (verifier : Fin (P.n + k)) :
    FragmentClassifier prog abstract (compileShorOrdered sigma cat verifier) := by
  cases cat with
  | nil =>
      simpa [compileShorOrdered] using FragmentClassifier.nil prog abstract
  | cons c0 rest =>
      let cat' : List (Fin (P.n + k)) := c0 :: rest
      let last : Fin (P.n + k) := cat'.getLast (by simp [cat'])
      simpa [compileShorOrdered, cat', last, List.append_assoc] using
        FragmentClassifier.append (orderedCatPrepZClassifier prim cat')
          (FragmentClassifier.append (prim.prepP verifier)
            (FragmentClassifier.append (prim.cnot verifier c0)
              (FragmentClassifier.append (prim.cnot verifier last)
                (FragmentClassifier.append (prim.hadamard verifier)
                  (FragmentClassifier.append (prim.flagMeasZ verifier)
                    (FragmentClassifier.append
                      (FragmentClassifier.flattenMap (List.zip sigma.slots cat')
                        (fun sc => shorCouplingSlot sc.1 sc.2)
                        (fun sc => shorCouplingSlotClassifier prim sc.2 sc.1))
                      (FragmentClassifier.flattenMap cat' rawMeasZ
                        (fun q => prim.rawMeasZ q))))))))

noncomputable def compileFlagOrderedClassifier {P : QECParams}
    {prog : QStabProgram P} {k : Nat}
    {abstract : QCState (P.n + k) -> State P}
    (prim : PrimitiveFragmentClassifiers prog abstract)
    (sigma : RuleSchedule (P.n + k))
    (anc flag : Fin (P.n + k)) :
    FragmentClassifier prog abstract (compileFlagOrdered sigma anc flag) := by
  let half := sigma.slots.length / 2
  simpa [compileFlagOrdered, half, List.append_assoc] using
    FragmentClassifier.append (prim.prep0 anc)
      (FragmentClassifier.append (prim.prepP flag)
        (FragmentClassifier.append
          (FragmentClassifier.flattenMap (sigma.slots.take half) (zParitySlot anc)
            (fun slot => zParitySlotClassifier prim anc slot))
          (FragmentClassifier.append (prim.cnot flag anc)
            (FragmentClassifier.append
              (FragmentClassifier.flattenMap (sigma.slots.drop half) (zParitySlot anc)
                (fun slot => zParitySlotClassifier prim anc slot))
              (FragmentClassifier.append (prim.cnot flag anc)
                (FragmentClassifier.append (prim.flagMeasZ anc)
                  (FragmentClassifier.append (prim.hadamard flag)
                    (prim.flagMeasZ flag))))))))

noncomputable def compileGadgetOrderedClassifier {P : QECParams}
    {prog : QStabProgram P} {k : Nat}
    {abstract : QCState (P.n + k) -> State P}
    (prim : PrimitiveFragmentClassifiers prog abstract)
    (scheme : Scheme) (sigma : RuleSchedule (P.n + k))
    (anc : AncillaConfig (P.n + k)) :
    FragmentClassifier prog abstract (compileGadgetOrdered scheme sigma anc) := by
  match scheme, anc with
  | .NZ, .nz a =>
      simpa [compileGadgetOrdered] using compileStandardOrderedClassifier prim sigma a
  | .Knill, .knill ancillas =>
      simpa [compileGadgetOrdered] using compileKnillOrderedClassifier prim sigma ancillas
  | .Shor, .shor cat verifier =>
      simpa [compileGadgetOrdered] using compileShorOrderedClassifier prim sigma cat verifier
  | .Flag, .flag a f =>
      simpa [compileGadgetOrdered] using compileFlagOrderedClassifier prim sigma a f
  | .NZ, .knill _ =>
      simpa [compileGadgetOrdered] using FragmentClassifier.nil prog abstract
  | .NZ, .shor _ _ =>
      simpa [compileGadgetOrdered] using FragmentClassifier.nil prog abstract
  | .NZ, .flag _ _ =>
      simpa [compileGadgetOrdered] using FragmentClassifier.nil prog abstract
  | .Knill, .nz _ =>
      simpa [compileGadgetOrdered] using FragmentClassifier.nil prog abstract
  | .Knill, .shor _ _ =>
      simpa [compileGadgetOrdered] using FragmentClassifier.nil prog abstract
  | .Knill, .flag _ _ =>
      simpa [compileGadgetOrdered] using FragmentClassifier.nil prog abstract
  | .Shor, .nz _ =>
      simpa [compileGadgetOrdered] using FragmentClassifier.nil prog abstract
  | .Shor, .knill _ =>
      simpa [compileGadgetOrdered] using FragmentClassifier.nil prog abstract
  | .Shor, .flag _ _ =>
      simpa [compileGadgetOrdered] using FragmentClassifier.nil prog abstract
  | .Flag, .nz _ =>
      simpa [compileGadgetOrdered] using FragmentClassifier.nil prog abstract
  | .Flag, .knill _ =>
      simpa [compileGadgetOrdered] using FragmentClassifier.nil prog abstract
  | .Flag, .shor _ _ =>
      simpa [compileGadgetOrdered] using FragmentClassifier.nil prog abstract

noncomputable def compileGadgetBlockClassifier {P : QECParams}
    (prog : QStabProgram P) {total : Nat}
    {abstract : QCState (P.n + total) -> State P}
    (prim : PrimitiveFragmentClassifiers prog abstract)
    (scheme : Scheme) (sigma : RuleSchedule P.n)
    (start : Nat) (hfit : start + helperCount scheme sigma <= total) :
    FragmentClassifier prog abstract (compileGadgetBlock scheme sigma start hfit) := by
  simpa [compileGadgetBlock] using
    compileGadgetOrderedClassifier prim scheme (liftSchedule (k := total) sigma)
      (blockAncillaConfig scheme sigma start hfit)

noncomputable def compileProgramAuxClassifier {P : QECParams}
    (prog : QStabProgram P) {total : Nat}
    {abstract : QCState (P.n + total) -> State P}
    (prim : PrimitiveFragmentClassifiers prog abstract) :
    (start : Nat) -> (program : XZProgram P.n) ->
      (hfit : start + programHelperCount program <= total) ->
        FragmentClassifier prog abstract (compileProgramAux start program hfit)
  | start, .skip, hfit => by
      simpa [compileProgramAux] using FragmentClassifier.nil prog abstract
  | start, .meas scheme sigma, hfit =>
      compileGadgetBlockClassifier prog prim scheme sigma start hfit
  | start, .seq first second, hfit => by
      simpa [compileProgramAux, List.append_assoc] using
        FragmentClassifier.append
          (compileProgramAuxClassifier prog prim start first
            (by simp [programHelperCount] at hfit ⊢; omega))
          (compileProgramAuxClassifier prog prim
            (start + programHelperCount first) second
            (by simp [programHelperCount] at hfit ⊢; omega))

noncomputable def compileProgramClassifier {P : QECParams}
    (prog : QStabProgram P) (program : XZProgram P.n)
    {abstract : QCState (P.n + programHelperCount program) -> State P}
    (prim : PrimitiveFragmentClassifiers prog abstract) :
    FragmentClassifier prog abstract (compileProgram program) := by
  simpa [compileProgram] using
    compileProgramAuxClassifier prog prim 0 program (by simp)

noncomputable def compileStandardOrderedCountClassifier {P : QECParams}
    (prog : QStabProgram P) {k : Nat}
    (sigma : RuleSchedule (P.n + k)) (anc : Fin (P.n + k)) :
    FragmentClassifier prog (countAbstract P prog) (compileStandardOrdered sigma anc) :=
  compileStandardOrderedClassifier (countPrimitiveFragmentClassifiers (k := k) prog) sigma anc

noncomputable def compileKnillOrderedCountClassifier {P : QECParams}
    (prog : QStabProgram P) {k : Nat}
    (sigma : RuleSchedule (P.n + k)) (ancillas : List (Fin (P.n + k))) :
    FragmentClassifier prog (countAbstract P prog) (compileKnillOrdered sigma ancillas) :=
  compileKnillOrderedClassifier (countPrimitiveFragmentClassifiers (k := k) prog) sigma ancillas

noncomputable def compileShorOrderedCountClassifier {P : QECParams}
    (prog : QStabProgram P) {k : Nat}
    (sigma : RuleSchedule (P.n + k))
    (cat : List (Fin (P.n + k))) (verifier : Fin (P.n + k)) :
    FragmentClassifier prog (countAbstract P prog) (compileShorOrdered sigma cat verifier) :=
  compileShorOrderedClassifier (countPrimitiveFragmentClassifiers (k := k) prog) sigma cat verifier

noncomputable def compileFlagOrderedCountClassifier {P : QECParams}
    (prog : QStabProgram P) {k : Nat}
    (sigma : RuleSchedule (P.n + k)) (anc flag : Fin (P.n + k)) :
    FragmentClassifier prog (countAbstract P prog) (compileFlagOrdered sigma anc flag) :=
  compileFlagOrderedClassifier (countPrimitiveFragmentClassifiers (k := k) prog) sigma anc flag

noncomputable def compileGadgetOrderedCountClassifier {P : QECParams}
    (prog : QStabProgram P) {k : Nat}
    (scheme : Scheme) (sigma : RuleSchedule (P.n + k))
    (anc : AncillaConfig (P.n + k)) :
    FragmentClassifier prog (countAbstract P prog) (compileGadgetOrdered scheme sigma anc) :=
  compileGadgetOrderedClassifier (countPrimitiveFragmentClassifiers (k := k) prog)
    scheme sigma anc

noncomputable def compileGadgetBlockCountClassifier {P : QECParams}
    (prog : QStabProgram P) {total : Nat}
    (scheme : Scheme) (sigma : RuleSchedule P.n)
    (start : Nat) (hfit : start + helperCount scheme sigma <= total) :
    FragmentClassifier prog (countAbstract P prog)
      (compileGadgetBlock scheme sigma start hfit) :=
  compileGadgetBlockClassifier prog (countPrimitiveFragmentClassifiers (k := total) prog)
    scheme sigma start hfit

noncomputable def compileProgramAuxCountClassifier {P : QECParams}
    (prog : QStabProgram P) {total : Nat} :
    (start : Nat) -> (program : XZProgram P.n) ->
      (hfit : start + programHelperCount program <= total) ->
        FragmentClassifier prog (countAbstract P prog)
          (compileProgramAux start program hfit) :=
  compileProgramAuxClassifier prog (countPrimitiveFragmentClassifiers (k := total) prog)

noncomputable def compileProgramCountClassifier {P : QECParams}
    (prog : QStabProgram P) (program : XZProgram P.n) :
    FragmentClassifier prog (countAbstract P prog) (compileProgram program) :=
  compileProgramClassifier prog program
    (countPrimitiveFragmentClassifiers (k := programHelperCount program) prog)

/-- A trace-level simulation is sufficient to instantiate the budgeted
program-simulation interface. -/
def TraceProgramSimulation.toBudgeted {P : QECParams} {prog : QStabProgram P}
    {k : Nat} {fc : FCircuit (P.n + k)} {A B : Formula P []}
    (sim : TraceProgramSimulation prog k fc A B) :
    BudgetedProgramSimulation prog k fc A B where
  abstract := sim.abstract
  run_refines := by
    intro sigma sigma' hrun hbudget
    obtain ⟨faults, hlen, hmem⟩ := qceval_context_faults hrun
    exact sim.run_refines_from_trace sigma sigma' faults hrun hlen hmem hbudget
  pre_refines := sim.pre_refines
  post_refines := sim.post_refines

/-- Whole-program Hoare preservation for a compiled QClifford circuit.

This is the compiler theorem shape requested in the paper: if a concrete QStab
program satisfies `{A} prog {B}`, and the compiler proves that the concrete
target circuit simulates source executions inside the source budget, then the
compiled circuit satisfies the translated QClifford Hoare triple. -/
theorem budgeted_program_hoare_preservation {P : QECParams}
    {prog : QStabProgram P} {k : Nat} {fc : FCircuit (P.n + k)}
    {A B : Formula P []}
    (hsrc : ProgramHoare prog A.denote B.denote)
    (sim : BudgetedProgramSimulation prog k fc A B) :
    FHoare
      (compileFormulaWithinBudget k A)
      fc
      (compileFormulaWithinBudget k B) := by
  intro sigma sigma' hrun hpre hbudget'
  have hmono : sigma.lambda <= sigma'.lambda := (fcevalW_of_qceval hrun).1
  have hbudget : sigma.lambda <= P.C_budget := Nat.le_trans hmono hbudget'
  exact sim.post_refines sigma' hbudget'
    (hsrc (sim.abstract sigma) (sim.abstract sigma')
      (sim.run_refines sigma sigma' hrun hbudget')
      (sim.pre_refines sigma (hpre hbudget)))

/-- The trace-level version of whole-program Hoare preservation. -/
theorem trace_program_hoare_preservation {P : QECParams}
    {prog : QStabProgram P} {k : Nat} {fc : FCircuit (P.n + k)}
    {A B : Formula P []}
    (hsrc : ProgramHoare prog A.denote B.denote)
    (sim : TraceProgramSimulation prog k fc A B) :
    FHoare
      (compileFormulaWithinBudget k A)
      fc
      (compileFormulaWithinBudget k B) :=
  budgeted_program_hoare_preservation hsrc sim.toBudgeted

/-! ## Full-program invariant preservation -/

/-- Evidence that a complete compiled QClifford run refines a reachable active
state of a concrete QStab program.

For a concrete `QStabProgram`, the scheme proof must map every concrete
QClifford execution of the generated circuit to a source `MultiStep` run.  The
last field is the assertion-translation proof for the invariant at the
abstract final state. -/
structure ProgramInvariantSimulation {P : QECParams}
    (prog : QStabProgram P) (k : Nat) (fc : FCircuit (P.n + k))
    (I : Formula P []) where
  abstract : QCState (P.n + k) -> State P
  run_refines :
    forall sigma,
      qceval fc (QCState.clean (P.n + k)) sigma ->
        MultiStep prog (.active (State.init P)) (.active (abstract sigma))
  post_refines :
    forall sigma,
      I.denote (abstract sigma) -> compileFormula k I sigma

/-- Full-program invariant preservation.

This is the closed meta-theorem used by the compiler path: source QED-HL proves
that `I` is invariant for a concrete QStab program; the compiler proves that
every concrete QClifford run simulates a source run; then the compiled circuit
satisfies the compiled invariant as a target `FHoare` triple. -/
theorem invariant_hoare_preservation {P : QECParams} {prog : QStabProgram P}
    {k : Nat} {fc : FCircuit (P.n + k)} {I : Formula P []}
    (D : InvariantDerivation prog I)
    (sim : ProgramInvariantSimulation prog k fc I) :
    FHoare
      (fun sigma : QCState (P.n + k) => sigma = QCState.clean (P.n + k))
      fc
      (compileFormula k I) := by
  intro sigma sigma' hrun hclean
  subst hclean
  exact sim.post_refines sigma'
    (D.check_active_sound (sim.abstract sigma')
      (sim.run_refines sigma' hrun))

/-- Certificate-level full-program preservation.  The source premise is the
verifier-facing invariant certificate that expands to one QED-HL branch proof
for every enabled abstract transition. -/
theorem invariant_certificate_hoare_preservation {P : QECParams}
    {prog : QStabProgram P} {k : Nat} {fc : FCircuit (P.n + k)}
    {I : Formula P []}
    (cert : InvariantCertificate prog I)
    (sim : ProgramInvariantSimulation prog k fc I) :
    FHoare
      (fun sigma : QCState (P.n + k) => sigma = QCState.clean (P.n + k))
      fc
      (compileFormula k I) :=
  invariant_hoare_preservation cert.toInvariantDerivation sim

/-- Budgeted simulation evidence for a compiled full program.  This is the
realistic form for QClifford, whose nondeterministic semantics permits more
faults than the finite QStab source budget. -/
structure BudgetedProgramInvariantSimulation {P : QECParams}
    (prog : QStabProgram P) (k : Nat) (fc : FCircuit (P.n + k))
    (I : Formula P []) where
  abstract : QCState (P.n + k) -> State P
  run_refines :
    forall sigma,
      qceval fc (QCState.clean (P.n + k)) sigma ->
        sigma.lambda <= P.C_budget ->
          MultiStep prog (.active (State.init P)) (.active (abstract sigma))
  post_refines :
    forall sigma,
      sigma.lambda <= P.C_budget ->
        I.denote (abstract sigma) -> compileFormula k I sigma

/-- Budgeted full-program invariant preservation.  This is the preservation
theorem scheme-specific compiler proofs should instantiate. -/
theorem budgeted_invariant_hoare_preservation {P : QECParams}
    {prog : QStabProgram P} {k : Nat} {fc : FCircuit (P.n + k)}
    {I : Formula P []}
    (D : InvariantDerivation prog I)
    (sim : BudgetedProgramInvariantSimulation prog k fc I) :
    FHoare
      (fun sigma : QCState (P.n + k) => sigma = QCState.clean (P.n + k))
      fc
      (compileFormulaWithinBudget k I) := by
  intro sigma sigma' hrun hclean hbudget
  subst hclean
  exact sim.post_refines sigma' hbudget
    (D.check_active_sound (sim.abstract sigma')
      (sim.run_refines sigma' hrun hbudget))

/-- Certificate-level budgeted preservation. -/
theorem budgeted_invariant_certificate_hoare_preservation {P : QECParams}
    {prog : QStabProgram P} {k : Nat} {fc : FCircuit (P.n + k)}
    {I : Formula P []}
    (cert : InvariantCertificate prog I)
    (sim : BudgetedProgramInvariantSimulation prog k fc I) :
    FHoare
      (fun sigma : QCState (P.n + k) => sigma = QCState.clean (P.n + k))
      fc
      (compileFormulaWithinBudget k I) :=
  budgeted_invariant_hoare_preservation cert.toInvariantDerivation sim

/-! ## Compiler-generated XZ circuits -/

/-- The concrete target circuit associated with a compiler-facing XZ source
program.  The program is concrete: its schedules and schemes are fixed in the
syntax, and the helper budget is computed from that syntax. -/
abbrev compiledXZCircuit {n : Nat} (program : XZProgram n) :
    FCircuit (n + programHelperCount program) :=
  compileProgram program

/-- The compilation derivation tree for every concrete `XZProgram`.  This is
the syntax-level half of the preservation story: the target program is computed
by the compiler rules, not supplied externally. -/
def compiledXZDerivation {n : Nat} (program : XZProgram n) :
    ProgramCompileDeriv 0 program (compiledXZCircuit program) :=
  compileProgramDeriv program

/-- Reverse-order compilation derivation for every concrete `XZProgram`.

This is the proof-producing companion to `compiledXZDerivation`: sequence nodes
derive the later target suffix first, so the fault classifier for an earlier
gadget receives the already known continuation used to compute current
back-action. -/
def compiledXZReverseDerivation {n : Nat} (program : XZProgram n) :
    ProgramReverseCompileDeriv 0 program (compiledXZCircuit program) :=
  compileProgramReverseDeriv program

/-- Proof-carrying package for preserving a source invariant through a concrete
compiler-facing `XZProgram`.  The target circuit and compilation derivation are
computed fields; the only non-generic field is the actual scheme-specific
simulation proof from concrete QClifford executions back to QStab reachability. -/
structure XZInvariantPreservationCertificate {P : QECParams}
    (sourceProg : QStabProgram P) (program : XZProgram P.n)
    (I : Formula P []) where
  source : InvariantCertificate sourceProg I
  simulation :
    ProgramInvariantSimulation sourceProg (programHelperCount program)
      (compiledXZCircuit program) I
  compileDeriv :
    ProgramCompileDeriv 0 program (compiledXZCircuit program) :=
      compiledXZDerivation program
  targetHoare :
    FHoare
      (fun sigma : QCState (P.n + programHelperCount program) =>
        sigma = QCState.clean (P.n + programHelperCount program))
      (compiledXZCircuit program)
      (compileFormula (programHelperCount program) I) :=
    invariant_certificate_hoare_preservation source simulation

/-- Budgeted proof-carrying package for preserving a source invariant through a
concrete compiler-facing `XZProgram`.  This is the intended non-vacuous target
for the four scheme-specific classifier proofs. -/
structure XZBudgetedInvariantPreservationCertificate {P : QECParams}
    (sourceProg : QStabProgram P) (program : XZProgram P.n)
    (I : Formula P []) where
  source : InvariantCertificate sourceProg I
  simulation :
    BudgetedProgramInvariantSimulation sourceProg (programHelperCount program)
      (compiledXZCircuit program) I
  compileDeriv :
    ProgramCompileDeriv 0 program (compiledXZCircuit program) :=
      compiledXZDerivation program
  targetHoare :
    FHoare
      (fun sigma : QCState (P.n + programHelperCount program) =>
        sigma = QCState.clean (P.n + programHelperCount program))
      (compiledXZCircuit program)
      (compileFormulaWithinBudget (programHelperCount program) I) :=
    budgeted_invariant_certificate_hoare_preservation source simulation

/-- XZ-level proof-carrying package for the general Hoare-preservation theorem.

The package binds all generated artifacts to the same concrete `XZProgram`:
the compiled circuit, the PL-style compilation derivation tree, and the
Hoare-backed `.syn` VC certificate consumed by QClifford VCGen.  The only
scheme-specific field is `simulation`, which must explain the actual concrete
target fault trace as a source QStab execution. -/
structure XZBudgetedHoarePreservationCertificate {P : QECParams}
    (sourceProg : QStabProgram P) (program : XZProgram P.n)
    (A B : Formula P [])
    (hnq : 0 < P.n + programHelperCount program)
    (hnumStab : 0 < QStab.QClifford.PCC.programNumStab program) where
  source : ProgramHoare sourceProg A.denote B.denote
  simulation :
    SyntacticTraceProgramSimulation sourceProg (programHelperCount program)
      (compiledXZCircuit program) A B
  compileDeriv :
    ProgramCompileDeriv 0 program (compiledXZCircuit program) :=
      compiledXZDerivation program
  syndrome :
    QStab.QClifford.PCC.ProgramCompilationHoareSynCertificate program hnq hnumStab :=
      QStab.QClifford.PCC.XZProgram.generatedCompilationHoareSynCertificate
        program hnq hnumStab
  targetHoare :
    FHoare
      (compileFormulaWithinBudget (programHelperCount program) A)
      (compiledXZCircuit program)
      (compileFormulaWithinBudget (programHelperCount program) B) :=
    trace_program_hoare_preservation source simulation.toTrace

/-- XZ-level preservation package using the scheme-specific fault classifier.

This is the non-count endpoint for the compiler proof.  The
`faultClassifierDeriv` field is a derivation tree whose measurement leaves are
scheme-specific gadget classifiers and whose sequencing nodes follow the
`XZProgram` syntax.  The `simulation` field is still the semantic bridge from
classified concrete target traces to source QStab traces; it is the remaining
place where the event classifier must be lifted through the assertion
translation.  Crucially, this package no longer abstracts a target fault as
only "one more count": each gadget classifier must assign the concrete
propagated residual/readout effect to a QStab branch. -/
structure XZSchemeFaultClassifierHoarePreservationCertificate {P : QECParams}
    (sourceProg : QStabProgram P) (program : XZProgram P.n)
    (A B : Formula P [])
    (hnq : 0 < P.n + programHelperCount program)
    (hnumStab : 0 < QStab.QClifford.PCC.programNumStab program) where
  source : ProgramHoare sourceProg A.denote B.denote
  faultClassifierDeriv :
    ProgramFaultClassifierDeriv
      (totalHelpers := programHelperCount program) sourceProg 0 0 program
  simulation :
    SyntacticTraceProgramSimulation sourceProg (programHelperCount program)
      (compiledXZCircuit program) A B
  compileDeriv :
    ProgramCompileDeriv 0 program (compiledXZCircuit program) :=
      compiledXZDerivation program
  syndrome :
    QStab.QClifford.PCC.ProgramCompilationHoareSynCertificate program hnq hnumStab :=
      QStab.QClifford.PCC.XZProgram.generatedCompilationHoareSynCertificate
        program hnq hnumStab
  targetHoare :
    FHoare
      (compileFormulaWithinBudget (programHelperCount program) A)
      (compiledXZCircuit program)
      (compileFormulaWithinBudget (programHelperCount program) B) :=
    trace_program_hoare_preservation source simulation.toTrace

/-- XZ-level preservation package with compiler-generated back-action
classification.

This is the closed-boundary version of
`XZSchemeFaultClassifierHoarePreservationCertificate`.  Instead of asking the
client to provide one classifier for every scheme/gadget/tail, the compiler
builds the exact-tail classifier by induction on `XZProgram` from the reverse
compilation rules and the shape-preserving source-row labels.  The remaining
code-specific assumption is just the inclusion of the row-indexed
compiler-generated residual set into the source `backActionSet`.

The construction is scheme-generic: the measurement leaf uses the reverse
gadget rule selected by `scheme`, so it covers `.NZ`, `.Knill`, `.Shor`, and
`.Flag` uniformly. -/
structure XZGeneratedBackActionHoarePreservationCertificate {P : QECParams}
    (sourceProg : QStabProgram P) (program : XZProgram P.n)
    (A B : Formula P [])
    (hnq : 0 < P.n + programHelperCount program)
    (hnumStab : 0 < QStab.QClifford.PCC.programNumStab program) where
  source : ProgramHoare sourceProg A.denote B.denote
  labels : ProgramStabLabels program
  generatedBackActionSubset :
    ∀ (s : Fin P.numStab) (residual : ErrorVec P.n),
      residual ∈ compilerGeneratedBackActionSet program labels s ->
        residual ∈ P.backActionSet s
  simulation :
    SyntacticTraceProgramSimulation sourceProg (programHelperCount program)
      (compiledXZCircuit program) A B
  faultClassifierTailDerivForLabels :
    ProgramFaultClassifierTailDerivForLabels
      (totalHelpers := programHelperCount program)
      sourceProg 0 0 program labels ([] : FCircuit (P.n + programHelperCount program)) :=
    compiledProgramFaultClassifierTailDerivForLabelsOfGeneratedBackActionSubset
      sourceProg program labels generatedBackActionSubset
  compileDeriv :
    ProgramCompileDeriv 0 program (compiledXZCircuit program) :=
      compiledXZDerivation program
  reverseCompileDeriv :
    ProgramReverseCompileDeriv 0 program (compiledXZCircuit program) :=
      compiledXZReverseDerivation program
  syndrome :
    QStab.QClifford.PCC.ProgramCompilationHoareSynCertificate program hnq hnumStab :=
      QStab.QClifford.PCC.XZProgram.generatedCompilationHoareSynCertificate
        program hnq hnumStab
  targetHoare :
    FHoare
      (compileFormulaWithinBudget (programHelperCount program) A)
      (compiledXZCircuit program)
      (compileFormulaWithinBudget (programHelperCount program) B) :=
    trace_program_hoare_preservation source simulation.toTrace

/-- Exact generated-backaction variant of
`XZGeneratedBackActionHoarePreservationCertificate`.

Use this when the source code instance chooses `P.backActionSet` to be exactly
the compiler-generated residual policy for the concrete `XZProgram`. -/
structure XZExactGeneratedBackActionHoarePreservationCertificate {P : QECParams}
    (sourceProg : QStabProgram P) (program : XZProgram P.n)
    (A B : Formula P [])
    (hnq : 0 < P.n + programHelperCount program)
    (hnumStab : 0 < QStab.QClifford.PCC.programNumStab program) where
  source : ProgramHoare sourceProg A.denote B.denote
  labels : ProgramStabLabels program
  generatedBackActionExact :
    ∀ s : Fin P.numStab,
      P.backActionSet s = compilerGeneratedBackActionSet program labels s
  simulation :
    SyntacticTraceProgramSimulation sourceProg (programHelperCount program)
      (compiledXZCircuit program) A B
  faultClassifierTailDerivForLabels :
    ProgramFaultClassifierTailDerivForLabels
      (totalHelpers := programHelperCount program)
      sourceProg 0 0 program labels ([] : FCircuit (P.n + programHelperCount program)) :=
    compiledProgramFaultClassifierTailDerivForLabelsOfExactGeneratedBackActions
      sourceProg program labels generatedBackActionExact
  compileDeriv :
    ProgramCompileDeriv 0 program (compiledXZCircuit program) :=
      compiledXZDerivation program
  reverseCompileDeriv :
    ProgramReverseCompileDeriv 0 program (compiledXZCircuit program) :=
      compiledXZReverseDerivation program
  syndrome :
    QStab.QClifford.PCC.ProgramCompilationHoareSynCertificate program hnq hnumStab :=
      QStab.QClifford.PCC.XZProgram.generatedCompilationHoareSynCertificate
        program hnq hnumStab
  targetHoare :
    FHoare
      (compileFormulaWithinBudget (programHelperCount program) A)
      (compiledXZCircuit program)
      (compileFormulaWithinBudget (programHelperCount program) B) :=
    trace_program_hoare_preservation source simulation.toTrace

/-- XZ-level preservation package generated from primitive scheme classifiers.

Unlike `XZBudgetedHoarePreservationCertificate`, this certificate does not ask
for a whole-program simulation field.  The full classifier is constructed from
`primitives` by:

* list induction over the stabilizer schedule inside the four scheme rules;
* structural induction over `XZProgram` for sequencing;
* the concrete compiler equations `compileGadgetBlock` and `compileProgramAux`.

Thus a client must prove the primitive operation classifiers, and the compiler
then assembles the complete QStab-to-QClifford Hoare-preservation path. -/
structure XZPrimitiveClassifierHoarePreservationCertificate {P : QECParams}
    (sourceProg : QStabProgram P) (program : XZProgram P.n)
    (A B : Formula P [])
    (hnq : 0 < P.n + programHelperCount program)
    (hnumStab : 0 < QStab.QClifford.PCC.programNumStab program) where
  source : ProgramHoare sourceProg A.denote B.denote
  abstract : QCState (P.n + programHelperCount program) -> State P
  primitives : PrimitiveFragmentClassifiers sourceProg abstract
  pre_refines :
    ∀ sigma, compileFormula (programHelperCount program) A sigma ->
      A.denote (abstract sigma)
  post_refines :
    ∀ sigma, sigma.lambda <= P.C_budget ->
      B.denote (abstract sigma) ->
        compileFormula (programHelperCount program) B sigma
  compileDeriv :
    ProgramCompileDeriv 0 program (compiledXZCircuit program) :=
      compiledXZDerivation program
  syndrome :
    QStab.QClifford.PCC.ProgramCompilationHoareSynCertificate program hnq hnumStab :=
      QStab.QClifford.PCC.XZProgram.generatedCompilationHoareSynCertificate
        program hnq hnumStab
  classifier :
    FragmentClassifier sourceProg abstract (compiledXZCircuit program) :=
      by
        simpa [compiledXZCircuit] using
          compileProgramClassifier sourceProg program primitives
  simulation :
    BudgetedProgramSimulation sourceProg (programHelperCount program)
      (compiledXZCircuit program) A B :=
    classifier.toBudgetedProgramSimulation pre_refines post_refines
  targetHoare :
    FHoare
      (compileFormulaWithinBudget (programHelperCount program) A)
      (compiledXZCircuit program)
      (compileFormulaWithinBudget (programHelperCount program) B) :=
    budgeted_program_hoare_preservation source simulation

/-- Legacy count-only scaffold.

This structure is kept only as a regression scaffold for the trace plumbing.
It is not the intended compiler-correctness theorem: it classifies every target
fault by count rather than by the scheme-specific propagated residual/readout
effect.  Use `XZSchemeFaultClassifierHoarePreservationCertificate` for the
paper theorem path. -/
structure XZLegacyCountClassifierHoarePreservationCertificate {P : QECParams}
    (sourceProg : QStabProgram P) (program : XZProgram P.n)
    (A B : Formula P [])
    (hnq : 0 < P.n + programHelperCount program)
    (hnumStab : 0 < QStab.QClifford.PCC.programNumStab program) where
  source : ProgramHoare sourceProg A.denote B.denote
  pre_refines :
    ∀ sigma, compileFormula (programHelperCount program) A sigma ->
      A.denote (countAbstract P (k := programHelperCount program) sourceProg sigma)
  post_refines :
    ∀ sigma, sigma.lambda <= P.C_budget ->
      B.denote (countAbstract P (k := programHelperCount program) sourceProg sigma) ->
        compileFormula (programHelperCount program) B sigma
  compileDeriv :
    ProgramCompileDeriv 0 program (compiledXZCircuit program) :=
      compiledXZDerivation program
  syndrome :
    QStab.QClifford.PCC.ProgramCompilationHoareSynCertificate program hnq hnumStab :=
      QStab.QClifford.PCC.XZProgram.generatedCompilationHoareSynCertificate
        program hnq hnumStab
  classifier :
    FragmentClassifier sourceProg
      (countAbstract P (k := programHelperCount program) sourceProg)
      (compiledXZCircuit program) :=
      by
        simpa [compiledXZCircuit] using
          compileProgramCountClassifier sourceProg program
  simulation :
    BudgetedProgramSimulation sourceProg (programHelperCount program)
      (compiledXZCircuit program) A B :=
    classifier.toBudgetedProgramSimulation pre_refines post_refines
  targetHoare :
    FHoare
      (compileFormulaWithinBudget (programHelperCount program) A)
      (compiledXZCircuit program)
      (compileFormulaWithinBudget (programHelperCount program) B) :=
    budgeted_program_hoare_preservation source simulation

/-- The existing generated PCC package for an `XZProgram` supplies the
scheme-generic syndrome obligations for all four schemes.  Hoare preservation
of arbitrary source invariants additionally requires a
`ProgramInvariantSimulation`, instantiated by the scheme-specific
source-to-target fault-classification proof. -/
abbrev compiledXZSyndromeCertificate {n : Nat} (program : XZProgram n)
    (hnq : 0 < n + programHelperCount program)
    (hnumStab : 0 < QStab.QClifford.PCC.programNumStab program) :
    QStab.QClifford.PCC.ProgramCompilationHoareSynCertificate program hnq hnumStab :=
  QStab.QClifford.PCC.XZProgram.generatedCompilationHoareSynCertificate program hnq hnumStab

end QStab.QClifford.Compile
