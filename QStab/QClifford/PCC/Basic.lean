import QStab.QClifford.FaultHoare
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

/-!
# Proof-carrying code kernel for QClifford distance certificates

This module is the trusted PCC layer.  A compiler may choose annotations
(`barrier`, witness scripts) and fill proof obligations, but the obligation
statements are generated here from the actual QClifford circuit and code spec.

The lower-bound proof of `certificate_sound` goes through the audited
QClifford `FDeriv` calculus and `fhoare_sound`.
-/

namespace QStab.QClifford.PCC

instance instFintypePauli : Fintype Pauli where
  elems := {Pauli.I, Pauli.X, Pauli.Y, Pauli.Z}
  complete := by
    intro p
    cases p <;> simp

noncomputable instance instDecidableEqErrorState {nq : Nat} : DecidableEq (ErrorState nq) :=
  Classical.decEq _

/-- Proof-erased gate syntax for decidable well-formedness checks. -/
inductive GateView (nq : Nat) where
  | cnot (control target : Fin nq)
  | hadamard (q : Fin nq)
  | prepZero (q : Fin nq)
  | prepPlus (q : Fin nq)
  | measZ (q : Fin nq)
  deriving DecidableEq, Repr

/-- Proof-erased instrumented instruction syntax. -/
inductive InstrView (nq : Nat) where
  | gate (g : GateView nq)
  | errLoc (q : Fin nq)
  deriving DecidableEq, Repr

def gateView {nq : Nat} : Gate nq -> GateView nq
  | .cnot c t _ => .cnot c t
  | .hadamard q => .hadamard q
  | .prepZero q => .prepZero q
  | .prepPlus q => .prepPlus q
  | .measZ q => .measZ q

def instrView {nq : Nat} : FInstr nq -> InstrView nq
  | .gate g => .gate (gateView g)
  | .errLoc q => .errLoc q

def circuitView {nq : Nat} (C : FCircuit nq) : List (InstrView nq) :=
  C.map instrView

/-- A stabilizer-code/syndrome-extraction specification at QClifford level.

`expectedProgram` and `gadget` are proof-erased/syntactic schedule data used by
`WellFormed` and `gadgetMeasFlip`; the fault-tolerance theorem itself still
runs over the concrete `FCircuit`.

`flagSlot` maps each raw measurement flag to a fresh time-resolved slot in
`ErrorState.detectors`; unlike the legacy qubit-indexed `measFlips`, this does
not merge repeated measurements of a reused syndrome ancilla.  A stabilizer may
be read out by several raw slots, as in Knill/Shor style transversal
measurements; `stabilizerReadout i` lists exactly the raw slots XORed to obtain
the syndrome bit for stabilizer `i`.  Extra verifier/flag slots are selected by
`postselectFlag` and are required to be zero by `allFlagsZero`.
-/
structure CodeSpec (nq : Nat) where
  numStab : Nat
  numFlags : Nat
  isData : Fin nq -> Bool
  stabilizer : Fin numStab -> Fin nq -> Pauli
  stabilizerReadout : Fin numStab -> List (Fin numFlags)
  postselectFlag : Fin numFlags -> Bool
  flagSlot : Fin numFlags -> Nat
  flagSlot_injective : Function.Injective flagSlot
  flagSlot_ordered : ∀ i, flagSlot i = i.val
  readout_disjoint :
    ∀ i j, i ≠ j -> ∀ s, s ∈ stabilizerReadout i -> s ∈ stabilizerReadout j -> False
  gadgetDetectorStart : Fin numStab -> Nat
  gadget : Fin numStab -> FCircuit nq
  expectedProgram : List (InstrView nq)
  d : Nat
  d_pos : 0 < d

def stateOfPauli {nq : Nat} (E : Fin nq -> Pauli) : ErrorState nq where
  paulis := E
  measFlips := fun _ => false
  detectors := fun _ => false
  detectorCursor := 0

def stateOfPauliAtDetector {nq : Nat} (slot : Nat) (E : Fin nq -> Pauli) :
    ErrorState nq where
  paulis := E
  measFlips := fun _ => false
  detectors := fun _ => false
  detectorCursor := slot

def dataOnlyPauli {nq : Nat} (spec : CodeSpec nq) (E : Fin nq -> Pauli) :
    Fin nq -> Pauli :=
  fun q => if spec.isData q then E q else Pauli.I

def stateOfDataPauliAtDetector {nq : Nat} (spec : CodeSpec nq)
    (slot : Nat) (E : Fin nq -> Pauli) : ErrorState nq :=
  stateOfPauliAtDetector slot (dataOnlyPauli spec E)

def vectorParity {nq : Nat} (S E : Fin nq -> Pauli) : Bool :=
  (List.finRange nq).foldl
    (fun acc q => xor acc (anticommute (S q) (E q)))
    false

def prodStab {nq : Nat} (spec : CodeSpec nq) (mask : Fin spec.numStab -> Bool) :
    Fin nq -> Pauli :=
  fun q =>
    (List.finRange spec.numStab).foldl
      (fun acc i => if mask i then pauliMul acc (spec.stabilizer i q) else acc)
      Pauli.I

def dataVector {nq : Nat} (spec : CodeSpec nq) (es : ErrorState nq) : Fin nq -> Pauli :=
  fun q => if spec.isData q then es.paulis q else Pauli.I

def Centralizer {nq : Nat} (spec : CodeSpec nq) (E : Fin nq -> Pauli) : Prop :=
  ∀ i : Fin spec.numStab, vectorParity (spec.stabilizer i) E = false

instance instDecidableCentralizer {nq : Nat} (spec : CodeSpec nq) (E : Fin nq -> Pauli) :
    Decidable (Centralizer spec E) := by
  unfold Centralizer
  infer_instance

def Stab {nq : Nat} (spec : CodeSpec nq) (E : Fin nq -> Pauli) : Prop :=
  ∃ mask : Fin spec.numStab -> Bool, ∀ q : Fin nq, E q = prodStab spec mask q

instance instDecidableStab {nq : Nat} (spec : CodeSpec nq) (E : Fin nq -> Pauli) :
    Decidable (Stab spec E) := by
  unfold Stab
  infer_instance

def logicalFailure {nq : Nat} (spec : CodeSpec nq) (es : ErrorState nq) : Prop :=
  Centralizer spec (dataVector spec es) ∧ ¬ Stab spec (dataVector spec es)

instance instDecidableLogicalFailure {nq : Nat} (spec : CodeSpec nq) (es : ErrorState nq) :
    Decidable (logicalFailure spec es) := by
  unfold logicalFailure
  infer_instance

def xorBools : List Bool -> Bool :=
  List.foldr xor false

def syndromeBit {nq : Nat} (spec : CodeSpec nq) (es : ErrorState nq)
    (i : Fin spec.numStab) : Bool :=
  xorBools ((spec.stabilizerReadout i).map fun f => es.detectors (spec.flagSlot f))

def undetected {nq : Nat} (spec : CodeSpec nq) (es : ErrorState nq) : Prop :=
  ∀ i : Fin spec.numStab, syndromeBit spec es i = false

def allPostselectionFlagsZero {nq : Nat} (spec : CodeSpec nq) (es : ErrorState nq) : Prop :=
  ∀ i : Fin spec.numFlags, spec.postselectFlag i = true -> es.detectors (spec.flagSlot i) = false

def allFlagsZero {nq : Nat} (spec : CodeSpec nq) (es : ErrorState nq) : Prop :=
  undetected spec es ∧ allPostselectionFlagsZero spec es

instance instDecidableUndetected {nq : Nat} (spec : CodeSpec nq) (es : ErrorState nq) :
    Decidable (undetected spec es) := by
  unfold undetected syndromeBit xorBools
  infer_instance

instance instDecidableAllPostselectionFlagsZero {nq : Nat}
    (spec : CodeSpec nq) (es : ErrorState nq) :
    Decidable (allPostselectionFlagsZero spec es) := by
  unfold allPostselectionFlagsZero
  infer_instance

instance instDecidableAllFlagsZero {nq : Nat} (spec : CodeSpec nq) (es : ErrorState nq) :
    Decidable (allFlagsZero spec es) := by
  unfold allFlagsZero
  infer_instance

def failure {nq : Nat} (spec : CodeSpec nq) (es : ErrorState nq) : Prop :=
  logicalFailure spec es ∧ allFlagsZero spec es

instance instDecidableFailure {nq : Nat} (spec : CodeSpec nq) (es : ErrorState nq) :
    Decidable (failure spec es) := by
  unfold failure
  infer_instance

/-- Minimal two-raw-slot combiner fixture used to pin the PCC readout policy. -/
def combinerTestSpec : CodeSpec 1 where
  numStab := 1
  numFlags := 2
  isData := fun _ => true
  stabilizer := fun _ _ => Pauli.I
  stabilizerReadout := fun _ => [⟨0, by decide⟩, ⟨1, by decide⟩]
  postselectFlag := fun _ => false
  flagSlot := fun i => i.val
  flagSlot_injective := by
    intro a b h
    exact Fin.ext h
  flagSlot_ordered := by
    intro i
    rfl
  readout_disjoint := by
    intro i j hij _ _ _
    exact hij (Subsingleton.elim i j)
  gadgetDetectorStart := fun _ => 0
  gadget := fun _ => []
  expectedProgram := []
  d := 1
  d_pos := by decide

def combinerPairFlipState : ErrorState 1 :=
  { ErrorState.clean 1 with
    detectors := fun k => decide (k = 0) || decide (k = 1) }

def combinerSingleFlipState : ErrorState 1 :=
  { ErrorState.clean 1 with
    detectors := fun k => decide (k = 0) }

theorem combinerPairFlip_syndrome_zero :
    syndromeBit combinerTestSpec combinerPairFlipState ⟨0, by decide⟩ = false := by
  decide

theorem combinerSingleFlip_syndrome_one :
    syndromeBit combinerTestSpec combinerSingleFlipState ⟨0, by decide⟩ = true := by
  decide

def WellFormed {nq : Nat} (C : FCircuit nq) (spec : CodeSpec nq) : Prop :=
  circuitView C = spec.expectedProgram

def specCircuit {nq : Nat} (spec : CodeSpec nq) : FCircuit nq :=
  (List.finRange spec.numStab).flatMap fun i => spec.gadget i

instance instDecidableWellFormed {nq : Nat} (C : FCircuit nq) (spec : CodeSpec nq) :
    Decidable (WellFormed C spec) := by
  unfold WellFormed
  infer_instance

/-- Fault-free syndrome readout for one specified gadget, computed with the
real QClifford `propagateCircuit` and the time-resolved detector log.  The
initial detector cursor is set to `gadgetDetectorStart i`; the syndrome bit is
then the XOR of exactly `stabilizerReadout i`, so Knill-style transversal raw
measurements combine only within their own stabilizer. -/
def gadgetMeasFlip {nq : Nat} (_C : FCircuit nq) (spec : CodeSpec nq)
    (i : Fin spec.numStab) (E : Fin nq -> Pauli) : Bool :=
  syndromeBit spec
    (propagateCircuit (eraseFaults (spec.gadget i))
      (stateOfDataPauliAtDetector spec (spec.gadgetDetectorStart i) E))
    i

def parity {nq : Nat} (_spec : CodeSpec nq) (S E : Fin nq -> Pauli) : Bool :=
  vectorParity S E

/-- Error location plus the deterministic gate suffix remaining after it. -/
structure ErrLocWithSuffix (nq : Nat) where
  q : Fin nq
  suffix : Circuit nq

def errLocsWithSuffix {nq : Nat} : FCircuit nq -> List (ErrLocWithSuffix nq)
  | [] => []
  | .gate _ :: rest => errLocsWithSuffix rest
  | .errLoc q :: rest => ⟨q, eraseFaults rest⟩ :: errLocsWithSuffix rest

/-- Error location plus the deterministic suffix and the detector cursor at
that point in the fault-free circuit.  The cursor is needed for
time-resolved detector obligations: the same physical syndrome qubit may be
measured many times, but each measurement writes a fresh detector slot. -/
structure ErrLocWithContext (nq : Nat) where
  q : Fin nq
  suffix : Circuit nq
  detectorStart : Nat

def ErrLocWithContext.toSuffix {nq : Nat} (site : ErrLocWithContext nq) :
    ErrLocWithSuffix nq :=
  ⟨site.q, site.suffix⟩

def gateDetectorAdvance {nq : Nat} : Gate nq -> Nat
  | .measZ _ => 1
  | _ => 0

def instrDetectorAdvance {nq : Nat} : FInstr nq -> Nat
  | .gate g => gateDetectorAdvance g
  | .errLoc _ => 0

def errLocsWithContextAux {nq : Nat} (cursor : Nat) :
    FCircuit nq -> List (ErrLocWithContext nq)
  | [] => []
  | .gate g :: rest => errLocsWithContextAux (cursor + gateDetectorAdvance g) rest
  | .errLoc q :: rest => ⟨q, eraseFaults rest, cursor⟩ :: errLocsWithContextAux cursor rest

/-- Concrete error sites annotated with the detector cursor at that site. -/
def errLocsWithContext {nq : Nat} (C : FCircuit nq) : List (ErrLocWithContext nq) :=
  errLocsWithContextAux 0 C

theorem toSuffix_mem_errLocsWithSuffix_of_contextAux_mem {nq : Nat} :
    ∀ (C : FCircuit nq) (cursor : Nat) (site : ErrLocWithContext nq),
      site ∈ errLocsWithContextAux cursor C ->
        site.toSuffix ∈ errLocsWithSuffix C
  | [], _, _, h => by cases h
  | .gate g :: rest, cursor, site, h => by
      exact toSuffix_mem_errLocsWithSuffix_of_contextAux_mem rest
        (cursor + gateDetectorAdvance g) site h
  | .errLoc q :: rest, cursor, site, h => by
      simp [errLocsWithContextAux, errLocsWithSuffix] at h ⊢
      rcases h with h | h
      · left
        cases h
        rfl
      · right
        exact toSuffix_mem_errLocsWithSuffix_of_contextAux_mem rest cursor site h

theorem toSuffix_mem_errLocsWithSuffix_of_context_mem {nq : Nat}
    {C : FCircuit nq} {site : ErrLocWithContext nq}
    (h : site ∈ errLocsWithContext C) :
    site.toSuffix ∈ errLocsWithSuffix C :=
  toSuffix_mem_errLocsWithSuffix_of_contextAux_mem C 0 site h

def cleanAtDetector {nq : Nat} (cursor : Nat) : ErrorState nq :=
  { ErrorState.clean nq with detectorCursor := cursor }

/-- The policy-visible detector bits differ: either a stabilizer syndrome
bit differs, or a post-selection flag slot differs.  This intentionally uses
the same XOR combiner as `undetected`; raw slots that cancel inside one
stabilizer do not count as a fired policy detector. -/
def detectorObservableDiff {nq : Nat} (spec : CodeSpec nq)
    (a b : ErrorState nq) : Prop :=
  (∃ i : Fin spec.numStab, syndromeBit spec a i ≠ syndromeBit spec b i) ∨
  (∃ f : Fin spec.numFlags,
    spec.postselectFlag f = true ∧
      a.detectors (spec.flagSlot f) ≠ b.detectors (spec.flagSlot f))

instance instDecidableDetectorObservableDiff {nq : Nat} (spec : CodeSpec nq)
    (a b : ErrorState nq) : Decidable (detectorObservableDiff spec a b) := by
  unfold detectorObservableDiff
  infer_instance

/-- A single injected branch changes at least one detector/flag bit that the
post-selected policy actually observes, compared with the fault-free suffix
from the same detector cursor. -/
def FiresDetector {nq : Nat} (_C : FCircuit nq) (spec : CodeSpec nq)
    (site : ErrLocWithContext nq) (p : Pauli) : Prop :=
  detectorObservableDiff spec
    (propagateCircuit site.suffix (cleanAtDetector site.detectorStart))
    (propagateCircuit site.suffix
      ((cleanAtDetector site.detectorStart).inject site.q p))

instance instDecidableFiresDetector {nq : Nat} (C : FCircuit nq)
    (spec : CodeSpec nq) (site : ErrLocWithContext nq) (p : Pauli) :
    Decidable (FiresDetector C spec site p) := by
  unfold FiresDetector
  infer_instance

/-- The generated local hook VC for a numeric barrier. -/
def SiteSafeβ {nq : Nat} (β : ErrorState nq -> Nat) (site : ErrLocWithSuffix nq) : Prop :=
  ∀ es p, p ≠ Pauli.I ->
    β (propagateCircuit site.suffix (es.inject site.q p)) ≤
      β (propagateCircuit site.suffix es) + 1

abbrev SiteSafeBeta {nq : Nat} (β : ErrorState nq -> Nat) (site : ErrLocWithSuffix nq) :
    Prop :=
  SiteSafeβ β site

noncomputable instance instDecidableSiteSafeβ {nq : Nat}
    (β : ErrorState nq -> Nat) (site : ErrLocWithSuffix nq) :
    Decidable (SiteSafeβ β site) :=
  Classical.propDecidable _

/-- One Pauli branch is benign for the numeric barrier. -/
def BranchSafeβ {nq : Nat} (β : ErrorState nq -> Nat)
    (site : ErrLocWithSuffix nq) (p : Pauli) : Prop :=
  ∀ es,
    β (propagateCircuit site.suffix (es.inject site.q p)) ≤
      β (propagateCircuit site.suffix es) + 1

noncomputable instance instDecidableBranchSafeβ {nq : Nat}
    (β : ErrorState nq -> Nat) (site : ErrLocWithSuffix nq) (p : Pauli) :
    Decidable (BranchSafeβ β site p) :=
  Classical.propDecidable _

theorem branchSafe_of_siteSafe {nq : Nat} {β : ErrorState nq -> Nat}
    {site : ErrLocWithSuffix nq} {p : Pauli}
    (h : SiteSafeβ β site) (hp : p ≠ Pauli.I) :
    BranchSafeβ β site p := by
  intro es
  exact h es p hp

/-- No single-location branch is both barrier-dangerous and invisible to the
policy detectors.  This is a first-class QClifford VC, computed from the
real deterministic suffix and detector log.  It is not by itself sufficient
for Shor/Flag soundness: detector-cancelling groups still require a separate
cancellation-benign theorem. -/
def NoUndetectedHook {nq : Nat} (C : FCircuit nq) (spec : CodeSpec nq)
    (β : ErrorState nq -> Nat) : Prop :=
  ∀ site, site ∈ errLocsWithContext C -> ∀ p, p ≠ Pauli.I ->
    BranchSafeβ β site.toSuffix p ∨ FiresDetector C spec site p

noncomputable instance instDecidableNoUndetectedHook {nq : Nat}
    (C : FCircuit nq) (spec : CodeSpec nq) (β : ErrorState nq -> Nat) :
    Decidable (NoUndetectedHook C spec β) :=
  Classical.propDecidable _

/-- Cheap discharge path for detection-free clients: if every concrete branch
is already benign for the barrier, `NoUndetectedHook` holds by the first
disjunct and never evaluates detector propagation. -/
theorem noUndetectedHook_of_allBranchSafe {nq : Nat} {C : FCircuit nq}
    {spec : CodeSpec nq} {β : ErrorState nq -> Nat}
    (hSafe : ∀ site, site ∈ errLocsWithContext C -> ∀ p, p ≠ Pauli.I ->
      BranchSafeβ β site.toSuffix p) :
    NoUndetectedHook C spec β := by
  intro site hmem p hp
  exact Or.inl (hSafe site hmem p hp)

theorem noUndetectedHook_of_siteSafe {nq : Nat} {C : FCircuit nq}
    {spec : CodeSpec nq} {β : ErrorState nq -> Nat}
    (hStep : ∀ site, site ∈ errLocsWithSuffix C -> SiteSafeβ β site) :
    NoUndetectedHook C spec β := by
  apply noUndetectedHook_of_allBranchSafe
  intro site hmem p hp
  exact branchSafe_of_siteSafe
    (hStep site.toSuffix (toSuffix_mem_errLocsWithSuffix_of_context_mem hmem)) hp

def frontier {nq : Nat} (β : ErrorState nq -> Nat) (suffix : Circuit nq) :
    AssertionF nq :=
  fun σ => β (propagateCircuit suffix σ.es) ≤ σ.lambda

theorem frontier_errLoc_pre {nq : Nat} {β : ErrorState nq -> Nat}
    {q : Fin nq} {suffix : Circuit nq}
    (hSafe : SiteSafeβ β ⟨q, suffix⟩) :
    ∀ σ, frontier β suffix σ ->
      frontier β suffix σ ∧
        ∀ p, p ≠ Pauli.I -> frontier β suffix ⟨σ.es.inject q p, σ.lambda + 1⟩ := by
  intro σ hFront
  refine ⟨hFront, ?_⟩
  intro p hp
  unfold frontier at hFront ⊢
  have hStep :
      β (propagateCircuit suffix (σ.es.inject q p)) ≤
        β (propagateCircuit suffix σ.es) + 1 := by
    simpa [SiteSafeβ] using hSafe σ.es p hp
  exact le_trans hStep (Nat.add_le_add_right hFront 1)

def errLocDeriv {nq : Nat} (β : ErrorState nq -> Nat)
    (q : Fin nq) (suffix : Circuit nq) (hSafe : SiteSafeβ β ⟨q, suffix⟩) :
    FDeriv (frontier β suffix) [.errLoc q] (frontier β suffix) :=
  FDeriv.F_Conseq (FDeriv.F_ErrLoc q (frontier β suffix))
    (frontier_errLoc_pre hSafe) (fun _ h => h)

def frontierDeriv {nq : Nat} (β : ErrorState nq -> Nat) :
    ∀ (fc : FCircuit nq),
      (∀ site, site ∈ errLocsWithSuffix fc -> SiteSafeβ β site) ->
      FDeriv (frontier β (eraseFaults fc)) fc (frontier β [])
  | [], _ => FDeriv.F_Nil (frontier β [])
  | .gate g :: rest, hStep =>
      FDeriv.F_App (FDeriv.F_Gate g (frontier β (eraseFaults rest)))
        (frontierDeriv β rest (fun site hmem => hStep site (by simpa [errLocsWithSuffix] using hmem)))
  | .errLoc q :: rest, hStep =>
      FDeriv.F_App
        (errLocDeriv β q (eraseFaults rest)
          (hStep ⟨q, eraseFaults rest⟩ (by simp [errLocsWithSuffix])))
        (frontierDeriv β rest (fun site hmem =>
          hStep site (by simp [errLocsWithSuffix, hmem])))

def gadgetFrontierDeriv {nq : Nat} (β : ErrorState nq -> Nat)
    (fc : FCircuit nq)
    (hStep : ∀ site, site ∈ errLocsWithSuffix fc -> SiteSafeβ β site)
    (hPreserve : ∀ es, β (propagateCircuit (eraseFaults fc) es) = β es) :
    FDeriv (frontier β []) fc (frontier β []) :=
  FDeriv.F_Conseq (frontierDeriv β fc hStep)
    (fun σ hFront => by
      unfold frontier at hFront ⊢
      simpa [propagateCircuit, hPreserve σ.es] using hFront)
    (fun _ h => h)

def gadgetListFrontierDeriv {nq : Nat} {spec : CodeSpec nq}
    (β : ErrorState nq -> Nat) :
    ∀ (idxs : List (Fin spec.numStab)),
      (∀ i, i ∈ idxs -> ∀ site,
        site ∈ errLocsWithSuffix (spec.gadget i) -> SiteSafeβ β site) ->
      (∀ i, i ∈ idxs -> ∀ es,
        β (propagateCircuit (eraseFaults (spec.gadget i)) es) = β es) ->
      FDeriv (frontier β []) (idxs.flatMap fun i => spec.gadget i) (frontier β [])
  | [], _, _ => FDeriv.F_Nil (frontier β [])
  | i :: rest, hStep, hPreserve =>
      FDeriv.F_App
        (gadgetFrontierDeriv β (spec.gadget i)
          (hStep i (by simp))
          (hPreserve i (by simp)))
        (gadgetListFrontierDeriv β rest
          (fun j hj site hsite => hStep j (by simp [hj]) site hsite)
          (fun j hj es => hPreserve j (by simp [hj]) es))

def cleanPre {nq : Nat} : AssertionF nq := fun σ => σ = QCState.clean nq

def distPost {nq : Nat} (spec : CodeSpec nq) : AssertionF nq :=
  fun σ => σ.lambda ≤ spec.d - 1 -> ¬ failure spec σ.es

def runFScript {nq : Nat} : FCircuit nq -> List (Option Pauli) -> ErrorState nq ->
    ErrorState nq × Nat
  | [], _, es => (es, 0)
  | .gate g :: rest, script, es => runFScript rest script (propagateGate g es)
  | .errLoc _ :: rest, [], es => runFScript rest [] es
  | .errLoc _ :: rest, none :: script, es => runFScript rest script es
  | .errLoc q :: rest, some p :: script, es =>
      if p = Pauli.I then
        runFScript rest script es
      else
        let out := runFScript rest script (es.inject q p)
        (out.1, out.2 + 1)

theorem runFScript_sound {nq : Nat} :
    ∀ (fc : FCircuit nq) (script : List (Option Pauli)) (es : ErrorState nq),
      fcevalW (runFScript fc script es).2 fc es (runFScript fc script es).1 := by
  intro fc
  induction fc with
  | nil =>
      intro script es
      simp [runFScript, fcevalW.nil]
  | cons i rest ih =>
      intro script es
      cases i with
      | gate g =>
          exact fcevalW.gate g rest es (runFScript rest script (propagateGate g es)).1
            (runFScript rest script (propagateGate g es)).2
            (ih script (propagateGate g es))
      | errLoc q =>
          cases script with
          | nil =>
              exact fcevalW.idle q rest es (runFScript rest [] es).1
                (runFScript rest [] es).2 (ih [] es)
          | cons step script =>
              cases step with
              | none =>
                  exact fcevalW.idle q rest es (runFScript rest script es).1
                    (runFScript rest script es).2 (ih script es)
              | some p =>
                  by_cases hpI : p = Pauli.I
                  · simp [runFScript, hpI]
                    exact fcevalW.idle q rest es (runFScript rest script es).1
                      (runFScript rest script es).2 (ih script es)
                  · simp [runFScript, hpI]
                    exact fcevalW.inject q rest es
                      (runFScript rest script (es.inject q p)).1 p hpI
                      (runFScript rest script (es.inject q p)).2
                      (ih script (es.inject q p))

/-- A complete PCC distance certificate.  The compiler supplies data and
proofs for these fields; the statement of every VC is generated here from
`C`, `spec`, and the chosen `barrier`. -/
structure DistanceCertificate {nq : Nat} (C : FCircuit nq) (spec : CodeSpec nq) where
  barrier : ErrorState nq -> Nat
  programEq : C = specCircuit spec
  wf : WellFormed C spec
  syn : ∀ i E, gadgetMeasFlip C spec i E = parity spec (spec.stabilizer i) E
  init : barrier (ErrorState.clean nq) = 0
  step : ∀ i, ∀ site, site ∈ errLocsWithSuffix (spec.gadget i) -> SiteSafeβ barrier site
  noUndetectedHook : ∀ i, NoUndetectedHook (spec.gadget i) spec barrier :=
    fun i => noUndetectedHook_of_siteSafe (step i)
  preserve : ∀ i, ∀ es, barrier (propagateCircuit (eraseFaults (spec.gadget i)) es) = barrier es
  dist : ∀ es, logicalFailure spec es -> spec.d ≤ barrier es
  reachScript : List (Option Pauli)
  reachOk :
    (runFScript C reachScript (ErrorState.clean nq)).2 = spec.d ∧
      failure spec (runFScript C reachScript (ErrorState.clean nq)).1

/-- The fixed safety policy produced from a valid certificate. -/
def Safe {nq : Nat} (C : FCircuit nq) (spec : CodeSpec nq) : Prop :=
  WellFormed C spec ∧
  (∀ i j, i ≠ j -> ∀ s, s ∈ spec.stabilizerReadout i ->
    s ∈ spec.stabilizerReadout j -> False) ∧
  (∀ i E, gadgetMeasFlip C spec i E = parity spec (spec.stabilizer i) E) ∧
  ToleratesFaultsΛ C (failure spec) (spec.d - 1) ∧
  (∃ es, fcevalW spec.d C (ErrorState.clean nq) es ∧ failure spec es)

def certificateDeriv {nq : Nat} {C : FCircuit nq} {spec : CodeSpec nq}
    (cert : DistanceCertificate C spec) :
    FDeriv cleanPre C (distPost spec) := by
  rw [cert.programEq]
  exact FDeriv.F_Conseq
    (gadgetListFrontierDeriv cert.barrier (List.finRange spec.numStab)
      (fun i _ => cert.step i)
      (fun i _ => cert.preserve i))
    (fun σ hClean => by
      subst hClean
      unfold frontier
      simpa [QCState.clean, propagateCircuit] using cert.init
    )
    (fun σ hFront hBudget hFail => by
      unfold frontier at hFront
      simp [propagateCircuit] at hFront
      have hDist := cert.dist σ.es hFail.1
      have hLe : spec.d ≤ σ.lambda := le_trans hDist hFront
      have hPos := spec.d_pos
      omega)

theorem certificate_hoare {nq : Nat} {C : FCircuit nq} {spec : CodeSpec nq}
    (cert : DistanceCertificate C spec) :
    FHoare cleanPre C (distPost spec) :=
  fhoare_sound (certificateDeriv cert)

theorem certificate_tolerates {nq : Nat} {C : FCircuit nq} {spec : CodeSpec nq}
    (cert : DistanceCertificate C spec) :
    ToleratesFaultsΛ C (failure spec) (spec.d - 1) :=
  toleratesFaultsΛ_of_hoare C (failure spec) (spec.d - 1)
    (certificate_hoare cert)

theorem certificate_reaches {nq : Nat} {C : FCircuit nq} {spec : CodeSpec nq}
    (cert : DistanceCertificate C spec) :
    ∃ es, fcevalW spec.d C (ErrorState.clean nq) es ∧ failure spec es := by
  let out := runFScript C cert.reachScript (ErrorState.clean nq)
  refine ⟨out.1, ?_, ?_⟩
  · have h := runFScript_sound C cert.reachScript (ErrorState.clean nq)
    simpa [out, cert.reachOk.1] using h
  · simpa [out] using cert.reachOk.2

theorem certificate_noUndetectedHook {nq : Nat} {C : FCircuit nq} {spec : CodeSpec nq}
    (cert : DistanceCertificate C spec) :
    ∀ i, NoUndetectedHook (spec.gadget i) spec cert.barrier :=
  cert.noUndetectedHook

theorem certificate_sound {nq : Nat} {C : FCircuit nq} {spec : CodeSpec nq}
    (cert : DistanceCertificate C spec) :
    Safe C spec :=
  ⟨cert.wf, spec.readout_disjoint, cert.syn, certificate_tolerates cert,
    certificate_reaches cert⟩

/-- Run-level post-selected barrier bound.

This is the explicit cancellation/grouping obligation for post-selected
schemes such as Shor and Flag.  A producer must prove that every accepted run
(`allFlagsZero`) has final barrier at most the number of injected faults.  For
Shor this is where detector-cancelling dangerous hooks must be grouped and
shown benign modulo the measured stabilizer. -/
def AcceptedBarrierBound {nq : Nat} (C : FCircuit nq) (spec : CodeSpec nq)
    (β : ErrorState nq -> Nat) : Prop :=
  ∀ {w : Nat} {es : ErrorState nq},
    fcevalW w C (ErrorState.clean nq) es -> allFlagsZero spec es -> β es ≤ w

/-- The cancellation field is phrased as a consequence of `NoUndetectedHook`:
single-fault detector completeness plus scheme-specific cancellation algebra
must imply the accepted-run barrier bound.  The generic verifier merely checks
and applies this proof; it does not search for the grouping itself. -/
def CancellationBenign {nq : Nat} (C : FCircuit nq) (spec : CodeSpec nq)
    (β : ErrorState nq -> Nat) : Prop :=
  (∀ i, NoUndetectedHook (spec.gadget i) spec β) -> AcceptedBarrierBound C spec β

/-- Detection-conditioned PCC certificate.  Compared with
`DistanceCertificate`, the Hoare/local unconditional `step` is replaced by a
global, proof-carrying cancellation obligation.  This is intentionally strong:
a scheme with detector-cancelling hooks that form a low-weight logical cannot
fill `cancellation`. -/
structure DistanceCertificate' {nq : Nat} (C : FCircuit nq) (spec : CodeSpec nq) where
  barrier : ErrorState nq -> Nat
  programEq : C = specCircuit spec
  wf : WellFormed C spec
  syn : ∀ i E, gadgetMeasFlip C spec i E = parity spec (spec.stabilizer i) E
  noUndetectedHook : ∀ i, NoUndetectedHook (spec.gadget i) spec barrier
  cancellation : CancellationBenign C spec barrier
  dist : ∀ es, logicalFailure spec es -> spec.d ≤ barrier es
  reachScript : List (Option Pauli)
  reachOk :
    (runFScript C reachScript (ErrorState.clean nq)).2 = spec.d ∧
      failure spec (runFScript C reachScript (ErrorState.clean nq)).1

theorem certificate'_accepted_bound {nq : Nat} {C : FCircuit nq} {spec : CodeSpec nq}
    (cert : DistanceCertificate' C spec) :
    AcceptedBarrierBound C spec cert.barrier :=
  cert.cancellation cert.noUndetectedHook

theorem certificate'_tolerates {nq : Nat} {C : FCircuit nq} {spec : CodeSpec nq}
    (cert : DistanceCertificate' C spec) :
    ToleratesFaultsΛ C (failure spec) (spec.d - 1) := by
  intro σ' hRun hBudget hFail
  obtain ⟨hLogical, hAccepted⟩ := hFail
  have hDist : spec.d ≤ cert.barrier σ'.es := cert.dist σ'.es hLogical
  obtain ⟨_, hCountRun0⟩ := fcevalW_of_qceval hRun
  have hCountRun : fcevalW σ'.lambda C (ErrorState.clean nq) σ'.es := by
    simpa [QCState.clean] using hCountRun0
  have hBarrier : cert.barrier σ'.es ≤ σ'.lambda := by
    exact certificate'_accepted_bound cert hCountRun hAccepted
  have hLe : spec.d ≤ σ'.lambda := le_trans hDist hBarrier
  have hPos := spec.d_pos
  omega

theorem certificate'_reaches {nq : Nat} {C : FCircuit nq} {spec : CodeSpec nq}
    (cert : DistanceCertificate' C spec) :
    ∃ es, fcevalW spec.d C (ErrorState.clean nq) es ∧ failure spec es := by
  let out := runFScript C cert.reachScript (ErrorState.clean nq)
  refine ⟨out.1, ?_, ?_⟩
  · have h := runFScript_sound C cert.reachScript (ErrorState.clean nq)
    simpa [out, cert.reachOk.1] using h
  · simpa [out] using cert.reachOk.2

theorem certificate_sound' {nq : Nat} {C : FCircuit nq} {spec : CodeSpec nq}
    (cert : DistanceCertificate' C spec) :
    Safe C spec :=
  ⟨cert.wf, spec.readout_disjoint, cert.syn, certificate'_tolerates cert,
    certificate'_reaches cert⟩

#print axioms certificate_sound
#print axioms certificate_sound'
#print axioms combinerPairFlip_syndrome_zero
#print axioms combinerSingleFlip_syndrome_one

end QStab.QClifford.PCC
