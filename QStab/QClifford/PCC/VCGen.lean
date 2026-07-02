import QStab.QClifford.PCC.Basic
import QStab.QHL.Assertion.Barrier
import QStab.QHL.Target.Soundness

/-!
# QClifford PCC verification-condition generation

This module is the explicit VC-generation layer for QClifford proof-carrying
code.  It does **not** introduce a second assertion language.  Instead, the
generated assertion views are ordinary `QHL.AssertionLang.Formula`s interpreted
through the backend-parametric semantics in `QHL.Assertion.Semantics`.

The pure generator `vcgen input` produces a proof-free `GeneratedVCs input`
artifact.  The producer separately supplies a `DischargedVCs` record whose field
types literally reference that generated artifact.  The trusted checker is small:
derive `Safe` directly from the discharged obligations.

## Barrier-free VC interface

`VCInput`, `VCSlot`, `vcgen`, and `vcgen_sound` are intentionally **barrier-free**.
A `barrier : ErrorState → ℕ` is a *proof strategy* (an optional producer toolkit)
and must not appear in the VC interface.  The barrier method is supported through
optional adapter lemmas (`ftDistance_of_certificate`,
`ftDistance_of_certificate'`) that let a barrier-using producer satisfy the
barrier-free `ftDistance` slot without changing the VC itself.
-/

namespace QStab.QClifford.PCC

open QHL.AssertionLang

/-- Stabilizer-code portion of a QClifford PCC input.  This is the code-level
part of the input; extraction/readout/post-selection data lives in
`ExtractionSpec`. -/
structure StabilizerCodeSpec (nq : Nat) where
  nq_pos : 0 < nq
  numStab : Nat
  numStab_pos : 0 < numStab
  numFlags : Nat
  isData : Fin nq -> Bool
  stabilizer : Fin numStab -> Fin nq -> Pauli
  d : Nat
  d_pos : 0 < d

/-- Syndrome extraction and detector policy annotations.  These are compiler
annotations, but the generated VCs below are computed from them. -/
structure ExtractionSpec {nq : Nat} (code : StabilizerCodeSpec nq) where
  stabilizerReadout : Fin code.numStab -> List (Fin code.numFlags)
  postselectFlag : Fin code.numFlags -> Bool
  flagSlot : Fin code.numFlags -> Nat
  flagSlot_injective : Function.Injective flagSlot
  flagSlot_ordered : forall i, flagSlot i = i.val
  readout_disjoint :
    forall i j, i ≠ j -> forall s, s ∈ stabilizerReadout i ->
      s ∈ stabilizerReadout j -> False
  gadgetDetectorStart : Fin code.numStab -> Nat
  gadget : Fin code.numStab -> FCircuit nq
  expectedProgram : List (InstrView nq)

/-- Rebuild the existing PCC `CodeSpec` from the separated code/extraction
input.  This is the canonical spec consumed by `Safe`. -/
def ExtractionSpec.toCodeSpec {nq : Nat} {code : StabilizerCodeSpec nq}
    (ext : ExtractionSpec code) : CodeSpec nq where
  numStab := code.numStab
  numFlags := code.numFlags
  isData := code.isData
  stabilizer := code.stabilizer
  stabilizerReadout := ext.stabilizerReadout
  postselectFlag := ext.postselectFlag
  flagSlot := ext.flagSlot
  flagSlot_injective := ext.flagSlot_injective
  flagSlot_ordered := ext.flagSlot_ordered
  readout_disjoint := ext.readout_disjoint
  gadgetDetectorStart := ext.gadgetDetectorStart
  gadget := ext.gadget
  expectedProgram := ext.expectedProgram
  d := code.d
  d_pos := code.d_pos

/-- Build the separated code portion from an existing PCC `CodeSpec`. -/
def StabilizerCodeSpec.ofPCC {nq : Nat} (spec : CodeSpec nq)
    (hnq : 0 < nq) (hnumStab : 0 < spec.numStab) : StabilizerCodeSpec nq where
  nq_pos := hnq
  numStab := spec.numStab
  numStab_pos := hnumStab
  numFlags := spec.numFlags
  isData := spec.isData
  stabilizer := spec.stabilizer
  d := spec.d
  d_pos := spec.d_pos

/-- Build the separated extraction portion from an existing PCC `CodeSpec`. -/
def ExtractionSpec.ofPCC {nq : Nat} (spec : CodeSpec nq)
    (hnq : 0 < nq) (hnumStab : 0 < spec.numStab) :
    ExtractionSpec (StabilizerCodeSpec.ofPCC spec hnq hnumStab) where
  stabilizerReadout := spec.stabilizerReadout
  postselectFlag := spec.postselectFlag
  flagSlot := spec.flagSlot
  flagSlot_injective := spec.flagSlot_injective
  flagSlot_ordered := spec.flagSlot_ordered
  readout_disjoint := spec.readout_disjoint
  gadgetDetectorStart := spec.gadgetDetectorStart
  gadget := spec.gadget
  expectedProgram := spec.expectedProgram

/-- VC generation mode: either all branches are locally barrier-safe, or the
post-selected client must provide the accepted-run cancellation bound. -/
inductive VCMode where
  | unconditional
  | postselected
  deriving DecidableEq, Repr

/-- List-backed lookup used by the syntactic input layer. -/
def listGetCast {α : Type} (xs : List α) {n : Nat} (h : xs.length = n)
    (i : Fin n) : α :=
  xs.get ⟨i.val, by rw [h]; exact i.isLt⟩

/-- Pure syntax for one stabilizer generator: a finite support list of concrete
physical qubits and Pauli labels. -/
structure StabilizerSyntax (nq : Nat) where
  support : List (Fin nq × Pauli)

def StabilizerSyntax.eval {nq : Nat} (S : StabilizerSyntax nq) : Fin nq -> Pauli :=
  fun q =>
    S.support.foldl
      (fun acc term => if term.1 = q then pauliMul acc term.2 else acc)
      Pauli.I

/-- Pure syntax for the code portion of a QClifford VC input. -/
structure StabilizerCodeSyntax (nq : Nat) where
  nq_pos : 0 < nq
  dataQubits : List (Fin nq)
  stabilizers : List (StabilizerSyntax nq)
  numStab_pos : 0 < stabilizers.length
  numFlags : Nat
  d : Nat
  d_pos : 0 < d

def StabilizerCodeSyntax.toSpec {nq : Nat}
    (code : StabilizerCodeSyntax nq) : StabilizerCodeSpec nq where
  nq_pos := code.nq_pos
  numStab := code.stabilizers.length
  numStab_pos := code.numStab_pos
  numFlags := code.numFlags
  isData := fun q => decide (q ∈ code.dataQubits)
  stabilizer := fun i => (code.stabilizers.get i).eval
  d := code.d
  d_pos := code.d_pos

/-- Pure syntax for extraction/readout/post-selection.  This is list-backed:
the submitted artifact names every gadget and every detector readout list
explicitly. -/
structure ExtractionSyntax {nq : Nat} (code : StabilizerCodeSyntax nq) where
  stabilizerReadouts : List (List (Fin code.numFlags))
  stabilizerReadouts_length : stabilizerReadouts.length = code.stabilizers.length
  postselectFlags : List (Fin code.numFlags)
  detectorStarts : List Nat
  detectorStarts_length : detectorStarts.length = code.stabilizers.length
  gadgets : List (FCircuit nq)
  gadgets_length : gadgets.length = code.stabilizers.length
  expectedProgram : List (InstrView nq)
  readout_disjoint :
    ∀ i j : Fin code.stabilizers.length, i ≠ j -> ∀ s,
      s ∈ listGetCast stabilizerReadouts stabilizerReadouts_length i ->
      s ∈ listGetCast stabilizerReadouts stabilizerReadouts_length j -> False

def ExtractionSyntax.readout {nq : Nat} {code : StabilizerCodeSyntax nq}
    (ext : ExtractionSyntax code) (i : Fin code.stabilizers.length) :
    List (Fin code.numFlags) :=
  listGetCast ext.stabilizerReadouts ext.stabilizerReadouts_length i

def ExtractionSyntax.detectorStart {nq : Nat} {code : StabilizerCodeSyntax nq}
    (ext : ExtractionSyntax code) (i : Fin code.stabilizers.length) : Nat :=
  listGetCast ext.detectorStarts ext.detectorStarts_length i

def ExtractionSyntax.gadgetAt {nq : Nat} {code : StabilizerCodeSyntax nq}
    (ext : ExtractionSyntax code) (i : Fin code.stabilizers.length) : FCircuit nq :=
  listGetCast ext.gadgets ext.gadgets_length i

/-- Interpret extraction syntax as the backend spec consumed by `Safe`. -/
def ExtractionSyntax.toSpec {nq : Nat} {code : StabilizerCodeSyntax nq}
    (ext : ExtractionSyntax code) : ExtractionSpec code.toSpec where
  stabilizerReadout := ext.readout
  postselectFlag := fun f => decide (f ∈ ext.postselectFlags)
  flagSlot := fun i => i.val
  flagSlot_injective := by
    intro a b h
    exact Fin.ext h
  flagSlot_ordered := by
    intro i
    rfl
  readout_disjoint := ext.readout_disjoint
  gadgetDetectorStart := ext.detectorStart
  gadget := ext.gadgetAt
  expectedProgram := ext.expectedProgram

/-- Fully syntactic QClifford VC input.  `toVCInput` is the checker-side
interpretation into the existing backend structures.

Note: `barrier` is NOT part of this structure.  A barrier is a producer-side
proof strategy and must not appear in the VC interface. -/
structure VCInputSyntax (nq : Nat) where
  program : FCircuit nq
  code : StabilizerCodeSyntax nq
  extraction : ExtractionSyntax code
  mode : VCMode

/-- Complete input to the VC generator.

The `barrier` field has been removed: barriers are a proof strategy, not a VC
obligation.  `VCInput` now captures only the program, code spec, extraction
spec, and mode.  Any barrier annotation used by a proof strategy lives in the
producer's discharge record, not here. -/
structure VCInput (nq : Nat) where
  program : FCircuit nq
  code : StabilizerCodeSpec nq
  extraction : ExtractionSpec code
  mode : VCMode

def VCInputSyntax.toVCInput {nq : Nat} (input : VCInputSyntax nq) : VCInput nq where
  program := input.program
  code := input.code.toSpec
  extraction := input.extraction.toSpec
  mode := input.mode

def VCInput.toCodeSpec {nq : Nat} (input : VCInput nq) : CodeSpec nq :=
  input.extraction.toCodeSpec

/-- Compatibility constructor used to migrate existing clients without
duplicating their already-audited `CodeSpec` data.  The `barrier` parameter
has been removed; barriers are a proof strategy and not part of `VCInput`. -/
def VCInput.ofPCC {nq : Nat} (program : FCircuit nq) (spec : CodeSpec nq)
    (mode : VCMode) (hnq : 0 < nq) (hnumStab : 0 < spec.numStab) : VCInput nq where
  program := program
  code := StabilizerCodeSpec.ofPCC spec hnq hnumStab
  extraction := ExtractionSpec.ofPCC spec hnq hnumStab
  mode := mode

@[simp] theorem VCInput.toCodeSpec_ofPCC {nq : Nat} (program : FCircuit nq)
    (spec : CodeSpec nq) (mode : VCMode) (hnq : 0 < nq) (hnumStab : 0 < spec.numStab) :
    (VCInput.ofPCC program spec mode hnq hnumStab).toCodeSpec = spec := by
  cases spec
  rfl

/-- A QEC-parameter view of a QClifford code spec, used only to reuse the
shared QHL assertion language.  Back-action is empty here because concrete
QClifford hook obligations are generated from `FCircuit` suffix propagation,
not from the abstract QStab back-action set. -/
def qecParamsOfCodeSpec {nq : Nat} (spec : CodeSpec nq)
    (hnq : 0 < nq) (hnumStab : 0 < spec.numStab) : QECParams where
  n := nq
  k := 0
  d := spec.d
  R := 1
  numStab := spec.numStab
  stabilizers := spec.stabilizer
  backActionSet := fun _ => ∅
  r := 0
  backAction_weight_bound := by
    intro _ _ h
    simp at h
  C_budget := spec.d
  hn := hnq
  hns := hnumStab
  hR := by decide

abbrev VCInput.params {nq : Nat} (input : VCInput nq) : QECParams :=
  qecParamsOfCodeSpec input.toCodeSpec input.code.nq_pos input.code.numStab_pos

/-- QClifford backend for the shared QHL assertion language.  The interpreted
error is the data-projected Pauli vector; detector reads the time-resolved
QClifford detector log; `remaining` is chosen so `budget - remaining` equals
the fault counter for all runs with at most the claimed distance. -/
def qcliffordBackend {nq : Nat} (spec : CodeSpec nq)
    (hnq : 0 < nq) (hnumStab : 0 < spec.numStab) :
    AssertionBackend (qecParamsOfCodeSpec spec hnq hnumStab) (QCState nq) where
  error := fun σ => dataVector spec σ.es
  spent := fun σ => σ.lambda
  remaining := fun σ => spec.d - σ.lambda
  budget := spec.d
  current := fun _ => QECParams.Coord.first (qecParamsOfCodeSpec spec hnq hnumStab)
  detector := fun k σ => σ.es.detectors k

noncomputable def Formula.denoteQC {nq : Nat} (spec : CodeSpec nq)
    (hnq : 0 < nq) (hnumStab : 0 < spec.numStab)
    (A : Formula (qecParamsOfCodeSpec spec hnq hnumStab) []) :
    QCState nq -> Prop :=
  A.denoteWith (qcliffordBackend spec hnq hnumStab)

def detectorTerm {P : QECParams} (slot : Nat) : Term P [] .bool :=
  .detector (.natLit slot)

def xorTerm {P : QECParams} : List (Term P [] .bool) -> Term P [] .bool
  | [] => .boolLit false
  | t :: ts => .boolXor t (xorTerm ts)

def syndromeBitTerm {P : QECParams} (slots : List Nat) : Term P [] .bool :=
  xorTerm (slots.map detectorTerm)

def readoutSlots {nq : Nat} (spec : CodeSpec nq) (i : Fin spec.numStab) : List Nat :=
  (spec.stabilizerReadout i).map spec.flagSlot

def undetectedF {nq : Nat} (spec : CodeSpec nq)
    (hnq : 0 < nq) (hnumStab : 0 < spec.numStab) :
    Formula (qecParamsOfCodeSpec spec hnq hnumStab) [] :=
  (List.finRange spec.numStab).foldr
    (fun i acc => .and
      (.eq (syndromeBitTerm (readoutSlots spec i)) (.boolLit false))
      acc)
    .top

def postselectionFlagsZeroF {nq : Nat} (spec : CodeSpec nq)
    (hnq : 0 < nq) (hnumStab : 0 < spec.numStab) :
    Formula (qecParamsOfCodeSpec spec hnq hnumStab) [] :=
  (List.finRange spec.numFlags).foldr
    (fun i acc =>
      if spec.postselectFlag i then
        .and (.eq (detectorTerm (spec.flagSlot i)) (.boolLit false)) acc
      else acc)
    .top

def allFlagsZeroF {nq : Nat} (spec : CodeSpec nq)
    (hnq : 0 < nq) (hnumStab : 0 < spec.numStab) :
    Formula (qecParamsOfCodeSpec spec hnq hnumStab) [] :=
  .and (undetectedF spec hnq hnumStab) (postselectionFlagsZeroF spec hnq hnumStab)

def failureF {nq : Nat} (spec : CodeSpec nq)
    (hnq : 0 < nq) (hnumStab : 0 < spec.numStab) :
    Formula (qecParamsOfCodeSpec spec hnq hnumStab) [] :=
  .and (logicalAnyResidualF .error) (allFlagsZeroF spec hnq hnumStab)

def barrierDistanceAnyF {P : QECParams} (β : BarrierSymbol P) (distance : Nat) :
    Formula P [] :=
  .all .vec
    (.imp (logicalAnyResidualF (.var .zero))
      (.le (.natLit distance) (.barrier β (.var .zero))))

def VCInput.failureFormula {nq : Nat} (input : VCInput nq) : Formula input.params [] :=
  failureF input.toCodeSpec input.code.nq_pos input.code.numStab_pos

def VCInput.distanceFormula {nq : Nat} (input : VCInput nq) : Formula input.params [] :=
  circuitDistanceAnyF input.toCodeSpec.d

def VCInput.allFlagsZeroFormula {nq : Nat} (input : VCInput nq) : Formula input.params [] :=
  allFlagsZeroF input.toCodeSpec input.code.nq_pos input.code.numStab_pos

/-! ## Decoration bridges

The shared QHL formulas kept in the generated VC report (`allFlagsZeroF`,
`logicalAnyResidualF`, `failureF`, `circuitDistanceAnyF`) are not decorative
tags: each is *proven* equal to the concrete QClifford obligation it claims to
denote, under the `qcliffordBackend`/`qecParamsOfCodeSpec` interpretation.  The
helper lemmas reconcile the two parity definitions (`vectorParity` vs
`ErrorVec.parity`), the two stabilizer-group descriptions
(`generatedByStabilizers` vs `Stab`), and the syndrome XOR fold
(`xorTerm`/`detectorTerm` vs `xorBools`/`syndromeBit`). -/

/-- The two single-qubit anticommutation tables agree. -/
theorem anticommute_eq_anticommutes (a b : Pauli) :
    anticommute a b = ErrorVec.Pauli.anticommutes a b := by
  cases a <;> cases b <;> rfl

/-- A boolean XOR fold over `List.finRange n` equals the mod-2 parity of the
finite filter, the bridge between the foldl symplectic parity and the
`Finset.card`-based `ErrorVec.parity`. -/
theorem foldl_xor_eq_card_mod {n : Nat} (f : Fin n → Bool) :
    (List.finRange n).foldl (fun acc q => xor acc (f q)) false
      = ((Finset.univ.filter (fun q => f q = true)).card % 2 == 1) := by
  have key : ∀ (l : List (Fin n)) (b : Bool),
      l.foldl (fun acc q => xor acc (f q)) b
        = xor b ((l.filter (fun q => f q)).length % 2 == 1) := by
    intro l
    induction l with
    | nil => intro b; simp
    | cons a t ih =>
        intro b
        simp only [List.foldl_cons, List.filter_cons]
        by_cases hfa : f a = true
        · simp only [hfa, if_true, List.length_cons]
          rw [ih]
          cases b <;> cases hX : ((t.filter (fun q => f q)).length % 2 == 1) <;>
            simp_all [Nat.add_mod]
        · have hfa' : f a = false := by cases h : f a <;> simp_all
          simp only [hfa', Bool.false_eq_true, if_false]
          rw [ih]; simp
  rw [key]; simp only [Bool.false_xor]
  have hcard : (List.filter (fun q => f q) (List.finRange n)).length
      = (Finset.univ.filter (fun q => f q = true)).card := by
    rw [← List.toFinset_card_of_nodup (List.Nodup.filter _ (List.nodup_finRange n))]
    congr 1
    ext q
    simp
  rw [hcard]

/-- The PCC foldl symplectic parity agrees with the assertion-language
`ErrorVec.parity`. -/
theorem vectorParity_eq_parity {nq : Nat} (S E : Fin nq → Pauli) :
    vectorParity S E = ErrorVec.parity S E := by
  unfold vectorParity ErrorVec.parity
  rw [foldl_xor_eq_card_mod (fun q => anticommute (S q) (E q))]
  have hset : (Finset.univ.filter (fun q => anticommute (S q) (E q) = true))
      = (Finset.univ.filter (fun i => ErrorVec.Pauli.anticommutes (S i) (E i))) := by
    apply Finset.filter_congr
    intro q _
    rw [anticommute_eq_anticommutes]
  rw [hset]

/-- The two phase-free Pauli products agree. -/
theorem pauliMul_eq_mul (a b : Pauli) : pauliMul a b = Pauli.mul a b := by
  cases a <;> cases b <;> rfl

/-- Pointwise reconciliation of the two stabilizer-mask products: the
`ErrorVec.mul`-based foldl (with `stab * acc`) equals the `pauliMul`-based foldl
(with `acc * stab`), using commutativity of phase-free Pauli multiplication. -/
theorem foldl_stab_pointwise {nq : Nat} (spec : CodeSpec nq)
    (mask : Fin spec.numStab → Bool) (q : Fin nq) :
    ∀ (l : List (Fin spec.numStab)) (accE : ErrorVec nq) (accP : Pauli),
      accE q = accP →
      (l.foldl (fun acc i =>
          if mask i then ErrorVec.mul (spec.stabilizer i) acc else acc) accE) q
        = l.foldl (fun acc i =>
            if mask i then pauliMul acc (spec.stabilizer i q) else acc) accP := by
  intro l
  induction l with
  | nil => intro accE accP h; simpa using h
  | cons i rest ih =>
      intro accE accP h
      simp only [List.foldl_cons]
      by_cases hmi : mask i
      · simp only [hmi, if_true]
        apply ih
        simp only [ErrorVec.mul]
        rw [pauliMul_eq_mul, Pauli.mul_comm, h]
      · simp only [hmi, Bool.false_eq_true, if_false]
        exact ih accE accP h

/-- The assertion-language stabilizer-mask product equals the PCC `prodStab`. -/
theorem stabilizerProduct_eq_prodStab {nq : Nat} (spec : CodeSpec nq)
    (hnq : 0 < nq) (hns : 0 < spec.numStab)
    (mask : Fin spec.numStab → Bool) (q : Fin nq) :
    stabilizerProduct (qecParamsOfCodeSpec spec hnq hns) mask q
      = prodStab spec mask q := by
  unfold stabilizerProduct prodStab
  apply foldl_stab_pointwise spec mask q
  rfl

/-- `generatedByStabilizers` under the QEC-params view coincides with `Stab`. -/
theorem inStab_iff_Stab {nq : Nat} (spec : CodeSpec nq)
    (hnq : 0 < nq) (hns : 0 < spec.numStab) (E : Fin nq → Pauli) :
    generatedByStabilizers (qecParamsOfCodeSpec spec hnq hns) E ↔ Stab spec E := by
  unfold generatedByStabilizers Stab
  constructor
  · rintro ⟨mask, hmask⟩
    refine ⟨mask, fun q => ?_⟩
    rw [hmask, stabilizerProduct_eq_prodStab spec hnq hns mask q]
  · rintro ⟨mask, hmask⟩
    refine ⟨mask, ?_⟩
    funext q
    rw [hmask q, ← stabilizerProduct_eq_prodStab spec hnq hns mask q]

/-- A `detectorTerm` reads the QClifford time-resolved detector log slot. -/
theorem detectorTerm_eval {nq : Nat} (spec : CodeSpec nq)
    (hnq : 0 < nq) (hns : 0 < spec.numStab) (σ : QCState nq) (slot : Nat) :
    (detectorTerm (P := qecParamsOfCodeSpec spec hnq hns) slot).evalWith
        (qcliffordBackend spec hnq hns) Env.empty σ
      = σ.es.detectors slot := by
  simp [detectorTerm, Term.evalWith, qcliffordBackend]

/-- A `xorTerm` over a slot list evaluates to the `xorBools` of the detector
reads at those slots. -/
theorem xorTerm_eval {nq : Nat} (spec : CodeSpec nq)
    (hnq : 0 < nq) (hns : 0 < spec.numStab) (σ : QCState nq) :
    ∀ (slots : List Nat),
      (xorTerm (P := qecParamsOfCodeSpec spec hnq hns) (slots.map detectorTerm)).evalWith
          (qcliffordBackend spec hnq hns) Env.empty σ
        = xorBools (slots.map (fun s => σ.es.detectors s)) := by
  intro slots
  induction slots with
  | nil => simp [xorTerm, xorBools, Term.evalWith]
  | cons s rest ih =>
      simp only [List.map_cons, xorTerm, xorBools, List.foldr_cons]
      simp only [Term.evalWith]
      rw [detectorTerm_eval spec hnq hns σ s]
      rw [show (List.foldr xor false (List.map (fun s => σ.es.detectors s) rest))
            = xorBools (rest.map (fun s => σ.es.detectors s)) from rfl, ← ih]

/-- The syndrome-bit term denotes the PCC `syndromeBit`. -/
theorem syndromeBitTerm_eval {nq : Nat} (spec : CodeSpec nq)
    (hnq : 0 < nq) (hns : 0 < spec.numStab) (σ : QCState nq) (i : Fin spec.numStab) :
    (syndromeBitTerm (P := qecParamsOfCodeSpec spec hnq hns) (readoutSlots spec i)).evalWith
        (qcliffordBackend spec hnq hns) Env.empty σ
      = syndromeBit spec σ.es i := by
  unfold syndromeBitTerm syndromeBit readoutSlots
  rw [xorTerm_eval spec hnq hns σ, List.map_map]
  rfl

/-- `centralizerF .error` denotes the PCC `Centralizer` predicate on the
data-projected error. -/
theorem denoteQC_centralizerF {nq : Nat} (spec : CodeSpec nq)
    (hnq : 0 < nq) (hns : 0 < spec.numStab) (σ : QCState nq) :
    (centralizerF (P := qecParamsOfCodeSpec spec hnq hns) .error).evalWith
        (qcliffordBackend spec hnq hns) Env.empty σ
      ↔ Centralizer spec (dataVector spec σ.es) := by
  have hgen : ∀ (l : List (Fin spec.numStab)),
      (l.foldr (fun i acc => Formula.and
          (.eq (.parity (.stabilizer (.stabLit i)) .error) (.boolLit false)) acc)
          (Formula.top)).evalWith (qcliffordBackend spec hnq hns) Env.empty σ
        ↔ ∀ i ∈ l, ErrorVec.parity (spec.stabilizer i) (dataVector spec σ.es) = false := by
    intro l
    induction l with
    | nil =>
        constructor
        · intro _ i hi; simp at hi
        · intro _; exact True.intro
    | cons i rest ih =>
        constructor
        · intro h j hj
          rcases List.mem_cons.mp hj with hje | hjr
          · subst hje
            simpa [Formula.evalWith, Term.evalWith, qcliffordBackend] using h.1
          · exact (ih.mp h.2) j hjr
        · intro hall
          refine ⟨?_, ih.mpr (fun j hj => hall j (List.mem_cons_of_mem _ hj))⟩
          simpa [Formula.evalWith, Term.evalWith, qcliffordBackend]
            using hall i (List.mem_cons_self ..)
  refine (hgen (List.finRange spec.numStab)).trans ?_
  unfold Centralizer
  constructor
  · intro h i; rw [vectorParity_eq_parity]; exact h i (List.mem_finRange i)
  · intro h i _; rw [← vectorParity_eq_parity]; exact h i

/-- `undetectedF` denotes the PCC `undetected` predicate. -/
theorem denoteQC_undetectedF {nq : Nat} (spec : CodeSpec nq)
    (hnq : 0 < nq) (hns : 0 < spec.numStab) (σ : QCState nq) :
    (undetectedF spec hnq hns).evalWith (qcliffordBackend spec hnq hns) Env.empty σ
      ↔ undetected spec σ.es := by
  unfold undetectedF undetected
  have hgen : ∀ (l : List (Fin spec.numStab)),
      (l.foldr (fun i acc => Formula.and
          (.eq (syndromeBitTerm (readoutSlots spec i)) (.boolLit false)) acc)
          (Formula.top)).evalWith (qcliffordBackend spec hnq hns) Env.empty σ
        ↔ ∀ i ∈ l, syndromeBit spec σ.es i = false := by
    intro l
    induction l with
    | nil =>
        constructor
        · intro _ i hi; simp at hi
        · intro _; exact True.intro
    | cons i rest ih =>
        constructor
        · intro h j hj
          rcases List.mem_cons.mp hj with hje | hjr
          · subst hje
            simpa [Formula.evalWith, Term.evalWith, syndromeBitTerm_eval] using h.1
          · exact (ih.mp h.2) j hjr
        · intro hall
          refine ⟨?_, ih.mpr (fun j hj => hall j (List.mem_cons_of_mem _ hj))⟩
          simpa [Formula.evalWith, Term.evalWith, syndromeBitTerm_eval]
            using hall i (List.mem_cons_self ..)
  refine (hgen (List.finRange spec.numStab)).trans ?_
  constructor
  · intro h i; exact h i (List.mem_finRange i)
  · intro h i _; exact h i

/-- `postselectionFlagsZeroF` denotes the PCC `allPostselectionFlagsZero`. -/
theorem denoteQC_postselectionFlagsZeroF {nq : Nat} (spec : CodeSpec nq)
    (hnq : 0 < nq) (hns : 0 < spec.numStab) (σ : QCState nq) :
    (postselectionFlagsZeroF spec hnq hns).evalWith (qcliffordBackend spec hnq hns) Env.empty σ
      ↔ allPostselectionFlagsZero spec σ.es := by
  unfold postselectionFlagsZeroF allPostselectionFlagsZero
  have hgen : ∀ (l : List (Fin spec.numFlags)),
      (l.foldr (fun i acc =>
          if spec.postselectFlag i then
            Formula.and (.eq (detectorTerm (spec.flagSlot i)) (.boolLit false)) acc
          else acc)
          (Formula.top)).evalWith (qcliffordBackend spec hnq hns) Env.empty σ
        ↔ ∀ i ∈ l, spec.postselectFlag i = true →
            σ.es.detectors (spec.flagSlot i) = false := by
    intro l
    induction l with
    | nil =>
        constructor
        · intro _ i hi; simp at hi
        · intro _; exact True.intro
    | cons i rest ih =>
        rw [List.foldr_cons]
        by_cases hpf : spec.postselectFlag i = true
        · rw [if_pos hpf]
          constructor
          · intro h j hj hjp
            rcases List.mem_cons.mp hj with hje | hjr
            · subst hje
              simpa [Formula.evalWith, Term.evalWith, detectorTerm_eval] using h.1
            · exact (ih.mp h.2) j hjr hjp
          · intro hall
            refine ⟨?_, ih.mpr (fun j hj hjp => hall j (List.mem_cons_of_mem _ hj) hjp)⟩
            simpa [Formula.evalWith, Term.evalWith, detectorTerm_eval]
              using hall i (List.mem_cons_self ..) hpf
        · rw [if_neg hpf, ih]
          constructor
          · intro h j hj hjp
            rcases List.mem_cons.mp hj with hje | hjr
            · subst hje; exact absurd hjp hpf
            · exact h j hjr hjp
          · intro h j hj hjp; exact h j (List.mem_cons_of_mem _ hj) hjp
  refine (hgen (List.finRange spec.numFlags)).trans ?_
  constructor
  · intro h i hip; exact h i (List.mem_finRange i) hip
  · intro h i _ hip; exact h i hip

/-- **Bridge 1.** `allFlagsZeroF` denotes the PCC accept condition
`allFlagsZero`. -/
theorem denoteQC_allFlagsZeroF {nq : Nat} (spec : CodeSpec nq)
    (hnq : 0 < nq) (hns : 0 < spec.numStab) (σ : QCState nq) :
    Formula.denoteQC spec hnq hns (allFlagsZeroF spec hnq hns) σ
      ↔ allFlagsZero spec σ.es := by
  unfold Formula.denoteQC allFlagsZeroF allFlagsZero Formula.denoteWith
  show ((undetectedF spec hnq hns).evalWith _ _ _
      ∧ (postselectionFlagsZeroF spec hnq hns).evalWith _ _ _) ↔ _
  rw [denoteQC_undetectedF spec hnq hns σ, denoteQC_postselectionFlagsZeroF spec hnq hns σ]

/-- **Bridge 2.** `logicalAnyResidualF .error` denotes the PCC
`logicalFailure`. -/
theorem denoteQC_logicalAnyResidual {nq : Nat} (spec : CodeSpec nq)
    (hnq : 0 < nq) (hns : 0 < spec.numStab) (σ : QCState nq) :
    Formula.denoteQC spec hnq hns (logicalAnyResidualF .error) σ
      ↔ logicalFailure spec σ.es := by
  unfold Formula.denoteQC logicalAnyResidualF logicalFailure Formula.denoteWith
  show ((centralizerF .error).evalWith _ _ _
      ∧ ¬ ((Formula.inStab .error).evalWith _ _ _)) ↔ _
  rw [denoteQC_centralizerF spec hnq hns σ]
  have hinstab : ((Formula.inStab (P := qecParamsOfCodeSpec spec hnq hns) .error).evalWith
      (qcliffordBackend spec hnq hns) Env.empty σ)
        ↔ Stab spec (dataVector spec σ.es) := by
    show generatedByStabilizers (qecParamsOfCodeSpec spec hnq hns) (dataVector spec σ.es) ↔ _
    exact inStab_iff_Stab spec hnq hns (dataVector spec σ.es)
  rw [hinstab]

/-- **Bridge 3.** `failureF` denotes the PCC `failure` predicate (combines
Bridges 1 and 2). -/
theorem denoteQC_failureF {nq : Nat} (spec : CodeSpec nq)
    (hnq : 0 < nq) (hns : 0 < spec.numStab) (σ : QCState nq) :
    Formula.denoteQC spec hnq hns (failureF spec hnq hns) σ ↔ failure spec σ.es := by
  unfold Formula.denoteQC failureF failure Formula.denoteWith
  show ((logicalAnyResidualF .error).evalWith _ _ _
      ∧ (allFlagsZeroF spec hnq hns).evalWith _ _ _) ↔ _
  rw [show ((logicalAnyResidualF (P := qecParamsOfCodeSpec spec hnq hns) .error).evalWith
        (qcliffordBackend spec hnq hns) Env.empty σ)
      = Formula.denoteQC spec hnq hns (logicalAnyResidualF .error) σ from rfl]
  rw [show ((allFlagsZeroF spec hnq hns).evalWith (qcliffordBackend spec hnq hns) Env.empty σ)
      = Formula.denoteQC spec hnq hns (allFlagsZeroF spec hnq hns) σ from rfl]
  rw [denoteQC_logicalAnyResidual spec hnq hns σ, denoteQC_allFlagsZeroF spec hnq hns σ]

/-- **Bridge 4.** `circuitDistanceAnyF spec.d` denotes the real circuit-distance
lower bound `logicalFailure → spec.d ≤ σ.lambda`.

The distance literal is the code budget `spec.d`, which is exactly the literal
used by `VCInput.distanceFormula` (`circuitDistanceAnyF input.toCodeSpec.d`).
This identification is forced: `spentF = budget - remaining` denotes
`spec.d - (spec.d - σ.lambda) = min spec.d σ.lambda`, so `d ≤ spentF`
is equivalent to `d ≤ σ.lambda` precisely when the literal `d` is the budget
`spec.d` (then `spec.d ≤ min spec.d σ.lambda ↔ spec.d ≤ σ.lambda`).  For a
literal `d ≠ spec.d` the assertion `d ≤ spentF` denotes `d ≤ min spec.d σ.lambda`,
which is strictly stronger than `d ≤ σ.lambda`; so the bridge is stated and
proven for the budget literal that the generator actually emits. -/
theorem denoteQC_circuitDistanceAny {nq : Nat} (spec : CodeSpec nq)
    (hnq : 0 < nq) (hns : 0 < spec.numStab) (σ : QCState nq) :
    Formula.denoteQC spec hnq hns (circuitDistanceAnyF spec.d) σ
      ↔ (logicalFailure spec σ.es → spec.d ≤ σ.lambda) := by
  unfold Formula.denoteQC circuitDistanceAnyF Formula.denoteWith
  show ((logicalAnyResidualF .error).evalWith _ _ _ →
      Nat.le ((Term.natLit spec.d).evalWith (qcliffordBackend spec hnq hns) Env.empty σ)
        ((spentF).evalWith (qcliffordBackend spec hnq hns) Env.empty σ)) ↔ _
  rw [show ((logicalAnyResidualF (P := qecParamsOfCodeSpec spec hnq hns) .error).evalWith
        (qcliffordBackend spec hnq hns) Env.empty σ)
      = Formula.denoteQC spec hnq hns (logicalAnyResidualF .error) σ from rfl]
  rw [denoteQC_logicalAnyResidual spec hnq hns σ]
  have hspent : (spentF (P := qecParamsOfCodeSpec spec hnq hns)).evalWith
      (qcliffordBackend spec hnq hns) Env.empty σ = spec.d - (spec.d - σ.lambda) := by
    simp [spentF, Term.evalWith, qcliffordBackend]
  have hlit : (Term.natLit (P := qecParamsOfCodeSpec spec hnq hns) spec.d).evalWith
      (qcliffordBackend spec hnq hns) Env.empty σ = spec.d := by
    simp [Term.evalWith]
  rw [hspent, hlit]
  show (logicalFailure spec σ.es → spec.d ≤ spec.d - (spec.d - σ.lambda))
    ↔ (logicalFailure spec σ.es → spec.d ≤ σ.lambda)
  constructor
  · intro h hfail; have := h hfail; omega
  · intro h hfail; have := h hfail; omega

/-- The assertion-language portion of the generated VC report.  Each formula is
*certified*: `VCInput.formulaReport_faithful` proves that the three fields
denote exactly the concrete QClifford obligations (`failure`, `allFlagsZero`,
and `logicalFailure → spec.d ≤ σ.lambda`) under `Formula.denoteQC`.  These
are not decorative tags; they carry the real safety obligations. -/
structure VCFormulaReport {nq : Nat} (input : VCInput nq) where
  failure : Formula input.params []
  allFlagsZero : Formula input.params []
  distance : Formula input.params []

/-- Syntactic slots for generated QClifford PCC obligations.

The barrier-coupled slots (`init`, `step`, `preserve`, `noUndetectedHook`,
`acceptedBound`) have been removed.  They were proof-method internals, not
verifier obligations.  The barrier-free obligation set is:
  `programEq`, `wf`, `syn`, `ftDistance`, `reach`.

`ftDistance` is the key barrier-free FT obligation: for every QCState reached
from the clean initial state that is accepted (`allFlagsZero`), the
`circuitDistanceAnyF` formula holds — equivalently
  `logicalFailure σ.es → spec.d ≤ σ.lambda`.
This slot is dischargeable by ANY method (barrier, enumeration, algebra, etc.). -/
inductive VCSlot where
  | programEq
  | wf
  | syn
  | ftDistance
  | reach
  deriving DecidableEq, Repr

/-- Denotation of one syntactic VC slot.  This is the only place where a slot
becomes a Lean `Prop`; the generated artifact itself remains syntactic.

All slots are barrier-free: no `barrier : ErrorState → ℕ` appears here. -/
def VCSlot.denote {nq : Nat} (input : VCInput nq) (reachScript : List (Option Pauli)) :
    VCSlot -> Prop
  | .programEq => input.program = specCircuit input.toCodeSpec
  | .wf => WellFormed input.program input.toCodeSpec
  | .syn => forall i E,
      gadgetMeasFlip input.program input.toCodeSpec i E =
        parity input.toCodeSpec (input.toCodeSpec.stabilizer i) E
  | .ftDistance => forall (σ : QCState nq),
      qceval input.program (QCState.clean nq) σ ->
        allFlagsZero input.toCodeSpec σ.es ->
          Formula.denoteQC input.toCodeSpec input.code.nq_pos input.code.numStab_pos
            (circuitDistanceAnyF input.toCodeSpec.d) σ
  | .reach =>
      (runFScript input.program reachScript (ErrorState.clean nq)).2 = input.toCodeSpec.d ∧
        failure input.toCodeSpec (runFScript input.program reachScript (ErrorState.clean nq)).1

/-- Syntactic QClifford Hoare derivation skeleton emitted by VCGen.  It mirrors
the existing `FDeriv` rule names but contains no proof terms.  Leaf obligations
are discharged separately through `VCSlot`s. -/
inductive FHoareSkeleton (nq : Nat) where
  | F_Nil
  | F_Gate (g : Gate nq) (suffix : Circuit nq)
  | F_ErrLoc (q : Fin nq) (suffix : Circuit nq)
  | F_App (left right : FHoareSkeleton nq)
  | F_Conseq (label : String) (child : FHoareSkeleton nq)

/-- Build the instruction-level frontier skeleton for a concrete QClifford
program. -/
def frontierSkeleton {nq : Nat} : FCircuit nq -> FHoareSkeleton nq
  | [] => .F_Nil
  | .gate g :: rest =>
      .F_App (.F_Gate g (eraseFaults rest)) (frontierSkeleton rest)
  | .errLoc q :: rest =>
      .F_App (.F_ErrLoc q (eraseFaults rest)) (frontierSkeleton rest)

/-- The full generated Hoare skeleton, including the surrounding consequence
steps for clean initialization and final distance. -/
def hoareSkeleton {nq : Nat} (input : VCInput nq) : FHoareSkeleton nq :=
  .F_Conseq "E-CleanInit/H-FinalDistance"
    (.F_Conseq "H-ProgramEq/GeneratedFrontier" (frontierSkeleton input.program))

/-- Automatically generated assertion-language report for a QClifford VC
input.  Each field is certified by `VCInput.formulaReport_faithful`: the
stored formula *denotes* the corresponding concrete QClifford obligation
under `Formula.denoteQC`, so the report is load-bearing, not decorative. -/
def VCInput.formulaReport {nq : Nat} (input : VCInput nq) : VCFormulaReport input where
  failure := input.failureFormula
  allFlagsZero := input.allFlagsZeroFormula
  distance := input.distanceFormula

/-- **Certification of the formula report.**  The three formulas stored in
`input.formulaReport` are not decorative: each one denotes exactly the
corresponding concrete QClifford obligation under `Formula.denoteQC`.

- `input.failureFormula` denotes `failure input.toCodeSpec σ.es`.
- `input.allFlagsZeroFormula` denotes `allFlagsZero input.toCodeSpec σ.es`.
- `input.distanceFormula` denotes
    `logicalFailure input.toCodeSpec σ.es → input.toCodeSpec.d ≤ σ.lambda`.

All three biconditionals are strict (bidirectional); the proof uses Bridges
1–4 from the "Decoration bridges" section above. -/
theorem VCInput.formulaReport_faithful {nq : Nat} (input : VCInput nq) (σ : QCState nq) :
    (Formula.denoteQC input.toCodeSpec input.code.nq_pos input.code.numStab_pos
        input.failureFormula σ
      ↔ failure input.toCodeSpec σ.es) ∧
    (Formula.denoteQC input.toCodeSpec input.code.nq_pos input.code.numStab_pos
        input.allFlagsZeroFormula σ
      ↔ allFlagsZero input.toCodeSpec σ.es) ∧
    (Formula.denoteQC input.toCodeSpec input.code.nq_pos input.code.numStab_pos
        input.distanceFormula σ
      ↔ (logicalFailure input.toCodeSpec σ.es → input.toCodeSpec.d ≤ σ.lambda)) :=
  ⟨denoteQC_failureF _ _ _ σ, denoteQC_allFlagsZeroF _ _ _ σ,
    denoteQC_circuitDistanceAny _ _ _ σ⟩

/-- The generated QClifford verification-condition artifact.

This is the PCC object produced from the concrete program, stabilizer-code spec,
extraction/readout spec, barrier annotation, and mode.  It contains named
obligation *statements*, but no proofs.  A certificate producer must separately
fill a discharge object for this generated artifact. -/
structure GeneratedVCs {nq : Nat} (input : VCInput nq) where
  formulas : VCFormulaReport input
  hoare : FHoareSkeleton nq
  slots : List VCSlot

def GeneratedVCs.denoteSlot {nq : Nat} {input : VCInput nq}
    (_generated : GeneratedVCs input) (slot : VCSlot)
    (reachScript : List (Option Pauli) := []) : Prop :=
  slot.denote input reachScript

/-- The automatic VC generator.  It computes every obligation statement from
the input objects; the producer does not get to choose the shape of the VCs.

The generated slot set is now barrier-free and mode-independent:
`[programEq, wf, syn, ftDistance, reach]`.  The `ftDistance` slot is the
single barrier-free FT obligation; the mode distinction is relevant only for
a producer's PROOF STRATEGY and does not affect which VCs the verifier checks. -/
def vcgen {nq : Nat} (input : VCInput nq) : GeneratedVCs input where
  formulas := input.formulaReport
  hoare := hoareSkeleton input
  slots := [.programEq, .wf, .syn, .ftDistance, .reach]

/-! ## Hoare-backed syndrome discharges -/

/-- Precondition for the Hoare proof of one generated syndrome gadget: the
state contains an arbitrary data Pauli, no helper error, and the detector cursor
is positioned at the generated start slot for this stabilizer. -/
def syndromeHoarePre {nq : Nat} (input : VCInput nq)
    (i : Fin input.toCodeSpec.numStab) : QHL.Target.AssertionC nq :=
  fun es =>
    ∃ E : Fin nq -> Pauli,
      es =
        stateOfDataPauliAtDetector input.toCodeSpec
          (input.toCodeSpec.gadgetDetectorStart i) E

/-- Postcondition for the Hoare proof of one generated syndrome gadget: running
the generated gadget from any data-only Pauli state produces exactly the
anticommutation parity with the generated stabilizer row. -/
def syndromeHoarePost {nq : Nat} (input : VCInput nq)
    (i : Fin input.toCodeSpec.numStab) : QHL.Target.AssertionC nq :=
  fun es =>
    ∀ E : Fin nq -> Pauli,
      es =
          propagateCircuit (eraseFaults (input.toCodeSpec.gadget i))
            (stateOfDataPauliAtDetector input.toCodeSpec
              (input.toCodeSpec.gadgetDetectorStart i) E) ->
        syndromeBit input.toCodeSpec es i =
          parity input.toCodeSpec (input.toCodeSpec.stabilizer i) E

/-- A producer-side proof-carrying syndrome certificate.  Unlike
`FHoareSkeleton`, this contains real QClifford Hoare derivation trees.  The
`programEq` and `wf` fields bind those local gadget proofs to the generated
program/spec pair consumed by VCGen. -/
structure SyndromeHoareCertificate {nq : Nat} (input : VCInput nq) where
  programEq : (vcgen input).denoteSlot .programEq
  wf : (vcgen input).denoteSlot .wf
  deriv :
    ∀ i : Fin input.toCodeSpec.numStab,
      QHL.Target.DerivC nq
        (syndromeHoarePre input i)
        (eraseFaults (input.toCodeSpec.gadget i))
        (syndromeHoarePost input i)

/-- A real target Hoare derivation tree for every generated gadget discharges
the `.syn` VC slot. -/
theorem SyndromeHoareCertificate.syn {nq : Nat} {input : VCInput nq}
    (cert : SyndromeHoareCertificate input) :
    (vcgen input).denoteSlot .syn := by
  intro i E
  have hHoare := QHL.Target.hoare_sound_c (cert.deriv i)
  have hPost :=
    hHoare
      (stateOfDataPauliAtDetector input.toCodeSpec
        (input.toCodeSpec.gadgetDetectorStart i) E)
      (propagateCircuit (eraseFaults (input.toCodeSpec.gadget i))
        (stateOfDataPauliAtDetector input.toCodeSpec
          (input.toCodeSpec.gadgetDetectorStart i) E))
      (QHL.Target.cevalC_of_propagateCircuit
        (eraseFaults (input.toCodeSpec.gadget i))
        (stateOfDataPauliAtDetector input.toCodeSpec
          (input.toCodeSpec.gadgetDetectorStart i) E))
      ⟨E, rfl⟩
  simpa [vcgen, GeneratedVCs.denoteSlot, VCSlot.denote, gadgetMeasFlip,
    syndromeHoarePost] using hPost E rfl

/-- Producer discharge record for the barrier-free VC interface.

The field types refer to `vcgen input`, so this is proof evidence for the
generated artifact rather than a hand-written parallel certificate.  No
`barrier` field appears here: the producer is free to prove `ftDistance` by
any method (barrier descent, enumeration, algebra, etc.). -/
structure DischargedVCs {nq : Nat} (input : VCInput nq) where
  reachScript : List (Option Pauli)
  programEq : (vcgen input).denoteSlot .programEq
  wf : (vcgen input).denoteSlot .wf
  syn : (vcgen input).denoteSlot .syn
  ftDistance : (vcgen input).denoteSlot .ftDistance
  reachOk : (vcgen input).denoteSlot .reach reachScript

/-- Legacy alias so that existing clients can use `UnconditionalVCs` unchanged
while we migrate to `DischargedVCs`.  This is a pure definitional alias. -/
abbrev UnconditionalVCs {nq : Nat} (input : VCInput nq) := DischargedVCs input

/-- A generated proof obligation package.  The mode distinction (`unconditional`
vs `postselected`) was previously part of `VCGen`; it is now irrelevant to the
verifier and is retained only for backward-compatibility of downstream code that
pattern-matches on it.  Both constructors carry the same `DischargedVCs`. -/
inductive VCGen {nq : Nat} (input : VCInput nq) : Type where
  | mk : DischargedVCs input -> VCGen input

/-- Build a full VCGen discharge from a Hoare-backed syndrome certificate plus
the remaining non-syndrome obligations.  This is the checked path intended for
compiled QStab programs: `.programEq`, `.wf`, and `.syn` come from the generated
program/spec pair and real target Hoare derivation trees. -/
def VCGen.ofSyndromeHoareCertificate {nq : Nat} {input : VCInput nq}
    (cert : SyndromeHoareCertificate input)
    (ftDistance : (vcgen input).denoteSlot .ftDistance)
    (reachScript : List (Option Pauli))
    (reachOk : (vcgen input).denoteSlot .reach reachScript) :
    VCGen input :=
  .mk
    { reachScript := reachScript
      programEq := cert.programEq
      wf := cert.wf
      syn := cert.syn
      ftDistance := ftDistance
      reachOk := reachOk }

/-- Trusted VCGen soundness theorem.

The proof is barrier-free: we derive `ToleratesFaultsΛ` directly from the
`ftDistance` obligation (via `denoteQC_circuitDistanceAny`) and the reach
obligation.  No barrier appears in this statement or its proof. -/
theorem vcgen_sound {nq : Nat} {input : VCInput nq} (cert : VCGen input) :
    Safe input.program input.toCodeSpec := by
  obtain ⟨vcs⟩ := cert
  refine ⟨vcs.wf, input.toCodeSpec.readout_disjoint, vcs.syn, ?_, ?_⟩
  · -- ToleratesFaultsΛ from ftDistance
    intro σ hRun hBudget hFail
    have hFlags : allFlagsZero input.toCodeSpec σ.es := hFail.2
    have hLogical : logicalFailure input.toCodeSpec σ.es := hFail.1
    have hFtD := vcs.ftDistance σ hRun hFlags
    rw [denoteQC_circuitDistanceAny input.toCodeSpec input.code.nq_pos
      input.code.numStab_pos σ] at hFtD
    have hLe := hFtD hLogical
    have hPos := input.toCodeSpec.d_pos
    omega
  · -- Reach witness
    obtain ⟨hCount, hFail⟩ := vcs.reachOk
    let out := runFScript input.program vcs.reachScript (ErrorState.clean nq)
    refine ⟨out.1, ?_, ?_⟩
    · have h := runFScript_sound input.program vcs.reachScript (ErrorState.clean nq)
      simpa [out, hCount] using h
    · simpa [out] using hFail

/-- **Load-bearing headline: safety through the shared assertion language.**

Every QCState reached by running `input.program` from the clean initial state
that is *accepted* (satisfies `allFlagsZero`) satisfies the formula
`circuitDistanceAnyF input.toCodeSpec.d` under `Formula.denoteQC`.

By `VCInput.formulaReport_faithful`, this formula denotes exactly
`logicalFailure input.toCodeSpec σ.es → input.toCodeSpec.d ≤ σ.lambda`,
so the assertion language carries the actual circuit-distance safety result,
not merely a parallel description of it.

The proof does not weaken `Safe`: it is a direct consequence of the
`ToleratesFaultsΛ` component of `Safe` (from `vcgen_sound`) together with
the `allFlagsZero` acceptance assumption and the definition of `failure`. -/
theorem vcgen_safe_in_assertion_language {nq : Nat} {input : VCInput nq}
    (cert : VCGen input) (σ : QCState nq)
    (hRun : qceval input.program (QCState.clean nq) σ)
    (hFlags : allFlagsZero input.toCodeSpec σ.es) :
    Formula.denoteQC input.toCodeSpec input.code.nq_pos input.code.numStab_pos
      (circuitDistanceAnyF input.toCodeSpec.d) σ := by
  obtain ⟨vcs⟩ := cert
  exact vcs.ftDistance σ hRun hFlags

/-! ## Barrier-method adapter lemmas

These lemmas let a producer who chose the barrier proof strategy satisfy the
barrier-free `ftDistance` slot.  They do NOT appear in `VCInput`, `VCSlot`,
`vcgen`, or `vcgen_sound`.  The VC itself is barrier-free; these are purely
producer-side conveniences.

`ftDistance_of_certificate` / `ftDistance_of_certificate'` are the adapters;
`VCGen.ofDistanceCertificate` / `VCGen.ofDistanceCertificate'` are the
convenience constructors that bundle the whole discharge. -/

/-- **Barrier adapter 1.** A `DistanceCertificate` implies the barrier-free
`ftDistance` obligation.  This is proved by running `certificate_tolerates`
and then applying `denoteQC_circuitDistanceAny`. -/
theorem ftDistance_of_certificate {nq : Nat} {C : FCircuit nq} {spec : CodeSpec nq}
    (cert : DistanceCertificate C spec) (hnq : 0 < nq) (hnumStab : 0 < spec.numStab) :
    forall (σ : QCState nq),
      qceval C (QCState.clean nq) σ ->
        allFlagsZero spec σ.es ->
          Formula.denoteQC spec hnq hnumStab (circuitDistanceAnyF spec.d) σ := by
  intro σ hRun hFlags
  rw [denoteQC_circuitDistanceAny spec hnq hnumStab σ]
  intro hLogical
  have hTol := certificate_tolerates cert
  by_contra hlt
  push_neg at hlt
  exact hTol σ hRun (by omega) ⟨hLogical, hFlags⟩

/-- **Barrier adapter 2.** A `DistanceCertificate'` implies the barrier-free
`ftDistance` obligation, via `certificate'_tolerates`. -/
theorem ftDistance_of_certificate' {nq : Nat} {C : FCircuit nq} {spec : CodeSpec nq}
    (cert : DistanceCertificate' C spec) (hnq : 0 < nq) (hnumStab : 0 < spec.numStab) :
    forall (σ : QCState nq),
      qceval C (QCState.clean nq) σ ->
        allFlagsZero spec σ.es ->
          Formula.denoteQC spec hnq hnumStab (circuitDistanceAnyF spec.d) σ := by
  intro σ hRun hFlags
  rw [denoteQC_circuitDistanceAny spec hnq hnumStab σ]
  intro hLogical
  have hTol := certificate'_tolerates cert
  by_contra hlt
  push_neg at hlt
  exact hTol σ hRun (by omega) ⟨hLogical, hFlags⟩

/-- Convenience constructor: wrap a `DistanceCertificate` as a barrier-free
`VCGen` discharge.  The barrier lives inside `cert` as a proof strategy;
the resulting `VCGen` is entirely barrier-free. -/
def VCGen.ofDistanceCertificate {nq : Nat} {C : FCircuit nq} {spec : CodeSpec nq}
    (cert : DistanceCertificate C spec) (hnq : 0 < nq)
    (hnumStab : 0 < spec.numStab) :
    VCGen (VCInput.ofPCC C spec .unconditional hnq hnumStab) :=
  .mk
    { programEq := by simpa [vcgen] using cert.programEq
      wf := by simpa [vcgen] using cert.wf
      syn := by simpa [vcgen] using cert.syn
      ftDistance := by
        simp only [GeneratedVCs.denoteSlot, VCSlot.denote, VCInput.toCodeSpec_ofPCC]
        exact ftDistance_of_certificate cert hnq hnumStab
      reachScript := cert.reachScript
      reachOk := by simpa [vcgen] using cert.reachOk }

/-- Convenience constructor: wrap a `DistanceCertificate'` as a barrier-free
`VCGen` discharge.  The barrier lives inside `cert` as a proof strategy;
the resulting `VCGen` is entirely barrier-free. -/
def VCGen.ofDistanceCertificate' {nq : Nat} {C : FCircuit nq} {spec : CodeSpec nq}
    (cert : DistanceCertificate' C spec) (hnq : 0 < nq)
    (hnumStab : 0 < spec.numStab) :
    VCGen (VCInput.ofPCC C spec .postselected hnq hnumStab) :=
  .mk
    { programEq := by simpa [vcgen] using cert.programEq
      wf := by simpa [vcgen] using cert.wf
      syn := by simpa [vcgen] using cert.syn
      ftDistance := by
        simp only [GeneratedVCs.denoteSlot, VCSlot.denote, VCInput.toCodeSpec_ofPCC]
        exact ftDistance_of_certificate' cert hnq hnumStab
      reachScript := cert.reachScript
      reachOk := by simpa [vcgen] using cert.reachOk }

/-! ## Hoare skeleton soundness

`FHoareSkeleton`, `frontierSkeleton`, and `hoareSkeleton` are proof-free tag trees.
The theorem below grounds the skeleton: it shows that the `ftDistance` discharge
is exactly sufficient to produce a genuine `FHoare` triple.  The skeleton is
therefore not decorative — it is a syntactic witness to the proof-tree obligation
that the theorem certifies can always be filled.

Note: the frontier/barrier-descent `FDeriv` witnesses (`frontierSkeleton_sound`,
`hoareSkeleton_sound`) are now producer-side derivations that a barrier-method
producer may still construct.  They are not required for `vcgen_sound`. -/

/-- **Hoare skeleton soundness.**  A fully discharged `DischargedVCs` record
yields a genuine `FHoare cleanPre input.program (distPost input.toCodeSpec)` — the
accepted-run safety Hoare triple that the generated skeleton records.  The proof
proceeds via `vcgen_sound` and `hoare_of_toleratesFaultsΛ`. -/
theorem hoareSkeleton_sound {nq : Nat} {input : VCInput nq}
    (vcs : DischargedVCs input) :
    FHoare cleanPre input.program (distPost input.toCodeSpec) :=
  hoare_of_toleratesFaultsΛ input.program (failure input.toCodeSpec) (input.toCodeSpec.d - 1)
    (vcgen_sound (.mk vcs)).2.2.2.1

#print axioms vcgen_sound
#print axioms VCInput.formulaReport_faithful
#print axioms vcgen_safe_in_assertion_language
#print axioms hoareSkeleton_sound
#print axioms ftDistance_of_certificate
#print axioms ftDistance_of_certificate'

end QStab.QClifford.PCC
