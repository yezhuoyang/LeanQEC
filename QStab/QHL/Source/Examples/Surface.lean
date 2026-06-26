import QStab.QHL.Source.Branch
import QStab.Paper.SurfaceBarrier

/-! # Surface code distance proof via fixed-program branch Hoare logic

This is the canonical QStab proof shape:

* the program is a fixed stabilizer-measurement schedule,
* error types are nondeterministic semantic branches,
* the proof object is an invariant certificate containing one derivation
  family per branch kind.

There is no `skip`, no sequencing command, and no fixed injected-error trace
in this file.
-/

namespace QHL.Source.Examples.Surface

open QStab QStab.Examples.SurfaceGeneral QStab.Paper.BarrierFramework
     QStab.Paper.SurfaceBarrier QHL.AssertionLang QHL.Source.Branch

/-- The fixed QStab program for the current Surface examples: at each coordinate,
    measure the stabilizer at that row-major coordinate. -/
noncomputable def surfaceProgram (d : Nat) (spec : NZSurfaceSpec d) :
    QStabProgram spec.params :=
  QStabProgram.rowMajor spec.params

theorem surfaceProgram_currentStab (d : Nat) (spec : NZSurfaceSpec d)
    (c : QECParams.Coord spec.params) :
    (surfaceProgram d spec).currentStab c = c.x :=
  rfl

def surface_parityZero (d : Nat) (spec : NZSurfaceSpec d) :
    List (ErrorVec spec.params.n) :=
  alignedBarZParityZero spec.toAligned

def surface_parityOne (d : Nat) (spec : NZSurfaceSpec d) :
    List (ErrorVec spec.params.n) :=
  alignedBarZParityOne spec.toAligned

theorem surface_parity_iff (d : Nat) (spec : NZSurfaceSpec d)
    (E : ErrorVec spec.params.n) :
    ((∀ S, S ∈ surface_parityZero d spec -> ErrorVec.parity S E = false) ∧
     (∀ T, T ∈ surface_parityOne d spec -> ErrorVec.parity T E = true)) ↔
    (barZClass spec).contains E :=
  alignedBarZ_contains_iff spec.toAligned E

noncomputable def surfaceLogicalClass (d : Nat) (spec : NZSurfaceSpec d) :
    LogicalClassSymbol spec.params :=
  LogicalClassSymbol.ofAlignedBarZ "surface.barZ" spec.toAligned

noncomputable def surfaceBarrierSymbol (d : Nat) (spec : NZSurfaceSpec d) :
    BarrierSymbol spec.params :=
  BarrierSymbol.ofAlignedCodeSpec "surface.beta" "surface.rows" spec.toAligned

/-- The branch-invariant formula checked by the QStab proof kernel. -/
noncomputable def surface_inv_formula (d : Nat) (spec : NZSurfaceSpec d) :
    Formula spec.params [] :=
  barrierInvF (surfaceBarrierSymbol d spec) (surfaceLogicalClass d spec)

/-- Assertion-language logical-error predicate for the Surface bar-Z class. -/
noncomputable def surface_logical_formula (d : Nat) (spec : NZSurfaceSpec d) :
    Formula spec.params [] :=
  .logicalMember (surfaceLogicalClass d spec) .error

theorem surface_logical_iff
    (d : Nat) (spec : NZSurfaceSpec d) (s : State spec.params) :
    (surface_logical_formula d spec).denote s ↔ (barZClass spec).contains s.E_tilde := by
  change (surfaceLogicalClass d spec).contains s.E_tilde ↔
    (barZClass spec).contains s.E_tilde
  exact alignedBarZ_contains_iff spec.toAligned s.E_tilde

noncomputable def surface_barrier_contract_certificate
    (d : Nat) (spec : NZSurfaceSpec d) :
    SyntacticBarrierContractCertificate
      (surfaceBarrierSymbol d spec) (surfaceLogicalClass d spec) :=
  SyntacticBarrierContractCertificate.ofAlignedSpreadCodeSpec
    "surface.beta" "surface.rows" "surface.barZ" spec.toAligned

theorem surface_barrier_contract_certificate_size (d : Nat) (spec : NZSurfaceSpec d) :
    (surface_barrier_contract_certificate d spec).size = 5 :=
  SyntacticBarrierContractCertificate.size_eq_five
    (surface_barrier_contract_certificate d spec)

/-- Type-0 branch derivation for the Surface barrier invariant:
    invariant entailment into the Type-0 WP, then the ordinary `H_Err0` rule. -/
noncomputable def surface_err0_derivation
    (d : Nat) (spec : NZSurfaceSpec d)
    (i : Fin spec.params.n) (p : Pauli) (hp : p ≠ Pauli.I) :
    ProofDerivation (surfaceProgram d spec)
      (surface_inv_formula d spec) (.err0 i p) (surface_inv_formula d spec) :=
  barrierInvErr0Certificate
    (prog := surfaceProgram d spec)
    (surface_barrier_contract_certificate d spec) i p hp

/-- Type-I branch derivation for the Surface barrier invariant. -/
noncomputable def surface_errI_derivation
    (d : Nat) (spec : NZSurfaceSpec d)
    (i : Fin spec.params.n) (p : Pauli) (hp : p ≠ Pauli.I) (mf : Bool) :
    ProofDerivation (surfaceProgram d spec)
      (surface_inv_formula d spec) (.errI i p mf) (surface_inv_formula d spec) :=
  barrierInvErrICertificate
    (prog := surfaceProgram d spec)
    (surface_barrier_contract_certificate d spec) i p hp mf

/-- Type-II branch derivation for the Surface barrier invariant. -/
noncomputable def surface_errII_derivation
    (d : Nat) (spec : NZSurfaceSpec d)
    (e : ErrorVec spec.params.n) (mf : Bool) :
    ProofDerivation (surfaceProgram d spec)
      (surface_inv_formula d spec) (.errII e mf) (surface_inv_formula d spec) :=
  barrierInvErrIICertificate
    (prog := surfaceProgram d spec)
    (surface_barrier_contract_certificate d spec) e mf

/-- Type-III branch derivation for the Surface barrier invariant. -/
noncomputable def surface_errIII_derivation
    (d : Nat) (spec : NZSurfaceSpec d) :
    ProofDerivation (surfaceProgram d spec)
      (surface_inv_formula d spec) .errIII (surface_inv_formula d spec) :=
  barrierInvErrIIICertificate
    (prog := surfaceProgram d spec)
    (surface_barrier_contract_certificate d spec)

/-- Measurement branch derivation for the Surface barrier invariant. -/
noncomputable def surface_meas_derivation
    (d : Nat) (spec : NZSurfaceSpec d) :
    ProofDerivation (surfaceProgram d spec)
      (surface_inv_formula d spec) .meas (surface_inv_formula d spec) :=
  barrierInvMeasCertificate
    (prog := surfaceProgram d spec)
    (surface_barrier_contract_certificate d spec)

theorem surface_err0_derivation_size
    (d : Nat) (spec : NZSurfaceSpec d)
    (i : Fin spec.params.n) (p : Pauli) (hp : p ≠ Pauli.I) :
    (surface_err0_derivation d spec i p hp).size = 2 :=
  rfl

theorem surface_errI_derivation_size
    (d : Nat) (spec : NZSurfaceSpec d)
    (i : Fin spec.params.n) (p : Pauli) (hp : p ≠ Pauli.I) (mf : Bool) :
    (surface_errI_derivation d spec i p hp mf).size = 2 :=
  rfl

theorem surface_errII_derivation_size
    (d : Nat) (spec : NZSurfaceSpec d) (e : ErrorVec spec.params.n) (mf : Bool) :
    (surface_errII_derivation d spec e mf).size = 2 :=
  rfl

theorem surface_errIII_derivation_size (d : Nat) (spec : NZSurfaceSpec d) :
    (surface_errIII_derivation d spec).size = 2 :=
  rfl

theorem surface_meas_derivation_size (d : Nat) (spec : NZSurfaceSpec d) :
    (surface_meas_derivation d spec).size = 2 :=
  rfl

/-- The single demonic one-step Surface invariant derivation. -/
noncomputable def surface_havoc_derivation (d : Nat) (spec : NZSurfaceSpec d) :
    HavocProofDerivation (surfaceProgram d spec)
      (surface_inv_formula d spec) (surface_inv_formula d spec) :=
  syntacticBarrierContractToHavocCertificate
    (prog := surfaceProgram d spec)
    (surface_barrier_contract_certificate d spec)

theorem surface_havoc_derivation_size (d : Nat) (spec : NZSurfaceSpec d) :
    (surface_havoc_derivation d spec).size = 1 :=
  rfl

/-- The complete Surface invariant derivation: initial invariant plus havoc. -/
noncomputable def surface_invariant_derivation (d : Nat) (spec : NZSurfaceSpec d) :
    InvariantDerivation (surfaceProgram d spec) (surface_inv_formula d spec) :=
  syntacticBarrierContractToInvariantDerivation
    (prog := surfaceProgram d spec)
    (surface_barrier_contract_certificate d spec)

/-- The complete all-branch invariant certificate. -/
noncomputable def surface_invariant_certificate (d : Nat) (spec : NZSurfaceSpec d) :
    InvariantCertificate (surfaceProgram d spec) (surface_inv_formula d spec) :=
  {
    init := (surface_invariant_derivation d spec).init
    err0 := fun i p hp => surface_err0_derivation d spec i p hp
    errI := fun i p hp mf => surface_errI_derivation d spec i p hp mf
    errII := fun e mf => surface_errII_derivation d spec e mf
    errIII := surface_errIII_derivation d spec
    meas := surface_meas_derivation d spec
  }

/-- Surface code distance bound for every done run of the fixed measurement
    program under nondeterministic QStab fault semantics. -/
theorem surface_dcirc_geq_d
    (d : Nat) (spec : NZSurfaceSpec d)
    (s : State spec.params)
    (hrun : Run (surfaceProgram d spec) (.done s))
    (h_in : (barZClass spec).contains s.E_tilde) :
    spec.params.C_budget - s.C ≥ d := by
  have h_inv : (surface_inv_formula d spec).denote s :=
    (surface_invariant_derivation d spec).check_sound s hrun
  obtain ⟨h_phi, _h_budget⟩ := h_inv
  have h_mu : (surfaceBarrierSymbol d spec).eval s.E_tilde = 0 := by
    calc
      (surfaceBarrierSymbol d spec).eval s.E_tilde =
          (QStab.Paper.AlignedBarrier.alignedBarrier spec.toAligned).mu s.E_tilde := by
            exact BarrierSymbol.ofAlignedCodeSpec_eval_eq_alignedBarrier
              "surface.beta" "surface.rows" spec.toAligned s.E_tilde
      _ = 0 := by
            simpa [surfaceBarrier] using (surfaceBarrier spec).mu_at_logical s.E_tilde h_in
  change d <=
    (surfaceBarrierSymbol d spec).eval s.E_tilde + (spec.params.C_budget - s.C) at h_phi
  rw [h_mu] at h_phi
  simpa using h_phi

/-- Assertion-language circuit-distance consequence of the same checked branch
    invariant certificate. -/
theorem surface_circuitDistanceF_at_done
    (d : Nat) (spec : NZSurfaceSpec d) (s : State spec.params)
    (hrun : Run (surfaceProgram d spec) (.done s)) :
    (circuitDistanceF (surfaceLogicalClass d spec)).denote s := by
  exact syntacticBarrierContractCircuitDistance_done
    (prog := surfaceProgram d spec)
    (surface_barrier_contract_certificate d spec) s hrun

/-- Operational lower bound over every active state reachable under the fixed
    Surface measurement program. -/
theorem surface_operational_lower_bound
    (d : Nat) (spec : NZSurfaceSpec d) :
    OperationalLowerBound (surfaceProgram d spec) (surface_logical_formula d spec) d := by
  intro s hreach
  have hdist : (circuitDistanceF (surfaceLogicalClass d spec)).denote s :=
    syntacticBarrierContractCircuitDistance_active
      (prog := surfaceProgram d spec)
      (surface_barrier_contract_certificate d spec) s hreach
  simpa [surface_logical_formula, distanceLowerF, circuitDistanceF,
    distanceLowerBoundF] using hdist

theorem surface_no_logical_error
    (d : Nat) (spec : NZSurfaceSpec d)
    (s : State spec.params) (hrun : Run (surfaceProgram d spec) (.done s))
    (h_budget : spec.params.C_budget < d) :
    ¬ (barZClass spec).contains s.E_tilde := by
  intro h_in
  have h := surface_dcirc_geq_d d spec s hrun h_in
  omega

#print axioms surface_dcirc_geq_d
#print axioms surface_no_logical_error

end QHL.Source.Examples.Surface
