import QStab.QHL.Source.Branch
import QStab.Examples.SurfaceGeneral
import QStab.Paper.AlignedBarrier

/-! # HGP distance proof via fixed-program branch Hoare logic

This file mirrors the canonical Surface example, but with the generic aligned
barrier used for HGP/LDPC-style codes.  The QStab program is a fixed
measurement schedule; fault types are nondeterministic semantic branches.
-/

namespace QHL.Source.Examples.HGP

open QStab QStab.Examples.SurfaceGeneral QStab.Paper.BarrierFramework
     QStab.Paper.AlignedBarrier QHL.AssertionLang QHL.Source.Branch

/-- Fixed row-major measurement program for the HGP examples. -/
noncomputable def hgpProgram (d : Nat) (spec : HGPSpec d) :
    QStabProgram spec.params :=
  QStabProgram.rowMajor spec.params

theorem hgpProgram_currentStab (d : Nat) (spec : HGPSpec d)
    (c : QECParams.Coord spec.params) :
    (hgpProgram d spec).currentStab c = c.x :=
  rfl

/-- HGP barrier function, supplied by the generic aligned-code framework. -/
noncomputable def hgpBarrier (d : Nat) (spec : HGPSpec d) :
    BarrierFunction spec.params (barZClass spec.toAligned) :=
  alignedBarrier spec.toAligned

theorem hgp_isLAligned (d : Nat) (spec : HGPSpec d) :
    IsLAligned (hgpBarrier d spec) :=
  aligned_isLAligned spec.toAligned

def hgp_parityZero (d : Nat) (spec : HGPSpec d) : List (ErrorVec spec.params.n) :=
  alignedBarZParityZero spec.toAligned

def hgp_parityOne (d : Nat) (spec : HGPSpec d) : List (ErrorVec spec.params.n) :=
  alignedBarZParityOne spec.toAligned

theorem hgp_parity_iff (d : Nat) (spec : HGPSpec d) (E : ErrorVec spec.params.n) :
    ((∀ S, S ∈ hgp_parityZero d spec -> ErrorVec.parity S E = false) ∧
     (∀ T, T ∈ hgp_parityOne d spec -> ErrorVec.parity T E = true)) ↔
    (barZClass spec.toAligned).contains E :=
  alignedBarZ_contains_iff spec.toAligned E

noncomputable def hgpLogicalClass (d : Nat) (spec : HGPSpec d) :
    LogicalClassSymbol spec.params :=
  LogicalClassSymbol.ofAlignedBarZ "hgp.barZ" spec.toAligned

noncomputable def hgpBarrierSymbol (d : Nat) (spec : HGPSpec d) :
    BarrierSymbol spec.params :=
  BarrierSymbol.ofAlignedCodeSpec "hgp.beta" "hgp.rows" spec.toAligned

noncomputable def hgp_inv_formula (d : Nat) (spec : HGPSpec d) :
    Formula spec.params [] :=
  barrierInvF (hgpBarrierSymbol d spec) (hgpLogicalClass d spec)

noncomputable def hgp_barrier_contract_certificate (d : Nat) (spec : HGPSpec d) :
    SyntacticBarrierContractCertificate (hgpBarrierSymbol d spec) (hgpLogicalClass d spec) :=
  SyntacticBarrierContractCertificate.ofAlignedSpreadCodeSpec
    "hgp.beta" "hgp.rows" "hgp.barZ" spec.toAligned

theorem hgp_barrier_contract_certificate_size (d : Nat) (spec : HGPSpec d) :
    (hgp_barrier_contract_certificate d spec).size = 5 :=
  SyntacticBarrierContractCertificate.size_eq_five
    (hgp_barrier_contract_certificate d spec)

noncomputable def hgp_err0_derivation
    (d : Nat) (spec : HGPSpec d)
    (i : Fin spec.params.n) (p : Pauli) (hp : p ≠ Pauli.I) :
    ProofDerivation (hgpProgram d spec)
      (hgp_inv_formula d spec) (.err0 i p) (hgp_inv_formula d spec) :=
  barrierInvErr0Certificate
    (prog := hgpProgram d spec)
    (hgp_barrier_contract_certificate d spec) i p hp

noncomputable def hgp_errI_derivation
    (d : Nat) (spec : HGPSpec d)
    (i : Fin spec.params.n) (p : Pauli) (hp : p ≠ Pauli.I) (mf : Bool) :
    ProofDerivation (hgpProgram d spec)
      (hgp_inv_formula d spec) (.errI i p mf) (hgp_inv_formula d spec) :=
  barrierInvErrICertificate
    (prog := hgpProgram d spec)
    (hgp_barrier_contract_certificate d spec) i p hp mf

noncomputable def hgp_errII_derivation
    (d : Nat) (spec : HGPSpec d)
    (e : ErrorVec spec.params.n) (mf : Bool) :
    ProofDerivation (hgpProgram d spec)
      (hgp_inv_formula d spec) (.errII e mf) (hgp_inv_formula d spec) :=
  barrierInvErrIICertificate
    (prog := hgpProgram d spec)
    (hgp_barrier_contract_certificate d spec) e mf

noncomputable def hgp_errIII_derivation
    (d : Nat) (spec : HGPSpec d) :
    ProofDerivation (hgpProgram d spec)
      (hgp_inv_formula d spec) .errIII (hgp_inv_formula d spec) :=
  barrierInvErrIIICertificate
    (prog := hgpProgram d spec)
    (hgp_barrier_contract_certificate d spec)

noncomputable def hgp_meas_derivation
    (d : Nat) (spec : HGPSpec d) :
    ProofDerivation (hgpProgram d spec)
      (hgp_inv_formula d spec) .meas (hgp_inv_formula d spec) :=
  barrierInvMeasCertificate
    (prog := hgpProgram d spec)
    (hgp_barrier_contract_certificate d spec)

theorem hgp_err0_derivation_size
    (d : Nat) (spec : HGPSpec d)
    (i : Fin spec.params.n) (p : Pauli) (hp : p ≠ Pauli.I) :
    (hgp_err0_derivation d spec i p hp).size = 2 :=
  rfl

theorem hgp_errI_derivation_size
    (d : Nat) (spec : HGPSpec d)
    (i : Fin spec.params.n) (p : Pauli) (hp : p ≠ Pauli.I) (mf : Bool) :
    (hgp_errI_derivation d spec i p hp mf).size = 2 :=
  rfl

theorem hgp_errII_derivation_size
    (d : Nat) (spec : HGPSpec d) (e : ErrorVec spec.params.n) (mf : Bool) :
    (hgp_errII_derivation d spec e mf).size = 2 :=
  rfl

theorem hgp_errIII_derivation_size (d : Nat) (spec : HGPSpec d) :
    (hgp_errIII_derivation d spec).size = 2 :=
  rfl

theorem hgp_meas_derivation_size (d : Nat) (spec : HGPSpec d) :
    (hgp_meas_derivation d spec).size = 2 :=
  rfl

noncomputable def hgp_havoc_derivation (d : Nat) (spec : HGPSpec d) :
    HavocProofDerivation (hgpProgram d spec)
      (hgp_inv_formula d spec) (hgp_inv_formula d spec) :=
  syntacticBarrierContractToHavocCertificate
    (prog := hgpProgram d spec)
    (hgp_barrier_contract_certificate d spec)

theorem hgp_havoc_derivation_size (d : Nat) (spec : HGPSpec d) :
    (hgp_havoc_derivation d spec).size = 1 :=
  rfl

noncomputable def hgp_invariant_derivation (d : Nat) (spec : HGPSpec d) :
    InvariantDerivation (hgpProgram d spec) (hgp_inv_formula d spec) :=
  syntacticBarrierContractToInvariantDerivation
    (prog := hgpProgram d spec)
    (hgp_barrier_contract_certificate d spec)

noncomputable def hgp_invariant_certificate (d : Nat) (spec : HGPSpec d) :
    InvariantCertificate (hgpProgram d spec) (hgp_inv_formula d spec) :=
  {
    init := (hgp_invariant_derivation d spec).init
    err0 := fun i p hp => hgp_err0_derivation d spec i p hp
    errI := fun i p hp mf => hgp_errI_derivation d spec i p hp mf
    errII := fun e mf => hgp_errII_derivation d spec e mf
    errIII := hgp_errIII_derivation d spec
    meas := hgp_meas_derivation d spec
  }

/-- HGP code distance bound for every done run of the fixed measurement program
    under nondeterministic QStab fault semantics. -/
theorem hgp_dcirc_geq_d
    (d : Nat) (spec : HGPSpec d)
    (s : State spec.params)
    (hrun : Run (hgpProgram d spec) (.done s))
    (h_in : (barZClass spec.toAligned).contains s.E_tilde) :
    spec.params.C_budget - s.C ≥ d := by
  have h_inv : (hgp_inv_formula d spec).denote s :=
    (hgp_invariant_derivation d spec).check_sound s hrun
  obtain ⟨h_phi, _h_budget⟩ := h_inv
  have h_mu : (hgpBarrierSymbol d spec).eval s.E_tilde = 0 := by
    calc
      (hgpBarrierSymbol d spec).eval s.E_tilde =
          (QStab.Paper.AlignedBarrier.alignedBarrier spec.toAligned).mu s.E_tilde := by
            exact BarrierSymbol.ofAlignedCodeSpec_eval_eq_alignedBarrier
              "hgp.beta" "hgp.rows" spec.toAligned s.E_tilde
      _ = 0 := by
            simpa [hgpBarrier] using (hgpBarrier d spec).mu_at_logical s.E_tilde h_in
  change d <= (hgpBarrierSymbol d spec).eval s.E_tilde + (spec.params.C_budget - s.C) at h_phi
  rw [h_mu] at h_phi
  simpa using h_phi

theorem hgp_circuitDistanceF_at_done
    (d : Nat) (spec : HGPSpec d) (s : State spec.params)
    (hrun : Run (hgpProgram d spec) (.done s)) :
    (circuitDistanceF (hgpLogicalClass d spec)).denote s := by
  exact syntacticBarrierContractCircuitDistance_done
    (prog := hgpProgram d spec)
    (hgp_barrier_contract_certificate d spec) s hrun

theorem hgp_no_logical_error
    (d : Nat) (spec : HGPSpec d)
    (s : State spec.params) (hrun : Run (hgpProgram d spec) (.done s))
    (h_budget : spec.params.C_budget < d) :
    ¬ (barZClass spec.toAligned).contains s.E_tilde := by
  intro h_in
  have h := hgp_dcirc_geq_d d spec s hrun h_in
  omega

#print axioms hgp_dcirc_geq_d
#print axioms hgp_no_logical_error

end QHL.Source.Examples.HGP
