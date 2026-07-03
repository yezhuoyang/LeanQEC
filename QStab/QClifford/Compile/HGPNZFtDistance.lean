import QStab.QClifford.Compile.HGPNZStabTransport
import QStab.QClifford.Compile.HGPLogicalOps

/-!
# The HGP `ftDistance` slot, discharged end-to-end

Unlike the surface's bar-Z-restricted `surfaceNZ_ftDistance_barZ` (coverage
gap, F3 pending there), the HGP slot closes **fully**:

* `hgpNZ_logicalFailure_iff` turns the PCC `logicalFailure` into a
  source-side `(Centralizer ∧ ¬ InStab)` statement;
* the **maximal-isotropic contrapositive** (`hgp_coverage`, from
  `hgp_maximal_isotropic`) shows any such residual anticommutes with `X̄` or
  with `Z̄` — `Ȳ`-type residuals do both, so either floor fires;
* the two landed floors (`hgp_compiled_barX_distance` /
  `hgp_compiled_barZ_distance`) each give the `d`-fault bound.

Deliverables: the self-contained `hgpNZ_ftDistance` and the discharged VCGen
slot `hgp_vcgen_ftDistanceD`, for every `d ≥ 2`.
-/

namespace QStab.QClifford.Compile

open QStab QStab.QClifford QStab.QClifford.PCC
open QStab.Examples.HGPParametric
open QHL
open QHL.AssertionLang
open QHL.Source.Examples.HGP
open QHL.Source.Examples.HGPUnionSpec

/-! ## The two `¬ InStab` halves (normalizer/parity arguments) -/

/-- Anticommuting with `Z̄` excludes the stabilizer subgroup. -/
theorem hgp_parityZ_not_InStab (d : Nat) (hd : 2 ≤ d)
    (E : ErrorVec (hgpN d))
    (hZ : ErrorVec.parity (mkHGPRepLogicalZ d) E = true) :
    ¬ InStab (hgpUParams d hd) E := by
  intro hInStab
  have hfalse : ErrorVec.parity (mkHGPRepLogicalZ d) E = false := by
    rw [ErrorVec.parity_symm]
    exact QStab.InStab.parity_of_normalizer
      (fun i => (exactUnionHGPSpec d hd).logicalZ_normalizer i) hInStab
  rw [hfalse] at hZ
  exact Bool.noConfusion hZ

/-- Anticommuting with `X̄ = Φ Z̄` excludes the stabilizer subgroup. -/
theorem hgp_parityX_not_InStab (d : Nat) (hd : 2 ≤ d)
    (E : ErrorVec (hgpN d))
    (hX : ErrorVec.parity (mkHGPRepLogicalX d hd) E = true) :
    ¬ InStab (hgpUParams d hd) E := by
  intro hInStab
  have hfalse : ErrorVec.parity (mkHGPRepLogicalX d hd) E = false := by
    rw [ErrorVec.parity_symm]
    exact QStab.InStab.parity_of_normalizer (hgp_Xbar_comm d hd) hInStab
  rw [hfalse] at hX
  exact Bool.noConfusion hX

/-! ## Coverage: the maximal-isotropic contrapositive -/

/-- **Coverage.**  A centralizer element outside the stabilizer subgroup
anticommutes with `X̄` or with `Z̄` (else `hgp_maximal_isotropic` would place
it inside).  `Ȳ`-type residuals satisfy both disjuncts. -/
theorem hgp_coverage (d : Nat) (hd : 2 ≤ d) (E : ErrorVec (hgpUParams d hd).n)
    (hcent : ∀ j : Fin (hgpUParams d hd).numStab,
      ErrorVec.parity ((hgpUParams d hd).stabilizers j) E = false)
    (hnot : ¬ InStab (hgpUParams d hd) E) :
    ErrorVec.parity (mkHGPRepLogicalX d hd) E = true
      ∨ ErrorVec.parity (mkHGPRepLogicalZ d) E = true :=
  QStab.Paper.LogicalCosets.LogicalOps.coverage (hgpLogicalOps d hd) E hcent hnot

/-! ## Class landing -/

/-- A centralizer element anticommuting with `X̄` lies in the bar-X class. -/
theorem hgp_barX_contains_of (d : Nat) (hd : 2 ≤ d)
    (E : ErrorVec (hgpUParams d hd).n)
    (hcent : ∀ j : Fin (hgpUParams d hd).numStab,
      ErrorVec.parity ((hgpUParams d hd).stabilizers j) E = false)
    (hx : ErrorVec.parity (mkHGPRepLogicalX d hd) E = true) :
    (hgpLogicalClassX d hd).contains E := by
  constructor
  · intro S hS
    have hS' : S ∈ (List.finRange (exactUnionHGPSpec d hd).params.numStab).map
        (exactUnionHGPSpec d hd).params.stabilizers := hS
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hS'
    exact hcent i
  · intro T hT
    have hT' : T = mkHGPRepLogicalX d hd := List.mem_singleton.mp hT
    subst hT'
    exact hx

/-- A centralizer element anticommuting with `Z̄` lies in the bar-Z class. -/
theorem hgp_barZ_contains_of (d : Nat) (hd : 2 ≤ d)
    (E : ErrorVec (hgpUParams d hd).n)
    (hcent : ∀ j : Fin (hgpUParams d hd).numStab,
      ErrorVec.parity ((hgpUParams d hd).stabilizers j) E = false)
    (hz : ErrorVec.parity (mkHGPRepLogicalZ d) E = true) :
    (hgpLogicalClass d (exactUnionHGPSpec d hd)).contains E := by
  constructor
  · intro S hS
    have hS' : S ∈ (List.finRange (exactUnionHGPSpec d hd).params.numStab).map
        (exactUnionHGPSpec d hd).params.stabilizers := hS
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hS'
    exact hcent i
  · intro T hT
    have hT' : T = mkHGPRepLogicalZ d := List.mem_singleton.mp hT
    subst hT'
    exact hz

/-! ## The full `ftDistance` statement -/

/-- **HGP circuit-level `ftDistance`, self-contained**: every clean-start run
of `compileProgram (hgpXZProgram d)` whose error state is a PCC
`logicalFailure` of the compiled spec fired at least `d` faults — full
coverage, no bar-Z restriction, for every `d ≥ 2`. -/
theorem hgpNZ_ftDistance (d : Nat) (hd : 2 ≤ d)
    (sigma : QCState (d * d + (d - 1) * (d - 1) + programHelperCount (hgpXZProgram d)))
    (hrun : qceval (compileProgram (hgpXZProgram d))
      (QCState.clean (d * d + (d - 1) * (d - 1) + programHelperCount (hgpXZProgram d)))
      sigma)
    (hfail : QStab.QClifford.PCC.logicalFailure (hgpSpec d hd) sigma.es) :
    d ≤ sigma.lambda := by
  rw [hgpNZ_logicalFailure_iff d hd sigma] at hfail
  obtain ⟨hcent, hnot⟩ := hfail
  rcases hgp_coverage d hd _ hcent hnot with hx | hz
  · exact hgp_compiled_barX_distance d hd sigma hrun
      (hgp_barX_contains_of d hd _ hcent hx)
  · exact hgp_compiled_barZ_distance d hd sigma hrun
      (hgp_barZ_contains_of d hd _ hcent hz)

/-- **The discharged VCGen `ftDistance` slot** for the compiled HGP program
at distance `d` — the verifier's ∀-logical obligation, met in full. -/
theorem hgp_vcgen_ftDistanceD (d : Nat) (hd : 2 ≤ d)
    (hnq : 0 < d * d + (d - 1) * (d - 1) + programHelperCount (hgpXZProgram d))
    (hnumStab : 0 < programNumStab (hgpXZProgram d)) :
    (vcgen (fullProgramVCInputD (hgpXZProgram d)
      (fullProgramReadoutDisjoint_auto (hgpXZProgram d)) d (by omega)
      hnq hnumStab)).denoteSlot .ftDistance := by
  intro sigma hrun _hflags
  rw [denoteQC_circuitDistanceAny]
  intro hfail
  have hfail' : QStab.QClifford.PCC.logicalFailure (hgpSpec d hd) sigma.es := hfail
  have hrun' : qceval (compileProgram (hgpXZProgram d))
      (QCState.clean (d * d + (d - 1) * (d - 1)
        + programHelperCount (hgpXZProgram d))) sigma := hrun
  exact hgpNZ_ftDistance d hd sigma hrun' hfail'

/-! ## The canonical slot form (`hnq` / `hnumStab` discharged internally) -/

theorem hgp_nq_pos (d : Nat) (hd : 2 ≤ d) :
    0 < d * d + (d - 1) * (d - 1) + programHelperCount (hgpXZProgram d) := by
  have h1 : 0 < d * d := Nat.mul_pos (by omega) (by omega)
  omega

theorem hgp_numStab_pos (d : Nat) (hd : 2 ≤ d) :
    0 < programNumStab (hgpXZProgram d) := by
  rw [programNumStab_hgpXZProgram d hd]
  have h1 : 0 < (d - 1) * d := Nat.mul_pos (by omega) (by omega)
  omega

/-- **HGP passes VCGen slot 4: `ftDistance`** — the canonical
`generatedFullProgramVCInputD` form, side conditions discharged
internally. -/
theorem hgpXZ_vcgen_ftDistanceD (d : Nat) (hd : 2 ≤ d) :
    (vcgen (generatedFullProgramVCInputD (hgpXZProgram d) d (by omega)
      (hgp_nq_pos d hd) (hgp_numStab_pos d hd))).denoteSlot .ftDistance :=
  hgp_vcgen_ftDistanceD d hd (hgp_nq_pos d hd) (hgp_numStab_pos d hd)

/--
info: 'QStab.QClifford.Compile.hgpXZ_vcgen_ftDistanceD' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hgpXZ_vcgen_ftDistanceD

-- Regression guards (axiom pins) for the slot headliners.
/--
info: 'QStab.QClifford.Compile.hgp_coverage' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hgp_coverage

/--
info: 'QStab.QClifford.Compile.hgpNZ_ftDistance' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hgpNZ_ftDistance

/--
info: 'QStab.QClifford.Compile.hgp_vcgen_ftDistanceD' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hgp_vcgen_ftDistanceD

end QStab.QClifford.Compile
