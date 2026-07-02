import QStab.QHL.Verify.SurfaceNormalizerDefined
import QStab.QHL.Verify.SurfaceRowsCommute

/-!
# Rows-commute definedness — Leaves

Leaf-layer well-formedness: the kernel `pauliNeqLit` leaf, reusable leaf-totality
helpers, the flat-entry pack WFs (reducing to `rowEntryFlatSym_WF`), and the leaf-layer WFs.
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

set_option maxHeartbeats 1600000


/-- Kernel WF rule: the closed `pauliNeqLit` leaf has no definedness obligations. -/
theorem derivWF_pauliNeqLit {arity : Nat} {Γ : List (SFormula arity)} (p q : Pauli)
    (h : decide (p = q) = false)
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer} :
    DerivWF (SFormula.Deriv.pauliNeqLit (Γ := Γ) p q h) cb fuel rho E := trivial

/-! ## Reusable leaf totality helpers -/

/-- Purity of the arity-3 distance term `dP3 D = lift0 (dP2 D)`. -/
def dP3_pure (D : OddSurfaceDistance) : SFormula.PureNatTerm (dP3 D) := by
  unfold dP3 dP2
  repeat (first | exact SFormula.PureNatTerm.lift _ | exact SFormula.PureNatTerm.natLit _ | constructor)

/-- `FormulaDefined` of `anticommutes (baseLeafTreeTA …) (lit)` — generic in fuel/rho. -/
theorem fd_anti_leaf (D : OddSurfaceDistance) {kT : Term 3 .nat} (hk : SFormula.PureNatTerm kT)
    (pl : Pauli) (bv : Bool) {fuel : Nat} {rho : Env 3} {E : PartialStabilizer} :
    SFormula.Deriv.FormulaDefined Surface.code.body fuel rho E
      (.eqBool (.anticommutes (SC.closed (baseLeafTreeTA (dP3 D) kT qP3)) (SC.p pl)) (SC.b bv)) :=
  formulaDefined_eqBool
    (sterm_eval_anticommutes (sterm_eval_closed (baseLeafTreeTA_eval_total (dP3_pure D) hk (.var _) _ _ _))
      (sterm_eval_p _)) (sterm_eval_b _)

/-! ## Flat-entry pack WFs (reduce to the existing rowEntryFlatSym_WF) -/

theorem entryAFlat_WF (D : OddSurfaceDistance) {rho : Env 3} {E : PartialStabilizer} :
    DerivWFA (entryAFlat D) rho E := by
  unfold entryAFlat
  exact rowEntryFlatSym_WF D.index (distP3 D) k1P3 qP3 (.var _) (.var _) rho E
    (by simp only [OddSurfaceDistance.distance, oddDistance]; omega)

theorem entryBFlat_WF (D : OddSurfaceDistance) {rho : Env 3} {E : PartialStabilizer} :
    DerivWFA (entryBFlat D) rho E := by
  unfold entryBFlat
  exact rowEntryFlatSym_WF D.index (distP3 D) k2P3 qP3 (.var _) (.var _) rho E
    (by simp only [OddSurfaceDistance.distance, oddDistance]; omega)

theorem entryAQuantPack_WF (D : OddSurfaceDistance) {rho : Env 2} {E : PartialStabilizer} :
    DerivWFA (entryAQuantPack D) rho E := by
  unfold entryAQuantPack
  refine derivWFA_allNatLtIntro _ ⟨nQubits D.distance, ?_, fun x _ => entryAFlat_WF D⟩
  simp [nP2, SC.closed, STerm.eval, Term.eval, Term.lift]

theorem entryBQuantPack_WF (D : OddSurfaceDistance) {rho : Env 2} {E : PartialStabilizer} :
    DerivWFA (entryBQuantPack D) rho E := by
  unfold entryBQuantPack
  refine derivWFA_allNatLtIntro _ ⟨nQubits D.distance, ?_, fun x _ => entryBFlat_WF D⟩
  simp [nP2, SC.closed, STerm.eval, Term.eval, Term.lift]

/-- The type-exclusion packs are `arithBool` leaves ⟹ `DerivWFA = True`. -/
theorem typeExclPackK1_WF (D : OddSurfaceDistance) {rho : Env 2} {E : PartialStabilizer} :
    DerivWFA (typeExclPackK1 D) rho E := True.intro

theorem typeExclPackK2_WF (D : OddSurfaceDistance) {rho : Env 2} {E : PartialStabilizer} :
    DerivWFA (typeExclPackK2 D) rho E := True.intro

/-- `DerivWFA` of `pfdaAnd2` from the two conjuncts (the `andIntro` core is trivial). -/
theorem pfdaAnd2_WF {D : OddSurfaceDistance} {A B : SFormula 2}
    {hA : PureFamilyDerivA Surface.code.body (D.distance + 2) A}
    {hB : PureFamilyDerivA Surface.code.body (D.distance + 2) B}
    {rho : Env 2} {E : PartialStabilizer}
    (wA : DerivWFA hA rho E) (wB : DerivWFA hB rho E) :
    DerivWFA (pfdaAnd2 (D := D) hA hB) rho E := by
  unfold pfdaAnd2
  exact derivWFA_cut2 (by comm_deriv_wf) wA wB

theorem pairBundle_WF (D : OddSurfaceDistance) {rho : Env 2} {E : PartialStabilizer} :
    DerivWFA (pairBundle D) rho E := by
  unfold pairBundle
  exact pfdaAnd2_WF (entryAQuantPack_WF D) (pfdaAnd2_WF (entryBQuantPack_WF D)
    (pfdaAnd2_WF (typeExclPackK1_WF D) (typeExclPackK2_WF D)))

/-- The pair bundle evals `true` at every `(k1,k2)` (soundness of `pairBundle`). -/
theorem pairBundleHolds (D : OddSurfaceDistance) (rho : Env 2) (E : PartialStabilizer) :
    (pairBundleF D).eval Surface.code.body (D.distance + 2) rho E = some true :=
  PureFamilyDerivA.sound (pairBundle D) rho E
    (pfda_defined (pairBundle D) rho E (pairBundle_WF D))

/-- Kernel WF rule: `applyNatSubstitutionBetaElim`'s obligations = the child's. -/
theorem derivWF_applyNatSubstitutionBetaElim {arity : Nat} {Γ : List (SFormula arity)}
    {x : Term arity .nat} {A : SFormula (arity + 1)} {hx : SFormula.PureNatTerm x}
    {child : SFormula.Deriv Γ (.applyNat (SC.closed x) A)}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (hchild : DerivWF child cb fuel rho E) :
    DerivWF (SFormula.Deriv.applyNatSubstitutionBetaElim x A hx child) cb fuel rho E := hchild

/-- Kernel WF rule: `commutesSymm`'s obligations = the child's. -/
theorem derivWF_commutesSymm {arity : Nat} {Γ : List (SFormula arity)}
    {n : STerm arity .nat} {A B : STerm arity .stab}
    {child : SFormula.Deriv Γ (.commutesUpTo n A B)}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (hchild : DerivWF child cb fuel rho E) :
    DerivWF (SFormula.Deriv.commutesSymm n A B child) cb fuel rho E := hchild

/-- Arity-generic `pfdaAndG` WFA (mirror of `pfdaAnd2_WF`). -/
theorem pfdaAndG_WF {D : OddSurfaceDistance} {arity : Nat} {A B : SFormula arity}
    {hA : PureFamilyDerivA Surface.code.body (D.distance + 2) A}
    {hB : PureFamilyDerivA Surface.code.body (D.distance + 2) B}
    {rho : Env arity} {E : PartialStabilizer}
    (wA : DerivWFA hA rho E) (wB : DerivWFA hB rho E) :
    DerivWFA (pfdaAndG (D := D) hA hB) rho E := by
  unfold pfdaAndG
  exact derivWFA_cut2 (by comm_deriv_wf) wA wB

/-! ## Leaf layer WFs -/

/-- `antiP_WF`: the literal anticommutation fact is WF (pauliAnticommutesLit). -/
theorem antiP_WF {Δ : List (SFormula 3)} (p1 p2 : Pauli)
    (h : ErrorVec.Pauli.anticommutes p1 p2 = false)
    {fuel : Nat} {rho : Env 3} {E : PartialStabilizer} :
    DerivWF (antiP (Δ := Δ) p1 p2 h) Surface.code.body fuel rho E := by
  unfold antiP
  exact derivWF_cast_type rfl (by rw [h]) _ _ (derivWF_pauliAnticommutesLit _ _)

theorem entryAAtBound_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)}
    {hW : SFormula.Deriv Δ (entryAQuant D).weaken}
    {hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken)}
    {fuel : Nat} {rho : Env 3} {E : PartialStabilizer}
    (wW : DerivWF hW Surface.code.body fuel rho E)
    (wq : DerivWF hq Surface.code.body fuel rho E) :
    DerivWF (entryAAtBound D hW hq) Surface.code.body fuel rho E := by
  unfold entryAAtBound
  exact derivWF_applyNatBoundNatBeta _ (derivWF_allNatLtElim _ _ _ wW wq)

theorem entryBAtBound_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)}
    {hW : SFormula.Deriv Δ (entryBQuant D).weaken}
    {hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken)}
    {fuel : Nat} {rho : Env 3} {E : PartialStabilizer}
    (wW : DerivWF hW Surface.code.body fuel rho E)
    (wq : DerivWF hq Surface.code.body fuel rho E) :
    DerivWF (entryBAtBound D hW hq) Surface.code.body fuel rho E := by
  unfold entryBAtBound
  exact derivWF_applyNatBoundNatBeta _ (derivWF_allNatLtElim _ _ _ wW wq)

/-- `leafNotPandZ_WF`: generic in fuel/rho (only baseLeafTreeTA leaves). -/
theorem leafNotPandZ_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)} {C : SFormula 3}
    {kT : Term 3 .nat} (hkP : SFormula.PureNatTerm kT) (p : Pauli)
    (hpX : ErrorVec.Pauli.anticommutes p Pauli.X = false)
    {hP : SFormula.Deriv Δ (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) kT qP3)) (SC.p p))}
    {hZ : SFormula.Deriv Δ (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) kT qP3)) (SC.p Pauli.Z))}
    {fuel : Nat} {rho : Env 3} {E : PartialStabilizer}
    (wP : DerivWF hP Surface.code.body fuel rho E)
    (wZ : DerivWF hZ Surface.code.body fuel rho E) :
    DerivWF (leafNotPandZ (C := C) D kT p hpX hP hZ) Surface.code.body fuel rho E := by
  unfold leafNotPandZ
  refine eqBoolContra_WF _ ?_ ?_
  · exact derivWF_anticommutesTransport _ _ _ _ _ wZ (derivWF_pauliEqLit' _)
      (derivWF_pauliAnticommutesLit _ _) (fd_anti_leaf D hkP _ _)
  · exact derivWF_anticommutesTransport _ _ _ _ _ wP (derivWF_pauliEqLit' _)
      (antiP_WF _ _ _) (fd_anti_leaf D hkP _ _)

/-- `leafNotPandX_WF`: dual of `leafNotPandZ_WF` (reference `Z`). -/
theorem leafNotPandX_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)} {C : SFormula 3}
    {kT : Term 3 .nat} (hkP : SFormula.PureNatTerm kT) (p : Pauli)
    (hpZ : ErrorVec.Pauli.anticommutes p Pauli.Z = false)
    {hP : SFormula.Deriv Δ (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) kT qP3)) (SC.p p))}
    {hX : SFormula.Deriv Δ (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) kT qP3)) (SC.p Pauli.X))}
    {fuel : Nat} {rho : Env 3} {E : PartialStabilizer}
    (wP : DerivWF hP Surface.code.body fuel rho E)
    (wX : DerivWF hX Surface.code.body fuel rho E) :
    DerivWF (leafNotPandX (C := C) D kT p hpZ hP hX) Surface.code.body fuel rho E := by
  unfold leafNotPandX
  refine eqBoolContra_WF _ ?_ ?_
  · exact derivWF_anticommutesTransport _ _ _ _ _ wX (derivWF_pauliEqLit' _)
      (derivWF_pauliAnticommutesLit _ _) (fd_anti_leaf D hkP _ _)
  · exact derivWF_anticommutesTransport _ _ _ _ _ wP (derivWF_pauliEqLit' _)
      (antiP_WF _ _ _) (fd_anti_leaf D hkP _ _)

/-- `lcFromLeftI_WF`: row-A leaf `I` ⟹ commute.  Needs the rowA stabilizer eval. -/
theorem lcFromLeftI_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)}
    {hEntryA : SFormula.Deriv Δ (entryAF D)}
    {hLeafA : SFormula.Deriv Δ (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3)) (SC.p Pauli.I))}
    {fuel : Nat} {rho : Env 3} {E : PartialStabilizer}
    (wEntryA : DerivWF hEntryA Surface.code.body fuel rho E)
    (wLeafA : DerivWF hLeafA Surface.code.body fuel rho E)
    (hAe : ∃ v, (STerm.stabAt (rowA D).weaken SFormula.boundNat).eval Surface.code.body fuel rho E = some v)
    (hBe : ∃ v, (STerm.stabAt (rowB D).weaken SFormula.boundNat).eval Surface.code.body fuel rho E = some v) :
    DerivWF (lcFromLeftI D hEntryA hLeafA) Surface.code.body fuel rho E := by
  unfold lcFromLeftI
  refine derivWF_localCommutesOfLeftI _ _ _ ?_ (formulaDefined_localCommutesAt hAe hBe)
  simp only [eq_mpr_eq_cast]
  exact derivWF_eqPauliTrans' wEntryA wLeafA

theorem lcFromRightI_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)}
    {hEntryB : SFormula.Deriv Δ (entryBF D)}
    {hLeafB : SFormula.Deriv Δ (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p Pauli.I))}
    {fuel : Nat} {rho : Env 3} {E : PartialStabilizer}
    (wEntryB : DerivWF hEntryB Surface.code.body fuel rho E)
    (wLeafB : DerivWF hLeafB Surface.code.body fuel rho E)
    (hAe : ∃ v, (STerm.stabAt (rowA D).weaken SFormula.boundNat).eval Surface.code.body fuel rho E = some v)
    (hBe : ∃ v, (STerm.stabAt (rowB D).weaken SFormula.boundNat).eval Surface.code.body fuel rho E = some v) :
    DerivWF (lcFromRightI D hEntryB hLeafB) Surface.code.body fuel rho E := by
  unfold lcFromRightI
  refine derivWF_localCommutesOfRightI _ _ _ ?_ (formulaDefined_localCommutesAt hAe hBe)
  simp only [eq_mpr_eq_cast]
  exact derivWF_eqPauliTrans' wEntryB wLeafB

/-- `lcFromTwoLeaves_WF`: both leaves resolved, anticommute false ⟹ commute. -/
theorem lcFromTwoLeaves_WF (D : OddSurfaceDistance) (pa pb : Pauli) {Δ : List (SFormula 3)}
    {hEntryA : SFormula.Deriv Δ (entryAF D)}
    {hLeafA : SFormula.Deriv Δ (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3)) (SC.p pa))}
    {hEntryB : SFormula.Deriv Δ (entryBF D)}
    {hLeafB : SFormula.Deriv Δ (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p pb))}
    {hAnti : SFormula.Deriv Δ (.eqBool (.anticommutes (SC.p pb) (SC.p pa)) (SC.b false))}
    {fuel : Nat} {rho : Env 3} {E : PartialStabilizer}
    (wEntryA : DerivWF hEntryA Surface.code.body fuel rho E)
    (wLeafA : DerivWF hLeafA Surface.code.body fuel rho E)
    (wEntryB : DerivWF hEntryB Surface.code.body fuel rho E)
    (wLeafB : DerivWF hLeafB Surface.code.body fuel rho E)
    (wAnti : DerivWF hAnti Surface.code.body fuel rho E)
    (hAe : ∃ v, (STerm.stabAt (rowA D).weaken SFormula.boundNat).eval Surface.code.body fuel rho E = some v)
    (hBe : ∃ v, (STerm.stabAt (rowB D).weaken SFormula.boundNat).eval Surface.code.body fuel rho E = some v) :
    DerivWF (lcFromTwoLeaves D pa pb hEntryA hLeafA hEntryB hLeafB hAnti) Surface.code.body fuel rho E := by
  unfold lcFromTwoLeaves
  refine derivWF_localCommutesOfLeftEqNoAntiRight _ _ _ _ ?_ ?_ (formulaDefined_localCommutesAt hAe hBe)
  · simp only [eq_mpr_eq_cast]; exact derivWF_eqPauliTrans' wEntryA wLeafA
  · refine derivWF_eqBoolFalseNotTrue (derivWF_anticommutesTransport _ _ _ _ _ ?_ (derivWF_pauliEqLit' _) wAnti ?_)
    · simp only [eq_mpr_eq_cast]; exact derivWF_eqPauliTrans' wEntryB wLeafB
    · exact formulaDefined_eqBool (sterm_eval_anticommutes hBe (sterm_eval_p _)) (sterm_eval_b _)

end QHL.CodeLang.Surface.Verify
