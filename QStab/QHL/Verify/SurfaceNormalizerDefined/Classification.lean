import QStab.QHL.Verify.SurfaceNormalizerDefined.ZMirror

/-!
# Normalizer sub-tree definedness — Classification

The per-`k` `boolCases` classification tree (`Dcore`) with the local `leaf_ctx` tactic, its
Z/col transpose, and the axiom audits of the sorry-free scaffolding.
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

set_option maxHeartbeats 1600000

/-! ## The per-`k` `boolCases` classification tree (`Dcore`)

The `cut1` head of `xNormCommuteSym` is a 5-deep `boolCases` over the cell guards
(`bulkGuard` / `cZero` / `kind` / `leftClass` / `rightClass`), bottoming out at the
six commutator leaves `commTwoAntiA` / `commPointwiseSym` (×4) / `commTwoAntiB`.
The `boolCases` structure + the five guard bool-evals are discharged here; the six
commutator-leaf `DerivWF`s are residual #2. -/

/-- The X-normalizer bundle evals `true` at every stabilizer index `x`: soundness of
the `xBundle` family derivation.  Supplies the `xBundleF` conjunct of the
`ContextHolds` each commutator leaf needs. -/
theorem xBundleHolds (D : OddSurfaceDistance) (x : Nat) (E : PartialStabilizer) :
    (xBundleF D).eval Surface.code.body (D.distance + 2) (Env.cons x Env.empty) E = some true :=
  PureFamilyDerivA.sound (xBundle D) (Env.cons x Env.empty) E
    (pfda_defined (xBundle D) (Env.cons x Env.empty) E (xBundle_WF D))

/-- Discharge a commutator leaf's `ContextHolds Γ` obligation: split `Γ` into its
conjuncts, reduce each guard conjunct from the boolCases truth already in context
(`hbulk` / `hcz` / `hkind` / …), and close the bundle conjunct with `bundleHolds`. -/
local macro "leaf_ctx " bundleHolds:term : tactic =>
  `(tactic|
    (intro A hA
     simp only [List.mem_cons, List.mem_singleton] at hA
     casesm* _ ∨ _ <;> subst_vars <;>
       first
         | exact $bundleHolds
         | simp_all [SFormula.eval, SC.closed, SC.b, STerm.eval, Term.eval]))

/-- Band-pin WF for the `cnz` pointwise leaf's bulk handler (`zhBulkByCNZ`).  Mirrors the
handler body at the `DerivWF` level: the `band ∧ col → c=0` pin (`allNatLtElim` +
`applyNatBoundNatBeta` + `mp`×2) builds `cZero2 true`, contradicting the context `c≠0`. -/
theorem zhBulkByCNZ_WF (D : OddSurfaceDistance) {Γ : List (SFormula 1)}
    {hCNZ : SFormula.Deriv Γ (cZero1 D false)}
    {hImp : SFormula.Deriv Γ (bandImpCZeroF D)}
    {rho : Env 1} {E : PartialStabilizer}
    (wCNZ : DerivWF hCNZ Surface.code.body (D.distance + 2) rho E)
    (wImp : DerivWF hImp Surface.code.body (D.distance + 2) rho E) :
    ∀ (x : Nat) (Δ' : List (SFormula 2))
        (lift : ∀ {A : SFormula 2}, SFormula.Deriv (.eqBool (logicalXColGuardAt2 D) (SC.b true)
            :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A),
        (∀ {A : SFormula 2} {h : SFormula.Deriv (.eqBool (logicalXColGuardAt2 D) (SC.b true)
            :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A},
          DerivWF h Surface.code.body (D.distance + 2) (Env.cons x rho) E →
          DerivWF (lift h) Surface.code.body (D.distance + 2) (Env.cons x rho) E) →
        ∀ {he : SFormula.Deriv Δ' (entryFlat2F D)},
          DerivWF he Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        ∀ {hc : SFormula.Deriv Δ' (.eqBool (logicalXColGuardAt2 D) (SC.b true))},
          DerivWF hc Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        ∀ {hbu : SFormula.Deriv Δ' (gBulk D true)},
          DerivWF hbu Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        ∀ {hba : SFormula.Deriv Δ' (gBand D true)},
          DerivWF hba Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        ∀ {hki : SFormula.Deriv Δ' (gKind D true)},
          DerivWF hki Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        DerivWF (zhBulkByCNZ D hCNZ hImp Δ' lift he hc hbu hba hki)
          Surface.code.body (D.distance + 2) (Env.cons x rho) E := by
  intro _ _ _ liftWF _ _whe _ whc _ _whbu _ whba _ _whki
  refine eqBoolContra_WF _ ?_ (liftWF (cw2_WF (derivWF_weakenFresh wCNZ)))
  refine derivWF_mp (derivWF_mp (derivWF_applyNatBoundNatBeta _
    (derivWF_allNatLtElim _ _ _
      (liftWF (cw2_WF (derivWF_weakenFresh wImp)))
      (liftWF (derivWF_hyp _)))) ?hcol) whba
  case hcol => exact derivWF_cast_type rfl (colGuard2_eq D) _ _ whc

/-- Band-pin WF for the `rzF` pointwise leaf's bulk handler (`zhXbulkByRNZ`); Z mirror
of `zhBulkByCNZ_WF` under col↔row (`band ∧ row → r=0`). -/
theorem zhXbulkByRNZ_WF (D : OddSurfaceDistance) {Γ : List (SFormula 1)}
    {hRNZ : SFormula.Deriv Γ (gRZero1 D false)}
    {hImp : SFormula.Deriv Γ (bandImpRZeroF D)}
    {rho : Env 1} {E : PartialStabilizer}
    (wRNZ : DerivWF hRNZ Surface.code.body (D.distance + 2) rho E)
    (wImp : DerivWF hImp Surface.code.body (D.distance + 2) rho E) :
    ∀ (x : Nat) (Δ' : List (SFormula 2))
        (lift : ∀ {A : SFormula 2}, SFormula.Deriv (.eqBool (logicalZRowGuardAt2 D) (SC.b true)
            :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A),
        (∀ {A : SFormula 2} {h : SFormula.Deriv (.eqBool (logicalZRowGuardAt2 D) (SC.b true)
            :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A},
          DerivWF h Surface.code.body (D.distance + 2) (Env.cons x rho) E →
          DerivWF (lift h) Surface.code.body (D.distance + 2) (Env.cons x rho) E) →
        ∀ {he : SFormula.Deriv Δ' (entryFlat2F D)},
          DerivWF he Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        ∀ {hr : SFormula.Deriv Δ' (.eqBool (logicalZRowGuardAt2 D) (SC.b true))},
          DerivWF hr Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        ∀ {hbu : SFormula.Deriv Δ' (gBulk D true)},
          DerivWF hbu Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        ∀ {hba : SFormula.Deriv Δ' (gBand D true)},
          DerivWF hba Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        ∀ {hki : SFormula.Deriv Δ' (gKind D false)},
          DerivWF hki Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        DerivWF (zhXbulkByRNZ D hRNZ hImp Δ' lift he hr hbu hba hki)
          Surface.code.body (D.distance + 2) (Env.cons x rho) E := by
  intro _ _ _ liftWF _ _whe _ whr _ _whbu _ whba _ _whki
  refine eqBoolContra_WF _ ?_ (liftWF (cw2_WF (derivWF_weakenFresh wRNZ)))
  refine derivWF_mp (derivWF_mp (derivWF_applyNatBoundNatBeta _
    (derivWF_allNatLtElim _ _ _
      (liftWF (cw2_WF (derivWF_weakenFresh wImp)))
      (liftWF (derivWF_hyp _)))) ?hrow) whba
  case hrow => exact derivWF_cast_type rfl (rowGuard2_eq D) _ _ whr

set_option maxHeartbeats 1000000 in
theorem xNormScaffold_WF (D : OddSurfaceDistance) (E : PartialStabilizer) :
    DerivWFA (xNormScaffold D) Env.empty E := by
  unfold xNormScaffold xNormCommuteSym
  simp only [eq_mpr_eq_cast, id]
  refine derivWFA_cast_type rfl _ _ ?_
  refine derivWFA_allNatLtIntro _ ⟨numStab D.distance, ?_, fun x hx => ?_⟩
  · simp [SC.closed, STerm.eval, Term.eval]
  · refine derivWFA_cut1 ?_ (xBundle_WF D)
    -- the 5-deep boolCases classification tree, now via `derivWF_boolCases_cond` so each
    -- branch carries its guard's truth (`intro h…`) — exactly the `ContextHolds` the leaf needs.
    refine derivWF_boolCases_cond _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?bulkT ?bulkF
    case bulkT =>
      intro hbulk
      refine derivWF_boolCases_cond _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?czT ?czF
      case czT =>
        intro hcz
        refine derivWF_boolCases_cond _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?kindT ?kindF
        case kindT =>
          intro hkind
          exact commTwoAntiA_WF D (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _)
            (by comm_deriv_wf) (by comm_deriv_wf) (by comm_deriv_wf) (by comm_deriv_wf)
            (by comm_deriv_wf) (by comm_deriv_wf) (by comm_deriv_wf)
            (by leaf_ctx (xBundleHolds D x E))
        case kindF =>
          intro hkindF
          exact commPointwiseSym_WF D (by comm_deriv_wf) (by comm_deriv_wf)
            (by intro _ _ _ liftWF _ _whe _ _whc _ _whbu _ _whba _ whki
                exact eqBoolContra_WF _ whki (liftWF (cw2_WF (derivWF_weakenFresh (derivWF_hyp _)))))
            (by intro _ _ _ liftWF _ _whe _ _whc _ whbu _ _whtc _ _whrc _ _whlc _ _whlb
                exact eqBoolContra_WF _ (liftWF (cw2_WF (derivWF_weakenFresh (derivWF_hyp _)))) whbu)
            (by leaf_ctx (xBundleHolds D x E))
      case czF =>
        intro hcnz
        exact commPointwiseSym_WF D (by comm_deriv_wf) (by comm_deriv_wf)
          (zhBulkByCNZ_WF D (derivWF_hyp _) (by comm_deriv_wf))
          (by intro _ _ _ liftWF _ _whe _ _whc _ whbu _ _whtc _ _whrc _ _whlc _ _whlb
              exact eqBoolContra_WF _ (liftWF (cw2_WF (derivWF_weakenFresh (derivWF_hyp _)))) whbu)
          (by leaf_ctx (xBundleHolds D x E))
    case bulkF =>
      intro hbulkF
      refine derivWF_boolCases_cond _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?lcT ?lcF
      case lcT =>
        intro hlc
        refine derivWF_boolCases_cond _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?rcT ?rcF
        case rcT =>
          intro hrc
          exact commPointwiseSym_WF D (by comm_deriv_wf) (by comm_deriv_wf)
            (by intro _ _ _ liftWF _ _whe _ _whc _ whbu _ _whba _ _whki
                exact eqBoolContra_WF _ whbu (liftWF (cw2_WF (derivWF_weakenFresh (derivWF_hyp _)))))
            (by intro _ _ _ liftWF _ _whe _ _whc _ _whbu _ _whtc _ whrc _ _whlc _ _whlb
                exact eqBoolContra_WF _ (liftWF (cw2_WF (derivWF_weakenFresh (derivWF_hyp _)))) whrc)
            (by leaf_ctx (xBundleHolds D x E))
        case rcF =>
          intro hrcF
          exact commTwoAntiB_WF D (derivWF_hyp _) (by comm_deriv_wf) (derivWF_hyp _) (derivWF_hyp _)
            (by comm_deriv_wf) (by comm_deriv_wf) (by comm_deriv_wf) (by comm_deriv_wf)
            (by comm_deriv_wf) (by comm_deriv_wf) (by comm_deriv_wf)
            (by leaf_ctx (xBundleHolds D x E))
      case lcF =>
        intro hlcF
        exact commPointwiseSym_WF D (by comm_deriv_wf) (by comm_deriv_wf)
          (by intro _ _ _ liftWF _ _whe _ _whc _ whbu _ _whba _ _whki
              exact eqBoolContra_WF _ whbu (liftWF (cw2_WF (derivWF_weakenFresh (derivWF_hyp _)))))
          (by intro _ _ _ liftWF _ _whe _ _whc _ _whbu _ _whtc _ _whrc _ whlc _ _whlb
              exact eqBoolContra_WF _ whlc (liftWF (cw2_WF (derivWF_weakenFresh (derivWF_hyp _)))))
          (by leaf_ctx (xBundleHolds D x E))

/-! ## Z/col transpose

`zNormScaffold D = zNormCommuteSym D` mirrors the X version under the div↔mod /
row↔col / X↔Z swap.  The bundle and boolCases scaffolding transpose cleanly; the
residuals are the same two (`rowEntryFlatSym_WF` and the commutator leaves
`commZTwoAntiA`/`commZTwoAntiB`/`commPointwiseZSym`). -/

theorem bottomBandFalsePack_WF (D : OddSurfaceDistance) {x : Nat} {E : PartialStabilizer} :
    DerivWFA (bottomBandFalsePack D) (Env.cons x Env.empty) E := by
  unfold bottomBandFalsePack; exact nQ1ArithBoolPack_WF

theorem classZABulkXPinPack_WF (D : OddSurfaceDistance) {x : Nat} {E : PartialStabilizer} :
    DerivWFA (classZABulkXPinPack D) (Env.cons x Env.empty) E := by
  unfold classZABulkXPinPack; exact nQ1ArithBoolPack_WF

theorem classZBTopXPinPack_WF (D : OddSurfaceDistance) {x : Nat} {E : PartialStabilizer} :
    DerivWFA (classZBTopXPinPack D) (Env.cons x Env.empty) E := by
  unfold classZBTopXPinPack; exact nQ1ArithBoolPack_WF

theorem bandImpRZeroPack_WF (D : OddSurfaceDistance) {x : Nat} {E : PartialStabilizer} :
    DerivWFA (bandImpRZeroPack D) (Env.cons x Env.empty) E := by
  unfold bandImpRZeroPack; exact nQ1ArithBoolPack_WF

/-- `DerivWFA (zBundle D)`: the 13-pack conjunction (transpose of `xBundle_WF`). -/
theorem zBundle_WF (D : OddSurfaceDistance) {x : Nat} {E : PartialStabilizer} :
    DerivWFA (zBundle D) (Env.cons x Env.empty) E := by
  unfold zBundle
  exact pfdaAnd_WF (entryFlatPack_WF D)
    (pfdaAnd_WF (bottomBandFalsePack_WF D)
      (pfdaAnd_WF True.intro
        (pfdaAnd_WF True.intro
          (pfdaAnd_WF (classZABulkXPinPack_WF D)
            (pfdaAnd_WF True.intro
              (pfdaAnd_WF True.intro
                (pfdaAnd_WF (classZBTopXPinPack_WF D)
                  (pfdaAnd_WF (xEntryFlat1_WF D (qza0 D) (qza0_pure D))
                    (pfdaAnd_WF (xEntryFlat1_WF D (qza1 D) (qza1_pure D))
                      (pfdaAnd_WF (xEntryFlat1_WF D (qzb0 D) (qzb0_pure D))
                        (pfdaAnd_WF (xEntryFlat1_WF D (qzb1 D) (qzb1_pure D))
                          (bandImpRZeroPack_WF D))))))))))))

/-- The Z-normalizer bundle evals `true` at every stabilizer index `x` (transpose of
`xBundleHolds`). -/
theorem zBundleHolds (D : OddSurfaceDistance) (x : Nat) (E : PartialStabilizer) :
    (zBundleF D).eval Surface.code.body (D.distance + 2) (Env.cons x Env.empty) E = some true :=
  PureFamilyDerivA.sound (zBundle D) (Env.cons x Env.empty) E
    (pfda_defined (zBundle D) (Env.cons x Env.empty) E (zBundle_WF D))

set_option maxHeartbeats 1000000 in
theorem zNormScaffold_WF (D : OddSurfaceDistance) (E : PartialStabilizer) :
    DerivWFA (zNormScaffold D) Env.empty E := by
  unfold zNormScaffold zNormCommuteSym
  simp only [eq_mpr_eq_cast, id]
  refine derivWFA_cast_type rfl _ _ ?_
  refine derivWFA_allNatLtIntro _ ⟨numStab D.distance, ?_, fun x hx => ?_⟩
  · simp [SC.closed, STerm.eval, Term.eval]
  · refine derivWFA_cut1 ?_ (zBundle_WF D)
    -- the boolCases classification tree (transpose) via `derivWF_boolCases_cond`.
    refine derivWF_boolCases_cond _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?bulkT ?bulkF
    case bulkT =>
      intro hbulk
      refine derivWF_boolCases_cond _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?rzT ?rzF
      case rzT =>
        intro hrz
        refine derivWF_boolCases_cond _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?kindT ?kindF
        case kindT =>
          intro hkind
          exact commPointwiseZSym_WF D (by comm_deriv_wf) (by comm_deriv_wf)
            (by intro _ _ _ liftWF _ _whe _ _whr _ _whbu _ _whba _ whki
                exact eqBoolContra_WF _ (liftWF (cw2_WF (derivWF_weakenFresh (derivWF_hyp _)))) whki)
            (by intro _ _ _ liftWF _ _whe _ _whr _ whbu _ _whtc _ _whtb
                exact eqBoolContra_WF _ (liftWF (cw2_WF (derivWF_weakenFresh (derivWF_hyp _)))) whbu)
            (by leaf_ctx (zBundleHolds D x E))
        case kindF =>
          intro hkindF
          exact commZTwoAntiA_WF D (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _)
            (by comm_deriv_wf) (by comm_deriv_wf) (by comm_deriv_wf) (by comm_deriv_wf)
            (by comm_deriv_wf) (by comm_deriv_wf) (by comm_deriv_wf)
            (by leaf_ctx (zBundleHolds D x E))
      case rzF =>
        intro hrnz
        exact commPointwiseZSym_WF D (by comm_deriv_wf) (by comm_deriv_wf)
          (zhXbulkByRNZ_WF D (derivWF_hyp _) (by comm_deriv_wf))
          (by intro _ _ _ liftWF _ _whe _ _whr _ whbu _ _whtc _ _whtb
              exact eqBoolContra_WF _ (liftWF (cw2_WF (derivWF_weakenFresh (derivWF_hyp _)))) whbu)
          (by leaf_ctx (zBundleHolds D x E))
    case bulkF =>
      intro hbulkF
      refine derivWF_boolCases_cond _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?tcT ?tcF
      case tcT =>
        intro htc
        exact commZTwoAntiB_WF D (derivWF_hyp _) (derivWF_hyp _)
          (by comm_deriv_wf) (by comm_deriv_wf) (by comm_deriv_wf) (by comm_deriv_wf)
          (by comm_deriv_wf) (by comm_deriv_wf) (by comm_deriv_wf)
          (by leaf_ctx (zBundleHolds D x E))
      case tcF =>
        intro htcF
        exact commPointwiseZSym_WF D (by comm_deriv_wf) (by comm_deriv_wf)
          (by intro _ _ _ liftWF _ _whe _ _whr _ whbu _ _whba _ _whki
              exact eqBoolContra_WF _ whbu (liftWF (cw2_WF (derivWF_weakenFresh (derivWF_hyp _)))))
          (by intro _ _ _ liftWF _ _whe _ _whr _ _whbu _ whtc _ _whtb
              exact eqBoolContra_WF _ whtc (liftWF (cw2_WF (derivWF_weakenFresh (derivWF_hyp _)))))
          (by leaf_ctx (zBundleHolds D x E))

/-! ## Axiom audit of the sorry-free scaffolding

The reusable combinators and the bundle glue carry no new axioms (no `sorryAx`).
Both headline `*_WF` lemmas (`xNormScaffold_WF` / `zNormScaffold_WF`) are now
fully discharged — the commutator leaves close through `commTwoAntiA_WF` /
`commTwoAntiB_WF` / `commPointwiseSym_WF` (+ Z mirrors), the per-leaf
`ContextHolds` through `xBundleHolds` / `zBundleHolds`, and the two band-pin
handlers through `zhBulkByCNZ_WF` / `zhXbulkByRNZ_WF`.  They carry the standard
axioms only (`propext`, `Classical.choice`, `Quot.sound`); no `sorryAx`. -/

#print axioms xNormScaffold_WF
#print axioms zNormScaffold_WF
#print axioms derivWFA_cast_type
#print axioms derivWFA_allNatLtIntro
#print axioms pfdaAnd_WF
#print axioms nQ1ArithBoolPack_WF
#print axioms xEntryFlat1_WF
#print axioms entryFlatPack_WF
#print axioms xBundle_WF
#print axioms zBundle_WF

/-! ## Axiom audit of the new combinators + the keystone `m`-induction collapse

The extra `DerivWF` node combinators (`derivWF_eqPauliTrans'` etc.) are
`rfl`-transparent and carry no new axioms.  `surfaceRowEntryCharSymbolicA_WF` — the
keystone `m`-induction — has a **sorry-free body**: it reduces to `baseRowConvergeA_WF`
(BASE master) + `recRowConvergeA_WF` (REC master), the two FLAT (non-`m`-recursing)
leaf-grind residuals.  Its transitive `#print axioms` therefore shows `sorryAx` *only*
through those two masters; closing them closes the keystone with no per-level multiply. -/
#print axioms derivWF_eqPauliTrans'
#print axioms derivWF_eqPauliSymm'
#print axioms derivWF_pauliIteSelectThen'
#print axioms surfaceRowEntryCharSymbolicA_WF

/-! ## Axiom audit of the STEP 0-2 rec-side foundation (sorry-free) -/
#print axioms pureNatTerm_eval_total_allFuel
#print axioms RecEvalData.lamBody_total
#print axioms recEvalData_of_DistAtA
#print axioms RecEvalData.recOkSubst_total
#print axioms RecEvalData.instRecOkSubst_total
#print axioms recPeel_lamFD

end QHL.CodeLang.Surface.Verify
