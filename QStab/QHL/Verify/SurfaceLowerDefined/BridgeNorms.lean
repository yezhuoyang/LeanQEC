import QStab.QHL.Verify.SurfaceLowerDefined.ParityProp

/-!
# Lower bound — BridgeNorms

The bridge-factor normalisation cores: `rowBridgeFactorsNorm_WF` / `colBridgeFactorsNorm_WF`,
with the strip-product commutation `FormulaDefined`s they consume.
-/

namespace QHL.CodeLang.Surface.Verify

open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

set_option maxHeartbeats 1600000

/-- Bridge norm: `rowBridgeFactorsFromGeneratedNormalizerDeriv` WF. `impIntro_cond`(normalizesOdd) + `mp`;
`hRule` = `impIntro_cond`(fd_rowZStripProductCommutesF) + `hBridge` (structural + rowBridgeGeneratedEqF truth);
`hProd` = the `commutesStabFoldLeft` walk (stabFold FD via totality + nested child + ctx via truths). -/
theorem rowBridgeFactorsNorm_WF (D : OddSurfaceDistance) {E : PartialStabilizer}
    (hTotal : TotalUpTo (nQubits D.distance) E) :
    DerivWF (rowBridgeFactorsFromGeneratedNormalizerDeriv D) Surface.code.body
      (bridgeProofFuel D) Env.empty E := by
  unfold rowBridgeFactorsFromGeneratedNormalizerDeriv
  refine derivWF_impIntro_cond (formulaDefined_normalizesOdd D hTotal) (fun hgNorm => ?_)
  refine derivWF_mp ?hRule ?hProd
  case hRule =>
    refine derivWF_impIntro_cond (fd_rowZStripProductCommutesF D hTotal) (fun hgProd => ?_)
    refine derivWF_allNatLtIntroBounded _ _
      ⟨D.distance - 1, scn_eval _ _ _ _ _, fun idx hidx => ⟨?bodyB, ?ctxB⟩⟩
    case bodyB =>
      -- commutesOfEqLeft ⟨eqStabSymm hEq, hProd⟩ — both structural (all True leaves).
      exact ⟨⟨True.intro, True.intro⟩, ⟨True.intro, True.intro⟩⟩
    case ctxB =>
      intro A hA
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl
      · exact rowBridgeGeneratedEqF_holds D E
      · exact hgProd
  case hProd =>
    refine derivWF_allNatLtIntroBounded _ _
      ⟨D.distance - 1, scn_eval _ _ _ _ _, fun idx hidx => ⟨?bodyP, ?ctxP⟩⟩
    case bodyP =>
      refine ⟨?childP, ?fdP⟩
      case fdP =>
        exact commutesUpTo_stabFold_FD D hTotal (stripWidth D.distance)
          (fun i q => surfaceCellPauli D.distance (stripIndexVal D.distance idx i) q) idx
          (scn_eval _ _ _ _ _)
          (stabFoldEval_total Surface.code.body (bridgeProofFuel D) E (rowStripBody D)
            (stripWidth D.distance) idx
            (fun iv q => surfaceCellPauli D.distance (stripIndexVal D.distance idx iv) q)
            (fun iv => rowStripBody_eval D E idx iv))
      case childP =>
        refine derivWF_allNatLtIntroBounded _ _
          ⟨stripWidth D.distance, scn_eval _ _ _ _ _, fun jdx hjdx => ⟨?bodyS, ?ctxS⟩⟩
        case bodyS =>
          -- body = `simpa … using hNorm`; hNorm = applyNatSubstitutionBetaElim + allNatLtElim +
          -- weakenFresh/weakenContext + hyp/assumption, with the inner `slotLt` simpa-cast.
          simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
          refine derivWF_cast_type rfl (by simp [
            rowZStripIndex, Formula.codeRow,
            
            STerm.lift, STerm.weaken, Term.lift,
            Term.weaken, Term.weakenVar, SC.n, SC.bound, rowVar1, 
            colVar]) _ _
            (derivWF_cast_type rfl (by simp [
              rowZStripIndex, Formula.codeRow,
              SFormula.instantiateTopNat, SFormula.instantiateNatAt, SFormula.lift, 
              STerm.instantiateNatAt, STerm.lift, STerm.weaken, Term.instantiateNatAt, Term.lift,
              Term.weaken, Term.weakenVar, SC.n, SC.bound, rowVar1, leftRowVar2,
              rightRowVar2]) _ _ ?_)
          -- DerivWF (applyNatSubstitutionBetaElim … child) = DerivWF child (structural clause); whnf past it.
          refine derivWF_allNatLtElim _ _ _ ?hfN ?hltN
          case hfN =>
            refine derivWF_weakenContext _ ?_
            refine derivWF_weakenFresh ?_
            exact derivWF_hyp _
          case hltN =>
            refine derivWF_applyNatBoundNatBeta _ ?_
            refine derivWF_allNatLtElim _ _ _ ?hfR ?hltR
            case hfR =>
              refine derivWF_weakenContext _ ?_
              refine derivWF_weakenFresh ?_
              refine derivWF_applyNatBoundNatBeta _ ?_
              refine derivWF_allNatLtElim _ _ _ (derivWF_hyp _) True.intro
            case hltR =>
              -- slotLt reduces to the bounded-`<` witness hypothesis directly.
              exact derivWF_hyp _
        case ctxS =>
          exact contextHolds_boundNatLt_cons Surface.code.body (bridgeProofFuel D)
            (SC.n (D.distance - 1)) Env.empty E
            [OpenStab.normalizesOddF D, rowZStripIndexInRangeF D] idx (D.distance - 1)
            (scn_eval _ _ _ _ _) hidx
            (fun A hA => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
              rcases hA with rfl | rfl
              · exact hgNorm
              · exact rowZStripIndexInRange_holds D E)
    case ctxP =>
      intro A hA
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl
      · exact hgNorm
      · exact rowZStripIndexInRange_holds D E

/-- Column dual of `fd_rowZStripProductCommutesF`. -/
theorem fd_colXStripProductCommutesF (D : OddSurfaceDistance) {E : PartialStabilizer}
    (hTotal : TotalUpTo (nQubits D.distance) E) :
    SFormula.Deriv.FormulaDefined Surface.code.body (bridgeProofFuel D) Env.empty E
      (colXStripProductCommutesF D) := by
  refine formulaDefined_allNatLt _ _ (scn_eval _ _ _ _ _) (fun col hcol => ?_)
  refine commutesUpTo_stabFold_FD D hTotal (stripWidth D.distance)
    (fun i q => surfaceCellPauli D.distance (colStripIndexVal D.distance col i) q) col
    (by rw [sterm_eval_weaken_top]; exact scn_eval _ _ _ _ _) ?_
  have hfold := stabFoldEval_total Surface.code.body (bridgeProofFuel D) E (colStripBody D)
    (stripWidth D.distance) col
    (fun iv q => surfaceCellPauli D.distance (colStripIndexVal D.distance col iv) q)
    (fun iv => colStripBody_eval D E col iv)
  simpa [colXStripProduct, colStripBody, SC.n] using hfold

/-- Column dual of `rowBridgeFactorsNorm_WF`. -/
theorem colBridgeFactorsNorm_WF (D : OddSurfaceDistance) {E : PartialStabilizer}
    (hTotal : TotalUpTo (nQubits D.distance) E) :
    DerivWF (colBridgeFactorsFromGeneratedNormalizerDeriv D) Surface.code.body
      (bridgeProofFuel D) Env.empty E := by
  unfold colBridgeFactorsFromGeneratedNormalizerDeriv
  refine derivWF_impIntro_cond (formulaDefined_normalizesOdd D hTotal) (fun hgNorm => ?_)
  refine derivWF_mp ?hRule ?hProd
  case hRule =>
    refine derivWF_impIntro_cond (fd_colXStripProductCommutesF D hTotal) (fun hgProd => ?_)
    refine derivWF_allNatLtIntroBounded _ _
      ⟨D.distance - 1, scn_eval _ _ _ _ _, fun idx hidx => ⟨?bodyB, ?ctxB⟩⟩
    case bodyB =>
      exact ⟨⟨True.intro, True.intro⟩, ⟨True.intro, True.intro⟩⟩
    case ctxB =>
      intro A hA
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl
      · exact colBridgeGeneratedEqF_holds D E
      · exact hgProd
  case hProd =>
    refine derivWF_allNatLtIntroBounded _ _
      ⟨D.distance - 1, scn_eval _ _ _ _ _, fun idx hidx => ⟨?bodyP, ?ctxP⟩⟩
    case bodyP =>
      refine ⟨?childP, ?fdP⟩
      case fdP =>
        exact commutesUpTo_stabFold_FD D hTotal (stripWidth D.distance)
          (fun i q => surfaceCellPauli D.distance (colStripIndexVal D.distance idx i) q) idx
          (scn_eval _ _ _ _ _)
          (stabFoldEval_total Surface.code.body (bridgeProofFuel D) E (colStripBody D)
            (stripWidth D.distance) idx
            (fun iv q => surfaceCellPauli D.distance (colStripIndexVal D.distance idx iv) q)
            (fun iv => colStripBody_eval D E idx iv))
      case childP =>
        refine derivWF_allNatLtIntroBounded _ _
          ⟨stripWidth D.distance, scn_eval _ _ _ _ _, fun jdx hjdx => ⟨?bodyS, ?ctxS⟩⟩
        case bodyS =>
          simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
          refine derivWF_cast_type rfl (by simp [
            colXStripIndex, Formula.codeRow,
            
            STerm.lift, STerm.weaken, Term.lift,
            Term.weaken, Term.weakenVar, SC.n, SC.bound, rowVar1, 
            colVar]) _ _
            (derivWF_cast_type rfl (by simp [
              colXStripIndex, Formula.codeRow,
              SFormula.instantiateTopNat, SFormula.instantiateNatAt, SFormula.lift, 
              STerm.instantiateNatAt, STerm.lift, STerm.weaken, Term.instantiateNatAt, Term.lift,
              Term.weaken, Term.weakenVar, SC.n, SC.bound, rowVar1, leftRowVar2,
              rightRowVar2]) _ _ ?_)
          refine derivWF_allNatLtElim _ _ _ ?hfN ?hltN
          case hfN =>
            refine derivWF_weakenContext _ ?_
            refine derivWF_weakenFresh ?_
            exact derivWF_hyp _
          case hltN =>
            refine derivWF_applyNatBoundNatBeta _ ?_
            refine derivWF_allNatLtElim _ _ _ ?hfR ?hltR
            case hfR =>
              refine derivWF_weakenContext _ ?_
              refine derivWF_weakenFresh ?_
              refine derivWF_applyNatBoundNatBeta _ ?_
              refine derivWF_allNatLtElim _ _ _ (derivWF_hyp _) True.intro
            case hltR =>
              -- slotLt reduces to the bounded-`<` witness hypothesis directly.
              exact derivWF_hyp _
        case ctxS =>
          exact contextHolds_boundNatLt_cons Surface.code.body (bridgeProofFuel D)
            (SC.n (D.distance - 1)) Env.empty E
            [OpenStab.normalizesOddF D, colXStripIndexInRangeF D] idx (D.distance - 1)
            (scn_eval _ _ _ _ _) hidx
            (fun A hA => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
              rcases hA with rfl | rfl
              · exact hgNorm
              · exact colXStripIndexInRange_holds D E)
    case ctxP =>
      intro A hA
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl
      · exact hgNorm
      · exact colXStripIndexInRange_holds D E

-- ARCHITECTURAL NOTE (core 4-6 sub-derivs): `xRowsOccupiedFromGeometryContextDeriv` and its siblings
-- CANNOT be proven as standalone `Env.empty`-WF helpers.  Their root `allNatLtIntroBounded` carries
-- `ContextHolds (boundNatLt n :: Γ.map weaken)` (CodeStabBinder:3577) with Γ = the family-rule context
-- [rowCutNoX, rowCutTelescoping, rowBridgeFactorsCommute, xNontrivial].  Of these: `boundNatLt` ⟵ the
-- bound `hrow`; `rowBridgeFactorsCommute` + `xNontrivial` are the impIntro guards of the *enclosing* core
-- (so they hold only inside `derivWF_impIntro_cond`, conditionally); `rowCutNoX` + `rowCutTelescoping` are
-- geometric truths needing soundness lemmas.  Hence cores 4-6 must be proven HOLISTICALLY: walk the core
-- with `derivWF_impIntro_cond` (guards ⟹ 2 rules), and discharge `ContextHolds` from the guards + the two
-- soundness facts.  `comm_deriv_wf` only stops at the first `allNatLtIntroBounded` — the body still needs a
-- manual walk of the notIntro/notElim/noncommutes* constructors + the FD `gridRowNoX` leaf.

end QHL.CodeLang.Surface.Verify
