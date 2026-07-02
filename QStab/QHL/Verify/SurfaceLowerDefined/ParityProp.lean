import QStab.QHL.Verify.SurfaceLowerDefined.LogicalOp

/-!
# Lower bound — ParityProp

The parity-propagation cores (cores 4/4'): `xParityPropRowsCore_WF` and its Z-dual
`zParityPropColsCore_WF` — the geometric walk that propagates the anticommutation into
every row / column.
-/

namespace QHL.CodeLang.Surface.Verify

open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

set_option maxHeartbeats 1600000

/-- Core 4 (holistic): `xParityPropagationRowsFromBridgeFactorsDeriv` WF. -/
theorem xParityPropRowsCore_WF (D : OddSurfaceDistance) {E : PartialStabilizer}
    (hTotal : TotalUpTo (nQubits D.distance) E) :
    DerivWF (xParityPropagationRowsFromBridgeFactorsDeriv D) Surface.code.body
      (bridgeProofFuel D) Env.empty E := by
  unfold xParityPropagationRowsFromBridgeFactorsDeriv
  refine derivWF_impIntro_cond
    (formulaDefined_and (formulaDefined_normalizesOdd D hTotal)
      (formulaDefined_anticommutesLogicalZ D hTotal))
    (fun hgX => ?_)
  -- body = mp (impIntro hRows) hBridge; hBridge = mp (hyp) (andElimLeft assumption) is trivial
  refine derivWF_mp (derivWF_impIntro_cond (formulaDefined_rowBridgeFactorsCommute D hTotal)
    (fun hgRB => ?_)) ⟨trivial, trivial⟩
  -- DerivWF hRows = DerivWF (weakenBy (weakenBy xRowsOccupied)) = DerivWF xRowsOccupied (defeq)
  show DerivWF (xRowsOccupiedFromGeometryContextDeriv D) Surface.code.body
    (bridgeProofFuel D) Env.empty E
  unfold xRowsOccupiedFromGeometryContextDeriv
  refine derivWF_allNatLtIntroBounded _ _
    ⟨D.distance, scn_eval _ _ _ _ _, fun row hrow => ⟨?body, ?ctx⟩⟩
  case body =>
    comm_deriv_wf
    · -- FD gridRowNoX (same as rowCutNoX_WF's fdGuard, with x↦row): cell qubit d*row+y < nQubits
      refine formulaDefined_allNatLt _ _ (scn_eval _ _ _ _ _) (fun y hy => ?_)
      refine formulaDefined_not (formulaDefined_eqBool
        (sterm_eval_anticommutes ?_ (sterm_eval_p Pauli.Z)) (sterm_eval_b true))
      obtain ⟨p, hp⟩ := hTotal (D.distance * row + y)
        (by have := NatArithmetic.gridIdxLeft_lt_square hrow hy; simpa [nQubits] using this)
      exact ⟨p, by
        simp [SC.bound, SC.gridIdx, NatArithmetic.gridIdxLeft, STerm.eval,
          STerm.weaken, STerm.lift, Term.eval, Term.weaken, Term.lift,
          Term.weakenVar, rowVar1, Env.cons, hp]⟩
    · refine derivWF_notElim ?pos ?neg
      case pos =>
        show DerivWF (rowBridgePrefixProductCommutesDeriv D) Surface.code.body
          (bridgeProofFuel D) (Env.cons row Env.empty) E
        unfold rowBridgePrefixProductCommutesDeriv
        refine ⟨?child, ?fd⟩
        case fd =>
          -- FD-stabFold, closed by the totality machinery (stabFoldEval_boundNat + fold totality).
          exact formulaDefined_commutesUpTo
            (Av := partialStabilizerFold row (fun i => fun q => some (tRow D.distance i q)))
            (Bv := E)
            (scn_eval _ _ _ _ _)
            (stabFoldEval_boundNat Surface.code.body (bridgeProofFuel D) E
              (OpenStab.rowBridge D.distance rightRowVar2) row
              (fun i q => tRow D.distance i q) (fun i => rowBridge_fold_eval D E row i))
            (by simp [SC.bound, STerm.eval, STerm.weaken, STerm.lift])
            (stabTotalUpTo_partialStabilizerFold _ _ _)
            (StabTotalUpTo_of_TotalUpTo hTotal)
        case child =>
          unfold rowBridgePrefixFactorsCommuteDeriv
          refine derivWF_allNatLtIntroBounded _ _
            ⟨row, ?bnEval, fun idx hidx => ⟨?bodyI, ?ctxI⟩⟩
          case bnEval => simp [SFormula.boundNat, SC.closed, STerm.eval, Term.eval, Env.cons]
          case bodyI => comm_deriv_wf; exact ⟨trivial, trivial⟩
          case ctxI =>
            exact contextHolds_boundNatLt_cons Surface.code.body (bridgeProofFuel D)
              (SC.n D.distance) Env.empty E [rowBridgeFactorsCommuteF D] row D.distance
              (scn_eval _ _ _ _ _) hrow
              (fun A hA => by simp only [List.mem_singleton] at hA; subst hA; exact hgRB)
      case neg =>
        -- noncommutesOfEqLeft ⟨eqD, noncommD⟩; noncommD = noncommutesStabMulRight ⟨left, right⟩
        refine ⟨?eqD, ?noncommD⟩
        · comm_deriv_wf
        · refine ⟨?_, ?_⟩ <;> comm_deriv_wf
  case ctx =>
    -- ContextHolds Env.empty [rowCutNoX, rowCutTelescoping, rowBridgeFactorsCommute, xNontrivial]:
    -- first two are universal truths (Deriv.sound), last two are the impIntro guards.
    intro A hA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
    rcases hA with rfl | rfl | rfl | rfl
    · exact rowCutNoXImpliesCommutes_holds D hTotal
    · exact rowCutTelescoping_holds D E
    · exact hgRB
    · exact hgX

/-- Core 4 z-dual (holistic): `zParityPropagationColsFromBridgeFactorsDeriv` WF. Exact mirror of
`xParityPropRowsCore_WF` with col/X/`colBridge`/`tCol`/`colBridge_fold_eval` substitutions; the
`gridColNoZ` cell is the transpose `d*y + col`. -/
theorem zParityPropColsCore_WF (D : OddSurfaceDistance) {E : PartialStabilizer}
    (hTotal : TotalUpTo (nQubits D.distance) E) :
    DerivWF (zParityPropagationColsFromBridgeFactorsDeriv D) Surface.code.body
      (bridgeProofFuel D) Env.empty E := by
  unfold zParityPropagationColsFromBridgeFactorsDeriv
  refine derivWF_impIntro_cond
    (formulaDefined_and (formulaDefined_normalizesOdd D hTotal)
      (formulaDefined_anticommutesLogicalX D hTotal))
    (fun hgX => ?_)
  refine derivWF_mp (derivWF_impIntro_cond (formulaDefined_colBridgeFactorsCommute D hTotal)
    (fun hgRB => ?_)) ⟨trivial, trivial⟩
  show DerivWF (zColsOccupiedFromGeometryContextDeriv D) Surface.code.body
    (bridgeProofFuel D) Env.empty E
  unfold zColsOccupiedFromGeometryContextDeriv
  refine derivWF_allNatLtIntroBounded _ _
    ⟨D.distance, scn_eval _ _ _ _ _, fun row hrow => ⟨?body, ?ctx⟩⟩
  case body =>
    comm_deriv_wf
    · -- FD gridColNoZ: cell qubit `d*y + row < nQubits` (transpose of the row case)
      refine formulaDefined_allNatLt _ _ (scn_eval _ _ _ _ _) (fun y hy => ?_)
      refine formulaDefined_not (formulaDefined_eqBool
        (sterm_eval_anticommutes ?_ (sterm_eval_p Pauli.X)) (sterm_eval_b true))
      obtain ⟨p, hp⟩ := hTotal (D.distance * y + row)
        (by have := NatArithmetic.gridIdxLeft_lt_square hy hrow; simpa [nQubits] using this)
      exact ⟨p, by
        simp [SC.bound, SC.gridIdx, NatArithmetic.gridIdxLeft, STerm.eval,
          STerm.weaken, STerm.lift, Term.eval, Term.weaken, Term.lift,
          Term.weakenVar, rowVar1, Env.cons, hp]⟩
    · refine derivWF_notElim ?pos ?neg
      case pos =>
        show DerivWF (colBridgePrefixProductCommutesDeriv D) Surface.code.body
          (bridgeProofFuel D) (Env.cons row Env.empty) E
        unfold colBridgePrefixProductCommutesDeriv
        refine ⟨?child, ?fd⟩
        case fd =>
          exact formulaDefined_commutesUpTo
            (Av := partialStabilizerFold row (fun i => fun q => some (tCol D.distance i q)))
            (Bv := E)
            (scn_eval _ _ _ _ _)
            (stabFoldEval_boundNat Surface.code.body (bridgeProofFuel D) E
              (OpenStab.colBridge D.distance rightRowVar2) row
              (fun i q => tCol D.distance i q) (fun i => colBridge_fold_eval D E row i))
            (by simp [SC.bound, STerm.eval, STerm.weaken, STerm.lift])
            (stabTotalUpTo_partialStabilizerFold _ _ _)
            (StabTotalUpTo_of_TotalUpTo hTotal)
        case child =>
          unfold colBridgePrefixFactorsCommuteDeriv
          refine derivWF_allNatLtIntroBounded _ _
            ⟨row, ?bnEval, fun idx hidx => ⟨?bodyI, ?ctxI⟩⟩
          case bnEval => simp [SFormula.boundNat, SC.closed, STerm.eval, Term.eval, Env.cons]
          case bodyI => comm_deriv_wf; exact ⟨trivial, trivial⟩
          case ctxI =>
            exact contextHolds_boundNatLt_cons Surface.code.body (bridgeProofFuel D)
              (SC.n D.distance) Env.empty E [colBridgeFactorsCommuteF D] row D.distance
              (scn_eval _ _ _ _ _) hrow
              (fun A hA => by simp only [List.mem_singleton] at hA; subst hA; exact hgRB)
      case neg =>
        refine ⟨?eqD, ?noncommD⟩
        · comm_deriv_wf
        · refine ⟨?_, ?_⟩ <;> comm_deriv_wf
  case ctx =>
    intro A hA
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
    rcases hA with rfl | rfl | rfl | rfl
    · exact colCutNoZImpliesCommutes_holds D hTotal
    · exact colCutTelescoping_holds D E
    · exact hgRB
    · exact hgX

end QHL.CodeLang.Surface.Verify
