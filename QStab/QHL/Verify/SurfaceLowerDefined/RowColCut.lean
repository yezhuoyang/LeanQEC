import QStab.QHL.Verify.SurfaceLowerDefined.Helpers

/-!
# Lower bound — RowColCut

Definedness of the row/column cut stabilizers: the cut-entry evaluations and the
`rowCutLocal`/`colCutLocal` local well-formedness, assembled into the `rowCutNoX`/
`colCutNoZ` core `DerivWF`s (cores 1-2).
-/

namespace QHL.CodeLang.Surface.Verify

open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

set_option maxHeartbeats 1600000

/-- Missing leaf combinator: `DerivWF` of `noAntiAtSubst` (the `eqD ∧ noAntiD ∧ FD`
clause).  Needed by the bridge cut-commutation sub-derivations. -/
theorem derivWF_noAntiAtSubst {arity : Nat} {Γ : List (SFormula arity)}
    (Eterm : STerm arity .stab) (p : STerm arity .pauli) (q₁ q₂ : Term arity .nat)
    (hq1 : SFormula.PureNatTerm q₁) (hq2 : SFormula.PureNatTerm q₂)
    {eqD : SFormula.Deriv Γ (.eqNat (SC.closed q₁) (SC.closed q₂))}
    {noAntiD : SFormula.Deriv Γ
      (.not (.eqBool (.anticommutes (.stabAt Eterm (SC.closed q₁)) p) (SC.b true)))}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wEqD : DerivWF eqD cb fuel rho E) (wNoAntiD : DerivWF noAntiD cb fuel rho E)
    (hFD : SFormula.Deriv.FormulaDefined cb fuel rho E
      (.not (.eqBool (.anticommutes (.stabAt Eterm (SC.closed q₂)) p) (SC.b true)))) :
    DerivWF (SFormula.Deriv.noAntiAtSubst Eterm p q₁ q₂ hq1 hq2 eqD noAntiD) cb fuel rho E :=
  ⟨wEqD, wNoAntiD, hFD⟩

/-- The row cut stabilizer (`stabLam (ite (q/d = row) Z I)`) evaluates totally at `boundNat`. -/
theorem rowZCut_boundNat_eval (D : OddSurfaceDistance) {fuel : Nat} {rho : Env 2}
    {E : PartialStabilizer} :
    ∃ v, (STerm.stabAt ((SC.rowZCut D.distance rowVar1).weaken) SFormula.boundNat).eval
      Surface.code.body fuel rho E = some v := by
  refine ⟨if rho 0 / D.distance = rho 1 then Pauli.Z else Pauli.I, ?_⟩
  simp [SC.rowZCut, SC.closed, STerm.weaken, STerm.lift, STerm.eval, Term.eval,
    Term.lift, Term.weaken, Term.weakenVar, Env.cons, bind, Option.bind,
    rowVar1, SFormula.boundNat]
  split <;> rfl

/-- The column cut stabilizer evaluates totally at `boundNat` (dual). -/
theorem colXCut_boundNat_eval (D : OddSurfaceDistance) {fuel : Nat} {rho : Env 2}
    {E : PartialStabilizer} :
    ∃ v, (STerm.stabAt ((SC.colXCut D.distance rowVar1).weaken) SFormula.boundNat).eval
      Surface.code.body fuel rho E = some v := by
  refine ⟨if rho 0 % D.distance = rho 1 then Pauli.X else Pauli.I, ?_⟩
  simp [SC.colXCut, SC.closed, STerm.weaken, STerm.lift, STerm.eval, Term.eval,
    Term.lift, Term.weaken, Term.weakenVar, Env.cons, bind, Option.bind,
    rowVar1, SFormula.boundNat]
  split <;> rfl

/-- The `stabLam(ite (rowCutQubitCond) Z I)` entry leaf evaluates totally at `colVar`. -/
theorem rowCutEntry_eval (D : OddSurfaceDistance) {fuel : Nat} {rho : Env 2}
    {E : PartialStabilizer} :
    ∃ v, (STerm.stabAt (SC.closed (.stabLam (.ite (rowCutQubitCond D)
        (Term.pauliLit Pauli.Z) (Term.pauliLit Pauli.I)))) (SC.closed colVar)).eval
      Surface.code.body fuel rho E = some v := by
  refine ⟨if rho 0 / D.distance = rho 1 then Pauli.Z else Pauli.I, ?_⟩
  simp [SC.closed, STerm.eval, Term.eval, rowCutQubitCond,
    NatArithmetic.rowOf, 
    Env.cons, bind, Option.bind, colVar, rowVar1, Term.lift, Term.weaken, Term.weakenVar]
  split <;> rfl

/-- The `stabLam(ite (colCutQubitCond) X I)` entry leaf evaluates totally at `colVar` (dual). -/
theorem colCutEntry_eval (D : OddSurfaceDistance) {fuel : Nat} {rho : Env 2}
    {E : PartialStabilizer} :
    ∃ v, (STerm.stabAt (SC.closed (.stabLam (.ite (colCutQubitCond D)
        (Term.pauliLit Pauli.X) (Term.pauliLit Pauli.I)))) (SC.closed colVar)).eval
      Surface.code.body fuel rho E = some v := by
  refine ⟨if rho 0 % D.distance = rho 1 then Pauli.X else Pauli.I, ?_⟩
  simp [SC.closed, STerm.eval, Term.eval, colCutQubitCond,
    NatArithmetic.colOf, 
    Env.cons, bind, Option.bind, colVar, rowVar1, Term.lift, Term.weaken, Term.weakenVar]
  split <;> rfl

/-- The bound stabilizer `E` evaluates at `boundNat` (= `rho 0`) whenever `E` is defined
there — the `TotalUpTo`→`E`-eval bridge the core WFs thread. -/
theorem bound_boundNat_eval_of_total (D : OddSurfaceDistance) {rho : Env 2} {E : PartialStabilizer}
    (hT : ∃ p, E (rho 0) = some p) :
    ∃ v, (STerm.stabAt ((STerm.weaken SC.bound).weaken) SFormula.boundNat).eval
      Surface.code.body (bridgeProofFuel D) rho E = some v := by
  obtain ⟨p, hp⟩ := hT
  exact ⟨p, by simp [SC.bound, STerm.eval, STerm.weaken, STerm.lift, Term.eval,
    SFormula.boundNat, SC.closed, hp]⟩

/-- Dual: `E` evaluates at `colVar` (= `rho 0`) when defined there. -/
theorem bound_colVar_eval_of_total (D : OddSurfaceDistance) {rho : Env 2} {E : PartialStabilizer}
    (hT : ∃ p, E (rho 0) = some p) :
    ∃ v, (STerm.stabAt ((STerm.weaken SC.bound).weaken) (SC.closed colVar)).eval
      Surface.code.body (bridgeProofFuel D) rho E = some v := by
  obtain ⟨p, hp⟩ := hT
  exact ⟨p, by simp [SC.bound, STerm.eval, STerm.weaken, STerm.lift, Term.eval,
    SC.closed, colVar, hp]⟩

theorem rowCutLocal_WF (D : OddSurfaceDistance) {rho : Env 2} {E : PartialStabilizer}
    (hEb : ∃ v, (STerm.stabAt ((STerm.weaken SC.bound).weaken) SFormula.boundNat).eval
      Surface.code.body (bridgeProofFuel D) rho E = some v)
    (hEc : ∃ v, (STerm.stabAt ((STerm.weaken SC.bound).weaken) (SC.closed colVar)).eval
      Surface.code.body (bridgeProofFuel D) rho E = some v) :
    DerivWF (rowCutLocalCommutesFromNoXDeriv D) Surface.code.body (bridgeProofFuel D) rho E := by
  unfold rowCutLocalCommutesFromNoXDeriv
  refine derivWF_boolCases _ _ (sterm_eval_closedPure ?pure) ?wT ?wF
  case pure =>
    convert SFormula.PureTerm.eqNat (rowOfQPure2 D) rowVarPure2 using 2
    simp [rowCutQubitCond, Term.instantiateTopNat, Term.instantiateNatAt, NatArithmetic.rowOf,
      rowVar1, Term.weaken, Term.lift, Term.weakenVar]
  case wT =>
    simp only [id_eq]
    refine derivWF_localCommutesOfLeftEqNoAntiRight _ _ _ _ ?wEntry ?wNoAnti ?wFD
    case wEntry =>
      simp only [eq_mpr_eq_cast]
      refine derivWF_cast_type rfl ?_ _ _ (derivWF_cast_type rfl ?_ _ _
        (derivWF_stabAtClosedIteLamEqThen _ _ _ _ _ True.intro (rowCutEntry_eval D)
          ⟨Pauli.Z, by simp [Term.instantiateTopNat, Term.instantiateNatAt, Term.eval]⟩))
      · simp [SC.rowZCut, SC.closed, SC.p, SFormula.boundNat,
          STerm.weaken, STerm.lift, Term.weaken, Term.lift, Term.weakenVar, rowVar1, 
          ]
      · simp [rowCutQubitCond, SC.closed, SC.p, NatArithmetic.rowOf, 
          Term.weaken, Term.lift, Term.weakenVar, rowVar1, colVar,
          Term.instantiateTopNat, Term.instantiateNatAt]
    case wNoAnti =>
      refine derivWF_noAntiAtSubst _ _ _ _ _ _ ?wIdx ?wNoX ?hFD
      · refine derivWF_gridIdxLeftDivModEqOfRow _ _ _ True.intro ?_
        simp only [eq_mpr_eq_cast]
        refine derivWF_cast_type rfl ?_ _ _ (derivWF_cast_type rfl ?_ _ _ True.intro) <;>
          simp [SC.closed, rowCutQubitCond, SC.b, NatArithmetic.rowOf, rowVar1, colVar,
            Term.instantiateTopNat, Term.instantiateNatAt, 
            Term.weaken, Term.lift, Term.weakenVar]
      · -- `DerivWF (applyNatSubstitutionBetaElim … child) = DerivWF child` (structural),
        -- so the child's WF discharges it directly — no extra combinator needed.
        simp only [eq_mpr_eq_cast]
        refine derivWF_cast_type rfl ?_ _ _ (derivWF_cast_type rfl ?_ _ _
          (derivWF_allNatLtElim _ _ _ True.intro (derivWF_modLtOfLtSquare _ _ True.intro))) <;>
          simp [SC.closed, SC.bound, SC.p, SC.b, NatArithmetic.colOf, NatArithmetic.gridIdxLeft,
            SFormula.xSupportAt, SFormula.instantiateTopNat, SFormula.instantiateNatAt, SC.gridIdx,
            rowVar1, colVar, STerm.weaken, STerm.lift, STerm.instantiateNatAt,
            Term.weaken, Term.lift, Term.weakenVar, Term.instantiateNatAt]
      · exact formulaDefined_not (formulaDefined_eqBool
          (sterm_eval_anticommutes hEc (sterm_eval_p _)) (sterm_eval_b _))
    case wFD =>
      exact formulaDefined_localCommutesAt (rowZCut_boundNat_eval D) hEb
  case wF =>
    simp only [id_eq]
    refine derivWF_localCommutesOfLeftI _ _ _ ?wEntryF ?wFDf
    case wEntryF =>
      simp only [eq_mpr_eq_cast]
      refine derivWF_cast_type rfl ?_ _ _ (derivWF_cast_type rfl ?_ _ _
        (derivWF_stabAtClosedIteLamEqElse _ _ _ _ _ True.intro (rowCutEntry_eval D)
          ⟨Pauli.I, by simp [Term.instantiateTopNat, Term.instantiateNatAt, Term.eval]⟩)) <;>
        simp [SC.rowZCut, rowCutQubitCond, SC.closed, SC.p, NatArithmetic.rowOf, SFormula.boundNat,
          STerm.weaken, STerm.lift, Term.weaken, Term.lift, Term.weakenVar, rowVar1, colVar,
          Term.instantiateTopNat, Term.instantiateNatAt]
    case wFDf =>
      exact formulaDefined_localCommutesAt (rowZCut_boundNat_eval D) hEb

/-- Column dual of `rowCutLocal_WF` (mirror: `colCutQubitCond`/`colXCut`/`gridColNoZ`/`X`). -/
theorem colCutLocal_WF (D : OddSurfaceDistance) {rho : Env 2} {E : PartialStabilizer}
    (hEb : ∃ v, (STerm.stabAt ((STerm.weaken SC.bound).weaken) SFormula.boundNat).eval
      Surface.code.body (bridgeProofFuel D) rho E = some v)
    (hEc : ∃ v, (STerm.stabAt ((STerm.weaken SC.bound).weaken) (SC.closed colVar)).eval
      Surface.code.body (bridgeProofFuel D) rho E = some v) :
    DerivWF (colCutLocalCommutesFromNoZDeriv D) Surface.code.body (bridgeProofFuel D) rho E := by
  unfold colCutLocalCommutesFromNoZDeriv
  refine derivWF_boolCases _ _ (sterm_eval_closedPure ?pure) ?wT ?wF
  case pure =>
    convert SFormula.PureTerm.eqNat (colOfQPure2 D) rowVarPure2 using 2
    simp [colCutQubitCond, Term.instantiateTopNat, Term.instantiateNatAt, NatArithmetic.colOf,
      rowVar1, Term.weaken, Term.lift, Term.weakenVar]
  case wT =>
    simp only [id_eq]
    refine derivWF_localCommutesOfLeftEqNoAntiRight _ _ _ _ ?wEntry ?wNoAnti ?wFD
    case wEntry =>
      simp only [eq_mpr_eq_cast]
      refine derivWF_cast_type rfl ?_ _ _ (derivWF_cast_type rfl ?_ _ _
        (derivWF_stabAtClosedIteLamEqThen _ _ _ _ _ True.intro (colCutEntry_eval D)
          ⟨Pauli.X, by simp [Term.instantiateTopNat, Term.instantiateNatAt, Term.eval]⟩))
      · simp [SC.colXCut, SC.closed, SC.p, SFormula.boundNat,
          STerm.weaken, STerm.lift, Term.weaken, Term.lift, Term.weakenVar, rowVar1, 
          ]
      · simp [colCutQubitCond, SC.closed, SC.p, NatArithmetic.colOf, 
          Term.weaken, Term.lift, Term.weakenVar, rowVar1, colVar,
          Term.instantiateTopNat, Term.instantiateNatAt]
    case wNoAnti =>
      refine derivWF_noAntiAtSubst _ _ _ _ _ _ ?wIdx ?wNoX ?hFD
      · refine derivWF_gridIdxLeftDivModEqOfCol _ _ _ True.intro ?_
        simp only [eq_mpr_eq_cast]
        refine derivWF_cast_type rfl ?_ _ _ (derivWF_cast_type rfl ?_ _ _ True.intro) <;>
          simp [SC.closed, colCutQubitCond, SC.b, NatArithmetic.colOf, rowVar1, colVar,
            Term.instantiateTopNat, Term.instantiateNatAt, 
            Term.weaken, Term.lift, Term.weakenVar]
      · simp only [eq_mpr_eq_cast]
        refine derivWF_cast_type rfl ?_ _ _ (derivWF_cast_type rfl ?_ _ _
          (derivWF_allNatLtElim _ _ _ True.intro (derivWF_divLtOfLtSquare _ _ True.intro))) <;>
          simp [SC.closed, SC.bound, SC.p, SC.b, NatArithmetic.rowOf, NatArithmetic.gridIdxLeft,
            SFormula.zSupportAt, SFormula.instantiateTopNat, SFormula.instantiateNatAt, SC.gridIdx,
            rowVar1, colVar, STerm.weaken, STerm.lift, STerm.instantiateNatAt,
            Term.weaken, Term.lift, Term.weakenVar, Term.instantiateNatAt]
      · exact formulaDefined_not (formulaDefined_eqBool
          (sterm_eval_anticommutes hEc (sterm_eval_p _)) (sterm_eval_b _))
    case wFD =>
      exact formulaDefined_localCommutesAt (colXCut_boundNat_eval D) hEb
  case wF =>
    simp only [id_eq]
    refine derivWF_localCommutesOfLeftI _ _ _ ?wEntryF ?wFDf
    case wEntryF =>
      simp only [eq_mpr_eq_cast]
      refine derivWF_cast_type rfl ?_ _ _ (derivWF_cast_type rfl ?_ _ _
        (derivWF_stabAtClosedIteLamEqElse _ _ _ _ _ True.intro (colCutEntry_eval D)
          ⟨Pauli.I, by simp [Term.instantiateTopNat, Term.instantiateNatAt, Term.eval]⟩)) <;>
        simp [SC.colXCut, colCutQubitCond, SC.closed, SC.p, NatArithmetic.colOf, SFormula.boundNat,
          STerm.weaken, STerm.lift, Term.weaken, Term.lift, Term.weakenVar, rowVar1, colVar,
          Term.instantiateTopNat, Term.instantiateNatAt]
    case wFDf =>
      exact formulaDefined_localCommutesAt (colXCut_boundNat_eval D) hEb

/-- Core: `rowCutNoXImpliesCommutesDeriv` WF — bounded-intro ×2 + `impIntro_cond` (the
`gridRowNoX` guard supplies `ContextHolds`) + `commutesOfPointwise`, threading `TotalUpTo`
through the `E`-eval bridges into `rowCutLocal_WF`. -/
theorem rowCutNoX_WF (D : OddSurfaceDistance) {E : PartialStabilizer}
    (hTotal : TotalUpTo (nQubits D.distance) E) :
    DerivWF (rowCutNoXImpliesCommutesDeriv D) Surface.code.body
      (bridgeProofFuel D) Env.empty E := by
  unfold rowCutNoXImpliesCommutesDeriv
  refine derivWF_allNatLtIntroBounded _ _
    ⟨D.distance, scn_eval _ _ _ _ _, fun x hx => ⟨?child, fun A hA => by cases hA⟩⟩
  refine derivWF_impIntro_cond ?fdGuard (fun hguard => ?childInner)
  case fdGuard =>
    -- `gridRowNoX = allNatLt (SC.n d) (not (xSupportAt E (gridIdx d row ·)))`;
    -- FD reduces to: bound evaluates (`scn_eval`) + body defined for each col `y < d`,
    -- where the body's only obligation is `E` evaluating at the cell `gridIdx d x y`.
    refine formulaDefined_allNatLt _ _ (scn_eval _ _ _ _ _) (fun y hy => ?_)
    refine formulaDefined_not (formulaDefined_eqBool
      (sterm_eval_anticommutes ?stabEval (sterm_eval_p Pauli.Z)) (sterm_eval_b true))
    case stabEval =>
      -- the cell qubit is `gridIdxLeft d x y = d*x + y < d*d = nQubits`, so `E` is total there
      obtain ⟨p, hp⟩ := hTotal (D.distance * x + y)
        (by have := NatArithmetic.gridIdxLeft_lt_square hx hy; simpa [nQubits] using this)
      exact ⟨p, by
        simp [SC.bound, SC.gridIdx, NatArithmetic.gridIdxLeft, STerm.eval,
          STerm.weaken, STerm.lift, Term.eval, Term.weaken, Term.lift,
          Term.weakenVar, rowVar1, Env.cons, hp]⟩
  case childInner =>
    refine derivWF_commutesOfPointwise ?innerBounded ?fdComm
    case fdComm =>
      -- FD of `commutesUpTo (SC.n nQubits) (rowZCut) (weaken bound)`: both stabilizers
      -- evaluate and are total up to `nQubits` — the cut is everywhere-some, the bound is
      -- `E` (total by `hTotal`).
      exact formulaDefined_commutesUpTo
        (Av := fun q => some (if q / D.distance = x then Pauli.Z else Pauli.I)) (Bv := E)
        (scn_eval _ _ _ _ _)
        (by simp [SC.rowZCut, STerm.eval, Term.eval, rowVar1, Term.weaken, Term.lift,
          Term.weakenVar, Env.cons, apply_ite])
        (by simp [SC.bound, STerm.eval, STerm.weaken, STerm.lift])
        StabTotalUpTo.ofTotal
        (StabTotalUpTo_of_TotalUpTo hTotal)
    case innerBounded =>
      refine derivWF_allNatLtIntroBounded _ _
        ⟨nQubits D.distance, scn_eval _ _ _ _ _, fun y hy => ⟨?subDeriv, ?ctxInner⟩⟩
      case subDeriv =>
        exact rowCutLocal_WF D (bound_boundNat_eval_of_total D (hTotal y hy))
          (bound_colVar_eval_of_total D (hTotal y hy))
      case ctxInner =>
        -- `Γ = [gridRowNoX, boundNatLt (SC.n d)]` at `(cons x empty)`: head from `hguard`,
        -- the `boundNatLt` tail from `x < d` via `contextHolds_boundNatLt_cons`.
        intro A hA
        cases hA with
        | head => exact hguard
        | tail _ hA' =>
            exact contextHolds_boundNatLt_cons Surface.code.body (bridgeProofFuel D)
              (SC.n D.distance) Env.empty E [] x D.distance (scn_eval _ _ _ _ _) hx
              (fun B hB => by cases hB) A hA'

/-- Core (column dual of `rowCutNoX_WF`): `colCutNoZImpliesCommutesDeriv` WF.  Mirror with
`colXCut`/`gridColNoZ`/`q % d`/`X`, cell qubit `gridIdxLeft d y x = d*y + x`, reusing
`colCutLocal_WF`. -/
theorem colCutNoZ_WF (D : OddSurfaceDistance) {E : PartialStabilizer}
    (hTotal : TotalUpTo (nQubits D.distance) E) :
    DerivWF (colCutNoZImpliesCommutesDeriv D) Surface.code.body
      (bridgeProofFuel D) Env.empty E := by
  unfold colCutNoZImpliesCommutesDeriv
  refine derivWF_allNatLtIntroBounded _ _
    ⟨D.distance, scn_eval _ _ _ _ _, fun x hx => ⟨?child, fun A hA => by cases hA⟩⟩
  refine derivWF_impIntro_cond ?fdGuard (fun hguard => ?childInner)
  case fdGuard =>
    refine formulaDefined_allNatLt _ _ (scn_eval _ _ _ _ _) (fun y hy => ?_)
    refine formulaDefined_not (formulaDefined_eqBool
      (sterm_eval_anticommutes ?stabEval (sterm_eval_p Pauli.X)) (sterm_eval_b true))
    case stabEval =>
      obtain ⟨p, hp⟩ := hTotal (D.distance * y + x)
        (by have := NatArithmetic.gridIdxLeft_lt_square hy hx; simpa [nQubits] using this)
      exact ⟨p, by
        simp [SC.bound, SC.gridIdx, NatArithmetic.gridIdxLeft, STerm.eval,
          STerm.weaken, STerm.lift, Term.eval, Term.weaken, Term.lift,
          Term.weakenVar, rowVar1, Env.cons, hp]⟩
  case childInner =>
    refine derivWF_commutesOfPointwise ?innerBounded ?fdComm
    case fdComm =>
      exact formulaDefined_commutesUpTo
        (Av := fun q => some (if q % D.distance = x then Pauli.X else Pauli.I)) (Bv := E)
        (scn_eval _ _ _ _ _)
        (by simp [SC.colXCut, STerm.eval, Term.eval, rowVar1, Term.weaken, Term.lift,
          Term.weakenVar, Env.cons, apply_ite])
        (by simp [SC.bound, STerm.eval, STerm.weaken, STerm.lift])
        StabTotalUpTo.ofTotal
        (StabTotalUpTo_of_TotalUpTo hTotal)
    case innerBounded =>
      refine derivWF_allNatLtIntroBounded _ _
        ⟨nQubits D.distance, scn_eval _ _ _ _ _, fun y hy => ⟨?subDeriv, ?ctxInner⟩⟩
      case subDeriv =>
        exact colCutLocal_WF D (bound_boundNat_eval_of_total D (hTotal y hy))
          (bound_colVar_eval_of_total D (hTotal y hy))
      case ctxInner =>
        intro A hA
        cases hA with
        | head => exact hguard
        | tail _ hA' =>
            exact contextHolds_boundNatLt_cons Surface.code.body (bridgeProofFuel D)
              (SC.n D.distance) Env.empty E [] x D.distance (scn_eval _ _ _ _ _) hx
              (fun B hB => by cases hB) A hA'

end QHL.CodeLang.Surface.Verify
