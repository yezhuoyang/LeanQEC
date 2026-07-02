import QStab.QHL.Verify.SurfaceCharEval
import QStab.QHL.Verify.SurfaceHunion
import QStab.QHL.Verify.SurfaceColHunion
import QStab.QHL.Verify.SurfacePureAssembly
import QStab.QHL.Verify.SurfaceAllTermsGood

namespace QHL.CodeLang.Surface.Verify

open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

set_option maxHeartbeats 1600000

/-- The executable entry evaluator agrees with the flat classifier, for every odd
distance — bridging the literal gateway to symbolic-index `recCall`s. -/
theorem evalEntry_surfaceCellPauli (D : OddSurfaceDistance) (kv qv : Nat) :
    Surface.code.evalEntry? (D.distance + 1) D.distance kv qv
      = some (surfaceCellPauli D.distance kv qv) := by
  rw [← CodeEvalHelpers.eval_stabAt_recCall_natLit Surface.code (D.distance + 1)
    D.distance kv qv Env.empty]
  have h2 := recCall_eval_surfaceCellPauli D kv qv (E := fun _ => none)
  simpa only [SC.closed, STerm.eval, Term.eval] using h2

/-- **Symbolic-index gateway** (STerm form): `stabAt(recCall (natLit d) kT) qT` evaluates
to `surfaceCellPauli d kv qv`, for symbolic index/qubit terms `kT`/`qT`. -/
theorem stabAt_recCall_surfaceCellPauli {arity : Nat} (D : OddSurfaceDistance)
    {kT qT : Term arity .nat} {rho : Env arity} {E : PartialStabilizer} {kv qv : Nat}
    (hk : Term.eval Surface.code.body (D.distance + 1) kT rho = some kv)
    (hq : Term.eval Surface.code.body (D.distance + 2) qT rho = some qv) :
    (STerm.stabAt (SC.closed (Term.recCall (Term.natLit D.distance) kT)) (SC.closed qT)).eval
        Surface.code.body (D.distance + 2) rho E
      = some (surfaceCellPauli D.distance kv qv) := by
  have hd : Term.eval Surface.code.body (D.distance + 1) (Term.natLit D.distance) rho
      = some D.distance := by simp [Term.eval]
  have key : Term.eval Surface.code.body (D.distance + 2)
      (.stabAt (.recCall (.natLit D.distance) kT) qT) rho
      = some (surfaceCellPauli D.distance kv qv) := by
    rw [CodeEvalHelpers.eval_stabAt_recCall Surface.code hd hk hq, evalEntry_surfaceCellPauli]
  simpa only [SC.closed, STerm.eval, Term.eval] using key

/-- **`hbody`**: the strip body evaluates to the (total) `surfaceCellPauli` stabilizer at
the strip index. -/
theorem rowStripBody_eval (D : OddSurfaceDistance) (E : PartialStabilizer) (row iv : Nat) :
    STerm.eval Surface.code.body (bridgeProofFuel D) (rowStripBody D)
        (Env.cons iv (Env.cons row Env.empty)) E
      = some (fun q => some (surfaceCellPauli D.distance (stripIndexVal D.distance row iv) q)) := by
  obtain ⟨sa, hsa, _⟩ := rowStripBody_total D E row iv
  rw [hsa]; congr 1; funext q
  have h1 : (STerm.stabAt (rowStripBody D) (SC.closed (Term.natLit q))).eval Surface.code.body
      (bridgeProofFuel D) (Env.cons iv (Env.cons row Env.empty)) E = sa q := by
    simp [STerm.eval, hsa, SC.closed, Term.eval, bind, Option.bind]
  rw [← h1]
  have hk : Term.eval Surface.code.body (D.distance + 1)
      (rowZStripIndex D.distance rowVar1.weaken colVar)
      (Env.cons iv (Env.cons row Env.empty)) = some (stripIndexVal D.distance row iv) :=
    gridRowZStripIndex_eval D.distance rowVar1.weaken colVar Surface.code.body (D.distance + 1)
      (Env.cons iv (Env.cons row Env.empty))
      (by simp [rowVar1, Term.eval, Term.weaken, Term.lift, Term.weakenVar, Env.cons])
      (by simp [colVar, Term.eval, Env.cons])
  have hq : Term.eval Surface.code.body (D.distance + 2) (Term.natLit q)
      (Env.cons iv (Env.cons row Env.empty)) = some q := by simp [Term.eval]
  exact stabAt_recCall_surfaceCellPauli D hk hq

/-- **The foldDisjoint `AllTermsGoodP`** for the row bridge:
`g = surfaceCellPauli∘stripIndexVal`, `t = tRow`, with `hbody`/`hlhs`/`hunion`
discharged.  `hunion` is bounded to `row < outerBound = D.distance - 1` (the
strip-tiling regime) and `q < nQubits`; `hunion_pure` holds for every `q`. -/
theorem rowBridgeGenerated_ATG (D : OddSurfaceDistance) (E : PartialStabilizer) :
    AllTermsGoodP (rowBridgeGeneratedPure D) E := by
  unfold rowBridgeGeneratedPure
  refine ⟨fun row iv q => surfaceCellPauli D.distance (stripIndexVal D.distance row iv) q,
    fun row q => tRow D.distance row q, ?_, ?_, ?_⟩
  · intro row iv; exact rowStripBody_eval D E row iv
  · intro row; exact rowBridge_eval D E row
  · intro row hrow q _hq
    have hodd : D.distance = 2 * D.index + 3 := rfl
    have hsw : stripWidth D.distance = (D.distance - 1) / 2 + 1 := gridStripWidth_eq D.distance
    rw [hsw]
    exact hunion_pure D.distance row q ((D.distance - 1) / 2) (by omega) (by omega) hrow
      (Nat.mod_lt q (by omega))

/-- Row bridge leaf is `DerivWFP` (the cut-assembly form). -/
theorem rowBridgeGenerated_WFP (D : OddSurfaceDistance) (E : PartialStabilizer) :
    DerivWFP (rowBridgeGeneratedPure D) E :=
  allTermsGoodP_derivWFP (rowBridgeGeneratedPure D) E (rowBridgeGenerated_ATG D E)

/-- Row bridge leaf discharges its `DefinedObligations`. -/
theorem rowBridgeGeneratedPure_defined (D : OddSurfaceDistance) (E : PartialStabilizer) :
    (rowBridgeGeneratedPure D).DefinedObligations E :=
  allTermsGoodP_defined (rowBridgeGeneratedPure D) E (rowBridgeGenerated_ATG D E)

/-- **`hbody` (column)**: the column strip body evaluates to the (total)
`surfaceCellPauli` stabilizer at the column strip index. -/
theorem colStripBody_eval (D : OddSurfaceDistance) (E : PartialStabilizer) (col iv : Nat) :
    STerm.eval Surface.code.body (bridgeProofFuel D) (colStripBody D)
        (Env.cons iv (Env.cons col Env.empty)) E
      = some (fun q => some (surfaceCellPauli D.distance (colStripIndexVal D.distance col iv) q)) := by
  obtain ⟨sa, hsa, _⟩ := colStripBody_total D E col iv
  rw [hsa]; congr 1; funext q
  have h1 : (STerm.stabAt (colStripBody D) (SC.closed (Term.natLit q))).eval Surface.code.body
      (bridgeProofFuel D) (Env.cons iv (Env.cons col Env.empty)) E = sa q := by
    simp [STerm.eval, hsa, SC.closed, Term.eval, bind, Option.bind]
  rw [← h1]
  have hk : Term.eval Surface.code.body (D.distance + 1)
      (colXStripIndex D.distance rowVar1.weaken colVar)
      (Env.cons iv (Env.cons col Env.empty)) = some (colStripIndexVal D.distance col iv) :=
    gridColXStripIndex_eval D.distance rowVar1.weaken colVar Surface.code.body (D.distance + 1)
      (Env.cons iv (Env.cons col Env.empty))
      (by simp [rowVar1, Term.eval, Term.weaken, Term.lift, Term.weakenVar, Env.cons])
      (by simp [colVar, Term.eval, Env.cons])
  have hq : Term.eval Surface.code.body (D.distance + 2) (Term.natLit q)
      (Env.cons iv (Env.cons col Env.empty)) = some q := by simp [Term.eval]
  exact stabAt_recCall_surfaceCellPauli D hk hq

/-- **The foldDisjoint `AllTermsGoodP`** for the column bridge (dual of the row
case).  `hunion` is bounded to `col < D.distance - 1` and `q < nQubits = d*d`,
giving `q / d < d` (the band is on `q % d`, coverage on `q / d`). -/
theorem colBridgeGenerated_ATG (D : OddSurfaceDistance) (E : PartialStabilizer) :
    AllTermsGoodP (colBridgeGeneratedPure D) E := by
  unfold colBridgeGeneratedPure
  refine ⟨fun col iv q => surfaceCellPauli D.distance (colStripIndexVal D.distance col iv) q,
    fun col q => tCol D.distance col q, ?_, ?_, ?_⟩
  · intro col iv; exact colStripBody_eval D E col iv
  · intro col; exact colBridge_eval D E col
  · intro col hcol q hq
    have hodd : D.distance = 2 * D.index + 3 := rfl
    have hsw : stripWidth D.distance = (D.distance - 1) / 2 + 1 := gridStripWidth_eq D.distance
    rw [hsw]
    have hqdiv : q / D.distance < D.distance :=
      Nat.div_lt_of_lt_mul (show q < D.distance * D.distance from hq)
    exact hunion_pure_col D.distance col q ((D.distance - 1) / 2) (by omega) (by omega) hcol hqdiv

/-- Column bridge leaf is `DerivWFP` (the cut-assembly form). -/
theorem colBridgeGenerated_WFP (D : OddSurfaceDistance) (E : PartialStabilizer) :
    DerivWFP (colBridgeGeneratedPure D) E :=
  allTermsGoodP_derivWFP (colBridgeGeneratedPure D) E (colBridgeGenerated_ATG D E)

/-- Column bridge leaf discharges its `DefinedObligations`. -/
theorem colBridgeGeneratedPure_defined (D : OddSurfaceDistance) (E : PartialStabilizer) :
    (colBridgeGeneratedPure D).DefinedObligations E :=
  allTermsGoodP_defined (colBridgeGeneratedPure D) E (colBridgeGenerated_ATG D E)

end QHL.CodeLang.Surface.Verify
