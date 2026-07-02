import QStab.QHL.Verify.SurfaceBridgeDefined
import QStab.QHL.Verify.SurfacePureAssembly
import QStab.QHL.Verify.SurfaceGenericDefined
import QStab.QHL.Verify.SurfaceNormalizerDefined

/-!
# Lower bound — Helpers

Reusable definedness building blocks for the lower bound: the bounded-quantifier
`FormulaDefined` helpers, product-fold totality, the strip-fold commutation FD, the
per-cell occupancy reads, and the trivial `DerivWFP` leaves.
-/

namespace QHL.CodeLang.Surface.Verify

open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

set_option maxHeartbeats 1600000

/-- The bounded-`∀` fold is total when its predicate is total below the bound. -/
theorem allNatLt_total (n : Nat) (pred : Nat → Option Bool)
    (h : ∀ x, x < n → ∃ b, pred x = some b) :
    ∃ b, QHL.CodeLang.allNatLt n pred = some b := by
  induction n with
  | zero => exact ⟨true, rfl⟩
  | succ m ih =>
    obtain ⟨bm, hbm⟩ := ih (fun x hx => h x (Nat.lt_succ_of_lt hx))
    simp only [QHL.CodeLang.allNatLt, hbm, bind, Option.bind]
    cases bm with
    | true => simpa using h m (Nat.lt_succ_self m)
    | false => exact ⟨false, rfl⟩

/-- `FormulaDefined` for an `allNatLt` formula: bound evaluates + body defined below it. -/
theorem formulaDefined_allNatLt {arity : Nat} (n : STerm arity .nat) (A : SFormula (arity + 1))
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer} {nv : Nat}
    (hn : n.eval cb fuel rho E = some nv)
    (hbody : ∀ x, x < nv → SFormula.Deriv.FormulaDefined cb fuel (Env.cons x rho) E A) :
    SFormula.Deriv.FormulaDefined cb fuel rho E (.allNatLt n A) := by
  obtain ⟨b, hb⟩ := allNatLt_total nv (fun x => A.eval cb fuel (Env.cons x rho) E)
    (fun x hx => hbody x hx)
  exact ⟨b, by simp only [SFormula.eval, hn, bind, Option.bind]; exact hb⟩

/-- The bounded-`∃` fold is total when its predicate is total below the bound (dual of
`allNatLt_total`). -/
theorem existsNatLt_total (n : Nat) (pred : Nat → Option Bool)
    (h : ∀ x, x < n → ∃ b, pred x = some b) :
    ∃ b, QHL.CodeLang.existsNatLt n pred = some b := by
  induction n with
  | zero => exact ⟨false, rfl⟩
  | succ m ih =>
    obtain ⟨bm, hbm⟩ := ih (fun x hx => h x (Nat.lt_succ_of_lt hx))
    simp only [QHL.CodeLang.existsNatLt, hbm, bind, Option.bind]
    cases bm with
    | true => exact ⟨true, rfl⟩
    | false => simpa using h m (Nat.lt_succ_self m)

/-- `FormulaDefined` for an `existsNatLt` formula (dual of `formulaDefined_allNatLt`). -/
theorem formulaDefined_existsNatLt {arity : Nat} (n : STerm arity .nat) (A : SFormula (arity + 1))
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer} {nv : Nat}
    (hn : n.eval cb fuel rho E = some nv)
    (hbody : ∀ x, x < nv → SFormula.Deriv.FormulaDefined cb fuel (Env.cons x rho) E A) :
    SFormula.Deriv.FormulaDefined cb fuel rho E (.existsNatLt n A) := by
  obtain ⟨b, hb⟩ := existsNatLt_total nv (fun x => A.eval cb fuel (Env.cons x rho) E)
    (fun x hx => hbody x hx)
  exact ⟨b, by simp only [SFormula.eval, hn, bind, Option.bind]; exact hb⟩

/-- The six closed leaves of the lower-bound derivation. -/
def mkL (D : OddSurfaceDistance) : PureLowerClosedLeaves D :=
  { rowBridgeGenerated := rowBridgeGeneratedPure D
    rowStripIndexInRange := rowStripRangePure D
    rowCutTelescoping := rowCutTelescopingPure D
    colBridgeGenerated := colBridgeGeneratedPure D
    colStripIndexInRange := colStripRangePure D
    colCutTelescoping := colCutTelescopingPure D }

/-- Column index-range leaf is `DerivWFP` (`True`). -/
theorem colStripRange_WFP (D : OddSurfaceDistance) (E : PartialStabilizer) :
    DerivWFP (colStripRangePure D) E := True.intro

/-- **stabFold totality wrapper** — the product-fold of everywhere-total slots is everywhere-total.
Pairs with the now-public `stabFoldEval_total` (PureDeriv) so the `SC.stabFold` `commutesUpTo` FD leaves
(core 4 `rowBridge` fold, bridge norm `rowZStripProduct` fold) get their `StabTotalUpTo`. -/
theorem partialStabilizerFold_total (width : Nat) (g : Nat → Nat → Pauli) (q : Nat) :
    ∃ p, partialStabilizerFold width (fun i => fun q => some (g i q)) q = some p := by
  induction width with
  | zero => exact ⟨Pauli.I, rfl⟩
  | succ n ih =>
    obtain ⟨pn, hpn⟩ := ih
    exact ⟨Pauli.mul pn (g n q), by
      simp [partialStabilizerFold, partialStabilizerMul, hpn, bind, Option.bind]⟩

/-- `StabTotalUpTo` form of `partialStabilizerFold_total`, ready for `formulaDefined_commutesUpTo`. -/
theorem stabTotalUpTo_partialStabilizerFold (m width : Nat) (g : Nat → Nat → Pauli) :
    StabTotalUpTo m (partialStabilizerFold width (fun i => fun q => some (g i q))) :=
  fun q _ => partialStabilizerFold_total width g q

/-- boundNat-bound variant of `stabFoldEval_total` (for core 4's `SC.stabFold boundNat …`): the
`.stabFold` eval folds `partialStabilizerFold nv` over the body, with `nv = boundNat.eval = row`. -/
theorem stabFoldEval_boundNat (cb : Term 2 .stab) (fuel : Nat) (E : PartialStabilizer)
    (body : STerm 2 .stab) (row : Nat) (g : Nat → Nat → Pauli)
    (hbody : ∀ iv, STerm.eval cb fuel body (Env.cons iv (Env.cons row Env.empty)) E =
      some (fun q => some (g iv q))) :
    STerm.eval cb fuel (SC.stabFold SFormula.boundNat body) (Env.cons row Env.empty) E =
      some (partialStabilizerFold row (fun i => fun q => some (g i q))) := by
  simp only [SC.stabFold, SFormula.boundNat, STerm.eval, Term.eval, bind, Option.bind,
    SC.closed, Env.cons, hbody]

/-- The `rowBridge` fold body at fold-index `i` (`rightRowVar2`) in `(cons i (cons row empty))`
evaluates to `tRow d i`. Mirror of `rowBridge_eval` at the 2-level fold env. -/
theorem rowBridge_fold_eval (D : OddSurfaceDistance) (E : PartialStabilizer) (row i : Nat) :
    STerm.eval Surface.code.body (bridgeProofFuel D)
        (OpenStab.rowBridge D.distance rightRowVar2) (Env.cons i (Env.cons row Env.empty)) E =
      some (fun q => some (tRow D.distance i q)) := by
  have hrow : Term.eval Surface.code.body (bridgeProofFuel D) rightRowVar2
      (Env.cons i (Env.cons row Env.empty)) = some i := by
    simp [rightRowVar2, Term.eval, Env.cons]
  have hsucc : Term.eval Surface.code.body (bridgeProofFuel D)
      (.add rightRowVar2 (.natLit 1)) (Env.cons i (Env.cons row Env.empty)) = some (i + 1) := by
    simp [Term.eval, hrow]
  have hA := rowCutInnerTerm_eval D.distance Surface.code.body (bridgeProofFuel D) i
    rightRowVar2 (Env.cons i (Env.cons row Env.empty)) hrow
  have hB := rowCutInnerTerm_eval D.distance Surface.code.body (bridgeProofFuel D) (i + 1)
    (.add rightRowVar2 (.natLit 1)) (Env.cons i (Env.cons row Env.empty)) hsucc
  have hmul := eval_stabMul_closed Surface.code.body (bridgeProofFuel D)
    (Env.cons i (Env.cons row Env.empty)) E
    (rowCutInnerTerm D.distance rightRowVar2)
    (rowCutInnerTerm D.distance (.add rightRowVar2 (.natLit 1))) hA hB
  rw [show OpenStab.rowBridge D.distance rightRowVar2
        = SC.stabMul (.closed (rowCutInnerTerm D.distance rightRowVar2))
            (.closed (rowCutInnerTerm D.distance (.add rightRowVar2 (.natLit 1)))) from rfl]
  rw [hmul]
  congr 1

/-- Column dual of `rowBridge_fold_eval` (for core 4's z-dual): `colBridge` fold body → `tCol d i`. -/
theorem colBridge_fold_eval (D : OddSurfaceDistance) (E : PartialStabilizer) (row i : Nat) :
    STerm.eval Surface.code.body (bridgeProofFuel D)
        (OpenStab.colBridge D.distance rightRowVar2) (Env.cons i (Env.cons row Env.empty)) E =
      some (fun q => some (tCol D.distance i q)) := by
  have hrow : Term.eval Surface.code.body (bridgeProofFuel D) rightRowVar2
      (Env.cons i (Env.cons row Env.empty)) = some i := by
    simp [rightRowVar2, Term.eval, Env.cons]
  have hsucc : Term.eval Surface.code.body (bridgeProofFuel D)
      (.add rightRowVar2 (.natLit 1)) (Env.cons i (Env.cons row Env.empty)) = some (i + 1) := by
    simp [Term.eval, hrow]
  have hA := colCutInnerTerm_eval D.distance Surface.code.body (bridgeProofFuel D) i
    rightRowVar2 (Env.cons i (Env.cons row Env.empty)) hrow
  have hB := colCutInnerTerm_eval D.distance Surface.code.body (bridgeProofFuel D) (i + 1)
    (.add rightRowVar2 (.natLit 1)) (Env.cons i (Env.cons row Env.empty)) hsucc
  have hmul := eval_stabMul_closed Surface.code.body (bridgeProofFuel D)
    (Env.cons i (Env.cons row Env.empty)) E
    (colCutInnerTerm D.distance rightRowVar2)
    (colCutInnerTerm D.distance (.add rightRowVar2 (.natLit 1))) hA hB
  rw [show OpenStab.colBridge D.distance rightRowVar2
        = SC.stabMul (.closed (colCutInnerTerm D.distance rightRowVar2))
            (.closed (colCutInnerTerm D.distance (.add rightRowVar2 (.natLit 1)))) from rfl]
  rw [hmul]
  congr 1

/-- **Shared strip-product commutation FD.**  The `FormulaDefined` obligation for
`commutesUpTo n stab (weaken SC.bound)` whenever `stab` evaluates to a strip product-fold
`partialStabilizerFold width (some ∘ g)` — an everywhere-total stabilizer — and `E` is total up to
`nQubits`.  This is the single reusable core behind every strip-product commutation obligation in the
lower bound (both row/`Z` and column/`X`, at the top `allNatLt` level and inside the bridge norms):
the fold's totality is `stabTotalUpTo_partialStabilizerFold`, `E`'s is `hTotal`. -/
theorem commutesUpTo_stabFold_FD (D : OddSurfaceDistance) {E : PartialStabilizer}
    (hTotal : TotalUpTo (nQubits D.distance) E)
    {n_stab : STerm 1 .nat} {stab : STerm 1 .stab} (width : Nat) (g : Nat → Nat → Pauli) (row : Nat)
    (hn : n_stab.eval Surface.code.body (bridgeProofFuel D) (Env.cons row Env.empty) E
      = some (nQubits D.distance))
    (hstab : stab.eval Surface.code.body (bridgeProofFuel D) (Env.cons row Env.empty) E
      = some (partialStabilizerFold width (fun i => fun q => some (g i q)))) :
    SFormula.Deriv.FormulaDefined Surface.code.body (bridgeProofFuel D) (Env.cons row Env.empty) E
      (SFormula.commutesUpTo n_stab stab (STerm.weaken SC.bound)) :=
  formulaDefined_commutesUpTo
    (Av := partialStabilizerFold width (fun i => fun q => some (g i q))) (Bv := E)
    hn hstab
    (by simp [SC.bound, STerm.eval, STerm.weaken, STerm.lift])
    (stabTotalUpTo_partialStabilizerFold _ _ _)
    (StabTotalUpTo_of_TotalUpTo hTotal)

/-- FD of `rowZStripProductCommutesF` — `allNatLt d` of the row strip-product commutation, via the
shared `commutesUpTo_stabFold_FD` (row strip body totality = `rowStripBody_eval`). -/
theorem fd_rowZStripProductCommutesF (D : OddSurfaceDistance) {E : PartialStabilizer}
    (hTotal : TotalUpTo (nQubits D.distance) E) :
    SFormula.Deriv.FormulaDefined Surface.code.body (bridgeProofFuel D) Env.empty E
      (rowZStripProductCommutesF D) := by
  refine formulaDefined_allNatLt _ _ (scn_eval _ _ _ _ _) (fun row hrow => ?_)
  refine commutesUpTo_stabFold_FD D hTotal (stripWidth D.distance)
    (fun i q => surfaceCellPauli D.distance (stripIndexVal D.distance row i) q) row
    (by rw [sterm_eval_weaken_top]; exact scn_eval _ _ _ _ _) ?_
  have hfold := stabFoldEval_total Surface.code.body (bridgeProofFuel D) E (rowStripBody D)
    (stripWidth D.distance) row
    (fun iv q => surfaceCellPauli D.distance (stripIndexVal D.distance row iv) q)
    (fun iv => rowStripBody_eval D E row iv)
  simpa [rowZStripProduct, rowStripBody, SC.n] using hfold

/-- Column telescoping leaf is `DerivWFP` (= its `DefinedObligations`). -/
theorem colCutTelescoping_WFP (D : OddSurfaceDistance) (E : PartialStabilizer) :
    DerivWFP (colCutTelescopingPure D) E :=
  colCutTelescopingPure_defined D E

-- The core bridge-deriv `DerivWF`s (to be proved; `sorry` pins their goals).
-- `distanceLowerBoundBody_WF` is defined after the FD-family helpers (below).
-- `xParityPropRowsCore_WF` is defined holistically after the rule-truth helpers (below).
-- `rowBridgeFactorsNorm_WF`/`colBridgeFactorsNorm_WF` are proved after the totality helpers + truths.
-- `xRowsWeight_WF` (core 6) is defined after the FD-family helpers (below).
-- `zParityPropColsCore_WF` (core 4 z-dual) is proved after the col helpers + `xParityPropRowsCore_WF`.
-- `colCutNoZ_WF` is defined after `colCutLocal_WF` (below) to avoid a forward reference.
-- `zColsWeight_WF` is proved after the z-dual chain (below), to avoid a forward reference.

/-- **Grid-cell read is defined (X-row orientation).**  At a valid cell `(row, col)`
(`row, col < d`) the surface `E`-stabilizer read `stabAt bound (gridIdx d row col)` evaluates: its
value is the (total-`E`) slot at the linear index `d*row + col < nQubits`.  This is the single
reusable occupancy leaf behind *every* `xRow…` `FormulaDefined` obligation — the De Morgan range,
`xRowOccupiedAtF`, and `xRowsOccupiedAllRowsSupportF`. -/
theorem xCellReadDefined (D : OddSurfaceDistance) {E : PartialStabilizer}
    (hTotal : TotalUpTo (nQubits D.distance) E) {row col : Nat}
    (hrow : row < D.distance) (hcol : col < D.distance) :
    ∃ av, STerm.eval Surface.code.body (bridgeProofFuel D)
        ((STerm.weaken SC.bound).weaken.stabAt
          (STerm.closed (gridIdx (Term.natLit D.distance) rowVar1.weaken colVar)))
        (Env.cons col (Env.cons row Env.empty)) E = some av := by
  obtain ⟨p, hp⟩ := hTotal (D.distance * row + col)
    (by have := NatArithmetic.gridIdxLeft_lt_square hrow hcol; simpa [nQubits] using this)
  exact ⟨p, by
    simp [SC.bound, gridIdx, STerm.eval, STerm.weaken, STerm.lift,
      Term.eval, Term.weaken, Term.lift, Term.weakenVar, rowVar1, colVar, Env.cons, hp]⟩

/-- Column dual of `xCellReadDefined` (Z-col orientation): valid cell `(col, inner)` at the linear
index `d*inner + col`, with the `gridIdx` arguments transposed.  The reusable leaf behind every
`zCol…` `FormulaDefined` obligation. -/
theorem zCellReadDefined (D : OddSurfaceDistance) {E : PartialStabilizer}
    (hTotal : TotalUpTo (nQubits D.distance) E) {col inner : Nat}
    (hcol : col < D.distance) (hinner : inner < D.distance) :
    ∃ av, STerm.eval Surface.code.body (bridgeProofFuel D)
        ((STerm.weaken SC.bound).weaken.stabAt
          (STerm.closed (gridIdx (Term.natLit D.distance) colVar rowVar1.weaken)))
        (Env.cons inner (Env.cons col Env.empty)) E = some av := by
  obtain ⟨p, hp⟩ := hTotal (D.distance * inner + col)
    (by have := NatArithmetic.gridIdxLeft_lt_square hinner hcol; simpa [nQubits] using this)
  exact ⟨p, by
    simp [SC.bound, gridIdx, STerm.eval, STerm.weaken, STerm.lift,
      Term.eval, Term.weaken, Term.lift, Term.weakenVar, rowVar1, colVar, Env.cons, hp]⟩

end QHL.CodeLang.Surface.Verify
