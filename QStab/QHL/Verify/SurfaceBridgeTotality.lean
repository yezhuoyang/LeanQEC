import QStab.QHL.Verify.SurfaceBridges
import QStab.QHL.Verify.SurfaceRecConvergence

/-!
# Reusable eval-totality helpers for the Surface bridge `foldDisjoint` obligations

The two lower-bound bridge leaves `rowBridgeGeneratedPure`/`colBridgeGeneratedPure`
are `PureFamilyDeriv.foldDisjoint` nodes (see `SurfaceBridges.lean`).  Their
`DefinedObligations` (PureDeriv, `foldDisjoint` case) decomposes into three
pieces, `hbody` (strip body totality), `hlhs` (bridge LHS totality), and `hunion`
(the disjoint-tiling product identity).

This file builds the two *totality* pieces, `hbody` and `hlhs`, which are
genuinely reusable evaluation facts (they reappear in `codeLevelDefined`).  Both
are founded on the already-proved closed-term machinery:

* `hbody` — the strip body is a `.closed (codeRow …)` over a *pure* index, hence a
  `recCall` at the literal Surface distance.  Totality is `recCall_total_symbolicK`
  (SurfaceRecConvergence), with the `.closed` wrapper collapsing `STerm.eval` to
  `Term.eval`.
* `hlhs` — the bridge LHS is `stabMul` of two closed `rowCut`/`colCut` stabLams,
  each an everywhere-defined `ite`-lambda.  Totality is a direct evaluation.

No `sorry`/`native_decide`/new `axiom`/`Formula.check` is used.
-/

namespace QHL.CodeLang.Surface.Verify

open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

/-! ## Strip body totality (`hbody`)

The Pauli interpretation realised by the row strip body is
`gRowStrip d row iv q = (the surface stabilizer entry `codeRow d (rowZStripIndex d
row iv)` at qubit `q`)`.  Rather than name the entry function explicitly, we read
it off the convergent `recCall` value via `recCall_total_symbolicK`; the witness
`g` is `fun q => Classical.choose …`-free because we pull the whole stabilizer out
of the existential. -/

/-- The row strip body at index slot `iv` (de Bruijn 0) and row `row` (de Bruijn 1)
is the `recCall`-defined surface row at the strip index, which is total up to
`nQubits D.distance`.  This is exactly the `hbody` shape of the row bridge's
`foldDisjoint` obligation, *uncurried over the chosen interpretation*. -/
theorem rowStripBody_total (D : OddSurfaceDistance) (E : PartialStabilizer)
    (row iv : Nat) :
    ∃ sa,
      STerm.eval Surface.code.body (bridgeProofFuel D) (rowStripBody D)
          (Env.cons iv (Env.cons row Env.empty)) E = some sa ∧
        ∀ q, q < Surface.nQubits D.distance → ∃ p, sa q = some p := by
  -- `.closed` collapses `STerm.eval` to `Term.eval`; the body is a `recCall` at
  -- the literal distance over a pure index.
  have hpure : SFormula.PureNatTerm
      (rowZStripIndex D.distance (rowVar1.weaken : Term 2 .nat) (colVar : Term 2 .nat)) :=
    rowZStripIndexPure D.distance
      (SFormula.PureNatTerm.var _) (SFormula.PureNatTerm.var _)
  have hdist : D.distance = 2 * D.index + 3 := rfl
  have hfuel : D.index + 2 ≤ bridgeProofFuel D := by
    simp only [bridgeProofFuel, hdist]; omega
  obtain ⟨sa, hsa, htot⟩ :=
    recCall_total_symbolicK D.index (bridgeProofFuel D) hfuel hpure
      (Env.cons iv (Env.cons row Env.empty))
  refine ⟨sa, ?_, ?_⟩
  · -- collapse `.closed` and rewrite `D.distance = 2*D.index+3`
    simp only [rowStripBody, Formula.codeRow, STerm.eval]
    rw [show (Term.natLit (arity := 2) D.distance) = Term.natLit (2 * D.index + 3) from by
        rw [hdist]]
    exact hsa
  · intro q hq
    have : q < (2 * D.index + 3) * (2 * D.index + 3) := by
      rw [show Surface.nQubits D.distance = (2 * D.index + 3) * (2 * D.index + 3) from by
          rw [hdist]; rfl] at hq
      exact hq
    exact htot q this

/-- The column strip body totality, dual to `rowStripBody_total`. -/
theorem colStripBody_total (D : OddSurfaceDistance) (E : PartialStabilizer)
    (row iv : Nat) :
    ∃ sa,
      STerm.eval Surface.code.body (bridgeProofFuel D) (colStripBody D)
          (Env.cons iv (Env.cons row Env.empty)) E = some sa ∧
        ∀ q, q < Surface.nQubits D.distance → ∃ p, sa q = some p := by
  have hpure : SFormula.PureNatTerm
      (colXStripIndex D.distance (rowVar1.weaken : Term 2 .nat) (colVar : Term 2 .nat)) :=
    colXStripIndexPure D.distance
      (SFormula.PureNatTerm.var _) (SFormula.PureNatTerm.var _)
  have hdist : D.distance = 2 * D.index + 3 := rfl
  have hfuel : D.index + 2 ≤ bridgeProofFuel D := by
    simp only [bridgeProofFuel, hdist]; omega
  obtain ⟨sa, hsa, htot⟩ :=
    recCall_total_symbolicK D.index (bridgeProofFuel D) hfuel hpure
      (Env.cons iv (Env.cons row Env.empty))
  refine ⟨sa, ?_, ?_⟩
  · simp only [colStripBody, Formula.codeRow, STerm.eval]
    rw [show (Term.natLit (arity := 2) D.distance) = Term.natLit (2 * D.index + 3) from by
        rw [hdist]]
    exact hsa
  · intro q hq
    have : q < (2 * D.index + 3) * (2 * D.index + 3) := by
      rw [show Surface.nQubits D.distance = (2 * D.index + 3) * (2 * D.index + 3) from by
          rw [hdist]; rfl] at hq
      exact hq
    exact htot q this

/-! ## Bridge LHS totality (`hlhs`)

The row bridge LHS `rowBridge d row = stabMul (rowCut d row) (rowCut d (row+1))` is
a product of two closed `ite`-lambda cuts.  Each cut evaluates pointwise to `Z` on
its grid row and `I` elsewhere; the product is the everywhere-defined
`fun q => some (Pauli.mul (Z-if-q/d=row) (Z-if-q/d=row+1))`.  We name that Pauli
interpretation `tRow` and prove the eval directly. -/

/-- Evaluation of `SC.stabMul` of two **closed** stabilizer terms, given each
    closed term's pointwise value.  A public, closed-term-specialised analogue of
    the kernel's private `eval_stabMul_of_eval` (which we cannot reach), proved by
    direct unfolding through the `.closed` weakening (public `Term.eval_weaken_top`)
    rather than the private `STerm` lifting lemmas. -/
theorem eval_stabMul_closed {arity : Nat} (cb : Term 2 .stab) (fuel : Nat)
    (rho : Env arity) (E : PartialStabilizer)
    (sA sB : Term arity .stab) {Av Bv : PartialStabilizer}
    (hA : Term.eval cb fuel sA rho = some Av)
    (hB : Term.eval cb fuel sB rho = some Bv) :
    STerm.eval cb fuel (SC.stabMul (.closed sA) (.closed sB)) rho E =
      some (partialStabilizerMul Av Bv) := by
  simp only [SC.stabMul, STerm.eval, STerm.weaken, STerm.lift, SC.qVar, Term.eval]
  congr 1
  funext q
  have hAq : Term.eval cb fuel (sA.lift 0) (Env.cons q rho) = some Av := by
    rw [Term.eval_weaken_top]; exact hA
  have hBq : Term.eval cb fuel (sB.lift 0) (Env.cons q rho) = some Bv := by
    rw [Term.eval_weaken_top]; exact hB
  simp only [Env.cons, hAq, hBq, partialStabilizerMul, bind, Option.bind]

/-- The Pauli interpretation of one row cut: `Z` on grid row `r`, else `I`. -/
def rowCutPauli (dist r q : Nat) : Pauli :=
  if q / dist = r then Pauli.Z else Pauli.I

/-- The Pauli interpretation of one column cut: `X` on grid column `c`, else `I`. -/
def colCutPauli (dist c q : Nat) : Pauli :=
  if q % dist = c then Pauli.X else Pauli.I

/-- The two-row Z indicator realised by the row bridge LHS. -/
def tRow (dist row q : Nat) : Pauli :=
  Pauli.mul (rowCutPauli dist row q) (rowCutPauli dist (row + 1) q)

/-- The two-column X indicator realised by the column bridge LHS. -/
def tCol (dist col q : Nat) : Pauli :=
  Pauli.mul (colCutPauli dist col q) (colCutPauli dist (col + 1) q)

/-- The inner closed `Term` of a row cut `Surface.rowCut dist idx`. -/
def rowCutInnerTerm {arity : Nat} (dist : Nat) (idx : Term arity .nat) :
    Term arity .stab :=
  .stabLam <|
    .ite (.eqNat (.div Formula.qVar (.natLit dist)) idx.weaken)
      (.pauliLit Pauli.Z)
      (.pauliLit Pauli.I)

/-- The inner closed `Term` of a column cut. -/
def colCutInnerTerm {arity : Nat} (dist : Nat) (idx : Term arity .nat) :
    Term arity .stab :=
  .stabLam <|
    .ite (.eqNat (.mod Formula.qVar (.natLit dist)) idx.weaken)
      (.pauliLit Pauli.X)
      (.pauliLit Pauli.I)

theorem rowCut_closed (dist : Nat) {arity : Nat} (idx : Term arity .nat) :
    OpenStab.rowCut dist idx = .closed (rowCutInnerTerm dist idx) := rfl

theorem colCut_closed (dist : Nat) {arity : Nat} (idx : Term arity .nat) :
    OpenStab.colCut dist idx = .closed (colCutInnerTerm dist idx) := rfl

/-- A single closed row cut's inner term evaluates to its `Z`-on-row indicator at
    any nat-term index whose value is `rv`. -/
theorem rowCutInnerTerm_eval {arity : Nat} (dist : Nat) (cb : Term 2 .stab)
    (fuel rv : Nat) (idx : Term arity .nat) (rho : Env arity)
    (hidx : Term.eval cb fuel idx rho = some rv) :
    Term.eval cb fuel (rowCutInnerTerm dist idx) rho =
      some (fun q => some (rowCutPauli dist rv q)) := by
  simp only [rowCutInnerTerm, Term.eval]
  congr 1
  funext q
  have hidxW : Term.eval cb fuel idx.weaken (Env.cons q rho) = some rv := by
    rw [Term.weaken, Term.eval_weaken_top]; exact hidx
  simp only [Formula.qVar, Term.eval, Env.cons, hidxW, rowCutPauli]
  by_cases h : q / dist = rv <;> simp [h]

/-- A single closed column cut's inner term evaluates to its `X`-on-column
    indicator. -/
theorem colCutInnerTerm_eval {arity : Nat} (dist : Nat) (cb : Term 2 .stab)
    (fuel cv : Nat) (idx : Term arity .nat) (rho : Env arity)
    (hidx : Term.eval cb fuel idx rho = some cv) :
    Term.eval cb fuel (colCutInnerTerm dist idx) rho =
      some (fun q => some (colCutPauli dist cv q)) := by
  simp only [colCutInnerTerm, Term.eval]
  congr 1
  funext q
  have hidxW : Term.eval cb fuel idx.weaken (Env.cons q rho) = some cv := by
    rw [Term.weaken, Term.eval_weaken_top]; exact hidx
  simp only [Formula.qVar, Term.eval, Env.cons, hidxW, colCutPauli]
  by_cases h : q % dist = cv <;> simp [h]

/-- The row bridge LHS at row `row` (de Bruijn 0) evaluates to the two-row Z
    indicator `tRow d row`.  This is the `hlhs` shape of the row bridge's
    `foldDisjoint` obligation. -/
theorem rowBridge_eval (D : OddSurfaceDistance) (E : PartialStabilizer) (row : Nat) :
    STerm.eval Surface.code.body (bridgeProofFuel D)
        (OpenStab.rowBridge D.distance rowVar1) (Env.cons row Env.empty) E =
      some (fun q => some (tRow D.distance row q)) := by
  have hrow : Term.eval Surface.code.body (bridgeProofFuel D) rowVar1
      (Env.cons row Env.empty) = some row := by
    simp [rowVar1, Term.eval, Env.cons]
  have hsucc : Term.eval Surface.code.body (bridgeProofFuel D)
      (.add rowVar1 (.natLit 1)) (Env.cons row Env.empty) = some (row + 1) := by
    simp [Term.eval, hrow]
  have hA := rowCutInnerTerm_eval D.distance Surface.code.body (bridgeProofFuel D) row
    rowVar1 (Env.cons row Env.empty) hrow
  have hB := rowCutInnerTerm_eval D.distance Surface.code.body (bridgeProofFuel D) (row + 1)
    (.add rowVar1 (.natLit 1)) (Env.cons row Env.empty) hsucc
  have hmul := eval_stabMul_closed Surface.code.body (bridgeProofFuel D)
    (Env.cons row Env.empty) E
    (rowCutInnerTerm D.distance rowVar1)
    (rowCutInnerTerm D.distance (.add rowVar1 (.natLit 1))) hA hB
  rw [show OpenStab.rowBridge D.distance rowVar1
        = SC.stabMul (.closed (rowCutInnerTerm D.distance rowVar1))
            (.closed (rowCutInnerTerm D.distance (.add rowVar1 (.natLit 1)))) from rfl]
  rw [hmul]
  congr 1

/-- The column bridge LHS evaluation, dual to `rowBridge_eval`. -/
theorem colBridge_eval (D : OddSurfaceDistance) (E : PartialStabilizer) (col : Nat) :
    STerm.eval Surface.code.body (bridgeProofFuel D)
        (OpenStab.colBridge D.distance rowVar1) (Env.cons col Env.empty) E =
      some (fun q => some (tCol D.distance col q)) := by
  have hcol : Term.eval Surface.code.body (bridgeProofFuel D) rowVar1
      (Env.cons col Env.empty) = some col := by
    simp [rowVar1, Term.eval, Env.cons]
  have hsucc : Term.eval Surface.code.body (bridgeProofFuel D)
      (.add rowVar1 (.natLit 1)) (Env.cons col Env.empty) = some (col + 1) := by
    simp [Term.eval, hcol]
  have hA := colCutInnerTerm_eval D.distance Surface.code.body (bridgeProofFuel D) col
    rowVar1 (Env.cons col Env.empty) hcol
  have hB := colCutInnerTerm_eval D.distance Surface.code.body (bridgeProofFuel D) (col + 1)
    (.add rowVar1 (.natLit 1)) (Env.cons col Env.empty) hsucc
  have hmul := eval_stabMul_closed Surface.code.body (bridgeProofFuel D)
    (Env.cons col Env.empty) E
    (colCutInnerTerm D.distance rowVar1)
    (colCutInnerTerm D.distance (.add rowVar1 (.natLit 1))) hA hB
  rw [show OpenStab.colBridge D.distance rowVar1
        = SC.stabMul (.closed (colCutInnerTerm D.distance rowVar1))
            (.closed (colCutInnerTerm D.distance (.add rowVar1 (.natLit 1)))) from rfl]
  rw [hmul]
  congr 1

#print axioms rowStripBody_total
#print axioms colStripBody_total
#print axioms eval_stabMul_closed
#print axioms rowBridge_eval
#print axioms colBridge_eval

end QHL.CodeLang.Surface.Verify
