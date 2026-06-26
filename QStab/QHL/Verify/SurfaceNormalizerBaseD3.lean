import QStab.QHL.Verify.SurfaceNormalizers
import QStab.QHL.Verify.SurfaceRowCharacterizationGrid

/-!
# `d = 3` base case of the logical normalizers (prover-side)

This file proves, for the base distance `d = 3` (`OddSurfaceDistance.d3`), that the
two logical operators `logicalX` / `logicalZ` commute with every generated
stabilizer row of the Surface code.  These are the `d = 3` base cases of the two
normalizer family derivations `xNormScaffold` / `zNormScaffold` (in
`SurfaceNormalizers.lean`), which the recursive step consumes elsewhere.

No `native_decide`, `Formula.check`, `Formula.eval`-as-proof, `deriveTrue?`,
`admit`, new `axiom`, `@[implemented_by]`, `unsafe`, or `sorry` in the final
result.
-/

namespace QHL.CodeLang.Surface.Verify

open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface

set_option maxRecDepth 65536

/-- The literal case-split formula for the bound stabilizer index `k = var 0`:
`k < 8 → (k = 0 ∨ … ∨ k = 7)`.  This is a pure (Nat/Bool) arithmetic formula, so
it lies in the `arithBoolFragment` and is dischargeable semantically. -/
def boundIndexLiteralSplitF : SFormula 1 :=
  .imp (SFormula.boundNatLt (SC.n (arity := 0) 8))
    (.or (.eqNat SFormula.boundNat (SC.n (arity := 1) 0))
      (.or (.eqNat SFormula.boundNat (SC.n (arity := 1) 1))
        (.or (.eqNat SFormula.boundNat (SC.n (arity := 1) 2))
          (.or (.eqNat SFormula.boundNat (SC.n (arity := 1) 3))
            (.or (.eqNat SFormula.boundNat (SC.n (arity := 1) 4))
              (.or (.eqNat SFormula.boundNat (SC.n (arity := 1) 5))
                (.or (.eqNat SFormula.boundNat (SC.n (arity := 1) 6))
                  (.eqNat SFormula.boundNat (SC.n (arity := 1) 7)))))))))

/-- **Linchpin (proven, axiom-clean `[propext, Quot.sound]`).**  The bound
stabilizer index `k` satisfies `k < 8 → (k = 0 ∨ … ∨ k = 7)`.  Discharged by
`PureFamilyDerivA.arithBool` — a closed, decidable Nat/Bool side condition
evaluated over every environment, NOT a commutation/Pauli goal.  This is exactly
the bridge a literal-`k` (ROUTE A) completion needs to turn the symbolic bound
index into the eight concrete base-cell cases. -/
def boundIndexLiteralSplit :
    PureFamilyDerivA Surface.code.body 5 boundIndexLiteralSplitF := by
  refine PureFamilyDerivA.arithBool boundIndexLiteralSplitF (by decide) ?_
  intro rho E
  simp only [boundIndexLiteralSplitF, SFormula.eval, SFormula.boundNatLt, SFormula.witnessLt,
    SFormula.boundNat, SC.n, SC.b, SC.closed, STerm.eval, STerm.weaken, STerm.lift,
    Term.lift, Term.eval, bind, Option.bind, decide_eq_true_eq]
  generalize rho ⟨0, Nat.succ_pos 0⟩ = m
  clear E rho
  by_cases h0 : m = 0
  · subst h0; rfl
  by_cases h1 : m = 1
  · subst h1; rfl
  by_cases h2 : m = 2
  · subst h2; rfl
  by_cases h3 : m = 3
  · subst h3; rfl
  by_cases h4 : m = 4
  · subst h4; rfl
  by_cases h5 : m = 5
  · subst h5; rfl
  by_cases h6 : m = 6
  · subst h6; rfl
  by_cases hlt : m < 8
  · have h7 : m = 7 := by omega
    subst h7; rfl
  · simp only [hlt, if_false]

/-- The `d = 3` distance literal as it appears in the resolved row entry:
`Term.lift 0 (Term.natLit 3)`. -/
abbrev d3dT : Term 1 .nat := Term.lift 0 (Term.natLit 3)


/-- The bound stabilizer index `k = var 0` at arity 1. -/
abbrev kVar1 : Term 1 .nat := Term.var ⟨0, by decide⟩

/-- Probe helper: resolve the row entry at a literal qubit `q < 9` from the
weakened doubly-quantified resolved-row hypothesis `hH`. -/
def probeEntryAt {Γ : List (SFormula 1)}
    (hH : SFormula.Deriv Γ
      (SFormula.allNatLt (SC.n (numStab OddSurfaceDistance.d3.distance))
              (SFormula.allNatLt (SC.n (nQubits OddSurfaceDistance.d3.distance))
                (SFormula.eqPauli
                  ((SC.closed ((distAtBoundIdx2 OddSurfaceDistance.d3).dT.recCall liftedBoundIdx)).stabAt
                    (SC.closed Formula.qVar))
                  (SC.closed
                    (rowSymTreeA OddSurfaceDistance.d3.index (distAtBoundIdx2 OddSurfaceDistance.d3).dT liftedBoundIdx
                      Formula.qVar))))).weaken)
    (hbnd : SFormula.Deriv Γ
      (SFormula.witnessLt SFormula.boundNat (SC.n (numStab OddSurfaceDistance.d3.distance)).weaken))
    (q : Nat) (hq : q < 9) :
    SFormula.Deriv Γ
      (SFormula.instantiateTopNat (Term.natLit q)
        (SFormula.eqPauli
          ((SC.closed ((distAtBoundIdx2 OddSurfaceDistance.d3).dT.recCall liftedBoundIdx)).stabAt
            (SC.closed Formula.qVar))
          (SC.closed
            (rowSymTreeA OddSurfaceDistance.d3.index (distAtBoundIdx2 OddSurfaceDistance.d3).dT liftedBoundIdx
              Formula.qVar)))) := by
  have hElim := SFormula.Deriv.allNatLtElim _ _ SFormula.boundNat hH hbnd
  have hBeta := SFormula.Deriv.applyNatBoundNatBeta _ hElim
  have hQ := SFormula.Deriv.allNatLtElim _ _ (SC.n q) hBeta
    (SFormula.Deriv.closedNatLt q 9 (by simpa using hq))
  exact SFormula.Deriv.applyNatSubstitutionBetaElim (Term.natLit q) _
    (SFormula.PureNatTerm.natLit q) hQ

/-- **Universal guard-implication bridge.**  For any purely-arithmetic Boolean
guard `G : Term 1 .bool` over the bound stabilizer index `k = var 0`, the
conditional `k = i → (G = v)` holds in every environment provided it holds at the
single relevant point `k = i` (a closed, decidable arithmetic check `hpoint`).
Discharged by the scoped `arithBool` rule — never a commutation/Pauli goal.  The
`m ≠ i` case is vacuous (the antecedent is false). -/
def guardImp (G : Term 1 .bool) (i : Nat) (v : Bool)
    (hfrag : arithBoolFragment
      (SFormula.imp (.eqNat SFormula.boundNat (SC.n (arity := 1) i))
        (.eqBool (SC.closed G) (SC.b v))) = true)
    (hpoint : ∀ (rho : Env 1), rho ⟨0, Nat.succ_pos 0⟩ = i →
      Term.eval Surface.code.body 5 G rho = some v) :
    PureFamilyDerivA Surface.code.body 5
      (SFormula.imp (.eqNat SFormula.boundNat (SC.n (arity := 1) i))
        (.eqBool (SC.closed G) (SC.b v))) := by
  refine PureFamilyDerivA.arithBool _ hfrag ?_
  intro rho E
  simp only [SFormula.eval, SFormula.boundNat, SC.n, SC.b, SC.closed, STerm.eval, Term.eval,
    bind, Option.bind]
  by_cases h0 : rho ⟨0, Nat.succ_pos 0⟩ = i
  · rw [if_pos (by simpa using h0), hpoint rho h0]; simp
  · rw [if_neg (by simpa using h0)]

/-! ### `d = 3` clean entries, guard facts, and parity assembly

`d3.index = 0`, so `rowSymTreeA d3.index = baseLeafTreeTA`.  At the consumer arity
1 (bound stabilizer index `k = var 0`) the resolved row entry at a literal qubit
`q < 9` is `baseLeafTreeTA (natLit 3) (var 0) (natLit q)`, with `dT = natLit 3`
(`d3.distance = 3`) and the binder `k` reduced back to `var 0`. -/

/-- Distance literal at arity 1, in the form the resolved entry normalizes to. -/
abbrev dN : Term 1 .nat := Term.natLit 3
/-- Bound stabilizer index `k = var 0` at arity 1, frozen form. -/
abbrev kN : Term 1 .nat := Term.var ⟨0, by decide⟩

/-- Clean resolved row entry at literal qubit `q < 9`: from the weakened
doubly-quantified resolved-row hypothesis `hH` and `boundNat < 8`, the generated
row entry at `q` equals the base leaf tree `baseLeafTreeTA (natLit 3) (var 0)
(natLit q)`.  Mirrors `probeEntryAt`, then normalizes `rowSymTreeA 0 = baseLeafTreeTA`
and pushes the qubit substitution `q := natLit q` through the leaf tree. -/
def xCleanProbe {Γ : List (SFormula 1)}
    (hH : SFormula.Deriv Γ
      (SFormula.allNatLt (SC.n (numStab OddSurfaceDistance.d3.distance))
              (SFormula.allNatLt (SC.n (nQubits OddSurfaceDistance.d3.distance))
                (SFormula.eqPauli
                  ((SC.closed ((distAtBoundIdx2 OddSurfaceDistance.d3).dT.recCall liftedBoundIdx)).stabAt
                    (SC.closed Formula.qVar))
                  (SC.closed
                    (rowSymTreeA OddSurfaceDistance.d3.index (distAtBoundIdx2 OddSurfaceDistance.d3).dT liftedBoundIdx
                      Formula.qVar))))).weaken)
    (hbnd : SFormula.Deriv Γ
      (SFormula.witnessLt SFormula.boundNat (SC.n (numStab OddSurfaceDistance.d3.distance)).weaken))
    (q : Nat) (hq : q < 9) :
    SFormula.Deriv Γ
      (SFormula.eqPauli
        ((SC.closed (Term.recCall dN kN)).stabAt (SC.closed (Term.natLit q)))
        (SC.closed (baseLeafTreeTA dN kN (Term.natLit q)))) := by
  have h := probeEntryAt hH hbnd q hq
  simp only [SFormula.instantiateTopNat, SFormula.instantiateNatAt, STerm.instantiateNatAt,
    SC.closed, rowSymTreeA, OddSurfaceDistance.d3,
    OddSurfaceDistance.distance, oddDistance, Formula.qVar,
    liftedBoundIdx, boundIdx, baseLeafTreeTA,
    bulkGuardTA, baseBulkBandGuardTA, baseKindGuardTA, topClassGuardTA, topBandGuardTA,
    rightClassGuardTA, rightBandGuardTA, leftClassGuardTA, leftBandGuardTA, bottomBandGuardTA,
    bulkCountTA, dm1TA, baseBTA, baseHalfTA, band3, orEqSucc, orEqPair, distAtBoundIdx2,
    Term.instantiateNatAt, Term.lift, Term.weakenVar,
    Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff,
    Nat.lt_irrefl, reduceDIte] at h
  exact h

/-! ### Leaf peels (public mirrors of the private `leaf*` peels)

Each reduces `baseLeafTreeTA dN kN (natLit q)` to its leaf Pauli given the cell
guards (as `SFormula.Deriv` premises).  They are `eqPauliTrans` chains of
`pauliIteSelectThen/Else` over the `ite`-tree structure of `baseLeafTreeTA`. -/

private def xleafZ {Γ : List (SFormula 1)} (q : Nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dN kN)) (SC.b true)))
    (hBand : SFormula.Deriv Γ (.eqBool (SC.closed (baseBulkBandGuardTA dN kN (Term.natLit q))) (SC.b true)))
    (hKind : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA dN kN)) (SC.b true))) :
    SFormula.Deriv Γ (.eqPauli (SC.closed (baseLeafTreeTA dN kN (Term.natLit q))) (SC.p Pauli.Z)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hBand)
      (SFormula.Deriv.pauliIteSelectThen _ _ _ hKind))

private def xleafBulkX {Γ : List (SFormula 1)} (q : Nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dN kN)) (SC.b true)))
    (hBand : SFormula.Deriv Γ (.eqBool (SC.closed (baseBulkBandGuardTA dN kN (Term.natLit q))) (SC.b true)))
    (hKind : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA dN kN)) (SC.b false))) :
    SFormula.Deriv Γ (.eqPauli (SC.closed (baseLeafTreeTA dN kN (Term.natLit q))) (SC.p Pauli.X)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hBand)
      (SFormula.Deriv.pauliIteSelectElse _ _ _ hKind))

private def xleafBulkI {Γ : List (SFormula 1)} (q : Nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dN kN)) (SC.b true)))
    (hBand : SFormula.Deriv Γ (.eqBool (SC.closed (baseBulkBandGuardTA dN kN (Term.natLit q))) (SC.b false))) :
    SFormula.Deriv Γ (.eqPauli (SC.closed (baseLeafTreeTA dN kN (Term.natLit q))) (SC.p Pauli.I)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hBulk)
    (SFormula.Deriv.pauliIteSelectElse _ _ _ hBand)

private def xleafTopX {Γ : List (SFormula 1)} (q : Nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dN kN)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dN kN)) (SC.b true)))
    (hTopBand : SFormula.Deriv Γ (.eqBool (SC.closed (topBandGuardTA dN kN (Term.natLit q))) (SC.b true))) :
    SFormula.Deriv Γ (.eqPauli (SC.closed (baseLeafTreeTA dN kN (Term.natLit q))) (SC.p Pauli.X)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hTopClass)
      (SFormula.Deriv.pauliIteSelectThen _ _ _ hTopBand))

private def xleafTopI {Γ : List (SFormula 1)} (q : Nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dN kN)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dN kN)) (SC.b true)))
    (hTopBand : SFormula.Deriv Γ (.eqBool (SC.closed (topBandGuardTA dN kN (Term.natLit q))) (SC.b false))) :
    SFormula.Deriv Γ (.eqPauli (SC.closed (baseLeafTreeTA dN kN (Term.natLit q))) (SC.p Pauli.I)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hTopClass)
      (SFormula.Deriv.pauliIteSelectElse _ _ _ hTopBand))

private def xleafRightI {Γ : List (SFormula 1)} (q : Nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dN kN)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dN kN)) (SC.b false)))
    (hRightClass : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA dN kN)) (SC.b true)))
    (hRightBand : SFormula.Deriv Γ (.eqBool (SC.closed (rightBandGuardTA dN kN (Term.natLit q))) (SC.b false))) :
    SFormula.Deriv Γ (.eqPauli (SC.closed (baseLeafTreeTA dN kN (Term.natLit q))) (SC.p Pauli.I)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hTopClass)
      (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hRightClass)
        (SFormula.Deriv.pauliIteSelectElse _ _ _ hRightBand)))

private def xleafLeftZ {Γ : List (SFormula 1)} (q : Nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dN kN)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dN kN)) (SC.b false)))
    (hRightClass : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA dN kN)) (SC.b false)))
    (hLeftClass : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA dN kN)) (SC.b true)))
    (hLeftBand : SFormula.Deriv Γ (.eqBool (SC.closed (leftBandGuardTA dN kN (Term.natLit q))) (SC.b true))) :
    SFormula.Deriv Γ (.eqPauli (SC.closed (baseLeafTreeTA dN kN (Term.natLit q))) (SC.p Pauli.Z)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hTopClass)
      (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hRightClass)
        (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hLeftClass)
          (SFormula.Deriv.pauliIteSelectThen _ _ _ hLeftBand))))

private def xleafLeftI {Γ : List (SFormula 1)} (q : Nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dN kN)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dN kN)) (SC.b false)))
    (hRightClass : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA dN kN)) (SC.b false)))
    (hLeftClass : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA dN kN)) (SC.b true)))
    (hLeftBand : SFormula.Deriv Γ (.eqBool (SC.closed (leftBandGuardTA dN kN (Term.natLit q))) (SC.b false))) :
    SFormula.Deriv Γ (.eqPauli (SC.closed (baseLeafTreeTA dN kN (Term.natLit q))) (SC.p Pauli.I)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hTopClass)
      (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hRightClass)
        (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hLeftClass)
          (SFormula.Deriv.pauliIteSelectElse _ _ _ hLeftBand))))

private def xleafBottomI {Γ : List (SFormula 1)} (q : Nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dN kN)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dN kN)) (SC.b false)))
    (hRightClass : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA dN kN)) (SC.b false)))
    (hLeftClass : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA dN kN)) (SC.b false)))
    (hBottomBand : SFormula.Deriv Γ (.eqBool (SC.closed (bottomBandGuardTA dN kN (Term.natLit q))) (SC.b false))) :
    SFormula.Deriv Γ (.eqPauli (SC.closed (baseLeafTreeTA dN kN (Term.natLit q))) (SC.p Pauli.I)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hTopClass)
      (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hRightClass)
        (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hLeftClass)
          (SFormula.Deriv.pauliIteSelectElse _ _ _ hBottomBand))))

/-- Guard fact abbreviation: `eqBool (SC.closed G) (SC.b v)` at arity 1. -/
abbrev gB (G : Term 1 .bool) (v : Bool) : SFormula 1 := .eqBool (SC.closed G) (SC.b v)

/-- Branch hypothesis `k = i` at arity 1. -/
abbrev kEq (i : Nat) : SFormula 1 := .eqNat SFormula.boundNat (SC.n (arity := 1) i)

-- Per-branch guard conjunctions (the guards along the peel paths of the col-0
-- qubits q ∈ {0,3,6}), computed for d = 3 (dm1 = 2, bulkCount = 4, half = 1).
abbrev bulk (v : Bool) : SFormula 1 := gB (bulkGuardTA dN kN) v
abbrev band (q : Nat) (v : Bool) : SFormula 1 := gB (baseBulkBandGuardTA dN kN (Term.natLit q)) v
abbrev kind (v : Bool) : SFormula 1 := gB (baseKindGuardTA dN kN) v
abbrev topC (v : Bool) : SFormula 1 := gB (topClassGuardTA dN kN) v
abbrev topB (q : Nat) (v : Bool) : SFormula 1 := gB (topBandGuardTA dN kN (Term.natLit q)) v
abbrev rightC (v : Bool) : SFormula 1 := gB (rightClassGuardTA dN kN) v
abbrev rightB (q : Nat) (v : Bool) : SFormula 1 := gB (rightBandGuardTA dN kN (Term.natLit q)) v
abbrev leftC (v : Bool) : SFormula 1 := gB (leftClassGuardTA dN kN) v
abbrev leftB (q : Nat) (v : Bool) : SFormula 1 := gB (leftBandGuardTA dN kN (Term.natLit q)) v
abbrev botB (q : Nat) (v : Bool) : SFormula 1 := gB (bottomBandGuardTA dN kN (Term.natLit q)) v

abbrev branchConj0 : SFormula 1 :=
  .and (bulk true) (.and (band 0 true) (.and (band 3 true) (.and (band 6 false) (kind true))))
abbrev branchConj1 : SFormula 1 :=
  .and (bulk true) (.and (band 0 false) (.and (band 3 false) (band 6 false)))
abbrev branchConj2 : SFormula 1 :=
  .and (bulk true) (.and (band 0 false) (.and (band 3 true) (.and (band 6 true) (kind false))))
abbrev branchConj3 : SFormula 1 :=
  .and (bulk true) (.and (band 0 false) (.and (band 3 false) (band 6 false)))
abbrev branchConj4 : SFormula 1 :=
  .and (bulk false) (.and (topC true) (.and (topB 0 true) (.and (topB 3 false) (topB 6 false))))
abbrev branchConj5 : SFormula 1 :=
  .and (bulk false) (.and (topC false) (.and (rightC true)
    (.and (rightB 0 false) (.and (rightB 3 false) (rightB 6 false)))))
abbrev branchConj6 : SFormula 1 :=
  .and (bulk false) (.and (topC false) (.and (rightC false) (.and (leftC true)
    (.and (leftB 0 false) (.and (leftB 3 true) (leftB 6 true))))))
abbrev branchConj7 : SFormula 1 :=
  .and (bulk false) (.and (topC false) (.and (rightC false) (.and (leftC false)
    (.and (botB 0 false) (.and (botB 3 false) (botB 6 false))))))

/-- The literal-split disjunction body `k = 0 ∨ … ∨ k = 7` at arity 1. -/
abbrev orDisj : SFormula 1 :=
  .or (kEq 0) (.or (kEq 1) (.or (kEq 2) (.or (kEq 3)
    (.or (kEq 4) (.or (kEq 5) (.or (kEq 6) (kEq 7)))))))

/-- Column-0 classifier body (arity 2, qubit binder = `boundNat`): if the
`logicalX` column guard `q mod 3 = 0` holds at `q < 9`, then `q ∈ {0,3,6}`. -/
abbrev qClassBody : SFormula 2 :=
  .imp (SFormula.boundNatLt (SC.n (arity := 1) 9))
    (.imp (.eqBool (SC.closed (.eqNat (.mod (Term.var ⟨0, by decide⟩) (Term.natLit 3)) (Term.natLit 0)))
          (SC.b true))
      (.or (.eqNat SFormula.boundNat (SC.n (arity := 2) 0))
        (.or (.eqNat SFormula.boundNat (SC.n (arity := 2) 3))
          (.eqNat SFormula.boundNat (SC.n (arity := 2) 6)))))

/-- The column classifier, universally quantified over qubits `q < 9` (arity 1). -/
abbrev qClassF : SFormula 1 := .allNatLt (SC.n (arity := 1) 9) qClassBody

/-- Flipped column-0 classifier body: the disjunction is stated with the literal on
the LEFT (`q_col = boundNat`), the exact `eqNat` orientation the
`noAntiAtSubst`-based literal→symbolic transport consumes. -/
abbrev qClassFlipBody : SFormula 2 :=
  .imp (SFormula.boundNatLt (SC.n (arity := 1) 9))
    (.imp (.eqBool (SC.closed (.eqNat (.mod (Term.var ⟨0, by decide⟩) (Term.natLit 3)) (Term.natLit 0)))
          (SC.b true))
      (.or (.eqNat (SC.n (arity := 2) 0) SFormula.boundNat)
        (.or (.eqNat (SC.n (arity := 2) 3) SFormula.boundNat)
          (.eqNat (SC.n (arity := 2) 6) SFormula.boundNat))))

/-- Flipped column classifier, universally quantified over qubits `q < 9` (arity 1). -/
abbrev qClassFlipF : SFormula 1 := .allNatLt (SC.n (arity := 1) 9) qClassFlipBody

/-- Body of the column-0 `eqNat`-symmetry pack (arity 2, qubit binder `boundNat`):
for each `v ∈ {0,3,6}`, `v = boundNat → boundNat = v`.  A pure arithmetic tautology
in every environment; lets the two-anti branches flip the flipped-classifier pin
`v = boundNat` into the `boundNat ≠ v` orientation `commutesOfTwoAnti` excludes. -/
abbrev eqSymmBody : SFormula 2 :=
  .and (.imp (.eqNat (SC.n (arity := 2) 0) SFormula.boundNat) (.eqNat SFormula.boundNat (SC.n (arity := 2) 0)))
    (.and (.imp (.eqNat (SC.n (arity := 2) 3) SFormula.boundNat) (.eqNat SFormula.boundNat (SC.n (arity := 2) 3)))
      (.imp (.eqNat (SC.n (arity := 2) 6) SFormula.boundNat) (.eqNat SFormula.boundNat (SC.n (arity := 2) 6))))

/-- The column-0 `eqNat`-symmetry pack, quantified over qubits `q < 9` (arity 1). -/
abbrev eqSymmF : SFormula 1 := .allNatLt (SC.n (arity := 1) 9) eqSymmBody

/-- The closed `logicalX` column guard `q mod 3 = 0` at the three column-0 literal
qubits `{0,3,6}`, plus the two column-0 distinctness facts `0 ≠ 3` and `3 ≠ 6`
(needed by the two-anti branches), as one conjunction.  A finite arithmetic fact
(each guard is closed and decidable), discharged by `arithBool`. -/
abbrev colGuardPackF : SFormula 1 :=
  .and (.eqBool (SC.closed (.eqNat (.mod (Term.natLit 0) (.natLit 3)) (.natLit 0))) (SC.b true))
    (.and (.eqBool (SC.closed (.eqNat (.mod (Term.natLit 3) (.natLit 3)) (.natLit 0))) (SC.b true))
      (.and (.eqBool (SC.closed (.eqNat (.mod (Term.natLit 6) (.natLit 3)) (.natLit 0))) (SC.b true))
        (.and (.eqBool (SC.closed (.eqNat (Term.natLit 0) (Term.natLit 3))) (SC.b false))
          (.eqBool (SC.closed (.eqNat (Term.natLit 3) (Term.natLit 6))) (SC.b false)))))

/-- The combined arity-1 guard pack: the literal split plus the eight per-branch
guard conjunctions (each guarded by its branch hypothesis `k = i`).  Every conjunct
is a purely arithmetic Nat/Bool formula, so the whole pack lies in
`arithBoolFragment` and is dischargeable by `arithBool`. -/
abbrev xPackF : SFormula 1 :=
  .and (.imp (SFormula.boundNatLt (SC.n (arity := 0) 8)) orDisj)
    (.and (.imp (kEq 0) branchConj0)
      (.and (.imp (kEq 1) branchConj1)
        (.and (.imp (kEq 2) branchConj2)
          (.and (.imp (kEq 3) branchConj3)
            (.and (.imp (kEq 4) branchConj4)
              (.and (.imp (kEq 5) branchConj5)
                (.and (.imp (kEq 6) branchConj6)
                  (.imp (kEq 7) branchConj7))))))))

/-- The guard pack as a pure family derivation, discharged in one `arithBool`. -/
def xPack : PureFamilyDerivA Surface.code.body 5 xPackF := by
  refine PureFamilyDerivA.arithBool _ (by decide) ?_
  intro rho E
  simp only [
    bulkGuardTA, baseBulkBandGuardTA, baseKindGuardTA, topClassGuardTA, topBandGuardTA,
    rightClassGuardTA, rightBandGuardTA, leftClassGuardTA, leftBandGuardTA, bottomBandGuardTA,
    bulkCountTA, dm1TA, baseBTA, baseHalfTA, band3, orEqSucc, orEqPair,
    SFormula.eval, SFormula.boundNat, SFormula.boundNatLt, SFormula.witnessLt,
    SC.n, SC.b, SC.closed, STerm.eval, STerm.weaken, STerm.lift, Term.lift,
    Term.eval, bind, Option.bind, dN, kN]
  generalize rho ⟨0, Nat.succ_pos 0⟩ = m
  by_cases h0 : m = 0
  · subst h0; decide
  by_cases h1 : m = 1
  · subst h1; decide
  by_cases h2 : m = 2
  · subst h2; decide
  by_cases h3 : m = 3
  · subst h3; decide
  by_cases h4 : m = 4
  · subst h4; decide
  by_cases h5 : m = 5
  · subst h5; decide
  by_cases h6 : m = 6
  · subst h6; decide
  by_cases h7 : m = 7
  · subst h7; decide
  · have hlt : ¬ m < 8 := by omega
    simp only [h0, h1, h2, h3, h4, h5, h6, h7, hlt, decide_false, decide_true,
      Bool.false_eq_true, if_false, decide_eq_false_iff_not, decide_eq_true_eq, reduceIte]

/-- The column-0 classifier as a pure family derivation: for every qubit `q < 9`,
`q mod 3 = 0 → q ∈ {0,3,6}`.  A finite arithmetic check, discharged in one
`arithBool`. -/
def qPack : PureFamilyDerivA Surface.code.body 5 qClassF := by
  refine PureFamilyDerivA.allNatLtIntro (SC.n (arity := 1) 9) ?_
  refine PureFamilyDerivA.arithBool _ (by decide) ?_
  intro rho E
  simp only [SFormula.eval, SFormula.boundNat, SFormula.boundNatLt, SFormula.witnessLt,
    SC.n, SC.b, SC.closed, STerm.eval, STerm.weaken, STerm.lift, Term.lift,
    Term.eval, bind, Option.bind]
  generalize rho ⟨0, Nat.succ_pos 1⟩ = q
  by_cases hq0 : q = 0
  · subst hq0; decide
  by_cases hq1 : q = 1
  · subst hq1; decide
  by_cases hq2 : q = 2
  · subst hq2; decide
  by_cases hq3 : q = 3
  · subst hq3; decide
  by_cases hq4 : q = 4
  · subst hq4; decide
  by_cases hq5 : q = 5
  · subst hq5; decide
  by_cases hq6 : q = 6
  · subst hq6; decide
  by_cases hq7 : q = 7
  · subst hq7; decide
  by_cases hq8 : q = 8
  · subst hq8; decide
  · have hlt : ¬ q < 9 := by omega
    simp only [hlt, decide_false, Bool.false_eq_true, if_false]

/-- The flipped column classifier as a pure family derivation: for every `q < 9`,
`q mod 3 = 0 → (0 = q ∨ 3 = q ∨ 6 = q)`.  Identical finite arithmetic check to
`qPack`, with the disjuncts' `eqNat` orientation flipped. -/
def qFlipPack : PureFamilyDerivA Surface.code.body 5 qClassFlipF := by
  refine PureFamilyDerivA.allNatLtIntro (SC.n (arity := 1) 9) ?_
  refine PureFamilyDerivA.arithBool _ (by decide) ?_
  intro rho E
  simp only [SFormula.eval, SFormula.boundNat, SFormula.boundNatLt, SFormula.witnessLt,
    SC.n, SC.b, SC.closed, STerm.eval, STerm.weaken, STerm.lift, Term.lift,
    Term.eval, bind, Option.bind]
  generalize rho ⟨0, Nat.succ_pos 1⟩ = q
  by_cases hq0 : q = 0
  · subst hq0; decide
  by_cases hq1 : q = 1
  · subst hq1; decide
  by_cases hq2 : q = 2
  · subst hq2; decide
  by_cases hq3 : q = 3
  · subst hq3; decide
  by_cases hq4 : q = 4
  · subst hq4; decide
  by_cases hq5 : q = 5
  · subst hq5; decide
  by_cases hq6 : q = 6
  · subst hq6; decide
  by_cases hq7 : q = 7
  · subst hq7; decide
  by_cases hq8 : q = 8
  · subst hq8; decide
  · have hlt : ¬ q < 9 := by omega
    simp only [hlt, decide_false, Bool.false_eq_true, if_false]

/-- The closed column-0 guard pack as a pure family derivation: `q mod 3 = 0`
holds at `q ∈ {0,3,6}`.  A finite closed arithmetic check, discharged in one
`arithBool`. -/
def colGuardPack : PureFamilyDerivA Surface.code.body 5 colGuardPackF := by
  refine PureFamilyDerivA.arithBool _ (by decide) ?_
  intro rho E
  simp only [SFormula.eval, SC.b, SC.closed, STerm.eval, Term.eval, bind, Option.bind,
    Nat.reduceMod, Nat.reduceEqDiff, decide_true, decide_false, reduceIte]

/-- The column-0 `eqNat`-symmetry pack as a pure family derivation: for every
`q < 9` and `v ∈ {0,3,6}`, `v = q → q = v`.  A finite arithmetic tautology,
discharged in one `arithBool`. -/
def eqSymmPack : PureFamilyDerivA Surface.code.body 5 eqSymmF := by
  refine PureFamilyDerivA.allNatLtIntro (SC.n (arity := 1) 9) ?_
  refine PureFamilyDerivA.arithBool _ (by decide) ?_
  intro rho E
  simp only [SFormula.eval, SFormula.boundNat, SC.n, SC.closed, STerm.eval, Term.eval, bind, Option.bind]
  generalize rho ⟨0, Nat.succ_pos 1⟩ = q
  by_cases h0 : (0 : Nat) = q
  · subst h0; decide
  by_cases h3 : (3 : Nat) = q
  · subst h3; decide
  by_cases h6 : (6 : Nat) = q
  · subst h6; decide
  · simp only [h0, h3, h6, decide_false, Bool.false_eq_true, if_false, if_true]

/-- In the all-others premise (arity 2, qubit binder = `boundNat`) under the
`logicalX` column guard `q mod 3 = 0` (true), pin the qubit to `q ∈ {0,3,6}` from
the column classifier `qClassF` (weakened to arity 2) and the bound `q < 9`. -/
def xColQDisj (Δ : List (SFormula 2))
    (hQ : SFormula.Deriv Δ qClassF.weaken)
    (hq9 : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (SC.n (arity := 1) 9).weaken))
    (hcol : SFormula.Deriv Δ (.eqBool (logicalXColGuardAt2 OddSurfaceDistance.d3) (SC.b true))) :
    SFormula.Deriv Δ
      (.or (.eqNat SFormula.boundNat (SC.n (arity := 2) 0))
        (.or (.eqNat SFormula.boundNat (SC.n (arity := 2) 3))
          (.eqNat SFormula.boundNat (SC.n (arity := 2) 6)))) := by
  -- Eliminate the column classifier at the current qubit `boundNat`.
  have hElim := SFormula.Deriv.allNatLtElim (SC.n (arity := 1) 9).weaken (qClassBody.lift 1)
    SFormula.boundNat hQ hq9
  have hBody := SFormula.Deriv.applyNatBoundNatBeta qClassBody hElim
  -- `hBody : imp (q<9) (imp (q%3=0) (q∈{0,3,6}))`.
  have hq9' : SFormula.Deriv Δ (SFormula.boundNatLt (SC.n (arity := 1) 9)) := hq9
  have hImp2 := SFormula.Deriv.mp hBody hq9'
  -- Bridge the column guard `logicalXColGuardAt2 d3 = true` to the raw `q%3=0` form.
  have hMod : SFormula.Deriv Δ
      (.eqBool (SC.closed (.eqNat (.mod (Term.var ⟨0, by decide⟩) (Term.natLit 3)) (Term.natLit 0)))
        (SC.b true)) := by
    have hd : oddDistance OddSurfaceDistance.d3.index = 3 := by decide
    simpa [logicalXColGuardAt2, Formula.qVar, OddSurfaceDistance.distance, oddDistance,
      OddSurfaceDistance.index, OddSurfaceDistance.d3, SC.closed, SC.n, SC.b,
      Term.instantiateTopNat, Term.instantiateNatAt, hd] using hcol
  exact SFormula.Deriv.mp hImp2 hMod

/-- Flipped mirror of `xColQDisj`: same hypotheses, but the conclusion's `eqNat`
disjuncts have the literal on the LEFT (`q_col = boundNat`) — the orientation the
literal→symbolic transport via `noAntiAtSubst` consumes. -/
def xColQDisjFlip (Δ : List (SFormula 2))
    (hQ : SFormula.Deriv Δ qClassFlipF.weaken)
    (hq9 : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (SC.n (arity := 1) 9).weaken))
    (hcol : SFormula.Deriv Δ (.eqBool (logicalXColGuardAt2 OddSurfaceDistance.d3) (SC.b true))) :
    SFormula.Deriv Δ
      (.or (.eqNat (SC.n (arity := 2) 0) SFormula.boundNat)
        (.or (.eqNat (SC.n (arity := 2) 3) SFormula.boundNat)
          (.eqNat (SC.n (arity := 2) 6) SFormula.boundNat))) := by
  have hElim := SFormula.Deriv.allNatLtElim (SC.n (arity := 1) 9).weaken (qClassFlipBody.lift 1)
    SFormula.boundNat hQ hq9
  have hBody := SFormula.Deriv.applyNatBoundNatBeta qClassFlipBody hElim
  have hq9' : SFormula.Deriv Δ (SFormula.boundNatLt (SC.n (arity := 1) 9)) := hq9
  have hImp2 := SFormula.Deriv.mp hBody hq9'
  have hMod : SFormula.Deriv Δ
      (.eqBool (SC.closed (.eqNat (.mod (Term.var ⟨0, by decide⟩) (Term.natLit 3)) (Term.natLit 0)))
        (SC.b true)) := by
    have hd : oddDistance OddSurfaceDistance.d3.index = 3 := by decide
    simpa [logicalXColGuardAt2, Formula.qVar, OddSurfaceDistance.distance, oddDistance,
      OddSurfaceDistance.index, OddSurfaceDistance.d3, SC.closed, SC.n, SC.b,
      Term.instantiateTopNat, Term.instantiateNatAt, hd] using hcol
  exact SFormula.Deriv.mp hImp2 hMod

/-- Distance literal at arity 2, in the form the resolved entry normalizes to. -/
abbrev dN2 : Term 2 .nat := Term.natLit 3
/-- Ambient stabilizer index `k = var 1` at arity 2 (the once-weakened bound idx). -/
abbrev kN2 : Term 2 .nat := Term.var ⟨1, by decide⟩

/-- The single-quantified resolved row at the ambient (object-logic) stabilizer
index `k = var 0` (arity 1): `∀ q < 9, stabAt (recCall 3 (var 0)) q = rowSymTreeA
0 3 (var 0) q`.  This is the inner `allNatLt 9` body of `hH` after eliminating the
outer stabilizer-index quantifier at `boundNat`. -/
abbrev rowAt1 : SFormula 1 :=
  SFormula.allNatLt (SC.n (arity := 1) (nQubits OddSurfaceDistance.d3.distance))
    (SFormula.eqPauli
      ((SC.closed (Term.recCall (Term.lift 0 (Term.lift 0 (Term.natLit 3)))
        (Term.lift 0 (Term.var ⟨0, by decide⟩)))).stabAt (SC.closed Formula.qVar))
      (SC.closed (rowSymTreeA OddSurfaceDistance.d3.index
        (Term.lift 0 (Term.lift 0 (Term.natLit 3)))
        (Term.lift 0 (Term.var ⟨0, by decide⟩)) Formula.qVar)))

/-- Arity-2 mirror of `xCleanProbe` at a LITERAL qubit `q < 9`.  Consumes the
single-quantified resolved row `rowAt1` (weakened to arity 2), eliminates its qubit
quantifier at `natLit q`, and normalizes `rowSymTreeA 0 = baseLeafTreeTA`.  The
ambient stabilizer index stays symbolic (`k = var 1`). -/
def xCleanProbeLit2 {Δ : List (SFormula 2)}
    (hRowW : SFormula.Deriv Δ rowAt1.weaken)
    (q : Nat) (hq : q < 9) :
    SFormula.Deriv Δ
      (SFormula.eqPauli
        ((SC.closed (Term.recCall dN2 kN2)).stabAt (SC.closed (Term.natLit q)))
        (SC.closed (baseLeafTreeTA dN2 kN2 (Term.natLit q)))) := by
  -- Eliminate the (qubit) quantifier at `natLit q`.
  have hInner := SFormula.Deriv.allNatLtElim _ _ (SC.n q) hRowW
    (SFormula.Deriv.closedNatLt q 9 (by simpa using hq))
  have hQ := SFormula.Deriv.applyNatSubstitutionBetaElim (Term.natLit q) _
    (SFormula.PureNatTerm.natLit q) hInner
  -- Normalize `rowSymTreeA 0 = baseLeafTreeTA`, cancel the weakening lift, push the
  -- qubit substitution `q := natLit q` through the leaf tree.
  simp only [rowAt1, SFormula.weaken, SFormula.lift, STerm.weaken, STerm.lift,
    SFormula.instantiateTopNat, SFormula.instantiateNatAt, STerm.instantiateNatAt,
    SC.closed, SC.n, rowSymTreeA, OddSurfaceDistance.d3, Formula.qVar,
    baseLeafTreeTA,
    bulkGuardTA, baseBulkBandGuardTA, baseKindGuardTA, topClassGuardTA, topBandGuardTA,
    rightClassGuardTA, rightBandGuardTA, leftClassGuardTA, leftBandGuardTA, bottomBandGuardTA,
    bulkCountTA, dm1TA, baseBTA, baseHalfTA, band3, orEqSucc, orEqPair,
    Term.instantiateNatAt, Term.lift, Term.weaken, Term.weakenVar, Nat.reduceAdd,
    Nat.lt_irrefl, reduceDIte, SFormula.boundNat] at hQ ⊢
  exact hQ

/-- Arity-2 mirror of `xCleanProbe` at the SYMBOLIC qubit `boundNat`.  Consumes the
single-quantified resolved row `rowAt1` (weakened to arity 2), eliminates its qubit
quantifier at `boundNat`, and normalizes `rowSymTreeA 0 = baseLeafTreeTA`. -/
def xCleanProbeBound {Δ : List (SFormula 2)}
    (hRowW : SFormula.Deriv Δ rowAt1.weaken)
    (hq9 : SFormula.Deriv Δ
      (SFormula.witnessLt SFormula.boundNat (SC.n (nQubits OddSurfaceDistance.d3.distance)).weaken)) :
    SFormula.Deriv Δ
      (SFormula.eqPauli
        ((SC.closed (Term.recCall dN2 kN2)).stabAt SFormula.boundNat)
        (SC.closed (baseLeafTreeTA dN2 kN2 (Term.var ⟨0, by decide⟩)))) := by
  have hInner := SFormula.Deriv.allNatLtElim _ _ SFormula.boundNat hRowW hq9
  have hQ := SFormula.Deriv.applyNatBoundNatBeta _ hInner
  simp only [SC.closed, rowSymTreeA, OddSurfaceDistance.d3, Formula.qVar,
    baseLeafTreeTA,
    bulkGuardTA, baseBulkBandGuardTA, baseKindGuardTA, topClassGuardTA, topBandGuardTA,
    rightClassGuardTA, rightBandGuardTA, leftClassGuardTA, leftBandGuardTA, bottomBandGuardTA,
    bulkCountTA, dm1TA, baseBTA, baseHalfTA, band3, orEqSucc, orEqPair,
    Term.lift, Term.weakenVar, Nat.reduceAdd,
    Nat.lt_irrefl, reduceDIte, SFormula.boundNat] at hQ ⊢
  exact hQ

/-! ### Arity-2 leaf peels (public mirrors of the private arity-general `leaf*`)

Each reduces `baseLeafTreeTA dN2 kN2 (natLit q)` to its leaf Pauli given the cell
guards (as `SFormula.Deriv` premises at the ambient symbolic index `k = var 1`).
Identical `eqPauliTrans` chains of `pauliIteSelectThen/Else` to the arity-1
`xleaf*`, but at arity 2. -/

private def xleafZ2 {Δ : List (SFormula 2)} (q : Nat)
    (hBulk : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA dN2 kN2)) (SC.b true)))
    (hBand : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA dN2 kN2 (Term.natLit q))) (SC.b true)))
    (hKind : SFormula.Deriv Δ (.eqBool (SC.closed (baseKindGuardTA dN2 kN2)) (SC.b true))) :
    SFormula.Deriv Δ (.eqPauli (SC.closed (baseLeafTreeTA dN2 kN2 (Term.natLit q))) (SC.p Pauli.Z)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hBand)
      (SFormula.Deriv.pauliIteSelectThen _ _ _ hKind))

private def xleafBulkX2 {Δ : List (SFormula 2)} (q : Nat)
    (hBulk : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA dN2 kN2)) (SC.b true)))
    (hBand : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA dN2 kN2 (Term.natLit q))) (SC.b true)))
    (hKind : SFormula.Deriv Δ (.eqBool (SC.closed (baseKindGuardTA dN2 kN2)) (SC.b false))) :
    SFormula.Deriv Δ (.eqPauli (SC.closed (baseLeafTreeTA dN2 kN2 (Term.natLit q))) (SC.p Pauli.X)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hBand)
      (SFormula.Deriv.pauliIteSelectElse _ _ _ hKind))

private def xleafBulkI2 {Δ : List (SFormula 2)} (q : Nat)
    (hBulk : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA dN2 kN2)) (SC.b true)))
    (hBand : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA dN2 kN2 (Term.natLit q))) (SC.b false))) :
    SFormula.Deriv Δ (.eqPauli (SC.closed (baseLeafTreeTA dN2 kN2 (Term.natLit q))) (SC.p Pauli.I)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hBulk)
    (SFormula.Deriv.pauliIteSelectElse _ _ _ hBand)

private def xleafTopX2 {Δ : List (SFormula 2)} (q : Nat)
    (hBulk : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA dN2 kN2)) (SC.b false)))
    (hTopClass : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA dN2 kN2)) (SC.b true)))
    (hTopBand : SFormula.Deriv Δ (.eqBool (SC.closed (topBandGuardTA dN2 kN2 (Term.natLit q))) (SC.b true))) :
    SFormula.Deriv Δ (.eqPauli (SC.closed (baseLeafTreeTA dN2 kN2 (Term.natLit q))) (SC.p Pauli.X)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hTopClass)
      (SFormula.Deriv.pauliIteSelectThen _ _ _ hTopBand))

private def xleafTopI2 {Δ : List (SFormula 2)} (q : Nat)
    (hBulk : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA dN2 kN2)) (SC.b false)))
    (hTopClass : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA dN2 kN2)) (SC.b true)))
    (hTopBand : SFormula.Deriv Δ (.eqBool (SC.closed (topBandGuardTA dN2 kN2 (Term.natLit q))) (SC.b false))) :
    SFormula.Deriv Δ (.eqPauli (SC.closed (baseLeafTreeTA dN2 kN2 (Term.natLit q))) (SC.p Pauli.I)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hTopClass)
      (SFormula.Deriv.pauliIteSelectElse _ _ _ hTopBand))

private def xleafRightI2 {Δ : List (SFormula 2)} (q : Nat)
    (hBulk : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA dN2 kN2)) (SC.b false)))
    (hTopClass : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA dN2 kN2)) (SC.b false)))
    (hRightClass : SFormula.Deriv Δ (.eqBool (SC.closed (rightClassGuardTA dN2 kN2)) (SC.b true)))
    (hRightBand : SFormula.Deriv Δ (.eqBool (SC.closed (rightBandGuardTA dN2 kN2 (Term.natLit q))) (SC.b false))) :
    SFormula.Deriv Δ (.eqPauli (SC.closed (baseLeafTreeTA dN2 kN2 (Term.natLit q))) (SC.p Pauli.I)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hTopClass)
      (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hRightClass)
        (SFormula.Deriv.pauliIteSelectElse _ _ _ hRightBand)))

private def xleafLeftZ2 {Δ : List (SFormula 2)} (q : Nat)
    (hBulk : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA dN2 kN2)) (SC.b false)))
    (hTopClass : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA dN2 kN2)) (SC.b false)))
    (hRightClass : SFormula.Deriv Δ (.eqBool (SC.closed (rightClassGuardTA dN2 kN2)) (SC.b false)))
    (hLeftClass : SFormula.Deriv Δ (.eqBool (SC.closed (leftClassGuardTA dN2 kN2)) (SC.b true)))
    (hLeftBand : SFormula.Deriv Δ (.eqBool (SC.closed (leftBandGuardTA dN2 kN2 (Term.natLit q))) (SC.b true))) :
    SFormula.Deriv Δ (.eqPauli (SC.closed (baseLeafTreeTA dN2 kN2 (Term.natLit q))) (SC.p Pauli.Z)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hTopClass)
      (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hRightClass)
        (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hLeftClass)
          (SFormula.Deriv.pauliIteSelectThen _ _ _ hLeftBand))))

private def xleafLeftI2 {Δ : List (SFormula 2)} (q : Nat)
    (hBulk : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA dN2 kN2)) (SC.b false)))
    (hTopClass : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA dN2 kN2)) (SC.b false)))
    (hRightClass : SFormula.Deriv Δ (.eqBool (SC.closed (rightClassGuardTA dN2 kN2)) (SC.b false)))
    (hLeftClass : SFormula.Deriv Δ (.eqBool (SC.closed (leftClassGuardTA dN2 kN2)) (SC.b true)))
    (hLeftBand : SFormula.Deriv Δ (.eqBool (SC.closed (leftBandGuardTA dN2 kN2 (Term.natLit q))) (SC.b false))) :
    SFormula.Deriv Δ (.eqPauli (SC.closed (baseLeafTreeTA dN2 kN2 (Term.natLit q))) (SC.p Pauli.I)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hTopClass)
      (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hRightClass)
        (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hLeftClass)
          (SFormula.Deriv.pauliIteSelectElse _ _ _ hLeftBand))))

private def xleafBottomI2 {Δ : List (SFormula 2)} (q : Nat)
    (hBulk : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA dN2 kN2)) (SC.b false)))
    (hTopClass : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA dN2 kN2)) (SC.b false)))
    (hRightClass : SFormula.Deriv Δ (.eqBool (SC.closed (rightClassGuardTA dN2 kN2)) (SC.b false)))
    (hLeftClass : SFormula.Deriv Δ (.eqBool (SC.closed (leftClassGuardTA dN2 kN2)) (SC.b false)))
    (hBottomBand : SFormula.Deriv Δ (.eqBool (SC.closed (bottomBandGuardTA dN2 kN2 (Term.natLit q))) (SC.b false))) :
    SFormula.Deriv Δ (.eqPauli (SC.closed (baseLeafTreeTA dN2 kN2 (Term.natLit q))) (SC.p Pauli.I)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hTopClass)
      (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hRightClass)
        (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hLeftClass)
          (SFormula.Deriv.pauliIteSelectElse _ _ _ hBottomBand))))

/-- The lifted `logicalX` operator at arity 2 (`(lift logicalXOdd d3).weaken`), as
it appears on the right of the pointwise commutation goal. -/
abbrev liftedLogicalX2 : STerm 2 .stab :=
  (SC.closed (Term.lift 0 (logicalXOdd OddSurfaceDistance.d3))).weaken

/-- On a column-0 qubit (column guard `q mod 3 = 0` TRUE), the `logicalX` entry at
the bound qubit is `X`.  Mirror of `logicalXOffColumnLocalCommutes` but selecting
the THEN branch of the `logicalX` lambda. -/
def logicalXOnColumnEntryX {Δ : List (SFormula 2)}
    (hTrue : SFormula.Deriv Δ (.eqBool (logicalXColGuardAt2 OddSurfaceDistance.d3) (SC.b true))) :
    SFormula.Deriv Δ (.eqPauli (.stabAt liftedLogicalX2 SFormula.boundNat) (SC.p Pauli.X)) := by
  have h := SFormula.Deriv.stabAtClosedIteLamEqThen (Γ := Δ)
    (.eqNat (.mod Formula.qVar (.natLit OddSurfaceDistance.d3.distance)) (.natLit 0))
    (.pauliLit Pauli.X) (.pauliLit Pauli.I)
    (Term.var ⟨0, by decide⟩)
    (SFormula.PureNatTerm.var ⟨0, by decide⟩)
    (by simpa [logicalXColGuardAt2] using hTrue)
  simpa [liftedLogicalX2, logicalXOdd, logicalX, Formula.qVar, SFormula.boundNat, SC.closed, SC.p,
    OddSurfaceDistance.distance, oddDistance, OddSurfaceDistance.d3,
    STerm.weaken, STerm.lift, Term.instantiateTopNat, Term.instantiateNatAt, Term.lift,
    Term.weaken, Term.weakenVar] using h

/-- The lifted `logicalX` operator at arity 1 (`lift logicalXOdd d3`), as it appears
on the right of the per-row commutation goal. -/
abbrev liftedLogicalX1 : STerm 1 .stab :=
  SC.closed (Term.lift 0 (logicalXOdd OddSurfaceDistance.d3))

/-- The closed `logicalX` column guard `q mod 3 = 0` at a LITERAL qubit `q`. -/
abbrev colGuardLit (q : Nat) : SFormula 1 :=
  .eqBool (SC.closed (.eqNat (.mod (Term.natLit q) (.natLit 3)) (.natLit 0))) (SC.b true)

/-- At a LITERAL column-0 qubit `q`, given the closed column guard `q mod 3 = 0`
(supplied from the arithmetic guard pack), the `logicalX` entry is `X`.  Arity-1
literal mirror of `logicalXOnColumnEntryX`. -/
def logicalXLitEntryX {Γ : List (SFormula 1)} (q : Nat)
    (hguardq : SFormula.Deriv Γ (colGuardLit q)) :
    SFormula.Deriv Γ (.eqPauli (.stabAt liftedLogicalX1 (SC.closed (Term.natLit q))) (SC.p Pauli.X)) := by
  have hguard : SFormula.Deriv Γ
      (.eqBool (SC.closed (Term.instantiateTopNat (Term.natLit q)
        (.eqNat (.mod Formula.qVar (.natLit OddSurfaceDistance.d3.distance)) (.natLit 0)))) (SC.b true)) := by
    simpa [colGuardLit, Formula.qVar, OddSurfaceDistance.distance, oddDistance, OddSurfaceDistance.d3,
      Term.instantiateTopNat, Term.instantiateNatAt] using hguardq
  have h := SFormula.Deriv.stabAtClosedIteLamEqThen (Γ := Γ)
    (.eqNat (.mod Formula.qVar (.natLit OddSurfaceDistance.d3.distance)) (.natLit 0))
    (.pauliLit Pauli.X) (.pauliLit Pauli.I)
    (Term.natLit q) (SFormula.PureNatTerm.natLit q) hguard
  simpa [liftedLogicalX1, logicalXOdd, logicalX, Formula.qVar, SC.closed, SC.p,
    OddSurfaceDistance.distance, oddDistance, OddSurfaceDistance.d3,
    Term.instantiateTopNat, Term.instantiateNatAt, Term.lift] using h

/-- **Column-0 pointwise commutation via a literal-qubit row entry.**  For a left
stabilizer `A` whose entry at the LITERAL column-0 qubit `q` is the Pauli `pL`
(which commutes with `X`), and given the flipped pin `q = boundNat` and the column
guard true, `A` locally commutes with `logicalX` at the symbolic `boundNat`.  The
literal-qubit entry is transported to `boundNat` by `noAntiAtSubst` (sound, since
`boundNat` is `SC.closed` of a pure var), and the `logicalX` entry there is `X`. -/
def colCommViaLeft {Δ : List (SFormula 2)} (A : STerm 2 .stab) (pL : Pauli) (q : Nat)
    (hLeft : SFormula.Deriv Δ (.eqPauli (.stabAt A (SC.closed (Term.natLit q))) (SC.p pL)))
    (hAnti : SFormula.Deriv Δ (.eqBool (.anticommutes (SC.p pL) (SC.p Pauli.X)) (SC.b false)))
    (hEq : SFormula.Deriv Δ (.eqNat (SC.n (arity := 2) q) SFormula.boundNat))
    (hSelf : SFormula.Deriv Δ (.eqPauli (.stabAt A SFormula.boundNat) (.stabAt A SFormula.boundNat)))
    (hcol : SFormula.Deriv Δ (.eqBool (logicalXColGuardAt2 OddSurfaceDistance.d3) (SC.b true))) :
    SFormula.Deriv Δ (SFormula.localCommutesAt A liftedLogicalX2 SFormula.boundNat) := by
  -- Literal-qubit `not(anticommutes (stabAt A (natLit q)) X = true)`.
  have hLitFalse : SFormula.Deriv Δ
      (.eqBool (.anticommutes (.stabAt A (SC.closed (Term.natLit q))) (SC.p Pauli.X)) (SC.b false)) :=
    SFormula.Deriv.anticommutesTransport _ (SC.p pL) _ (SC.p Pauli.X) (SC.b false)
      hLeft (SFormula.Deriv.pauliEqLit Pauli.X) hAnti
  have hLitNot : SFormula.Deriv Δ
      (.not (.eqBool (.anticommutes (.stabAt A (SC.closed (Term.natLit q))) (SC.p Pauli.X)) (SC.b true))) :=
    SFormula.Deriv.eqBoolFalseNotTrue _ hLitFalse
  -- Transport literal → symbolic `boundNat`.
  have hBoundNot : SFormula.Deriv Δ
      (.not (.eqBool (.anticommutes (.stabAt A SFormula.boundNat) (SC.p Pauli.X)) (SC.b true))) :=
    SFormula.Deriv.noAntiAtSubst A (SC.p Pauli.X) (Term.natLit q) (Term.var ⟨0, by decide⟩)
      (SFormula.PureNatTerm.natLit q) (SFormula.PureNatTerm.var ⟨0, by decide⟩) hEq hLitNot
  -- The `logicalX` entry at `boundNat` is `X` (column guard true).
  have hRightX := logicalXOnColumnEntryX (Δ := Δ) hcol
  -- Assemble `localCommutesAt = not(anticommutes (stabAt A bn) (stabAt logicalX bn) = true)`.
  -- Inside `notIntro`, transport the head `anti(stabAt A bn, stabAt logicalX bn) = true`
  -- to `anti(stabAt A bn, X) = true`, contradicting `hBoundNot`.
  refine SFormula.Deriv.notIntro (SFormula.Deriv.notElim
    (SFormula.Deriv.anticommutesTransport (.stabAt A SFormula.boundNat) (.stabAt A SFormula.boundNat)
      (SC.p Pauli.X) (.stabAt liftedLogicalX2 SFormula.boundNat) (SC.b true)
      (SFormula.Deriv.contextWeakening (fun C hC => List.mem_cons_of_mem _ hC) hSelf)
      (SFormula.Deriv.eqPauliSymm _ _
        (SFormula.Deriv.contextWeakening (fun C hC => List.mem_cons_of_mem _ hC) hRightX))
      (.assumption))
    (SFormula.Deriv.contextWeakening (fun C hC => List.mem_cons_of_mem _ hC) hBoundNot))

/-- **Pointwise column-0 commutation dispatch (arity 2).**  Proves the
`localCommutesAt A (lift logicalX) boundNat` premise (the body of
`pointwiseCommutesUpTo` after the qubit binder is introduced), for a left stabilizer
`A` whose entries at the three column-0 qubits `{0,3,6}` are the literal Paulis
`p0, p3, p6` (each commuting with `X`).  Off-column-0 the `logicalX` entry is `I`
(`logicalXOffColumnLocalCommutes`); on-column-0 the qubit is pinned to `{0,3,6}` by
`xColQDisjFlip` and each case discharged by `colCommViaLeft`. -/
def colCommPointwise {Δ : List (SFormula 2)} (A : STerm 2 .stab)
    (hQFlipW : SFormula.Deriv Δ qClassFlipF.weaken)
    (hq9 : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (SC.n (arity := 1) 9).weaken))
    (p0 p3 p6 : Pauli)
    (h0 : SFormula.Deriv Δ (.eqPauli (.stabAt A (SC.closed (Term.natLit 0))) (SC.p p0)))
    (h3 : SFormula.Deriv Δ (.eqPauli (.stabAt A (SC.closed (Term.natLit 3))) (SC.p p3)))
    (h6 : SFormula.Deriv Δ (.eqPauli (.stabAt A (SC.closed (Term.natLit 6))) (SC.p p6)))
    (ha0 : SFormula.Deriv Δ (.eqBool (.anticommutes (SC.p p0) (SC.p Pauli.X)) (SC.b false)))
    (ha3 : SFormula.Deriv Δ (.eqBool (.anticommutes (SC.p p3) (SC.p Pauli.X)) (SC.b false)))
    (ha6 : SFormula.Deriv Δ (.eqBool (.anticommutes (SC.p p6) (SC.p Pauli.X)) (SC.b false)))
    (hself : SFormula.Deriv Δ (.eqPauli (.stabAt A SFormula.boundNat) (.stabAt A SFormula.boundNat))) :
    SFormula.Deriv Δ (SFormula.localCommutesAt A liftedLogicalX2 SFormula.boundNat) := by
  refine SFormula.Deriv.boolCases (logicalXColGuardAt2 OddSurfaceDistance.d3) _ ?_ ?_
  · -- column guard TRUE: boundNat ∈ {0,3,6}
    refine SFormula.Deriv.orElim
      (xColQDisjFlip _
        (SFormula.Deriv.contextWeakening (fun C hC => List.mem_cons_of_mem _ hC) hQFlipW)
        (SFormula.Deriv.contextWeakening (fun C hC => List.mem_cons_of_mem _ hC) hq9)
        (.assumption)) ?_ ?_
    · -- boundNat = 0
      exact colCommViaLeft A p0 0
        (SFormula.Deriv.contextWeakening (fun C hC =>
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC)) h0)
        (SFormula.Deriv.contextWeakening (fun C hC =>
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC)) ha0)
        (.assumption)
        (SFormula.Deriv.contextWeakening (fun C hC =>
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC)) hself)
        (.hyp (by right; left))
    refine SFormula.Deriv.orElim (.assumption) ?_ ?_
    · -- boundNat = 3
      exact colCommViaLeft A p3 3
        (SFormula.Deriv.contextWeakening (fun C hC =>
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC))) h3)
        (SFormula.Deriv.contextWeakening (fun C hC =>
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC))) ha3)
        (.assumption)
        (SFormula.Deriv.contextWeakening (fun C hC =>
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC))) hself)
        (.hyp (by right; right; left))
    · -- boundNat = 6
      exact colCommViaLeft A p6 6
        (SFormula.Deriv.contextWeakening (fun C hC =>
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC))) h6)
        (SFormula.Deriv.contextWeakening (fun C hC =>
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC))) ha6)
        (.assumption)
        (SFormula.Deriv.contextWeakening (fun C hC =>
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC))) hself)
        (.hyp (by right; right; left))
  · -- column guard FALSE: logicalX entry is I, off-column commutation
    exact logicalXOffColumnLocalCommutes OddSurfaceDistance.d3 _ (.assumption)

/-- Arity-1 → arity-2 row resolution at the qubit binder (context `Γ' → boundNatLt
9 :: Γ'.map weaken`). -/
private def rowAt1Weaken {Γ' : List (SFormula 1)} (hRow : SFormula.Deriv Γ' rowAt1) :
    SFormula.Deriv (SFormula.boundNatLt (SC.n (arity := 1) 9) :: Γ'.map (fun G => G.weaken))
      rowAt1.weaken :=
  SFormula.Deriv.contextWeakening (fun _C hC => List.mem_cons_of_mem _ hC)
    (SFormula.Deriv.weakenFresh (A := rowAt1) hRow)

/-- Arity-1 → arity-2 flipped classifier at the qubit binder. -/
private def qFlipWeaken {Γ' : List (SFormula 1)} (hQFlip : SFormula.Deriv Γ' qClassFlipF) :
    SFormula.Deriv (SFormula.boundNatLt (SC.n (arity := 1) 9) :: Γ'.map (fun G => G.weaken))
      qClassFlipF.weaken :=
  SFormula.Deriv.contextWeakening (fun _C hC => List.mem_cons_of_mem _ hC)
    (SFormula.Deriv.weakenFresh (A := qClassFlipF) hQFlip)

/-- The arity-2 `boundNatLt 9` at the qubit binder (head of context). -/
private def hq9At {Γ' : List (SFormula 1)} :
    SFormula.Deriv (SFormula.boundNatLt (SC.n (arity := 1) 9) :: Γ'.map (fun G => G.weaken))
      (SFormula.witnessLt SFormula.boundNat (SC.n (arity := 1) 9).weaken) :=
  .hyp List.mem_cons_self

/-- Self-reflexivity of the resolved row entry at `boundNat`, via the symbolic
row resolver. -/
private def rowSelfRefl {Γ' : List (SFormula 1)} (hRow : SFormula.Deriv Γ' rowAt1) :
    SFormula.Deriv (SFormula.boundNatLt (SC.n (arity := 1) 9) :: Γ'.map (fun G => G.weaken))
      (.eqPauli ((SC.closed (Term.recCall dN2 kN2)).stabAt SFormula.boundNat)
        ((SC.closed (Term.recCall dN2 kN2)).stabAt SFormula.boundNat)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ (xCleanProbeBound (rowAt1Weaken hRow) hq9At)
    (SFormula.Deriv.eqPauliSymm _ _ (xCleanProbeBound (rowAt1Weaken hRow) hq9At))

/-- **All-`I` pointwise branch (bulk strip case, e.g. `k = 1, 3`).**  Given the
branch guard conjunction `bulk true ∧ band 0 false ∧ band 3 false ∧ band 6 false`
(the shape of `branchConj1` / `branchConj3`), every column-0 entry of the row is
`I` (via `xleafBulkI2`), so the row commutes with `logicalX`. -/
def branchBulkAllI {Γ' : List (SFormula 1)} (hRow : SFormula.Deriv Γ' rowAt1)
    (hQFlip : SFormula.Deriv Γ' qClassFlipF)
    (hBC : SFormula.Deriv Γ'
      (.and (bulk true) (.and (band 0 false) (.and (band 3 false) (band 6 false))))) :
    SFormula.Deriv Γ'
      (SFormula.commutesUpTo (SC.closed (Term.lift 0 (Term.natLit (nQubits OddSurfaceDistance.d3.distance))))
        (SC.closed
          ((Term.lift 0 (Term.natLit OddSurfaceDistance.d3.distance)).recCall
            (Term.var ⟨0, Formula.normalizesCodeUpTo._proof_1⟩)))
        (SC.closed (Term.lift 0 (logicalXOdd OddSurfaceDistance.d3)))) := by
  refine SFormula.Deriv.commutesOfPointwise _ _ _ ?_
  refine SFormula.Deriv.allNatLtIntroBounded _ _ ?_
  have hBCW := SFormula.Deriv.contextWeakening
    (Δ := SFormula.boundNatLt (SC.n (arity := 1) 9) :: Γ'.map (fun G => G.weaken))
    (fun C hC => List.mem_cons_of_mem _ hC)
    (SFormula.Deriv.weakenFresh
      (A := .and (bulk true) (.and (band 0 false) (.and (band 3 false) (band 6 false)))) hBC)
  have hBulk := SFormula.Deriv.andElimLeft hBCW
  have hBand0 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hBCW)
  have hBand3 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hBCW))
  have hBand6 := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hBCW))
  exact colCommPointwise _ (qFlipWeaken hQFlip) hq9At Pauli.I Pauli.I Pauli.I
    (SFormula.Deriv.eqPauliTrans _ _ _ (xCleanProbeLit2 (rowAt1Weaken hRow) 0 (by decide)) (xleafBulkI2 0 hBulk hBand0))
    (SFormula.Deriv.eqPauliTrans _ _ _ (xCleanProbeLit2 (rowAt1Weaken hRow) 3 (by decide)) (xleafBulkI2 3 hBulk hBand3))
    (SFormula.Deriv.eqPauliTrans _ _ _ (xCleanProbeLit2 (rowAt1Weaken hRow) 6 (by decide)) (xleafBulkI2 6 hBulk hBand6))
    (SFormula.Deriv.pauliAnticommutesLit Pauli.I Pauli.X)
    (SFormula.Deriv.pauliAnticommutesLit Pauli.I Pauli.X)
    (SFormula.Deriv.pauliAnticommutesLit Pauli.I Pauli.X)
    (rowSelfRefl hRow)

/-- **All-`I` pointwise branch (right-boundary case, `k = 5`).**  Guard conjunction
`bulk false ∧ topC false ∧ rightC true ∧ rightB 0/3/6 false`; every column-0 entry
is `I` (via `xleafRightI2`). -/
def branchRightAllI {Γ' : List (SFormula 1)} (hRow : SFormula.Deriv Γ' rowAt1)
    (hQFlip : SFormula.Deriv Γ' qClassFlipF)
    (hBC : SFormula.Deriv Γ'
      (.and (bulk false) (.and (topC false) (.and (rightC true)
        (.and (rightB 0 false) (.and (rightB 3 false) (rightB 6 false))))))) :
    SFormula.Deriv Γ'
      (SFormula.commutesUpTo (SC.closed (Term.lift 0 (Term.natLit (nQubits OddSurfaceDistance.d3.distance))))
        (SC.closed
          ((Term.lift 0 (Term.natLit OddSurfaceDistance.d3.distance)).recCall
            (Term.var ⟨0, Formula.normalizesCodeUpTo._proof_1⟩)))
        (SC.closed (Term.lift 0 (logicalXOdd OddSurfaceDistance.d3)))) := by
  refine SFormula.Deriv.commutesOfPointwise _ _ _ ?_
  refine SFormula.Deriv.allNatLtIntroBounded _ _ ?_
  have hBCW := SFormula.Deriv.contextWeakening
    (Δ := SFormula.boundNatLt (SC.n (arity := 1) 9) :: Γ'.map (fun G => G.weaken))
    (fun C hC => List.mem_cons_of_mem _ hC)
    (SFormula.Deriv.weakenFresh
      (A := .and (bulk false) (.and (topC false) (.and (rightC true)
        (.and (rightB 0 false) (.and (rightB 3 false) (rightB 6 false)))))) hBC)
  have hBulk := SFormula.Deriv.andElimLeft hBCW
  have hTopC := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hBCW)
  have hRightC := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hBCW))
  have hRest := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hBCW))
  have hR0 := SFormula.Deriv.andElimLeft hRest
  have hR3 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hRest)
  have hR6 := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hRest)
  exact colCommPointwise _ (qFlipWeaken hQFlip) hq9At Pauli.I Pauli.I Pauli.I
    (SFormula.Deriv.eqPauliTrans _ _ _ (xCleanProbeLit2 (rowAt1Weaken hRow) 0 (by decide)) (xleafRightI2 0 hBulk hTopC hRightC hR0))
    (SFormula.Deriv.eqPauliTrans _ _ _ (xCleanProbeLit2 (rowAt1Weaken hRow) 3 (by decide)) (xleafRightI2 3 hBulk hTopC hRightC hR3))
    (SFormula.Deriv.eqPauliTrans _ _ _ (xCleanProbeLit2 (rowAt1Weaken hRow) 6 (by decide)) (xleafRightI2 6 hBulk hTopC hRightC hR6))
    (SFormula.Deriv.pauliAnticommutesLit Pauli.I Pauli.X)
    (SFormula.Deriv.pauliAnticommutesLit Pauli.I Pauli.X)
    (SFormula.Deriv.pauliAnticommutesLit Pauli.I Pauli.X)
    (rowSelfRefl hRow)

/-- **All-`I` pointwise branch (bottom-boundary case, `k = 7`).**  Guard conjunction
`bulk false ∧ topC false ∧ rightC false ∧ leftC false ∧ botB 0/3/6 false`; every
column-0 entry is `I` (via `xleafBottomI2`). -/
def branchBottomAllI {Γ' : List (SFormula 1)} (hRow : SFormula.Deriv Γ' rowAt1)
    (hQFlip : SFormula.Deriv Γ' qClassFlipF)
    (hBC : SFormula.Deriv Γ'
      (.and (bulk false) (.and (topC false) (.and (rightC false) (.and (leftC false)
        (.and (botB 0 false) (.and (botB 3 false) (botB 6 false)))))))) :
    SFormula.Deriv Γ'
      (SFormula.commutesUpTo (SC.closed (Term.lift 0 (Term.natLit (nQubits OddSurfaceDistance.d3.distance))))
        (SC.closed
          ((Term.lift 0 (Term.natLit OddSurfaceDistance.d3.distance)).recCall
            (Term.var ⟨0, Formula.normalizesCodeUpTo._proof_1⟩)))
        (SC.closed (Term.lift 0 (logicalXOdd OddSurfaceDistance.d3)))) := by
  refine SFormula.Deriv.commutesOfPointwise _ _ _ ?_
  refine SFormula.Deriv.allNatLtIntroBounded _ _ ?_
  have hBCW := SFormula.Deriv.contextWeakening
    (Δ := SFormula.boundNatLt (SC.n (arity := 1) 9) :: Γ'.map (fun G => G.weaken))
    (fun C hC => List.mem_cons_of_mem _ hC)
    (SFormula.Deriv.weakenFresh
      (A := .and (bulk false) (.and (topC false) (.and (rightC false) (.and (leftC false)
        (.and (botB 0 false) (.and (botB 3 false) (botB 6 false))))))) hBC)
  have hBulk := SFormula.Deriv.andElimLeft hBCW
  have hTopC := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hBCW)
  have hRightC := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hBCW))
  have hLeftC := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hBCW)))
  have hRest := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hBCW)))
  have hB0 := SFormula.Deriv.andElimLeft hRest
  have hB3 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hRest)
  have hB6 := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hRest)
  exact colCommPointwise _ (qFlipWeaken hQFlip) hq9At Pauli.I Pauli.I Pauli.I
    (SFormula.Deriv.eqPauliTrans _ _ _ (xCleanProbeLit2 (rowAt1Weaken hRow) 0 (by decide)) (xleafBottomI2 0 hBulk hTopC hRightC hLeftC hB0))
    (SFormula.Deriv.eqPauliTrans _ _ _ (xCleanProbeLit2 (rowAt1Weaken hRow) 3 (by decide)) (xleafBottomI2 3 hBulk hTopC hRightC hLeftC hB3))
    (SFormula.Deriv.eqPauliTrans _ _ _ (xCleanProbeLit2 (rowAt1Weaken hRow) 6 (by decide)) (xleafBottomI2 6 hBulk hTopC hRightC hLeftC hB6))
    (SFormula.Deriv.pauliAnticommutesLit Pauli.I Pauli.X)
    (SFormula.Deriv.pauliAnticommutesLit Pauli.I Pauli.X)
    (SFormula.Deriv.pauliAnticommutesLit Pauli.I Pauli.X)
    (rowSelfRefl hRow)

/-- **Mixed `I`/`X` pointwise branch (bulk strip, `k = 2`).**  Guard conjunction
`bulk true ∧ band 0 false ∧ band 3 true ∧ band 6 true ∧ kind false`; column-0
entries are `I @ 0` and `X @ {3,6}`.  Both `I` and `X` commute with `X`, so the row
commutes with `logicalX`. -/
def branchK2 {Γ' : List (SFormula 1)} (hRow : SFormula.Deriv Γ' rowAt1)
    (hQFlip : SFormula.Deriv Γ' qClassFlipF)
    (hBC : SFormula.Deriv Γ'
      (.and (bulk true) (.and (band 0 false) (.and (band 3 true) (.and (band 6 true) (kind false)))))) :
    SFormula.Deriv Γ'
      (SFormula.commutesUpTo (SC.closed (Term.lift 0 (Term.natLit (nQubits OddSurfaceDistance.d3.distance))))
        (SC.closed
          ((Term.lift 0 (Term.natLit OddSurfaceDistance.d3.distance)).recCall
            (Term.var ⟨0, Formula.normalizesCodeUpTo._proof_1⟩)))
        (SC.closed (Term.lift 0 (logicalXOdd OddSurfaceDistance.d3)))) := by
  refine SFormula.Deriv.commutesOfPointwise _ _ _ ?_
  refine SFormula.Deriv.allNatLtIntroBounded _ _ ?_
  have hBCW := SFormula.Deriv.contextWeakening
    (Δ := SFormula.boundNatLt (SC.n (arity := 1) 9) :: Γ'.map (fun G => G.weaken))
    (fun C hC => List.mem_cons_of_mem _ hC)
    (SFormula.Deriv.weakenFresh
      (A := .and (bulk true) (.and (band 0 false) (.and (band 3 true) (.and (band 6 true) (kind false))))) hBC)
  have hBulk := SFormula.Deriv.andElimLeft hBCW
  have hBand0 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hBCW)
  have hBand3 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hBCW))
  have hBand6 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hBCW)))
  have hKind := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hBCW)))
  exact colCommPointwise _ (qFlipWeaken hQFlip) hq9At Pauli.I Pauli.X Pauli.X
    (SFormula.Deriv.eqPauliTrans _ _ _ (xCleanProbeLit2 (rowAt1Weaken hRow) 0 (by decide)) (xleafBulkI2 0 hBulk hBand0))
    (SFormula.Deriv.eqPauliTrans _ _ _ (xCleanProbeLit2 (rowAt1Weaken hRow) 3 (by decide)) (xleafBulkX2 3 hBulk hBand3 hKind))
    (SFormula.Deriv.eqPauliTrans _ _ _ (xCleanProbeLit2 (rowAt1Weaken hRow) 6 (by decide)) (xleafBulkX2 6 hBulk hBand6 hKind))
    (SFormula.Deriv.pauliAnticommutesLit Pauli.I Pauli.X)
    (SFormula.Deriv.pauliAnticommutesLit Pauli.X Pauli.X)
    (SFormula.Deriv.pauliAnticommutesLit Pauli.X Pauli.X)
    (rowSelfRefl hRow)

/-- **Mixed `I`/`X` pointwise branch (top boundary, `k = 4`).**  Guard conjunction
`bulk false ∧ topC true ∧ topB 0 true ∧ topB 3 false ∧ topB 6 false`; column-0
entries are `X @ 0` and `I @ {3,6}`. -/
def branchK4 {Γ' : List (SFormula 1)} (hRow : SFormula.Deriv Γ' rowAt1)
    (hQFlip : SFormula.Deriv Γ' qClassFlipF)
    (hBC : SFormula.Deriv Γ'
      (.and (bulk false) (.and (topC true) (.and (topB 0 true) (.and (topB 3 false) (topB 6 false)))))) :
    SFormula.Deriv Γ'
      (SFormula.commutesUpTo (SC.closed (Term.lift 0 (Term.natLit (nQubits OddSurfaceDistance.d3.distance))))
        (SC.closed
          ((Term.lift 0 (Term.natLit OddSurfaceDistance.d3.distance)).recCall
            (Term.var ⟨0, Formula.normalizesCodeUpTo._proof_1⟩)))
        (SC.closed (Term.lift 0 (logicalXOdd OddSurfaceDistance.d3)))) := by
  refine SFormula.Deriv.commutesOfPointwise _ _ _ ?_
  refine SFormula.Deriv.allNatLtIntroBounded _ _ ?_
  have hBCW := SFormula.Deriv.contextWeakening
    (Δ := SFormula.boundNatLt (SC.n (arity := 1) 9) :: Γ'.map (fun G => G.weaken))
    (fun C hC => List.mem_cons_of_mem _ hC)
    (SFormula.Deriv.weakenFresh
      (A := .and (bulk false) (.and (topC true) (.and (topB 0 true) (.and (topB 3 false) (topB 6 false))))) hBC)
  have hBulk := SFormula.Deriv.andElimLeft hBCW
  have hTopC := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hBCW)
  have hTop0 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hBCW))
  have hTop3 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hBCW)))
  have hTop6 := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hBCW)))
  exact colCommPointwise _ (qFlipWeaken hQFlip) hq9At Pauli.X Pauli.I Pauli.I
    (SFormula.Deriv.eqPauliTrans _ _ _ (xCleanProbeLit2 (rowAt1Weaken hRow) 0 (by decide)) (xleafTopX2 0 hBulk hTopC hTop0))
    (SFormula.Deriv.eqPauliTrans _ _ _ (xCleanProbeLit2 (rowAt1Weaken hRow) 3 (by decide)) (xleafTopI2 3 hBulk hTopC hTop3))
    (SFormula.Deriv.eqPauliTrans _ _ _ (xCleanProbeLit2 (rowAt1Weaken hRow) 6 (by decide)) (xleafTopI2 6 hBulk hTopC hTop6))
    (SFormula.Deriv.pauliAnticommutesLit Pauli.X Pauli.X)
    (SFormula.Deriv.pauliAnticommutesLit Pauli.I Pauli.X)
    (SFormula.Deriv.pauliAnticommutesLit Pauli.I Pauli.X)
    (rowSelfRefl hRow)

/-- Arity-1 literal-qubit row resolver: from the single-quantified resolved row
`rowAt1`, the row entry at a LITERAL qubit `q < 9` equals the recursion-free leaf
tree `baseLeafTreeTA (natLit 3) (var 0) (natLit q)`. -/
def xCleanProbeLit1 {Γ : List (SFormula 1)} (hRow : SFormula.Deriv Γ rowAt1)
    (q : Nat) (hq : q < 9) :
    SFormula.Deriv Γ
      (SFormula.eqPauli
        ((SC.closed (Term.recCall dN kN)).stabAt (SC.closed (Term.natLit q)))
        (SC.closed (baseLeafTreeTA dN kN (Term.natLit q)))) := by
  have hElim := SFormula.Deriv.allNatLtElim _ _ (SC.n q) hRow
    (SFormula.Deriv.closedNatLt q 9 (by simpa using hq))
  have hQ := SFormula.Deriv.applyNatSubstitutionBetaElim (Term.natLit q) _
    (SFormula.PureNatTerm.natLit q) hElim
  simp only [rowAt1, SFormula.instantiateTopNat, SFormula.instantiateNatAt, STerm.instantiateNatAt,
    SC.closed, SC.n, rowSymTreeA, OddSurfaceDistance.d3, Formula.qVar, dN, kN,
    baseLeafTreeTA,
    bulkGuardTA, baseBulkBandGuardTA, baseKindGuardTA, topClassGuardTA, topBandGuardTA,
    rightClassGuardTA, rightBandGuardTA, leftClassGuardTA, leftBandGuardTA, bottomBandGuardTA,
    bulkCountTA, dm1TA, baseBTA, baseHalfTA, band3, orEqSucc, orEqPair,
    Term.instantiateNatAt, Term.lift, Term.weakenVar, Nat.reduceAdd,
    Nat.lt_irrefl, reduceDIte] at hQ ⊢
  exact hQ

/-- The closed `0 ≠ 3` distinctness fact at arity 1 (the column-0 two-anti slots for
`k = 0`), as a derivation, from the guard pack. -/
def colNeq {Γ : List (SFormula 1)} (a b : Nat)
    (hne : SFormula.Deriv Γ (.eqBool (SC.closed (.eqNat (Term.natLit a) (Term.natLit b))) (SC.b false))) :
    SFormula.Deriv Γ (.not (.eqNat (SC.n (arity := 1) a) (SC.n (arity := 1) b))) := by
  refine SFormula.Deriv.notIntro ?_
  refine SFormula.Deriv.notElim (SFormula.Deriv.eqNatBoolTrue (Γ := _) (Term.natLit a) (Term.natLit b) .assumption) ?_
  exact SFormula.Deriv.eqBoolFalseNotTrue _
    (SFormula.Deriv.contextWeakening (fun C hC => List.mem_cons_of_mem _ hC) hne)

/-- **Two-anti column-0 branch.**  For a row whose column-0 entries are `Z @ {q0,q1}`
and `I @ q2` (the `{q0,q1,q2}` a permutation of `{0,3,6}`), the row commutes with
`logicalX` by the even-parity rule `commutesOfTwoAnti`: it anticommutes with
`logicalX` at exactly the two `Z` slots `q0, q1` (`anti(Z,X) = true`), and commutes
everywhere else.  The two anti premises are supplied at the literal `Z` qubits; the
all-others premise pins the remaining column-0 qubit to the `I` slot `q2` (the
`≠ q0 ∧ ≠ q1` hypotheses exclude `q0, q1`) and off-column-0 uses
`logicalXOffColumnLocalCommutes`. -/
def branchTwoAntiZ {Γ' : List (SFormula 1)} (q0 q1 : Nat)
    (hq0lt : q0 < 9) (hq1lt : q1 < 9)
    (hZ0 : SFormula.Deriv Γ' (.eqPauli ((SC.closed (Term.recCall dN kN)).stabAt (SC.closed (Term.natLit q0))) (SC.p Pauli.Z)))
    (hZ1 : SFormula.Deriv Γ' (.eqPauli ((SC.closed (Term.recCall dN kN)).stabAt (SC.closed (Term.natLit q1))) (SC.p Pauli.Z)))
    (hX0 : SFormula.Deriv Γ' (.eqPauli (.stabAt liftedLogicalX1 (SC.closed (Term.natLit q0))) (SC.p Pauli.X)))
    (hX1 : SFormula.Deriv Γ' (.eqPauli (.stabAt liftedLogicalX1 (SC.closed (Term.natLit q1))) (SC.p Pauli.X)))
    (hne : SFormula.Deriv Γ' (.not (.eqNat (SC.n (arity := 1) q0) (SC.n (arity := 1) q1))))
    (hAllOthers : SFormula.Deriv Γ'
      (SFormula.allNatLt (SC.n (arity := 1) (nQubits OddSurfaceDistance.d3.distance))
        (.imp (.not (.eqNat SFormula.boundNat (SC.n (arity := 1) q0).weaken))
          (.imp (.not (.eqNat SFormula.boundNat (SC.n (arity := 1) q1).weaken))
            (SFormula.localCommutesAt
              (SC.closed ((Term.lift 0 (Term.natLit OddSurfaceDistance.d3.distance)).recCall
                (Term.var ⟨0, Formula.normalizesCodeUpTo._proof_1⟩))).weaken
              (SC.closed (Term.lift 0 (logicalXOdd OddSurfaceDistance.d3))).weaken SFormula.boundNat))))) :
    SFormula.Deriv Γ'
      (SFormula.commutesUpTo (SC.closed (Term.lift 0 (Term.natLit (nQubits OddSurfaceDistance.d3.distance))))
        (SC.closed
          ((Term.lift 0 (Term.natLit OddSurfaceDistance.d3.distance)).recCall
            (Term.var ⟨0, Formula.normalizesCodeUpTo._proof_1⟩)))
        (SC.closed (Term.lift 0 (logicalXOdd OddSurfaceDistance.d3)))) :=
  SFormula.Deriv.commutesOfTwoAnti _ _ _ (SC.n q0) (SC.n q1)
    (SFormula.Deriv.closedNatLt q0 9 (by simpa using hq0lt))
    (SFormula.Deriv.closedNatLt q1 9 (by simpa using hq1lt))
    hne
    (SFormula.Deriv.anticommutesTransport _ (SC.p Pauli.Z) _ (SC.p Pauli.X) (SC.b true)
      hZ0 hX0 (SFormula.Deriv.pauliAnticommutesLit Pauli.Z Pauli.X))
    (SFormula.Deriv.anticommutesTransport _ (SC.p Pauli.Z) _ (SC.p Pauli.X) (SC.b true)
      hZ1 hX1 (SFormula.Deriv.pauliAnticommutesLit Pauli.Z Pauli.X))
    hAllOthers

/-- A contradiction at a `Z`-slot `v` excluded by the `commutesOfTwoAnti` all-others
premise: the flipped-classifier pin `v = boundNat`, flipped via `hEqSymm` to
`boundNat = v`, contradicts the exclusion hypothesis `boundNat ≠ v`. -/
def twoAntiContra {Δ : List (SFormula 2)} (v : Nat)
    (hPin : SFormula.Deriv Δ (.eqNat (SC.n (arity := 2) v) SFormula.boundNat))
    (hSymmV : SFormula.Deriv Δ (.imp (.eqNat (SC.n (arity := 2) v) SFormula.boundNat)
      (.eqNat SFormula.boundNat (SC.n (arity := 2) v))))
    (hNe : SFormula.Deriv Δ (.not (.eqNat SFormula.boundNat (SC.n (arity := 2) v))))
    (A : STerm 2 .stab) :
    SFormula.Deriv Δ (SFormula.localCommutesAt A liftedLogicalX2 SFormula.boundNat) :=
  SFormula.Deriv.botElim (SFormula.Deriv.notElim (SFormula.Deriv.mp hSymmV hPin) hNe)

/-- Extract the per-`v` `eqNat`-symmetry implication at `boundNat` from the weakened
symmetry pack `eqSymmF`. -/
def symmAt {Δ : List (SFormula 2)} (_which : Nat)
    (hEqSymmW : SFormula.Deriv Δ eqSymmF.weaken)
    (hq9 : SFormula.Deriv Δ (SFormula.boundNatLt (SC.n (arity := 1) (nQubits OddSurfaceDistance.d3.distance)))) :
    SFormula.Deriv Δ eqSymmBody := by
  have hElim := SFormula.Deriv.allNatLtElim (SC.n (arity := 1) 9).weaken (eqSymmBody.lift 1)
    SFormula.boundNat hEqSymmW hq9
  exact SFormula.Deriv.applyNatBoundNatBeta eqSymmBody hElim

/-- Common scaffold for the all-others premise of a two-anti branch: introduce the
qubit binder and the two exclusion hypotheses, `boolCases` on the column guard
(off-column via `logicalXOffColumnLocalCommutes`), and on-column pin to `{0,3,6}` via
`xColQDisjFlip`, leaving the three pinned cases as goals.  `hAt0/hAt3/hAt6` discharge
`boundNat = v` (`v ∈ {0,3,6}`): either a contradiction (`Z` slot) or the `I`-slot
local commutation. -/
def twoAntiAllOthers {Γ' : List (SFormula 1)} (q0 q1 q2 : Nat)
    (hRow : SFormula.Deriv Γ' rowAt1) (hQFlip : SFormula.Deriv Γ' qClassFlipF)
    (hILeaf1 : SFormula.Deriv Γ'
      (.eqPauli ((SC.closed (Term.recCall dN kN)).stabAt (SC.closed (Term.natLit q2))) (SC.p Pauli.I)))
    (hAt0 : ∀ (Δ : List (SFormula 2)),
      SFormula.Deriv Δ (.eqNat (SC.n (arity := 2) 0) SFormula.boundNat) →
      SFormula.Deriv Δ eqSymmBody →
      SFormula.Deriv Δ (.not (.eqNat SFormula.boundNat (SC.n (arity := 1) q0).weaken)) →
      SFormula.Deriv Δ (.not (.eqNat SFormula.boundNat (SC.n (arity := 1) q1).weaken)) →
      SFormula.Deriv Δ (SFormula.boundNatLt (SC.n (arity := 1) (nQubits OddSurfaceDistance.d3.distance))) →
      SFormula.Deriv Δ rowAt1.weaken →
      SFormula.Deriv Δ (.eqBool (logicalXColGuardAt2 OddSurfaceDistance.d3) (SC.b true)) →
      SFormula.Deriv Δ (.eqPauli ((SC.closed (Term.recCall dN kN)).stabAt (SC.closed (Term.natLit q2))).weaken (SC.p Pauli.I)) →
      SFormula.Deriv Δ (SFormula.localCommutesAt
        (SC.closed ((Term.lift 0 (Term.natLit OddSurfaceDistance.d3.distance)).recCall
          (Term.var ⟨0, Formula.normalizesCodeUpTo._proof_1⟩))).weaken
        liftedLogicalX2 SFormula.boundNat))
    (hAt3 : ∀ (Δ : List (SFormula 2)),
      SFormula.Deriv Δ (.eqNat (SC.n (arity := 2) 3) SFormula.boundNat) →
      SFormula.Deriv Δ eqSymmBody →
      SFormula.Deriv Δ (.not (.eqNat SFormula.boundNat (SC.n (arity := 1) q0).weaken)) →
      SFormula.Deriv Δ (.not (.eqNat SFormula.boundNat (SC.n (arity := 1) q1).weaken)) →
      SFormula.Deriv Δ (SFormula.boundNatLt (SC.n (arity := 1) (nQubits OddSurfaceDistance.d3.distance))) →
      SFormula.Deriv Δ rowAt1.weaken →
      SFormula.Deriv Δ (.eqBool (logicalXColGuardAt2 OddSurfaceDistance.d3) (SC.b true)) →
      SFormula.Deriv Δ (.eqPauli ((SC.closed (Term.recCall dN kN)).stabAt (SC.closed (Term.natLit q2))).weaken (SC.p Pauli.I)) →
      SFormula.Deriv Δ (SFormula.localCommutesAt
        (SC.closed ((Term.lift 0 (Term.natLit OddSurfaceDistance.d3.distance)).recCall
          (Term.var ⟨0, Formula.normalizesCodeUpTo._proof_1⟩))).weaken
        liftedLogicalX2 SFormula.boundNat))
    (hAt6 : ∀ (Δ : List (SFormula 2)),
      SFormula.Deriv Δ (.eqNat (SC.n (arity := 2) 6) SFormula.boundNat) →
      SFormula.Deriv Δ eqSymmBody →
      SFormula.Deriv Δ (.not (.eqNat SFormula.boundNat (SC.n (arity := 1) q0).weaken)) →
      SFormula.Deriv Δ (.not (.eqNat SFormula.boundNat (SC.n (arity := 1) q1).weaken)) →
      SFormula.Deriv Δ (SFormula.boundNatLt (SC.n (arity := 1) (nQubits OddSurfaceDistance.d3.distance))) →
      SFormula.Deriv Δ rowAt1.weaken →
      SFormula.Deriv Δ (.eqBool (logicalXColGuardAt2 OddSurfaceDistance.d3) (SC.b true)) →
      SFormula.Deriv Δ (.eqPauli ((SC.closed (Term.recCall dN kN)).stabAt (SC.closed (Term.natLit q2))).weaken (SC.p Pauli.I)) →
      SFormula.Deriv Δ (SFormula.localCommutesAt
        (SC.closed ((Term.lift 0 (Term.natLit OddSurfaceDistance.d3.distance)).recCall
          (Term.var ⟨0, Formula.normalizesCodeUpTo._proof_1⟩))).weaken
        liftedLogicalX2 SFormula.boundNat))
    (hEqSymm : SFormula.Deriv Γ' eqSymmF) :
    SFormula.Deriv Γ'
      (SFormula.allNatLt (SC.n (arity := 1) (nQubits OddSurfaceDistance.d3.distance))
        (.imp (.not (.eqNat SFormula.boundNat (SC.n (arity := 1) q0).weaken))
          (.imp (.not (.eqNat SFormula.boundNat (SC.n (arity := 1) q1).weaken))
            (SFormula.localCommutesAt
              (SC.closed ((Term.lift 0 (Term.natLit OddSurfaceDistance.d3.distance)).recCall
                (Term.var ⟨0, Formula.normalizesCodeUpTo._proof_1⟩))).weaken
              (SC.closed (Term.lift 0 (logicalXOdd OddSurfaceDistance.d3))).weaken SFormula.boundNat)))) := by
  refine SFormula.Deriv.allNatLtIntroBounded _ _ ?_
  refine SFormula.Deriv.impIntro (SFormula.Deriv.impIntro ?_)
  -- Context: [≠q1, ≠q0, boundNatLt 9, Γ'.map weaken].
  refine SFormula.Deriv.boolCases (logicalXColGuardAt2 OddSurfaceDistance.d3) _ ?_ ?_
  · -- guard TRUE.  Context: [colTrue(0), ≠q1(1), ≠q0(2), boundNatLt(3), Γ'.w].
    refine SFormula.Deriv.orElim
      (xColQDisjFlip _
        (SFormula.Deriv.contextWeakening (fun C hC => List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC))))
          (SFormula.Deriv.weakenFresh (A := qClassFlipF) hQFlip))
        (.hyp (by right; right; right; left)) (.assumption)) ?_ ?_
    · -- boundNat = 0.  Context: [eqNat0(0), colTrue(1), ≠q1(2), ≠q0(3), boundNatLt(4), Γ'.w].
      exact hAt0 _ .assumption
        (symmAt 0 (SFormula.Deriv.contextWeakening (fun C hC => List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC)))))
          (SFormula.Deriv.weakenFresh (A := eqSymmF) hEqSymm)) (.hyp (by right; right; right; right; left)))
        (.hyp (by right; right; right; left)) (.hyp (by right; right; left)) (.hyp (by right; right; right; right; left))
        (SFormula.Deriv.contextWeakening (fun C hC => List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC)))))
          (SFormula.Deriv.weakenFresh (A := rowAt1) hRow))
        (.hyp (by right; left))
        (SFormula.Deriv.contextWeakening (fun C hC => List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC)))))
          (SFormula.Deriv.weakenFresh
            (A := .eqPauli ((SC.closed (Term.recCall dN kN)).stabAt (SC.closed (Term.natLit q2))) (SC.p Pauli.I))
            hILeaf1))
    -- Context: [(eqNat3∨eqNat6)(0), colTrue(1), ≠q1(2), ≠q0(3), boundNatLt(4), Γ'.w].
    refine SFormula.Deriv.orElim (.assumption) ?_ ?_
    · -- boundNat = 3.  Context: [eqNat3(0), (eqNat3∨eqNat6)(1), colTrue(2), ≠q1(3), ≠q0(4), boundNatLt(5), Γ'.w].
      exact hAt3 _ .assumption
        (symmAt 3 (SFormula.Deriv.contextWeakening (fun C hC => List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC))))))
          (SFormula.Deriv.weakenFresh (A := eqSymmF) hEqSymm)) (.hyp (by right; right; right; right; right; left)))
        (.hyp (by right; right; right; right; left)) (.hyp (by right; right; right; left))
        (.hyp (by right; right; right; right; right; left))
        (SFormula.Deriv.contextWeakening (fun C hC => List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC))))))
          (SFormula.Deriv.weakenFresh (A := rowAt1) hRow))
        (.hyp (by right; right; left))
        (SFormula.Deriv.contextWeakening (fun C hC => List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC))))))
          (SFormula.Deriv.weakenFresh
            (A := .eqPauli ((SC.closed (Term.recCall dN kN)).stabAt (SC.closed (Term.natLit q2))) (SC.p Pauli.I))
            hILeaf1))
    · -- boundNat = 6.  Same shape as boundNat = 3.
      exact hAt6 _ .assumption
        (symmAt 6 (SFormula.Deriv.contextWeakening (fun C hC => List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC))))))
          (SFormula.Deriv.weakenFresh (A := eqSymmF) hEqSymm)) (.hyp (by right; right; right; right; right; left)))
        (.hyp (by right; right; right; right; left)) (.hyp (by right; right; right; left))
        (.hyp (by right; right; right; right; right; left))
        (SFormula.Deriv.contextWeakening (fun C hC => List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC))))))
          (SFormula.Deriv.weakenFresh (A := rowAt1) hRow))
        (.hyp (by right; right; left))
        (SFormula.Deriv.contextWeakening (fun C hC => List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC))))))
          (SFormula.Deriv.weakenFresh
            (A := .eqPauli ((SC.closed (Term.recCall dN kN)).stabAt (SC.closed (Term.natLit q2))) (SC.p Pauli.I))
            hILeaf1))
  · -- guard FALSE: off-column
    exact logicalXOffColumnLocalCommutes OddSurfaceDistance.d3 _ (.assumption)

/-- The frozen left stabilizer `A` of the per-row commutation goal at arity 2. -/
abbrev rowStab2 : STerm 2 .stab :=
  (SC.closed ((Term.lift 0 (Term.natLit OddSurfaceDistance.d3.distance)).recCall
    (Term.var ⟨0, Formula.normalizesCodeUpTo._proof_1⟩))).weaken

/-- **Branch `k = 0` (two-anti: `Z @ {0,3}`, `I @ 6`).** -/
def branchK0 {Γ' : List (SFormula 1)} (hRow : SFormula.Deriv Γ' rowAt1)
    (hQFlip : SFormula.Deriv Γ' qClassFlipF) (hColGuard : SFormula.Deriv Γ' colGuardPackF)
    (hEqSymm : SFormula.Deriv Γ' eqSymmF)
    (hBC : SFormula.Deriv Γ'
      (.and (bulk true) (.and (band 0 true) (.and (band 3 true) (.and (band 6 false) (kind true)))))) :
    SFormula.Deriv Γ'
      (SFormula.commutesUpTo (SC.closed (Term.lift 0 (Term.natLit (nQubits OddSurfaceDistance.d3.distance))))
        (SC.closed
          ((Term.lift 0 (Term.natLit OddSurfaceDistance.d3.distance)).recCall
            (Term.var ⟨0, Formula.normalizesCodeUpTo._proof_1⟩)))
        (SC.closed (Term.lift 0 (logicalXOdd OddSurfaceDistance.d3)))) := by
  have hBulk := SFormula.Deriv.andElimLeft hBC
  have hB0 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hBC)
  have hB3 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hBC))
  have hB6 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight hBC)))
  have hKind := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight hBC)))
  refine branchTwoAntiZ 0 3 (by decide) (by decide)
    (SFormula.Deriv.eqPauliTrans _ _ _ (xCleanProbeLit1 hRow 0 (by decide)) (xleafZ 0 hBulk hB0 hKind))
    (SFormula.Deriv.eqPauliTrans _ _ _ (xCleanProbeLit1 hRow 3 (by decide)) (xleafZ 3 hBulk hB3 hKind))
    (logicalXLitEntryX 0 (SFormula.Deriv.andElimLeft hColGuard))
    (logicalXLitEntryX 3 (SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hColGuard)))
    (colNeq 0 3 (SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight hColGuard)))))
    ?_
  refine twoAntiAllOthers 0 3 6 hRow hQFlip
    (SFormula.Deriv.eqPauliTrans _ _ _ (xCleanProbeLit1 hRow 6 (by decide)) (xleafBulkI 6 hBulk hB6))
    ?hAt0 ?hAt3 ?hAt6 hEqSymm
  case hAt0 =>
    intro Δ hPin hSymm hNeq0 _ _ _ _ _
    exact twoAntiContra 0 hPin (SFormula.Deriv.andElimLeft hSymm) hNeq0 rowStab2
  case hAt3 =>
    intro Δ hPin hSymm _ hNeq1 _ _ _ _
    exact twoAntiContra 3 hPin (SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hSymm)) hNeq1 rowStab2
  case hAt6 =>
    intro Δ hPin _ _ _ hq9 hRowW hColTrue hILeafW
    exact colCommViaLeft rowStab2 Pauli.I 6 hILeafW
      (SFormula.Deriv.pauliAnticommutesLit Pauli.I Pauli.X)
      hPin
      (SFormula.Deriv.eqPauliTrans _ _ _ (xCleanProbeBound hRowW hq9)
        (SFormula.Deriv.eqPauliSymm _ _ (xCleanProbeBound hRowW hq9)))
      hColTrue

/-- **Branch `k = 6` (two-anti: `Z @ {3,6}`, `I @ 0`).** -/
def branchK6 {Γ' : List (SFormula 1)} (hRow : SFormula.Deriv Γ' rowAt1)
    (hQFlip : SFormula.Deriv Γ' qClassFlipF) (hColGuard : SFormula.Deriv Γ' colGuardPackF)
    (hEqSymm : SFormula.Deriv Γ' eqSymmF)
    (hBC : SFormula.Deriv Γ'
      (.and (bulk false) (.and (topC false) (.and (rightC false) (.and (leftC true)
        (.and (leftB 0 false) (.and (leftB 3 true) (leftB 6 true)))))))) :
    SFormula.Deriv Γ'
      (SFormula.commutesUpTo (SC.closed (Term.lift 0 (Term.natLit (nQubits OddSurfaceDistance.d3.distance))))
        (SC.closed
          ((Term.lift 0 (Term.natLit OddSurfaceDistance.d3.distance)).recCall
            (Term.var ⟨0, Formula.normalizesCodeUpTo._proof_1⟩)))
        (SC.closed (Term.lift 0 (logicalXOdd OddSurfaceDistance.d3)))) := by
  have hBulk := SFormula.Deriv.andElimLeft hBC
  have hTopC := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hBC)
  have hRightC := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hBC))
  have hLeftC := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight hBC)))
  have hRest := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight hBC)))
  have hL0 := SFormula.Deriv.andElimLeft hRest
  have hL3 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hRest)
  have hL6 := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hRest)
  refine branchTwoAntiZ 3 6 (by decide) (by decide)
    (SFormula.Deriv.eqPauliTrans _ _ _ (xCleanProbeLit1 hRow 3 (by decide)) (xleafLeftZ 3 hBulk hTopC hRightC hLeftC hL3))
    (SFormula.Deriv.eqPauliTrans _ _ _ (xCleanProbeLit1 hRow 6 (by decide)) (xleafLeftZ 6 hBulk hTopC hRightC hLeftC hL6))
    (logicalXLitEntryX 3 (SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hColGuard)))
    (logicalXLitEntryX 6 (SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hColGuard))))
    (colNeq 3 6 (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight hColGuard)))))
    ?_
  refine twoAntiAllOthers 3 6 0 hRow hQFlip
    (SFormula.Deriv.eqPauliTrans _ _ _ (xCleanProbeLit1 hRow 0 (by decide)) (xleafLeftI 0 hBulk hTopC hRightC hLeftC hL0))
    ?hAt0 ?hAt3 ?hAt6 hEqSymm
  case hAt0 =>
    intro Δ hPin _ _ _ hq9 hRowW hColTrue hILeafW
    exact colCommViaLeft rowStab2 Pauli.I 0 hILeafW
      (SFormula.Deriv.pauliAnticommutesLit Pauli.I Pauli.X)
      hPin
      (SFormula.Deriv.eqPauliTrans _ _ _ (xCleanProbeBound hRowW hq9)
        (SFormula.Deriv.eqPauliSymm _ _ (xCleanProbeBound hRowW hq9)))
      hColTrue
  case hAt3 =>
    intro Δ hPin hSymm hNeq0 _ _ _ _ _
    exact twoAntiContra 3 hPin (SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hSymm)) hNeq0 rowStab2
  case hAt6 =>
    intro Δ hPin hSymm _ hNeq1 _ _ _ _
    exact twoAntiContra 6 hPin (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hSymm)) hNeq1 rowStab2

/-- The arity-1 parity body, parameterized by a generic context `Γ` and the three
context facts: the weakened doubly-quantified resolved rows `hH`, the bound
`boundNat < 8` (`hbnd`), and the guard pack `hPack`.  Proves the per-row
commutation `commutesUpTo 9 (recCall 3 (var 0)) (lift logicalX)`. -/
def xCommBody (Γ : List (SFormula 1))
    (hH : SFormula.Deriv Γ
      (SFormula.allNatLt (SC.n (numStab OddSurfaceDistance.d3.distance))
              (SFormula.allNatLt (SC.n (nQubits OddSurfaceDistance.d3.distance))
                (SFormula.eqPauli
                  ((SC.closed ((distAtBoundIdx2 OddSurfaceDistance.d3).dT.recCall liftedBoundIdx)).stabAt
                    (SC.closed Formula.qVar))
                  (SC.closed
                    (rowSymTreeA OddSurfaceDistance.d3.index (distAtBoundIdx2 OddSurfaceDistance.d3).dT
                      liftedBoundIdx Formula.qVar))))).weaken)
    (hbnd : SFormula.Deriv Γ
      (SFormula.witnessLt SFormula.boundNat (SC.n (numStab OddSurfaceDistance.d3.distance)).weaken))
    (hPack : SFormula.Deriv Γ xPackF)
    (_hQClass : SFormula.Deriv Γ qClassF)
    (hQFlip : SFormula.Deriv Γ qClassFlipF)
    (hColGuard : SFormula.Deriv Γ colGuardPackF)
    (hEqSymm : SFormula.Deriv Γ eqSymmF) :
    SFormula.Deriv Γ
      (SFormula.commutesUpTo (SC.closed (Term.lift 0 (Term.natLit (nQubits OddSurfaceDistance.d3.distance))))
        (SC.closed
          ((Term.lift 0 (Term.natLit OddSurfaceDistance.d3.distance)).recCall
            (Term.var ⟨0, Formula.normalizesCodeUpTo._proof_1⟩)))
        (SC.closed (Term.lift 0 (logicalXOdd OddSurfaceDistance.d3)))) := by
  -- `boundNat < 8` in the `SC.n 8` form for the literal split.
  have hBnd8 : SFormula.Deriv Γ (SFormula.boundNatLt (SC.n (arity := 0) 8)) := by
    have h8 : (numStab OddSurfaceDistance.d3.distance) = 8 := by decide
    simpa [SFormula.boundNatLt, h8] using hbnd
  -- The literal-split disjunction `k = 0 ∨ … ∨ k = 7`.
  have hDisj : SFormula.Deriv Γ orDisj :=
    SFormula.Deriv.mp (SFormula.Deriv.andElimLeft hPack) hBnd8
  -- Eliminate the OUTER (stabilizer-index) quantifier of `hH` at `boundNat`,
  -- giving the single-quantified resolved row `rowAt1` at the ambient `k = var 0`.
  have hRow : SFormula.Deriv Γ rowAt1 :=
    SFormula.Deriv.applyNatBoundNatBeta _
      (SFormula.Deriv.allNatLtElim _ _ SFormula.boundNat hH hbnd)
  -- Eight-way case split on the bound stabilizer index.
  -- REMAINING (open) per-branch parity assembly.  For each branch `k = i` the
  -- off-column-0 half of the all-others premise is fully discharged by
  -- `logicalXOffColumnLocalCommutes`, and the column-0 qubits are pinned to
  -- `{0,3,6}` by `xColQDisj`.  What remains is resolving the row entry at the
  -- *symbolic* column-0 qubit `boundNat` (the `commutesOfPointwise` /
  -- `commutesOfTwoAnti` premise lives at the symbolic qubit, and the proof system
  -- has no `stabAt`-under-`eqNat` congruence to transport a literal-qubit entry to
  -- `boundNat`).  That needs an arity-2 row-entry resolver (double-weakened `hH`,
  -- eliminated at the fixed index `var 1` and the qubit `boundNat`), arity-2 leaf
  -- peels, and an arity-2 guard pack giving the band guards as functions of both
  -- `k` and the column-0 qubit.  k0/k6 additionally use `commutesOfTwoAnti` (the
  -- Z@col-0 two-anti rows).  Genuinely deep; OPEN.
  refine SFormula.Deriv.orElim hDisj ?_ ?_
  · -- k = 0  (two-anti: Z@{0,3})
    refine branchK0 (SFormula.Deriv.contextWeakening (fun C hC => List.mem_cons_of_mem _ hC) hRow)
      (SFormula.Deriv.contextWeakening (fun C hC => List.mem_cons_of_mem _ hC) hQFlip)
      (SFormula.Deriv.contextWeakening (fun C hC => List.mem_cons_of_mem _ hC) hColGuard)
      (SFormula.Deriv.contextWeakening (fun C hC => List.mem_cons_of_mem _ hC) hEqSymm) ?_
    exact SFormula.Deriv.mp
      ((SFormula.Deriv.contextWeakening (fun C hC => List.mem_cons_of_mem _ hC) hPack).andElimRight.andElimLeft)
      .assumption
  refine SFormula.Deriv.orElim (.assumption) ?_ ?_
  · -- k = 1  (pointwise: col-0 all I)
    refine branchBulkAllI (SFormula.Deriv.contextWeakening (fun C hC =>
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC)) hRow)
      (SFormula.Deriv.contextWeakening (fun C hC =>
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC)) hQFlip) ?_
    exact SFormula.Deriv.mp
      (SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
        (SFormula.Deriv.contextWeakening (fun C hC => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC)) hPack))))
      .assumption
  refine SFormula.Deriv.orElim (.assumption) ?_ ?_
  · -- k = 2  (pointwise: X@{3,6})
    refine branchK2 (SFormula.Deriv.contextWeakening (fun C hC =>
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC))) hRow)
      (SFormula.Deriv.contextWeakening (fun C hC =>
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC))) hQFlip) ?_
    refine SFormula.Deriv.mp
      ((SFormula.Deriv.contextWeakening (fun C hC =>
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC))) hPack).andElimRight.andElimRight.andElimRight.andElimLeft)
      .assumption
  refine SFormula.Deriv.orElim (.assumption) ?_ ?_
  · -- k = 3  (pointwise: col-0 all I)
    refine branchBulkAllI (SFormula.Deriv.contextWeakening (fun C hC =>
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC)))) hRow)
      (SFormula.Deriv.contextWeakening (fun C hC =>
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC)))) hQFlip) ?_
    exact SFormula.Deriv.mp
      (SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
        (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
          (SFormula.Deriv.contextWeakening (fun C hC =>
            List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC)))) hPack))))))
      .assumption
  refine SFormula.Deriv.orElim (.assumption) ?_ ?_
  · -- k = 4  (pointwise: X@{0})
    refine branchK4 (SFormula.Deriv.contextWeakening (fun C hC =>
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ hC))))) hRow)
      (SFormula.Deriv.contextWeakening (fun C hC =>
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ hC))))) hQFlip) ?_
    refine SFormula.Deriv.mp
      ((SFormula.Deriv.contextWeakening (fun C hC =>
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ hC))))) hPack).andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimLeft)
      .assumption
  refine SFormula.Deriv.orElim (.assumption) ?_ ?_
  · -- k = 5  (pointwise: col-0 all I)
    refine branchRightAllI (SFormula.Deriv.contextWeakening (fun C hC =>
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC)))))) hRow)
      (SFormula.Deriv.contextWeakening (fun C hC =>
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC)))))) hQFlip) ?_
    exact SFormula.Deriv.mp
      (SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
        (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
          (SFormula.Deriv.andElimRight
            (SFormula.Deriv.contextWeakening (fun C hC =>
              List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC)))))) hPack))))))))
      .assumption
  refine SFormula.Deriv.orElim (.assumption) ?_ ?_
  · -- k = 6  (two-anti: Z@{3,6})
    refine branchK6 (SFormula.Deriv.contextWeakening (fun C hC =>
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC))))))) hRow)
      (SFormula.Deriv.contextWeakening (fun C hC =>
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC))))))) hQFlip)
      (SFormula.Deriv.contextWeakening (fun C hC =>
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC))))))) hColGuard)
      (SFormula.Deriv.contextWeakening (fun C hC =>
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC))))))) hEqSymm) ?_
    refine SFormula.Deriv.mp
      (SFormula.Deriv.contextWeakening (Δ := kEq 6 ::
          (kEq 6).or (kEq 7) ::
          (kEq 5).or ((kEq 6).or (kEq 7)) ::
          (kEq 4).or ((kEq 5).or ((kEq 6).or (kEq 7))) ::
          (kEq 3).or ((kEq 4).or ((kEq 5).or ((kEq 6).or (kEq 7)))) ::
          (kEq 2).or ((kEq 3).or ((kEq 4).or ((kEq 5).or ((kEq 6).or (kEq 7))))) ::
          (kEq 1).or ((kEq 2).or ((kEq 3).or ((kEq 4).or ((kEq 5).or ((kEq 6).or (kEq 7)))))) :: Γ)
        (fun C hC => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC)))))))
        ((SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
          (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
            (SFormula.Deriv.andElimRight hPack))))))).andElimLeft))
      .assumption
  · -- k = 7  (pointwise: col-0 all I)
    refine branchBottomAllI (SFormula.Deriv.contextWeakening (fun C hC =>
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC))))))) hRow)
      (SFormula.Deriv.contextWeakening (fun C hC =>
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC))))))) hQFlip) ?_
    refine SFormula.Deriv.mp
      (SFormula.Deriv.contextWeakening (Δ := kEq 7 ::
          (kEq 6).or (kEq 7) ::
          (kEq 5).or ((kEq 6).or (kEq 7)) ::
          (kEq 4).or ((kEq 5).or ((kEq 6).or (kEq 7))) ::
          (kEq 3).or ((kEq 4).or ((kEq 5).or ((kEq 6).or (kEq 7)))) ::
          (kEq 2).or ((kEq 3).or ((kEq 4).or ((kEq 5).or ((kEq 6).or (kEq 7))))) ::
          (kEq 1).or ((kEq 2).or ((kEq 3).or ((kEq 4).or ((kEq 5).or ((kEq 6).or (kEq 7)))))) :: Γ)
        (fun C hC => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hC)))))))
        (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
          (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
            (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hPack)))))))))
      .assumption

def xNormCommuteD3 :
    PureFamilyDerivA Surface.code.body (OddSurfaceDistance.d3.distance + 2)
      (closedSF (logicalXNormalizesOddF OddSurfaceDistance.d3)) := by
  unfold closedSF logicalXNormalizesOddF Formula.normalizesCodeUpTo
  simp only [closedSF, Formula.codeRow, Term.weaken]
  -- ARCHITECTURE (ROUTE A, bound-exposing).  We do NOT use `allNatLtIntro`
  -- directly (that discharges `allNatLt 8 body` by proving `body` UNIFORMLY in the
  -- stabilizer index `k`, losing the `k < 8` side condition).  Instead we `cut1`
  -- the doubly-quantified row resolution `∀ k < 8, ∀ q < 9, stabAt (recCall 3 k) q
  -- = rowSymTreeA 0 3 k q` and then introduce `k` with `allNatLtIntroBounded`,
  -- which keeps `boundNatLt 8` (i.e. `k < 8`) in context.  With `k < 8` available,
  -- `boundIndexLiteralSplit` yields the literal case split `k = 0 ∨ … ∨ k = 7`
  -- (the linchpin, proven above via `arithBool`).
  -- Combine the guard pack and the two column classifiers into one arity-1 fact via
  -- PFDA-level `andIntro`s (`cut2` with an `andIntro` core derivation).
  have qCE : PureFamilyDerivA Surface.code.body 5 (.and colGuardPackF eqSymmF) :=
    PureFamilyDerivA.cut2 (SFormula.Deriv.andIntro .assumption (.hyp (by right; left))) colGuardPack eqSymmPack
  have qTriple : PureFamilyDerivA Surface.code.body 5 (.and qClassFlipF (.and colGuardPackF eqSymmF)) :=
    PureFamilyDerivA.cut2 (SFormula.Deriv.andIntro .assumption (.hyp (by right; left))) qFlipPack qCE
  have qBoth : PureFamilyDerivA Surface.code.body 5
      (.and qClassF (.and qClassFlipF (.and colGuardPackF eqSymmF))) :=
    PureFamilyDerivA.cut2 (SFormula.Deriv.andIntro .assumption (.hyp (by right; left))) qPack qTriple
  have xqPack : PureFamilyDerivA Surface.code.body 5
      (.and xPackF (.and qClassF (.and qClassFlipF (.and colGuardPackF eqSymmF)))) :=
    PureFamilyDerivA.cut2 (SFormula.Deriv.andIntro .assumption (.hyp (by right; left))) xPack qBoth
  refine PureFamilyDerivA.cut2 ?_
    (PureFamilyDerivA.allNatLtIntro (SC.n (numStab OddSurfaceDistance.d3.distance)) xqPack)
    (PureFamilyDerivA.allNatLtIntro (SC.n (numStab OddSurfaceDistance.d3.distance))
      (boundRowsResolved OddSurfaceDistance.d3))
  refine SFormula.Deriv.allNatLtIntroBounded _ _ ?_
  have hCombined :
      SFormula.Deriv
        (SFormula.boundNatLt (SC.n (numStab OddSurfaceDistance.d3.distance)) ::
          List.map (fun G => G.weaken)
            [SFormula.allNatLt (SC.n (numStab OddSurfaceDistance.d3.distance))
                (.and xPackF (.and qClassF (.and qClassFlipF (.and colGuardPackF eqSymmF)))),
              SFormula.allNatLt (SC.n (numStab OddSurfaceDistance.d3.distance))
                (SFormula.allNatLt (SC.n (nQubits OddSurfaceDistance.d3.distance))
                  (.eqPauli
                    ((SC.closed ((distAtBoundIdx2 OddSurfaceDistance.d3).dT.recCall liftedBoundIdx)).stabAt
                      (SC.closed Formula.qVar))
                    (SC.closed (rowSymTreeA OddSurfaceDistance.d3.index (distAtBoundIdx2 OddSurfaceDistance.d3).dT
                      liftedBoundIdx Formula.qVar))))])
        (.and xPackF (.and qClassF (.and qClassFlipF (.and colGuardPackF eqSymmF)))) :=
    SFormula.Deriv.applyNatBoundNatBeta (.and xPackF (.and qClassF (.and qClassFlipF (.and colGuardPackF eqSymmF))))
      (SFormula.Deriv.allNatLtElim
        (SC.n (numStab OddSurfaceDistance.d3.distance)).weaken
        ((SFormula.and xPackF (.and qClassF (.and qClassFlipF (.and colGuardPackF eqSymmF)))).lift 1)
        SFormula.boundNat (.hyp (List.mem_cons_of_mem _ List.mem_cons_self))
        (.hyp List.mem_cons_self))
  apply xCommBody
  · -- Weakened doubly-quantified resolved rows (third context hypothesis).
    exact .hyp (by right; right; left)
  · -- The bound `boundNat < 8` is the head of context.
    exact .hyp List.mem_cons_self
  · -- The guard pack `xPackF`.
    exact SFormula.Deriv.andElimLeft hCombined
  · -- The column classifier `qClassF`.
    exact SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hCombined)
  · -- The flipped column classifier `qClassFlipF`.
    exact SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hCombined))
  · -- The closed column guard pack `colGuardPackF`.
    exact SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight hCombined)))
  · -- The `eqNat`-symmetry pack `eqSymmF`.
    exact SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight hCombined)))

def zNormCommuteD3 :
    PureFamilyDerivA Surface.code.body (OddSurfaceDistance.d3.distance + 2)
      (closedSF (logicalZNormalizesOddF OddSurfaceDistance.d3)) := by
  -- Transpose of `xNormCommuteD3`.  Identical bound-exposing reduction: `cut1` the
  -- doubly-quantified row resolution, then `allNatLtIntroBounded` to keep `k < 8`.
  unfold closedSF logicalZNormalizesOddF Formula.normalizesCodeUpTo
  simp only [closedSF, Formula.codeRow, Term.weaken]
  refine PureFamilyDerivA.cut1 ?_
    (PureFamilyDerivA.allNatLtIntro (SC.n (numStab OddSurfaceDistance.d3.distance))
      (boundRowsResolved OddSurfaceDistance.d3))
  refine SFormula.Deriv.allNatLtIntroBounded _ _ ?_
  -- REMAINING (open) goal, at arity 1 with `k = var 0`, `k < 8` in context:
  --   ⊢ SFormula.commutesUpTo 9 (recCall 3 (var 0)) (lift logicalZ)
  -- Blocked by the same missing recursion-index substitution as `xNormCommuteD3`;
  -- the symbolic ROUTE-B residual here is the TOP-ROW (row-guard `q / 3 = 0`)
  -- even-parity argument (transpose of xNorm's column-0 frontier).  OPEN.
  sorry

end QHL.CodeLang.Surface.Verify
