import QStab.QHL.Verify.SurfaceGenericDefined

/-!
# `AllTermsGood` — the uniform term-totality strengthening of `DerivWF*`

This file builds the *term-totality* strengthening of the structural
well-formedness invariants (`DerivWF` / `DerivWFA` / `DerivWFP`) from
`SurfaceGenericDefined.lean`, plus the `∀ d` cast-robust bridge

    allTermsGood_derivWF*  :  AllTermsGood* d → DerivWF* d

so that, composed with the already-proved generic engine
`deriv_defined` / `pfda_defined` / `pfd_defined`, one obtains

    AllTermsGood* d → d.DefinedObligations.

## Design

`DerivWF*` already mirrors the frozen `DefinedObligations` arm-for-arm: recursive
arms are the children's `DerivWF*`; leaf arms carry the *library-input hypothesis*
(`FormulaDefined`/range facts).  `AllTermsGood*` is one step further: at every
`FormulaDefined`-bearing leaf it carries the **term-totalities** (`∃ v,
STerm.eval … = some v`, total-up-to-`n` for stabilizers) that the leaf libraries
(`formulaDefined_eqPauli`, `formulaDefined_eqStabUpTo`,
`formulaDefined_commutesUpTo`, `formulaDefined_weightLe`, …) consume to produce
the `FormulaDefined`.  The recursive arms are *identical* to `DerivWF*`.

`allTermsGood_derivWF*` is a clean `∀ d` induction over the derivation recursors:
recursive arms relay the IH; leaf arms discharge the matching `DerivWF*` leaf
clause from `AllTermsGood*`'s carried term-totalities via the leaf library.
Because it is `∀ d` it is CAST-ROBUST — the IH applies to whole subtrees through
any `Eq.mpr`/`cast` wrapper, so the bridge itself never touches the
`derivWF_cast_type` friction (that friction lives only in *establishing*
`AllTermsGood*` of a concrete tree, exactly as it did for `DerivWF*`).

## Scope / cost finding (recorded here for soundness transparency)

`AllTermsGood*` is a *strengthening*, not a shortcut.  Establishing
`AllTermsGood* (codeLevel D)` is **still a per-tree structural walk** — see the
file-level report — because `codeLevel D` embeds the ~14 kLOC symbolic
derivations `rowsCommuteSym D` / `xNormScaffold D` / `zNormScaffold D`, and the
frozen `DefinedObligations` recurses on the concrete tree node-by-node.  The
term-totality leaves *are* uniformly dischargeable (closed-pure terms via
`PureTerm.eval_total`; `recCall (natLit dist) (pure)` via
`recCall_total_symbolicK`; open `E` under `TotalUpTo`), but the walk over the
tree itself is irreducible.  `AllTermsGood*` therefore does not make
`codeLevelDefined` cheap; it is the reusable per-node leaf interface for the walk.
-/

namespace QHL.CodeLang.Surface.Verify

open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface

/-! ## `AllTermsGood` over `SFormula.Deriv`

Mirror of `DerivWF`.  Recursive arms are byte-identical; the
`FormulaDefined`-bearing leaf arms are replaced by the term-totalities that imply
them through the leaf library.  For the few leaves whose carried formula is a
*generic compound* `A` (`orIntroRight`/`notIntro`/`impIntro`) we keep the
`FormulaDefined A` premise verbatim (there is no simpler term-totality form for an
arbitrary `A`); these are not surface-atom leaves. -/
def AllTermsGood {arity : Nat} {Γ : List (SFormula arity)} {A : SFormula arity}
    (D : SFormula.Deriv Γ A) (cb : Term 2 .stab) (fuel : Nat)
    (rho : Env arity) (E : PartialStabilizer) : Prop :=
  match D with
  | .hyp _ => True
  | .contextWeakening _ child => AllTermsGood child cb fuel rho E
  | .weakenFresh child => AllTermsGood child cb fuel (envTail' rho) E
  | .top => True
  | .botElim child => AllTermsGood child cb fuel rho E
  | .andIntro left right =>
      AllTermsGood left cb fuel rho E ∧ AllTermsGood right cb fuel rho E
  | .andElimLeft child => AllTermsGood child cb fuel rho E
  | .andElimRight child => AllTermsGood child cb fuel rho E
  | .orIntroLeft child => AllTermsGood child cb fuel rho E
  | .orIntroRight (A := A) child =>
      SFormula.Deriv.FormulaDefined cb fuel rho E A ∧ AllTermsGood child cb fuel rho E
  | .orElim disj left right =>
      AllTermsGood disj cb fuel rho E ∧ AllTermsGood left cb fuel rho E ∧
        AllTermsGood right cb fuel rho E
  | .notIntro (A := A) child =>
      SFormula.Deriv.FormulaDefined cb fuel rho E A ∧ AllTermsGood child cb fuel rho E
  | .notElim positive negative =>
      AllTermsGood positive cb fuel rho E ∧ AllTermsGood negative cb fuel rho E
  | .impIntro (A := A) child =>
      SFormula.Deriv.FormulaDefined cb fuel rho E A ∧ AllTermsGood child cb fuel rho E
  | .mp implication antecedent =>
      AllTermsGood implication cb fuel rho E ∧ AllTermsGood antecedent cb fuel rho E
  | .boolCases b _ left right =>
      (∃ bv, b.eval cb fuel rho E = some bv) ∧
        AllTermsGood left cb fuel rho E ∧ AllTermsGood right cb fuel rho E
  | .allNatLtIntro (Γ := Γ) n _ child =>
      ∃ bound, n.eval cb fuel rho E = some bound ∧
        ∀ x, x < bound →
          AllTermsGood child cb fuel (Env.cons x rho) E ∧
            SFormula.ContextHolds cb fuel rho E Γ
  | .allNatLtIntroBounded (Γ := Γ) n _ child =>
      ∃ bound, n.eval cb fuel rho E = some bound ∧
        ∀ x, x < bound →
          AllTermsGood child cb fuel (Env.cons x rho) E ∧
            SFormula.ContextHolds cb fuel rho E Γ
  | .allNatLtElim _ _ _ forallD ltD =>
      AllTermsGood forallD cb fuel rho E ∧ AllTermsGood ltD cb fuel rho E
  | .applyNatBoundNatBeta _ child => AllTermsGood child cb fuel rho E
  | .applyNatSubstitutionBeta _ _ _ child => AllTermsGood child cb fuel rho E
  | .applyNatSubstitutionBetaElim _ _ _ child => AllTermsGood child cb fuel rho E
  | .closedNatLt _ _ _ => True
  | .divLtOfLtSquare _ _ child => AllTermsGood child cb fuel rho E
  | .modLtOfLtSquare _ _ child => AllTermsGood child cb fuel rho E
  | .gridIdxLeftLtSquare _ _ _ rowLt colLt =>
      AllTermsGood rowLt cb fuel rho E ∧ AllTermsGood colLt cb fuel rho E
  | .gridIdxLeftDivEq _ _ _ rowLt colLt =>
      AllTermsGood rowLt cb fuel rho E ∧ AllTermsGood colLt cb fuel rho E
  | .gridIdxLeftModEq _ _ _ rowLt colLt =>
      AllTermsGood rowLt cb fuel rho E ∧ AllTermsGood colLt cb fuel rho E
  | .gridIdxLeftDivModEqOfRow _ _ _ qLt rowEq =>
      AllTermsGood qLt cb fuel rho E ∧ AllTermsGood rowEq cb fuel rho E
  | .gridIdxLeftDivModEqOfCol _ _ _ qLt colEq =>
      AllTermsGood qLt cb fuel rho E ∧ AllTermsGood colEq cb fuel rho E
  | .ltOfLtLtClosedPred _ _ _ xy ylimit =>
      AllTermsGood xy cb fuel rho E ∧ AllTermsGood ylimit cb fuel rho E
  -- `eqStabRefl n A`: `FormulaDefined (.eqStabUpTo n A A)` ← n total + A total-up-to-n.
  | .eqStabRefl n A =>
      ∃ nv Av, n.eval cb fuel rho E = some nv ∧ A.eval cb fuel rho E = some Av ∧
        StabTotalUpTo nv Av
  | .eqStabSymm _ _ _ child => AllTermsGood child cb fuel rho E
  | .eqStabTrans _ _ _ _ left right =>
      AllTermsGood left cb fuel rho E ∧ AllTermsGood right cb fuel rho E
  | .eqPauliSymm _ _ child => AllTermsGood child cb fuel rho E
  | .eqPauliTrans _ _ _ left right =>
      AllTermsGood left cb fuel rho E ∧ AllTermsGood right cb fuel rho E
  | .eqNatBoolTrue _ _ child => AllTermsGood child cb fuel rho E
  | .eqBoolFalseNotTrue _ child => AllTermsGood child cb fuel rho E
  | .eqBoolTrueNotFalse _ child => AllTermsGood child cb fuel rho E
  | .eqStabMulCongr _ _ _ _ _ left right =>
      AllTermsGood left cb fuel rho E ∧ AllTermsGood right cb fuel rho E
  | .eqStabMulAssoc _ _ _ _ hA hB hC =>
      AllTermsGood hA cb fuel rho E ∧ AllTermsGood hB cb fuel rho E ∧
        AllTermsGood hC cb fuel rho E
  | .eqStabMulComm _ _ _ hA hB =>
      AllTermsGood hA cb fuel rho E ∧ AllTermsGood hB cb fuel rho E
  | .eqStabMulSelf _ _ child => AllTermsGood child cb fuel rho E
  | .eqStabMulOneLeft _ _ child => AllTermsGood child cb fuel rho E
  | .eqStabMulOneRight _ _ child => AllTermsGood child cb fuel rho E
  -- `eqStabFoldZero/Succ`: keep the `FormulaDefined` verbatim (the fold-eval form
  -- is not a flat term-totality; these do not occur in the surface code-level tree).
  | .eqStabFoldZero n body =>
      SFormula.Deriv.FormulaDefined cb fuel rho E
        (.eqStabUpTo n (SC.stabFold (SC.n 0) body) SC.stabOne)
  | .eqStabFoldSucc n bound body =>
      SFormula.Deriv.FormulaDefined cb fuel rho E (.eqStabUpTo n
        (SC.stabFold (SC.succClosed bound) body)
        (SC.stabMul (SC.stabFold (SC.closed bound) body) (SC.applyNat bound body)))
  | .commutesSymm _ _ _ child => AllTermsGood child cb fuel rho E
  | .noncommutesSymm _ _ _ child => AllTermsGood child cb fuel rho E
  | .commutesOfEqLeft _ _ _ _ eqD commD =>
      AllTermsGood eqD cb fuel rho E ∧ AllTermsGood commD cb fuel rho E
  | .commutesOfEqRight _ _ _ _ eqD commD =>
      AllTermsGood eqD cb fuel rho E ∧ AllTermsGood commD cb fuel rho E
  | .noncommutesOfEqLeft _ _ _ _ eqD noncommD =>
      AllTermsGood eqD cb fuel rho E ∧ AllTermsGood noncommD cb fuel rho E
  | .noncommutesOfEqRight _ _ _ _ eqD noncommD =>
      AllTermsGood eqD cb fuel rho E ∧ AllTermsGood noncommD cb fuel rho E
  | .commutesStabMulLeft _ _ _ _ left right =>
      AllTermsGood left cb fuel rho E ∧ AllTermsGood right cb fuel rho E
  | .noncommutesStabMulLeft _ _ _ _ left right =>
      AllTermsGood left cb fuel rho E ∧ AllTermsGood right cb fuel rho E
  | .noncommutesStabMulRight _ _ _ _ left right =>
      AllTermsGood left cb fuel rho E ∧ AllTermsGood right cb fuel rho E
  -- `commutesStabFoldLeft`: child + `FormulaDefined (commutesUpTo n (stabFold..) C)`
  -- ← n total + (stabFold..) total-up-to-n + C total-up-to-n.
  | .commutesStabFoldLeft n bound body C child =>
      AllTermsGood child cb fuel rho E ∧
        ∃ nv fv Cv, n.eval cb fuel rho E = some nv ∧
          (SC.stabFold bound body).eval cb fuel rho E = some fv ∧
            C.eval cb fuel rho E = some Cv ∧
              StabTotalUpTo nv fv ∧ StabTotalUpTo nv Cv
  | .commutesOfPointwise n A B child =>
      AllTermsGood child cb fuel rho E ∧
        ∃ nv Av Bv, n.eval cb fuel rho E = some nv ∧
          A.eval cb fuel rho E = some Av ∧ B.eval cb fuel rho E = some Bv ∧
            StabTotalUpTo nv Av ∧ StabTotalUpTo nv Bv
  | .noncommutesOfSingleAnti _ _ _ _ ltD antiD restD =>
      AllTermsGood ltD cb fuel rho E ∧ AllTermsGood antiD cb fuel rho E ∧
        AllTermsGood restD cb fuel rho E
  | .commutesOfTwoAnti _ _ _ _ _ lt0D lt1D neD anti0D anti1D restD =>
      AllTermsGood lt0D cb fuel rho E ∧ AllTermsGood lt1D cb fuel rho E ∧
        AllTermsGood neD cb fuel rho E ∧ AllTermsGood anti0D cb fuel rho E ∧
          AllTermsGood anti1D cb fuel rho E ∧ AllTermsGood restD cb fuel rho E
  -- `stabAtClosedIteLamEq{Then,Else}`: child + `FormulaDefined (eqPauli LHS RHS)`
  -- ← both pauli sides total.
  | .stabAtClosedIteLamEqThen cond thenP elseP q _ child =>
      AllTermsGood child cb fuel rho E ∧
        (∃ v, (STerm.stabAt (SC.closed (.stabLam (.ite cond thenP elseP)))
            (SC.closed q)).eval cb fuel rho E = some v) ∧
          (∃ v, Term.eval cb fuel (Term.instantiateTopNat q thenP) rho = some v)
  | .stabAtClosedIteLamEqElse cond thenP elseP q _ child =>
      AllTermsGood child cb fuel rho E ∧
        (∃ v, (STerm.stabAt (SC.closed (.stabLam (.ite cond thenP elseP)))
            (SC.closed q)).eval cb fuel rho E = some v) ∧
          (∃ v, Term.eval cb fuel (Term.instantiateTopNat q elseP) rho = some v)
  | .pauliIteSelectThen cond p1 p2 child =>
      AllTermsGood child cb fuel rho E ∧
        (∃ v, Term.eval cb fuel (.ite cond p1 p2) rho = some v) ∧
          (∃ v, Term.eval cb fuel p1 rho = some v)
  | .pauliIteSelectElse cond p1 p2 child =>
      AllTermsGood child cb fuel rho E ∧
        (∃ v, Term.eval cb fuel (.ite cond p1 p2) rho = some v) ∧
          (∃ v, Term.eval cb fuel p2 rho = some v)
  -- `localCommutesOf*`: child(ren) + `FormulaDefined (localCommutesAt A B q)`
  -- ← both `A@q`, `B@q` total.
  | .localCommutesOfLeftI A B q child =>
      AllTermsGood child cb fuel rho E ∧
        (∃ v, (STerm.stabAt A q).eval cb fuel rho E = some v) ∧
          (∃ v, (STerm.stabAt B q).eval cb fuel rho E = some v)
  | .localCommutesOfLeftEqNoAntiRight A B q p eqD noAntiD =>
      AllTermsGood eqD cb fuel rho E ∧ AllTermsGood noAntiD cb fuel rho E ∧
        (∃ v, (STerm.stabAt A q).eval cb fuel rho E = some v) ∧
          (∃ v, (STerm.stabAt B q).eval cb fuel rho E = some v)
  | .localCommutesOfRightI A B q child =>
      AllTermsGood child cb fuel rho E ∧
        (∃ v, (STerm.stabAt A q).eval cb fuel rho E = some v) ∧
          (∃ v, (STerm.stabAt B q).eval cb fuel rho E = some v)
  -- `anticommutesTransport`: 3 children + `FormulaDefined (eqBool (anticommutes a b) rhs)`
  -- ← both pauli sides total + rhs bool total.
  | .anticommutesTransport a b _ _ rhs eqAD eqBD antiD =>
      AllTermsGood eqAD cb fuel rho E ∧ AllTermsGood eqBD cb fuel rho E ∧
        AllTermsGood antiD cb fuel rho E ∧
          (∃ v, a.eval cb fuel rho E = some v) ∧ (∃ v, b.eval cb fuel rho E = some v) ∧
            (∃ v, rhs.eval cb fuel rho E = some v)
  -- `noAntiAtSubst`: 2 children + `FormulaDefined (not (eqBool (anticommutes (E@q₂) p) true))`
  -- ← `E@q₂` total + p total.
  | .noAntiAtSubst Eterm p _ q₂ _ _ eqD noAntiD =>
      AllTermsGood eqD cb fuel rho E ∧ AllTermsGood noAntiD cb fuel rho E ∧
        (∃ v, (STerm.stabAt Eterm (SC.closed q₂)).eval cb fuel rho E = some v) ∧
          (∃ v, p.eval cb fuel rho E = some v)
  | .pauliAnticommutesNonI _ _ child => AllTermsGood child cb fuel rho E
  | .pauliAnticommutesLit _ _ => True
  | .pauliMulLit _ _ => True
  | .pauliEqLit _ => True
  | .pauliNeqLit _ _ _ => True
  -- `finite{Injective,Surjective}WeightLower`: children + `FormulaDefined (weightLe n E limit)`
  -- ← n total + E total + limit total + E total-up-to-n.
  | .finiteInjectiveWeightLower n Eterm limit _ _ support inj lt =>
      AllTermsGood support cb fuel rho E ∧ AllTermsGood inj cb fuel rho E ∧
        AllTermsGood lt cb fuel rho E ∧
          ∃ nv Ev lv, n.eval cb fuel rho E = some nv ∧
            Eterm.eval cb fuel rho E = some Ev ∧ limit.eval cb fuel rho E = some lv ∧
              StabTotalUpTo nv Ev
  | .finiteSurjectiveWeightLower n Eterm limit _ _ cover lt =>
      AllTermsGood cover cb fuel rho E ∧ AllTermsGood lt cb fuel rho E ∧
        ∃ nv Ev lv, n.eval cb fuel rho E = some nv ∧
          Eterm.eval cb fuel rho E = some Ev ∧ limit.eval cb fuel rho E = some lv ∧
            StabTotalUpTo nv Ev
  | .finiteDeMorgan n A child =>
      AllTermsGood child cb fuel rho E ∧
        ∃ bound, n.eval cb fuel rho E = some bound ∧
          ∀ x, x < bound →
            SFormula.Deriv.FormulaDefined cb fuel (Env.cons x rho) E A
  | .existsNatLtIntro (Γ := Γ) n A witness child =>
      ∃ bound, n.eval cb fuel rho E = some bound ∧ witness < bound ∧
        (∀ x, x < bound →
          SFormula.Deriv.FormulaDefined cb fuel (Env.cons x rho) E A) ∧
          AllTermsGood child cb fuel (Env.cons witness rho) E ∧
            SFormula.ContextHolds cb fuel rho E Γ
  | .existsNatLtIntroTerm n A _ ltD bodyD =>
      AllTermsGood ltD cb fuel rho E ∧ AllTermsGood bodyD cb fuel rho E ∧
        ∃ bound, n.eval cb fuel rho E = some bound ∧
          ∀ x, x < bound →
            SFormula.Deriv.FormulaDefined cb fuel (Env.cons x rho) E A
  | .existsNatLtElim (Γ := Γ) n A _ existsD bodyD =>
      AllTermsGood existsD cb fuel rho E ∧
        ∃ bound, n.eval cb fuel rho E = some bound ∧
          ∀ x, x < bound →
            A.eval cb fuel (Env.cons x rho) E = some true →
              AllTermsGood bodyD cb fuel (Env.cons x rho) E ∧
                SFormula.ContextHolds cb fuel rho E Γ

/-! ## The cast-robust bridge `allTermsGood_derivWF`

`∀ d` induction.  Recursive arms relay the IH; leaf arms discharge the matching
`DerivWF` `FormulaDefined` clause from the carried term-totalities via the leaf
library (`formulaDefined_*`, `sterm_eval_*`). -/

set_option maxHeartbeats 1000000 in
theorem allTermsGood_derivWF {arity : Nat} {Γ : List (SFormula arity)}
    {A : SFormula arity} (D : SFormula.Deriv Γ A) (cb : Term 2 .stab) (fuel : Nat)
    (rho : Env arity) (E : PartialStabilizer)
    (hG : AllTermsGood D cb fuel rho E) :
    DerivWF D cb fuel rho E := by
  induction D with
  | hyp _ => exact True.intro
  | contextWeakening _ child ih => exact ih rho hG
  | weakenFresh child ih => exact ih (envTail' rho) hG
  | top => exact True.intro
  | botElim child ih => exact ih rho hG
  | andIntro left right ihL ihR => exact ⟨ihL rho hG.1, ihR rho hG.2⟩
  | andElimLeft child ih => exact ih rho hG
  | andElimRight child ih => exact ih rho hG
  | orIntroLeft child ih => exact ih rho hG
  | orIntroRight child ih => exact ⟨hG.1, ih rho hG.2⟩
  | orElim disj left right ihD ihL ihR =>
      exact ⟨ihD rho hG.1, ihL rho hG.2.1, ihR rho hG.2.2⟩
  | notIntro child ih => exact ⟨hG.1, ih rho hG.2⟩
  | notElim positive negative ihP ihN => exact ⟨ihP rho hG.1, ihN rho hG.2⟩
  | impIntro child ih => exact ⟨hG.1, fun _ => ih rho hG.2⟩
  | mp implication antecedent ihI ihA => exact ⟨ihI rho hG.1, ihA rho hG.2⟩
  | boolCases b C left right ihL ihR =>
      exact ⟨hG.1, fun _ => ihL rho hG.2.1, fun _ => ihR rho hG.2.2⟩
  | allNatLtIntro n A child ih =>
      obtain ⟨bound, hbound, hbody⟩ := hG
      exact ⟨bound, hbound, fun x hx => ⟨ih (Env.cons x rho) (hbody x hx).1, (hbody x hx).2⟩⟩
  | allNatLtIntroBounded n A child ih =>
      obtain ⟨bound, hbound, hbody⟩ := hG
      exact ⟨bound, hbound, fun x hx => ⟨ih (Env.cons x rho) (hbody x hx).1, (hbody x hx).2⟩⟩
  | allNatLtElim n A witness forallD ltD ihF ihL => exact ⟨ihF rho hG.1, ihL rho hG.2⟩
  | applyNatBoundNatBeta A child ih => exact ih rho hG
  | applyNatSubstitutionBeta x A hx child ih => exact ih rho hG
  | applyNatSubstitutionBetaElim x A hx child ih => exact ih rho hG
  | closedNatLt a b h => exact True.intro
  | divLtOfLtSquare dist q child ih => exact ih rho hG
  | modLtOfLtSquare dist q child ih => exact ih rho hG
  | gridIdxLeftLtSquare dist row col rowLt colLt ihR ihC => exact ⟨ihR rho hG.1, ihC rho hG.2⟩
  | gridIdxLeftDivEq dist row col rowLt colLt ihR ihC => exact ⟨ihR rho hG.1, ihC rho hG.2⟩
  | gridIdxLeftModEq dist row col rowLt colLt ihR ihC => exact ⟨ihR rho hG.1, ihC rho hG.2⟩
  | gridIdxLeftDivModEqOfRow dist row q qLt rowEq ihQ ihR => exact ⟨ihQ rho hG.1, ihR rho hG.2⟩
  | gridIdxLeftDivModEqOfCol dist col q qLt colEq ihQ ihC => exact ⟨ihQ rho hG.1, ihC rho hG.2⟩
  | ltOfLtLtClosedPred limit x y xy ylimit ihXY ihYL => exact ⟨ihXY rho hG.1, ihYL rho hG.2⟩
  | eqStabRefl n A =>
      obtain ⟨nv, Av, hn, hA, htA⟩ := hG
      exact formulaDefined_eqStabUpTo hn hA hA htA htA
  | eqStabSymm n A B child ih => exact ih rho hG
  | eqStabTrans n A B C left right ihL ihR => exact ⟨ihL rho hG.1, ihR rho hG.2⟩
  | eqPauliSymm a b child ih => exact ih rho hG
  | eqPauliTrans a b c left right ihL ihR => exact ⟨ihL rho hG.1, ihR rho hG.2⟩
  | eqNatBoolTrue a b child ih => exact ih rho hG
  | eqBoolFalseNotTrue b child ih => exact ih rho hG
  | eqBoolTrueNotFalse b child ih => exact ih rho hG
  | eqStabMulCongr n A A' B B' left right ihL ihR => exact ⟨ihL rho hG.1, ihR rho hG.2⟩
  | eqStabMulAssoc n A B C hA hB hC ihA ihB ihC => exact ⟨ihA rho hG.1, ihB rho hG.2.1, ihC rho hG.2.2⟩
  | eqStabMulComm n A B hA hB ihA ihB => exact ⟨ihA rho hG.1, ihB rho hG.2⟩
  | eqStabMulSelf n A child ih => exact ih rho hG
  | eqStabMulOneLeft n A child ih => exact ih rho hG
  | eqStabMulOneRight n A child ih => exact ih rho hG
  | eqStabFoldZero n body => exact hG
  | eqStabFoldSucc n bound body => exact hG
  | commutesSymm n A B child ih => exact ih rho hG
  | noncommutesSymm n A B child ih => exact ih rho hG
  | commutesOfEqLeft n A B C eqD commD ihE ihC => exact ⟨ihE rho hG.1, ihC rho hG.2⟩
  | commutesOfEqRight n A B C eqD commD ihE ihC => exact ⟨ihE rho hG.1, ihC rho hG.2⟩
  | noncommutesOfEqLeft n A B C eqD noncommD ihE ihN => exact ⟨ihE rho hG.1, ihN rho hG.2⟩
  | noncommutesOfEqRight n A B C eqD noncommD ihE ihN => exact ⟨ihE rho hG.1, ihN rho hG.2⟩
  | commutesStabMulLeft n A B C left right ihL ihR => exact ⟨ihL rho hG.1, ihR rho hG.2⟩
  | noncommutesStabMulLeft n A B C left right ihL ihR => exact ⟨ihL rho hG.1, ihR rho hG.2⟩
  | noncommutesStabMulRight n A B C left right ihL ihR => exact ⟨ihL rho hG.1, ihR rho hG.2⟩
  | commutesStabFoldLeft n bound body C child ih =>
      obtain ⟨hchild, nv, fv, Cv, hn, hf, hC, htf, htC⟩ := hG
      exact ⟨ih rho hchild, formulaDefined_commutesUpTo hn hf hC htf htC⟩
  | commutesOfPointwise n A B child ih =>
      obtain ⟨hchild, nv, Av, Bv, hn, hA, hB, htA, htB⟩ := hG
      exact ⟨ih rho hchild, formulaDefined_commutesUpTo hn hA hB htA htB⟩
  | noncommutesOfSingleAnti n A B q0 ltD antiD restD ihL ihA ihR =>
      exact ⟨ihL rho hG.1, ihA rho hG.2.1, ihR rho hG.2.2⟩
  | commutesOfTwoAnti n A B q0 q1 lt0D lt1D neD anti0D anti1D restD ih0 ih1 ihN ihA0 ihA1 ihR =>
      exact ⟨ih0 rho hG.1, ih1 rho hG.2.1, ihN rho hG.2.2.1, ihA0 rho hG.2.2.2.1,
        ihA1 rho hG.2.2.2.2.1, ihR rho hG.2.2.2.2.2⟩
  | stabAtClosedIteLamEqThen cond thenP elseP q hq child ih =>
      exact ⟨ih rho hG.1, formulaDefined_eqPauli hG.2.1 (sterm_eval_closed hG.2.2)⟩
  | stabAtClosedIteLamEqElse cond thenP elseP q hq child ih =>
      exact ⟨ih rho hG.1, formulaDefined_eqPauli hG.2.1 (sterm_eval_closed hG.2.2)⟩
  | pauliIteSelectThen cond p1 p2 child ih =>
      exact ⟨ih rho hG.1, formulaDefined_eqPauli (sterm_eval_closed hG.2.1) (sterm_eval_closed hG.2.2)⟩
  | pauliIteSelectElse cond p1 p2 child ih =>
      exact ⟨ih rho hG.1, formulaDefined_eqPauli (sterm_eval_closed hG.2.1) (sterm_eval_closed hG.2.2)⟩
  | localCommutesOfLeftI A B q child ih =>
      exact ⟨ih rho hG.1, formulaDefined_localCommutesAt hG.2.1 hG.2.2⟩
  | localCommutesOfLeftEqNoAntiRight A B q p eqD noAntiD ihE ihN =>
      exact ⟨ihE rho hG.1, ihN rho hG.2.1, formulaDefined_localCommutesAt hG.2.2.1 hG.2.2.2⟩
  | localCommutesOfRightI A B q child ih =>
      exact ⟨ih rho hG.1, formulaDefined_localCommutesAt hG.2.1 hG.2.2⟩
  | anticommutesTransport a a' b b' rhs eqAD eqBD antiD ihA ihB ihAnti =>
      refine ⟨ihA rho hG.1, ihB rho hG.2.1, ihAnti rho hG.2.2.1, ?_⟩
      exact formulaDefined_eqBool (sterm_eval_anticommutes hG.2.2.2.1 hG.2.2.2.2.1) hG.2.2.2.2.2
  | noAntiAtSubst Eterm p q₁ q₂ hq1 hq2 eqD noAntiD ihE ihN =>
      refine ⟨ihE rho hG.1, ihN rho hG.2.1, ?_⟩
      exact formulaDefined_not (formulaDefined_eqBool
        (sterm_eval_anticommutes hG.2.2.1 hG.2.2.2) (sterm_eval_b true))
  | pauliAnticommutesNonI p a child ih => exact ih rho hG
  | pauliAnticommutesLit p q => exact True.intro
  | pauliMulLit p q => exact True.intro
  | pauliEqLit p => exact True.intro
  | pauliNeqLit p q h => exact True.intro
  | finiteInjectiveWeightLower n Eterm limit k slot support inj lt ihS ihI ihL =>
      obtain ⟨hS, hI, hLt, nv, Ev, lv, hn, hE, hlim, htE⟩ := hG
      exact ⟨ihS rho hS, ihI rho hI, ihL rho hLt, formulaDefined_weightLe hn hE hlim htE⟩
  | finiteSurjectiveWeightLower n Eterm limit k rowOf cover lt ihC ihL =>
      obtain ⟨hC, hLt, nv, Ev, lv, hn, hE, hlim, htE⟩ := hG
      exact ⟨ihC rho hC, ihL rho hLt, formulaDefined_weightLe hn hE hlim htE⟩
  | finiteDeMorgan n A child ih => exact ⟨ih rho hG.1, hG.2⟩
  | existsNatLtIntro n A witness child ih =>
      obtain ⟨bound, hbound, hwlt, hfd, hchild, hctx⟩ := hG
      exact ⟨bound, hbound, hwlt, hfd, ih (Env.cons witness rho) hchild, hctx⟩
  | existsNatLtIntroTerm n A witness ltD bodyD ihL ihB =>
      exact ⟨ihL rho hG.1, ihB rho hG.2.1, hG.2.2⟩
  | existsNatLtElim n A C existsD bodyD ihE ihB =>
      obtain ⟨hex, bound, hbound, hbody⟩ := hG
      refine ⟨ihE rho hex, bound, hbound, fun x hx hAtrue => ?_⟩
      obtain ⟨hbodyG, hctx⟩ := hbody x hx hAtrue
      exact ⟨ihB (Env.cons x rho) hbodyG, hctx⟩

/-! ## `AllTermsGoodA` over `PureFamilyDerivA`

Mirror of `DerivWFA`.  The `core`/`cut*` arms route to `AllTermsGood` (instead of
`DerivWF`); every other arm of `DerivWFA` is *already* a term-totality clause and
is reproduced verbatim. -/
def AllTermsGoodA {cb : Term 2 .stab} {fuel arity : Nat} {A : SFormula arity}
    (D : PureFamilyDerivA cb fuel A) (rho : Env arity) (E : PartialStabilizer) :
    Prop :=
  match D with
  | .core Dcore => AllTermsGood Dcore cb fuel rho E
  | .recUnfold n dT kT _ _ =>
      ∃ nv dv kv sa,
        n.eval cb fuel rho E = some nv ∧
          Term.eval cb fuel dT rho = some dv ∧
            Term.eval cb fuel kT rho = some kv ∧
              Term.eval cb fuel (.recCall dT kT) rho = some sa ∧
                ∀ q, q < nv → ∃ p, sa q = some p
  | .allNatLtIntro n child =>
      ∃ bound, n.eval cb fuel rho E = some bound ∧
        ∀ x, x < bound → AllTermsGoodA child (Env.cons x rho) E
  | .foldCongr n bound _ _ child =>
      ∃ nv bv, n.eval cb fuel rho E = some nv ∧
        bound.eval cb fuel rho E = some bv ∧ AllTermsGoodA child rho E
  | .eqStabOfPointwiseEq n A B child =>
      ∃ nv Av Bv,
        n.eval cb fuel rho E = some nv ∧
          A.eval cb fuel rho E = some Av ∧
            B.eval cb fuel rho E = some Bv ∧
              AllTermsGoodA child rho E
  | .arithBool _ _ _ => True
  | .iteSelectThen n _ S1 _ child =>
      ∃ nv s1, n.eval cb fuel rho E = some nv ∧
        AllTermsGoodA child rho E ∧
          Term.eval cb fuel S1 rho = some s1 ∧
            ∀ q, q < nv → ∃ p, s1 q = some p
  | .iteSelectElse n _ _ S2 child =>
      ∃ nv s2, n.eval cb fuel rho E = some nv ∧
        AllTermsGoodA child rho E ∧
          Term.eval cb fuel S2 rho = some s2 ∧
            ∀ q, q < nv → ∃ p, s2 q = some p
  | .eqPauliProj n _ _ q child =>
      ∃ nv qv, n.eval cb fuel rho E = some nv ∧
        q.eval cb fuel rho E = some qv ∧ qv < nv ∧
          AllTermsGoodA child rho E
  | .eqPauliRefl a =>
      ∃ av, a.eval cb fuel rho E = some av
  | .eqPauliSymm _ _ child => AllTermsGoodA child rho E
  | .eqPauliTrans _ _ _ child1 child2 =>
      AllTermsGoodA child1 rho E ∧ AllTermsGoodA child2 rho E
  | .pauliIteSelectThen _ p1 _ child =>
      AllTermsGoodA child rho E ∧ ∃ pv, Term.eval cb fuel p1 rho = some pv
  | .pauliIteSelectElse _ _ p2 child =>
      AllTermsGoodA child rho E ∧ ∃ pv, Term.eval cb fuel p2 rho = some pv
  | .closedStabAtSplit s q =>
      ∃ pv, Term.eval cb fuel (.stabAt s q) rho = some pv
  | .weightLeBySupport n Eterm w _ child =>
      ∃ nv Ev wv,
        n.eval cb fuel rho E = some nv ∧
          Eterm.eval cb fuel rho E = some Ev ∧
            w.eval cb fuel rho E = some wv ∧
              (∃ v, weightUpTo nv Ev = some v) ∧
                AllTermsGoodA child rho E
  | .cut1 Dcore hA =>
      AllTermsGood Dcore cb fuel rho E ∧ AllTermsGoodA hA rho E
  | .cut2 Dcore hA hB =>
      AllTermsGood Dcore cb fuel rho E ∧ AllTermsGoodA hA rho E ∧ AllTermsGoodA hB rho E

theorem allTermsGoodA_derivWFA {cb : Term 2 .stab} {fuel arity : Nat}
    {A : SFormula arity} (D : PureFamilyDerivA cb fuel A) (rho : Env arity)
    (E : PartialStabilizer) (hG : AllTermsGoodA D rho E) :
    DerivWFA D rho E := by
  induction D with
  | core Dcore => exact allTermsGood_derivWF Dcore cb fuel rho E hG
  | recUnfold n dT kT hd hk => exact hG
  | allNatLtIntro n child ih =>
      obtain ⟨bound, hbound, hbody⟩ := hG
      exact ⟨bound, hbound, fun x hx => ih (Env.cons x rho) (hbody x hx)⟩
  | foldCongr n bound body1 body2 child ih =>
      obtain ⟨nv, bv, hn, hb, hchild⟩ := hG
      exact ⟨nv, bv, hn, hb, ih rho hchild⟩
  | eqStabOfPointwiseEq n A B child ih =>
      obtain ⟨nv, Av, Bv, hn, hA, hB, hchild⟩ := hG
      exact ⟨nv, Av, Bv, hn, hA, hB, ih rho hchild⟩
  | arithBool A hfrag hvalid => exact True.intro
  | iteSelectThen n cond S1 S2 child ih =>
      obtain ⟨nv, s1, hn, hchild, hS1, hS1def⟩ := hG
      exact ⟨nv, s1, hn, ih rho hchild, hS1, hS1def⟩
  | iteSelectElse n cond S1 S2 child ih =>
      obtain ⟨nv, s2, hn, hchild, hS2, hS2def⟩ := hG
      exact ⟨nv, s2, hn, ih rho hchild, hS2, hS2def⟩
  | eqPauliProj n A B q child ih =>
      obtain ⟨nv, qv, hn, hq, hqlt, hchild⟩ := hG
      exact ⟨nv, qv, hn, hq, hqlt, ih rho hchild⟩
  | eqPauliRefl a => exact hG
  | eqPauliSymm a b child ih => exact ih rho hG
  | eqPauliTrans a b c child1 child2 ih1 ih2 => exact ⟨ih1 rho hG.1, ih2 rho hG.2⟩
  | pauliIteSelectThen cond p1 p2 child ih => exact ⟨ih rho hG.1, hG.2⟩
  | pauliIteSelectElse cond p1 p2 child ih => exact ⟨ih rho hG.1, hG.2⟩
  | closedStabAtSplit s q => exact hG
  | weightLeBySupport n Eterm w cover child ih =>
      obtain ⟨nv, Ev, wv, hn, hE, hw, hweight, hchild⟩ := hG
      exact ⟨nv, Ev, wv, hn, hE, hw, hweight, ih rho hchild⟩
  | cut1 Dcore hA ihA =>
      exact ⟨allTermsGood_derivWF Dcore cb fuel rho E hG.1, ihA rho hG.2⟩
  | cut2 Dcore hA hB ihA ihB =>
      exact ⟨allTermsGood_derivWF Dcore cb fuel rho E hG.1, ihA rho hG.2.1, ihB rho hG.2.2⟩

/-! ## `AllTermsGoodP` over `PureFamilyDeriv` (top level)

Mirror of `DerivWFP`.  `arity0` routes to `AllTermsGoodA`; `core`/`cut*` cores
route to `AllTermsGood`; the three closed leaves carry their eval side-data
verbatim. -/
def AllTermsGoodP {cb : Term 2 .stab} {fuel : Nat} {A : SFormula 0}
    (D : PureFamilyDeriv cb fuel A) (E : PartialStabilizer) : Prop :=
  match D with
  | .arity0 Da => AllTermsGoodA Da Env.empty E
  | .core Dcore => AllTermsGood Dcore cb fuel Env.empty E
  | .recUnfold n d k =>
      ∃ sa,
        Term.eval cb fuel (.recCall (.natLit d) (.natLit k)) Env.empty = some sa ∧
          ∀ q, q < n → ∃ p, sa q = some p
  | .gridRowStripRange _ => True
  | .gridColStripRange _ => True
  | .foldTelescope cut _outerBound _N =>
      ∃ g : Nat → Nat → Pauli,
        (∀ (row iv : Nat),
          Term.eval cb fuel (cut telFoldVar) (Env.cons iv (Env.cons row Env.empty)) =
            some (fun q => some (g iv q))) ∧
        (∀ (row iv : Nat),
          Term.eval cb fuel (cut (.add telFoldVar (.natLit 1)))
              (Env.cons iv (Env.cons row Env.empty)) =
            some (fun q => some (g (iv + 1) q))) ∧
        (∀ (row : Nat),
          Term.eval cb fuel (cut (.natLit 0)) (Env.cons row Env.empty) =
            some (fun q => some (g 0 q))) ∧
        (∀ (row : Nat),
          Term.eval cb fuel (cut telRowVar) (Env.cons row Env.empty) =
            some (fun q => some (g row q)))
  | .foldDisjoint lhs body outerBound width N =>
      ∃ (g : Nat → Nat → Nat → Pauli) (t : Nat → Nat → Pauli),
        (∀ (row iv : Nat),
          STerm.eval cb fuel body (Env.cons iv (Env.cons row Env.empty)) E =
            some (fun q => some (g row iv q))) ∧
        (∀ (row : Nat),
          STerm.eval cb fuel lhs (Env.cons row Env.empty) E =
            some (fun q => some (t row q))) ∧
        (∀ (row : Nat), row < outerBound → ∀ (q : Nat), q < N →
          partialStabilizerFold width (fun i => fun q => some (g row i q)) q =
            some (t row q))
  | .cut1 Dcore hA =>
      AllTermsGood Dcore cb fuel Env.empty E ∧ AllTermsGoodP hA E
  | .cut2 Dcore hA hB =>
      AllTermsGood Dcore cb fuel Env.empty E ∧ AllTermsGoodP hA E ∧ AllTermsGoodP hB E
  | .cut3 Dcore hA hB hC =>
      AllTermsGood Dcore cb fuel Env.empty E ∧
        AllTermsGoodP hA E ∧ AllTermsGoodP hB E ∧ AllTermsGoodP hC E
  | .cut4 Dcore hA hB hC hD =>
      AllTermsGood Dcore cb fuel Env.empty E ∧
        AllTermsGoodP hA E ∧ AllTermsGoodP hB E ∧ AllTermsGoodP hC E ∧ AllTermsGoodP hD E

theorem allTermsGoodP_derivWFP {cb : Term 2 .stab} {fuel : Nat} {A : SFormula 0}
    (D : PureFamilyDeriv cb fuel A) (E : PartialStabilizer)
    (hG : AllTermsGoodP D E) :
    DerivWFP D E := by
  induction D with
  | arity0 Da => exact allTermsGoodA_derivWFA Da Env.empty E hG
  | core Dcore => exact allTermsGood_derivWF Dcore cb fuel Env.empty E hG
  | recUnfold n d k => exact hG
  | gridRowStripRange dist => exact True.intro
  | gridColStripRange dist => exact True.intro
  | foldTelescope cut outerBound N => exact hG
  | foldDisjoint lhs body outerBound width N => exact hG
  | cut1 Dcore hA ihA =>
      exact ⟨allTermsGood_derivWF Dcore cb fuel Env.empty E hG.1, ihA hG.2⟩
  | cut2 Dcore hA hB ihA ihB =>
      exact ⟨allTermsGood_derivWF Dcore cb fuel Env.empty E hG.1, ihA hG.2.1, ihB hG.2.2⟩
  | cut3 Dcore hA hB hC ihA ihB ihC =>
      exact ⟨allTermsGood_derivWF Dcore cb fuel Env.empty E hG.1,
        ihA hG.2.1, ihB hG.2.2.1, ihC hG.2.2.2⟩
  | cut4 Dcore hA hB hC hD ihA ihB ihC ihD =>
      exact ⟨allTermsGood_derivWF Dcore cb fuel Env.empty E hG.1,
        ihA hG.2.1, ihB hG.2.2.1, ihC hG.2.2.2.1, ihD hG.2.2.2.2⟩

/-- End-to-end: `AllTermsGoodP` discharges the top-level `DefinedObligations`
through the generic engine `pfd_defined`.  This is the composed bridge a caller
uses once `AllTermsGoodP (codeLevel D)` is established. -/
theorem allTermsGoodP_defined {cb : Term 2 .stab} {fuel : Nat} {A : SFormula 0}
    (D : PureFamilyDeriv cb fuel A) (E : PartialStabilizer)
    (hG : AllTermsGoodP D E) :
    D.DefinedObligations E :=
  pfd_defined D E (allTermsGoodP_derivWFP D E hG)

/-! ## Non-vacuity sanity checks

`AllTermsGood*` is a genuine (satisfiable) invariant: we run the already-built
surface telescoping witness through the new bridge, recovering the real
`DefinedObligations`. -/

/-- The row telescoping leaf satisfies `AllTermsGoodP` (its clause is its proved
    `DefinedObligations`). -/
theorem rowCutTelescoping_AllTermsGoodP (D : OddSurfaceDistance) (E : PartialStabilizer) :
    AllTermsGoodP (rowCutTelescopingPure D) E :=
  rowCutTelescopingPure_defined D E

/-- Running the telescoping witness through the new term-totality bridge recovers
    the real `DefinedObligations` — concrete proof `AllTermsGoodP` is non-vacuous. -/
theorem rowCutTelescoping_defined_via_allTermsGood
    (D : OddSurfaceDistance) (E : PartialStabilizer) :
    (rowCutTelescopingPure D).DefinedObligations E :=
  allTermsGoodP_defined (rowCutTelescopingPure D) E (rowCutTelescoping_AllTermsGoodP D E)

/-- The `core` path is live through the new bridge: a `core` of `Deriv [] .top`. -/
theorem core_top_defined_via_allTermsGood
    (cb : Term 2 .stab) (fuel : Nat) (E : PartialStabilizer) :
    (PureFamilyDeriv.core (cb := cb) (fuel := fuel) (SFormula.Deriv.top)).DefinedObligations E :=
  allTermsGoodP_defined _ E True.intro

#print axioms allTermsGood_derivWF
#print axioms allTermsGoodA_derivWFA
#print axioms allTermsGoodP_derivWFP
#print axioms allTermsGoodP_defined
#print axioms rowCutTelescoping_defined_via_allTermsGood
#print axioms core_top_defined_via_allTermsGood

end QHL.CodeLang.Surface.Verify
