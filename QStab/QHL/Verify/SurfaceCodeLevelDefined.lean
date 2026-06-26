import QStab.QHL.Verify.SurfaceGenericDefined
import QStab.QHL.Verify.SurfaceAllTermsGood
import QStab.QHL.Verify.SurfaceCodeLevelPure

/-!
# `DerivWF*` companions for the code-level tree

This file builds the `DerivWF` / `DerivWFA` / `DerivWFP` well-formedness witnesses
required to wire the prover's `codeLevelDefined` field through the generic engine
`pfd_defined` (in `SurfaceGenericDefined.lean`).

The approach is *per-building-block*: generic combinator `_wf` lemmas (proved
once, reusable) reduce a node's `DerivWF*` to the children's, and the leaf
libraries (`SurfaceFormulaDefined`) discharge the `FormulaDefined` obligations.
-/

namespace QHL.CodeLang.Surface.Verify

open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

/-! ## Generic combinator `_wf` lemmas (reusable, prove once)

These reduce a node's `DerivWF*` to its children's `DerivWF*` plus the node's own
leaf obligation.  Each is `rfl`-transparent: `DerivWF*` is defined by the same
structural recursion as `DefinedObligations`, so the combinator's clause unfolds
definitionally to the conjunction of the children's clauses. -/

/-- `DerivWF (andIntro left right)` from both children. -/
theorem derivWF_andIntro {arity : Nat} {Γ : List (SFormula arity)} {A B : SFormula arity}
    {left : SFormula.Deriv Γ A} {right : SFormula.Deriv Γ B}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (hl : DerivWF left cb fuel rho E) (hr : DerivWF right cb fuel rho E) :
    DerivWF (left.andIntro right) cb fuel rho E := ⟨hl, hr⟩

/-- `DerivWF (hyp h)` is trivially `True`. -/
theorem derivWF_hyp {arity : Nat} {Γ : List (SFormula arity)} {A : SFormula arity}
    (h : A ∈ Γ) {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity}
    {E : PartialStabilizer} :
    DerivWF (SFormula.Deriv.hyp h) cb fuel rho E := True.intro

/-- The `andIntro (hyp _) (hyp _)` core that appears in every `cut*` combiner is
trivially well-formed. -/
theorem derivWF_andIntro_hyp_hyp {arity : Nat} {Γ : List (SFormula arity)}
    {A B : SFormula arity} (hA : A ∈ Γ) (hB : B ∈ Γ)
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer} :
    DerivWF ((SFormula.Deriv.hyp hA).andIntro (SFormula.Deriv.hyp hB)) cb fuel rho E :=
  ⟨True.intro, True.intro⟩

/-- `DerivWF` transports across a formula-equality cast of the derivation.  This
punches through the `Eq.mpr`/`▸` casts that `simpa using …` inserts into the
prover-side trees. -/
theorem derivWF_cast {arity : Nat} {Γ : List (SFormula arity)} {A A' : SFormula arity}
    (hA : A = A') (d : SFormula.Deriv Γ A)
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (h : DerivWF d cb fuel rho E) :
    DerivWF (hA ▸ d) cb fuel rho E := by
  subst hA; exact h

/-- `DerivWF` transports across a *type-level* `cast` of the derivation, given the
type equality arises from a context+formula equality.  This punches through the
`cast _ d` form `simp [eq_mpr_eq_cast]` exposes from `simpa using d`. -/
theorem derivWF_cast_type {arity : Nat} {Γ Γ' : List (SFormula arity)}
    {A A' : SFormula arity}
    (hΓ : Γ = Γ') (hA : A = A') (d : SFormula.Deriv Γ A)
    (htype : SFormula.Deriv Γ A = SFormula.Deriv Γ' A')
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (h : DerivWF d cb fuel rho E) :
    DerivWF (cast htype d) cb fuel rho E := by
  subst hΓ; subst hA
  rw [cast_eq]
  exact h

/-- `DerivWF (impIntro child)` from the antecedent's `FormulaDefined` and the
child's `DerivWF`. -/
theorem derivWF_impIntro {arity : Nat} {Γ : List (SFormula arity)}
    {A B : SFormula arity} {child : SFormula.Deriv (A :: Γ) B}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (hA : SFormula.Deriv.FormulaDefined cb fuel rho E A)
    (hchild : DerivWF child cb fuel rho E) :
    DerivWF (SFormula.Deriv.impIntro child) cb fuel rho E := ⟨hA, hchild⟩

/-- `DerivWF (notElim positive negative)` from both children. -/
theorem derivWF_notElim {arity : Nat} {Γ : List (SFormula arity)}
    {A : SFormula arity} {positive : SFormula.Deriv Γ A}
    {negative : SFormula.Deriv Γ (.not A)}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (hp : DerivWF positive cb fuel rho E) (hn : DerivWF negative cb fuel rho E) :
    DerivWF (SFormula.Deriv.notElim positive negative) cb fuel rho E := ⟨hp, hn⟩

/-- `DerivWF (botElim child)` from the child. -/
theorem derivWF_botElim {arity : Nat} {Γ : List (SFormula arity)}
    {A : SFormula arity} {child : SFormula.Deriv Γ .bot}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (hchild : DerivWF child cb fuel rho E) :
    DerivWF (SFormula.Deriv.botElim (A := A) child) cb fuel rho E := hchild

/-- `DerivWF (boolCases b C left right)` from the bool's evaluation and both
branch children. -/
theorem derivWF_boolCases {arity : Nat} {Γ : List (SFormula arity)}
    (b : STerm arity .bool) (C : SFormula arity)
    {left : SFormula.Deriv (.eqBool b (SC.b true) :: Γ) C}
    {right : SFormula.Deriv (.eqBool b (SC.b false) :: Γ) C}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (hb : ∃ bv, b.eval cb fuel rho E = some bv)
    (hl : DerivWF left cb fuel rho E) (hr : DerivWF right cb fuel rho E) :
    DerivWF (SFormula.Deriv.boolCases b C left right) cb fuel rho E := ⟨hb, hl, hr⟩

/-- `DerivWF (applyNatSubstitutionBeta x A hx child)` from the child. -/
theorem derivWF_applyNatSubstitutionBeta {arity : Nat} {Γ : List (SFormula arity)}
    {x : Term arity .nat} {A : SFormula (arity + 1)} {hx : SFormula.PureNatTerm x}
    {child : SFormula.Deriv Γ (A.instantiateTopNat x)}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (hchild : DerivWF child cb fuel rho E) :
    DerivWF (SFormula.Deriv.applyNatSubstitutionBeta x A hx child) cb fuel rho E :=
  hchild

/-- `DerivWF (applyNatBoundNatBeta A child)` from the child. -/
theorem derivWF_applyNatBoundNatBeta {base : Nat} {Γ : List (SFormula (base + 1))}
    (A : SFormula (base + 1))
    {child : SFormula.Deriv Γ (.applyNat (SFormula.boundNat (arity := base)) (A.lift 1))}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env (base + 1)} {E : PartialStabilizer}
    (hchild : DerivWF child cb fuel rho E) :
    DerivWF (SFormula.Deriv.applyNatBoundNatBeta A child) cb fuel rho E := hchild

/-- `DerivWF (divLtOfLtSquare dist q child)` from the child. -/
theorem derivWF_divLtOfLtSquare {arity : Nat} {Γ : List (SFormula arity)}
    (dist : Nat) (q : Term arity .nat)
    {child : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed q) (SC.n (dist * dist)))}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (hchild : DerivWF child cb fuel rho E) :
    DerivWF (SFormula.Deriv.divLtOfLtSquare dist q child) cb fuel rho E := hchild

/-- `DerivWF (modLtOfLtSquare dist q child)` from the child. -/
theorem derivWF_modLtOfLtSquare {arity : Nat} {Γ : List (SFormula arity)}
    (dist : Nat) (q : Term arity .nat)
    {child : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed q) (SC.n (dist * dist)))}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (hchild : DerivWF child cb fuel rho E) :
    DerivWF (SFormula.Deriv.modLtOfLtSquare dist q child) cb fuel rho E := hchild

/-- `DerivWF (gridIdxLeftDivModEqOfCol dist col q qLt colEq)` from both children. -/
theorem derivWF_gridIdxLeftDivModEqOfCol {arity : Nat} {Γ : List (SFormula arity)}
    (dist : Nat) (col q : Term arity .nat)
    {qLt : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed q) (SC.n (dist * dist)))}
    {colEq : SFormula.Deriv Γ (.eqBool
      (SC.closed (.eqNat (NatArithmetic.colOf q (.natLit dist)) col)) (SC.b true))}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (hq : DerivWF qLt cb fuel rho E) (hc : DerivWF colEq cb fuel rho E) :
    DerivWF (SFormula.Deriv.gridIdxLeftDivModEqOfCol dist col q qLt colEq) cb fuel rho E :=
  ⟨hq, hc⟩

/-- `DerivWF (gridIdxLeftDivModEqOfRow dist row q qLt rowEq)` from both children. -/
theorem derivWF_gridIdxLeftDivModEqOfRow {arity : Nat} {Γ : List (SFormula arity)}
    (dist : Nat) (row q : Term arity .nat)
    {qLt : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed q) (SC.n (dist * dist)))}
    {rowEq : SFormula.Deriv Γ (.eqBool
      (SC.closed (.eqNat (NatArithmetic.rowOf q (.natLit dist)) row)) (SC.b true))}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (hq : DerivWF qLt cb fuel rho E) (hr : DerivWF rowEq cb fuel rho E) :
    DerivWF (SFormula.Deriv.gridIdxLeftDivModEqOfRow dist row q qLt rowEq) cb fuel rho E :=
  ⟨hq, hr⟩

/-- `DerivWF (gridIdxLeftLtSquare dist row col rowLt colLt)` from both children. -/
theorem derivWF_gridIdxLeftLtSquare {arity : Nat} {Γ : List (SFormula arity)}
    (dist : Nat) (row col : Term arity .nat)
    {rowLt : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed row) (SC.n dist))}
    {colLt : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed col) (SC.n dist))}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (hr : DerivWF rowLt cb fuel rho E) (hc : DerivWF colLt cb fuel rho E) :
    DerivWF (SFormula.Deriv.gridIdxLeftLtSquare dist row col rowLt colLt) cb fuel rho E :=
  ⟨hr, hc⟩

/-- `DerivWF (existsNatLtIntroTerm n A witness ltD bodyD)` from both children plus
the per-`x` `FormulaDefined` range. -/
theorem derivWF_existsNatLtIntroTerm {arity : Nat} {Γ : List (SFormula arity)}
    (n : STerm arity .nat) (A : SFormula (arity + 1)) (witness : STerm arity .nat)
    {ltD : SFormula.Deriv Γ (SFormula.witnessLt witness n)}
    {bodyD : SFormula.Deriv Γ (.applyNat witness A)}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (hlt : DerivWF ltD cb fuel rho E) (hbody : DerivWF bodyD cb fuel rho E)
    (hrange : ∃ bound, n.eval cb fuel rho E = some bound ∧
      ∀ x, x < bound → SFormula.Deriv.FormulaDefined cb fuel (Env.cons x rho) E A) :
    DerivWF (SFormula.Deriv.existsNatLtIntroTerm n A witness ltD bodyD) cb fuel rho E :=
  ⟨hlt, hbody, hrange⟩

/-- `DerivWF (allNatLtIntroBounded n A child)` from the range eval, per-`x` child
`DerivWF`, and base `ContextHolds`. -/
theorem derivWF_allNatLtIntroBounded {arity : Nat} {Γ : List (SFormula arity)}
    (n : STerm arity .nat) (A : SFormula (arity + 1))
    {child : SFormula.Deriv (SFormula.boundNatLt n :: Γ.map (fun G => G.weaken)) A}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (hwf : ∃ bound, n.eval cb fuel rho E = some bound ∧
      ∀ x, x < bound →
        DerivWF child cb fuel (Env.cons x rho) E ∧
          SFormula.ContextHolds cb fuel rho E Γ) :
    DerivWF (SFormula.Deriv.allNatLtIntroBounded n A child) cb fuel rho E := hwf

/-- `DerivWF (stabAtClosedIteLamEqElse cond thenP elseP q hq child)` from the child
plus the closed `eqPauli` `FormulaDefined` (both sides total). -/
theorem derivWF_stabAtClosedIteLamEqElse {arity : Nat} {Γ : List (SFormula arity)}
    (cond : Term (arity + 1) .bool) (thenP elseP : Term (arity + 1) .pauli)
    (q : Term arity .nat) (hq : SFormula.PureNatTerm q)
    {child : SFormula.Deriv Γ
      (.eqBool (SC.closed (Term.instantiateTopNat q cond)) (SC.b false))}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (hchild : DerivWF child cb fuel rho E)
    (hLhs : ∃ v, (STerm.stabAt (SC.closed (.stabLam (.ite cond thenP elseP)))
      (SC.closed q)).eval cb fuel rho E = some v)
    (hRhs : ∃ v, Term.eval cb fuel (Term.instantiateTopNat q elseP) rho = some v) :
    DerivWF (SFormula.Deriv.stabAtClosedIteLamEqElse cond thenP elseP q hq child)
      cb fuel rho E :=
  ⟨hchild, formulaDefined_eqPauli hLhs (sterm_eval_closed hRhs)⟩

/-- `DerivWF (stabAtClosedIteLamEqThen cond thenP elseP q hq child)` from the child
plus the closed `eqPauli` `FormulaDefined`. -/
theorem derivWF_stabAtClosedIteLamEqThen {arity : Nat} {Γ : List (SFormula arity)}
    (cond : Term (arity + 1) .bool) (thenP elseP : Term (arity + 1) .pauli)
    (q : Term arity .nat) (hq : SFormula.PureNatTerm q)
    {child : SFormula.Deriv Γ
      (.eqBool (SC.closed (Term.instantiateTopNat q cond)) (SC.b true))}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (hchild : DerivWF child cb fuel rho E)
    (hLhs : ∃ v, (STerm.stabAt (SC.closed (.stabLam (.ite cond thenP elseP)))
      (SC.closed q)).eval cb fuel rho E = some v)
    (hRhs : ∃ v, Term.eval cb fuel (Term.instantiateTopNat q thenP) rho = some v) :
    DerivWF (SFormula.Deriv.stabAtClosedIteLamEqThen cond thenP elseP q hq child)
      cb fuel rho E :=
  ⟨hchild, formulaDefined_eqPauli hLhs (sterm_eval_closed hRhs)⟩

/-- `DerivWF (finiteSurjectiveWeightLower n Eterm limit k rowOf cover lt)` from the
two children plus the `weightLe` `FormulaDefined`. -/
theorem derivWF_finiteSurjectiveWeightLower {arity : Nat} {Γ : List (SFormula arity)}
    (n : STerm arity .nat) (Eterm : STerm arity .stab) (limit : STerm arity .nat)
    (k : STerm arity .nat) (rowOf : STerm (arity + 1) .nat)
    {cover : SFormula.Deriv Γ (SFormula.supportSurjectiveF k n Eterm rowOf)}
    {lt : SFormula.Deriv Γ (SFormula.witnessLt limit k)}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (hcover : DerivWF cover cb fuel rho E) (hlt : DerivWF lt cb fuel rho E)
    (hwLe : SFormula.Deriv.FormulaDefined cb fuel rho E (.weightLe n Eterm limit)) :
    DerivWF (SFormula.Deriv.finiteSurjectiveWeightLower n Eterm limit k rowOf cover lt)
      cb fuel rho E :=
  ⟨hcover, hlt, hwLe⟩

/-- `DerivWF (noncommutesOfSingleAnti n A B q0 ltD antiD restD)` from all three
children. -/
theorem derivWF_noncommutesOfSingleAnti {arity : Nat} {Γ : List (SFormula arity)}
    (n : STerm arity .nat) (A B : STerm arity .stab) (q0 : STerm arity .nat)
    {ltD : SFormula.Deriv Γ (SFormula.witnessLt q0 n)}
    {antiD : SFormula.Deriv Γ (.eqBool (.anticommutes (.stabAt A q0) (.stabAt B q0)) (SC.b true))}
    {restD : SFormula.Deriv Γ (.allNatLt n
      (.imp (.not (.eqNat SFormula.boundNat q0.weaken))
        (SFormula.localCommutesAt A.weaken B.weaken SFormula.boundNat)))}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (hlt : DerivWF ltD cb fuel rho E) (hanti : DerivWF antiD cb fuel rho E)
    (hrest : DerivWF restD cb fuel rho E) :
    DerivWF (SFormula.Deriv.noncommutesOfSingleAnti n A B q0 ltD antiD restD)
      cb fuel rho E :=
  ⟨hlt, hanti, hrest⟩

/-- `DerivWF (anticommutesTransport a a' b b' rhs eqAD eqBD antiD)` from the three
children plus the `.eqBool (.anticommutes a b) rhs` `FormulaDefined`. -/
theorem derivWF_anticommutesTransport {arity : Nat} {Γ : List (SFormula arity)}
    (a a' b b' : STerm arity .pauli) (rhs : STerm arity .bool)
    {eqAD : SFormula.Deriv Γ (.eqPauli a a')} {eqBD : SFormula.Deriv Γ (.eqPauli b b')}
    {antiD : SFormula.Deriv Γ (.eqBool (.anticommutes a' b') rhs)}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (hA : DerivWF eqAD cb fuel rho E) (hB : DerivWF eqBD cb fuel rho E)
    (hAnti : DerivWF antiD cb fuel rho E)
    (hfd : SFormula.Deriv.FormulaDefined cb fuel rho E (.eqBool (.anticommutes a a') rhs)) :
    DerivWF (SFormula.Deriv.anticommutesTransport a a' b b' rhs eqAD eqBD antiD)
      cb fuel rho E :=
  ⟨hA, hB, hAnti, hfd⟩

/-- `DerivWF (localCommutesOfLeftI A B q child)` from the child plus the
`localCommutesAt` `FormulaDefined`. -/
theorem derivWF_localCommutesOfLeftI {arity : Nat} {Γ : List (SFormula arity)}
    (A B : STerm arity .stab) (q : STerm arity .nat)
    {child : SFormula.Deriv Γ (.eqPauli (.stabAt A q) (SC.p Pauli.I))}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (hchild : DerivWF child cb fuel rho E)
    (hfd : SFormula.Deriv.FormulaDefined cb fuel rho E (SFormula.localCommutesAt A B q)) :
    DerivWF (SFormula.Deriv.localCommutesOfLeftI A B q child) cb fuel rho E :=
  ⟨hchild, hfd⟩

/-- `DerivWF (localCommutesOfRightI A B q child)` from the child plus the
`localCommutesAt` `FormulaDefined`. -/
theorem derivWF_localCommutesOfRightI {arity : Nat} {Γ : List (SFormula arity)}
    (A B : STerm arity .stab) (q : STerm arity .nat)
    {child : SFormula.Deriv Γ (.eqPauli (.stabAt B q) (SC.p Pauli.I))}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (hchild : DerivWF child cb fuel rho E)
    (hfd : SFormula.Deriv.FormulaDefined cb fuel rho E (SFormula.localCommutesAt A B q)) :
    DerivWF (SFormula.Deriv.localCommutesOfRightI A B q child) cb fuel rho E :=
  ⟨hchild, hfd⟩

/-- `DerivWF (mp implication antecedent)` from both children. -/
theorem derivWF_mp {arity : Nat} {Γ : List (SFormula arity)} {A B : SFormula arity}
    {implication : SFormula.Deriv Γ (.imp A B)} {antecedent : SFormula.Deriv Γ A}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (hi : DerivWF implication cb fuel rho E) (ha : DerivWF antecedent cb fuel rho E) :
    DerivWF (SFormula.Deriv.mp implication antecedent) cb fuel rho E := ⟨hi, ha⟩

/-- `DerivWF (allNatLtElim n A witness forallD ltD)` from both children. -/
theorem derivWF_allNatLtElim {arity : Nat} {Γ : List (SFormula arity)}
    (n : STerm arity .nat) (A : SFormula (arity + 1)) (witness : STerm arity .nat)
    {forallD : SFormula.Deriv Γ (.allNatLt n A)}
    {ltD : SFormula.Deriv Γ (SFormula.witnessLt witness n)}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (hf : DerivWF forallD cb fuel rho E) (hlt : DerivWF ltD cb fuel rho E) :
    DerivWF (SFormula.Deriv.allNatLtElim n A witness forallD ltD) cb fuel rho E :=
  ⟨hf, hlt⟩

/-- `DerivWF (eqNatBoolTrue a b child)` from the child. -/
theorem derivWF_eqNatBoolTrue {arity : Nat} {Γ : List (SFormula arity)}
    (a b : Term arity .nat)
    {child : SFormula.Deriv Γ (.eqNat (SC.closed a) (SC.closed b))}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (hchild : DerivWF child cb fuel rho E) :
    DerivWF (SFormula.Deriv.eqNatBoolTrue a b child) cb fuel rho E := hchild

/-- `DerivWF (gridIdxLeftDivEq dist row col rowLt colLt)` from both children. -/
theorem derivWF_gridIdxLeftDivEq {arity : Nat} {Γ : List (SFormula arity)}
    (dist : Nat) (row col : Term arity .nat)
    {rowLt : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed row) (SC.n dist))}
    {colLt : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed col) (SC.n dist))}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (hr : DerivWF rowLt cb fuel rho E) (hc : DerivWF colLt cb fuel rho E) :
    DerivWF (SFormula.Deriv.gridIdxLeftDivEq dist row col rowLt colLt) cb fuel rho E :=
  ⟨hr, hc⟩

/-- `DerivWF (gridIdxLeftModEq dist row col rowLt colLt)` from both children. -/
theorem derivWF_gridIdxLeftModEq {arity : Nat} {Γ : List (SFormula arity)}
    (dist : Nat) (row col : Term arity .nat)
    {rowLt : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed row) (SC.n dist))}
    {colLt : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed col) (SC.n dist))}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (hr : DerivWF rowLt cb fuel rho E) (hc : DerivWF colLt cb fuel rho E) :
    DerivWF (SFormula.Deriv.gridIdxLeftModEq dist row col rowLt colLt) cb fuel rho E :=
  ⟨hr, hc⟩

/-- `DerivWF (pauliAnticommutesLit p q)` is trivially `True`. -/
theorem derivWF_pauliAnticommutesLit {arity : Nat} {Γ : List (SFormula arity)}
    (p q : Pauli) {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity}
    {E : PartialStabilizer} :
    DerivWF (SFormula.Deriv.pauliAnticommutesLit (Γ := Γ) (arity := arity) p q)
      cb fuel rho E := True.intro

/-- `DerivWFA (PureFamilyDerivA.arithBool A hfrag hvalid)` is trivially `True`. -/
theorem derivWFA_arithBool {cb : Term 2 .stab} {fuel : Nat} {A : SFormula 0}
    (hfrag : arithBoolFragment A = true)
    (hvalid : ∀ (rho : Env 0) (E : PartialStabilizer),
      A.eval cb fuel rho E = some true)
    {rho : Env 0} {E : PartialStabilizer} :
    DerivWFA (PureFamilyDerivA.arithBool A hfrag hvalid) rho E := True.intro

/-- `DerivWFA (PureFamilyDerivA.core Dcore)` from `DerivWF Dcore`. -/
theorem derivWFA_core (cb : Term 2 .stab) (fuel : Nat) {arity : Nat} {A : SFormula arity}
    (Dcore : SFormula.Deriv [] A) {rho : Env arity} {E : PartialStabilizer}
    (h : DerivWF Dcore cb fuel rho E) :
    DerivWFA (cb := cb) (fuel := fuel) (PureFamilyDerivA.core Dcore) rho E := h

/-- `DerivWFA (cut1 Dcore hA)` from the core's `DerivWF` and `hA`'s `DerivWFA`. -/
theorem derivWFA_cut1 {cb : Term 2 .stab} {fuel arity : Nat} {A B : SFormula arity}
    {Dcore : SFormula.Deriv [B] A} {hA : PureFamilyDerivA cb fuel B}
    {rho : Env arity} {E : PartialStabilizer}
    (hc : DerivWF Dcore cb fuel rho E) (ha : DerivWFA hA rho E) :
    DerivWFA (PureFamilyDerivA.cut1 Dcore hA) rho E := ⟨hc, ha⟩

/-- `DerivWFA (cut2 Dcore hA hB)` from the core's `DerivWF` and both `DerivWFA`. -/
theorem derivWFA_cut2 {cb : Term 2 .stab} {fuel arity : Nat} {A B C : SFormula arity}
    {Dcore : SFormula.Deriv [B, C] A} {hA : PureFamilyDerivA cb fuel B}
    {hB : PureFamilyDerivA cb fuel C} {rho : Env arity} {E : PartialStabilizer}
    (hc : DerivWF Dcore cb fuel rho E) (ha : DerivWFA hA rho E)
    (hb : DerivWFA hB rho E) :
    DerivWFA (PureFamilyDerivA.cut2 Dcore hA hB) rho E := ⟨hc, ha, hb⟩

/-- `DerivWFA (weightLeBySupport n Eterm w cover child)` from the eval side-data
plus the child's `DerivWFA`. -/
theorem derivWFA_weightLeBySupport {cb : Term 2 .stab} {fuel arity : Nat}
    {n : STerm arity .nat} {Eterm : STerm arity .stab} {w : STerm arity .nat}
    {cover : STerm (arity + 1) .nat} {child : PureFamilyDerivA cb fuel _}
    {rho : Env arity} {E : PartialStabilizer} {nv : Nat} {Ev : PartialStabilizer}
    {wv : Nat}
    (hn : n.eval cb fuel rho E = some nv)
    (hE : Eterm.eval cb fuel rho E = some Ev)
    (hw : w.eval cb fuel rho E = some wv)
    (htotal : StabTotalUpTo nv Ev)
    (hchild : DerivWFA child rho E) :
    DerivWFA (PureFamilyDerivA.weightLeBySupport n Eterm w cover child) rho E :=
  ⟨nv, Ev, wv, hn, hE, hw, weightUpTo_total htotal, hchild⟩

/-- `DerivWFP (PureFamilyDeriv.arity0 Da)` from `DerivWFA Da`. -/
theorem derivWFP_arity0 {cb : Term 2 .stab} {fuel : Nat} {A : SFormula 0}
    {Da : PureFamilyDerivA cb fuel A} {E : PartialStabilizer}
    (h : DerivWFA Da Env.empty E) :
    DerivWFP (PureFamilyDeriv.arity0 Da) E := h

/-- `SC.n x` evaluates to `some x`. -/
theorem scn_eval {arity : Nat} (cb : Term 2 .stab) (fuel : Nat) (x : Nat)
    (rho : Env arity) (E : PartialStabilizer) :
    (SC.n x : STerm arity .nat).eval cb fuel rho E = some x := by
  simp [SC.n, STerm.eval, Term.eval]

/-! ## Totality of the closed logical operators

`logicalX dist` / `logicalZ dist` are `stabLam (ite … (pauliLit _) (pauliLit I))`,
hence evaluate to an everywhere-`some` partial stabilizer, total up to any bound. -/

/-- The `stabLam (ite (mod-guard) X I)` body of `logicalX`, at any arity/env, is a
total everywhere-`some` partial stabilizer.  (Stated over the raw `stabLam` term so
it applies to the closed `logicalX dist` and its arity-shifted copies inside the
derivation trees.) -/
theorem logicalXBody_eval_total {arity : Nat} (cb : Term 2 .stab) (fuel : Nat)
    (dist : Nat) (rho : Env arity) :
    ∃ g : Nat → Pauli,
      Term.eval cb (fuel + 1)
        (.stabLam (.ite (.eqNat (.mod Formula.qVar (.natLit dist)) (.natLit 0))
          (.pauliLit Pauli.X) (.pauliLit Pauli.I))) rho
        = some (fun q => some (g q)) := by
  refine ⟨fun q => if q % dist = 0 then Pauli.X else Pauli.I, ?_⟩
  simp only [Term.eval, Formula.qVar, Env.cons]
  refine congrArg some (funext fun q => ?_)
  by_cases h : q % dist = 0 <;>
    simp [h, bind, Option.bind]

theorem logicalZBody_eval_total {arity : Nat} (cb : Term 2 .stab) (fuel : Nat)
    (dist : Nat) (rho : Env arity) :
    ∃ g : Nat → Pauli,
      Term.eval cb (fuel + 1)
        (.stabLam (.ite (.eqNat (.div Formula.qVar (.natLit dist)) (.natLit 0))
          (.pauliLit Pauli.Z) (.pauliLit Pauli.I))) rho
        = some (fun q => some (g q)) := by
  refine ⟨fun q => if q / dist = 0 then Pauli.Z else Pauli.I, ?_⟩
  simp only [Term.eval, Formula.qVar, Env.cons]
  refine congrArg some (funext fun q => ?_)
  by_cases h : q / dist = 0 <;>
    simp [h, bind, Option.bind]

theorem logicalX_eval_total (cb : Term 2 .stab) (fuel : Nat)
    (dist : Nat) (rho : Env 0) :
    ∃ g : Nat → Pauli,
      Term.eval cb (fuel + 1) (logicalX dist) rho = some (fun q => some (g q)) :=
  logicalXBody_eval_total cb fuel dist rho

theorem logicalZ_eval_total (cb : Term 2 .stab) (fuel : Nat)
    (dist : Nat) (rho : Env 0) :
    ∃ g : Nat → Pauli,
      Term.eval cb (fuel + 1) (logicalZ dist) rho = some (fun q => some (g q)) :=
  logicalZBody_eval_total cb fuel dist rho

/-! ## Validated leaf: `DerivWF (logicalXSupportCoveredDeriv D)`

A fully sorry-free walk of a real prover-side `SFormula.Deriv` tree, exercising
every node kind that occurs in these trees: `allNatLtIntroBounded` (binder, range
+ `ContextHolds`), `impIntro`/`boolCases` (`FormulaDefined` antecedent + bool
eval), `existsNatLtIntroTerm`/`applyNatSubstitutionBeta`, the grid leaves, and
`stabAtClosedIteLamEqElse`/`notElim`/`botElim` — *including* the `simpa`-inserted
`Eq.mpr`/`cast` casts (stripped via `derivWF_cast_type`). -/
theorem logicalXSupportCoveredDeriv_WF (D : OddSurfaceDistance) (E : PartialStabilizer) :
    DerivWF (logicalXSupportCoveredDeriv D) Surface.code.body (D.distance + 2)
      Env.empty E := by
  unfold logicalXSupportCoveredDeriv
  refine derivWF_allNatLtIntroBounded _ _ ⟨nQubits D.distance, scn_eval _ _ _ _ _, ?_⟩
  intro x hx
  refine ⟨?_, by simp [SFormula.ContextHolds]⟩
  refine derivWF_impIntro ?_ ?_
  · -- `FormulaDefined (nonIAt (closed logicalX).weaken boundNat)`
    refine formulaDefined_not (formulaDefined_eqPauli ?_ (sterm_eval_p _))
    obtain ⟨g, hg⟩ := logicalX_eval_total Surface.code.body (D.distance + 1) D.distance
      Env.empty
    refine sterm_eval_stabAt (s := (SC.closed (logicalX D.distance)).weaken)
      (sv := fun q => some (g q)) (qv := x) ?_ ?_ ⟨g x, rfl⟩
    · rw [sterm_eval_weaken_top]
      simpa [SC.closed, STerm.eval] using hg
    · simp [SFormula.boundNat, SC.closed, STerm.eval, Term.eval, Env.cons]
  · refine derivWF_boolCases _ _ ?_ ?_ ?_
    · refine ⟨decide (x % D.distance = 0), ?_⟩
      simp [SC.closed, STerm.eval, rowVar1, Formula.qVar, Term.instantiateTopNat,
        Term.instantiateNatAt, Term.eval, Env.cons, bind, Option.bind]
    · -- trueBranch: `existsNatLtIntroTerm … rowLt (applyNatSubstitutionBeta … (⋯.mpr eqGrid))`
      refine derivWF_existsNatLtIntroTerm _ _ _
        (derivWF_divLtOfLtSquare _ _ (derivWF_hyp _)) ?_ ?_
      · -- bodyD: strip the `eqGrid` cast, then `gridIdxLeftDivModEqOfCol`
        refine derivWF_applyNatSubstitutionBeta ?_
        simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
        refine derivWF_cast_type rfl ?_ _ _
          (derivWF_gridIdxLeftDivModEqOfCol _ _ _ (derivWF_hyp _) ?_)
        · simp [SFormula.instantiateTopNat, SFormula.instantiateNatAt, STerm.instantiateNatAt,
            STerm.lift, STerm.weaken, SC.closed, logicalXSupportCover,
            NatArithmetic.gridIdxLeft, NatArithmetic.rowOf, rowVar1, SFormula.boundNat,
            Term.instantiateNatAt, Term.lift, Term.weakenVar]
        · -- colZero: `id (cast ⋯ assumption)`; `id` defeq, transport the cast
          show DerivWF (cast _ SFormula.Deriv.assumption) _ _ _ _
          refine derivWF_cast_type rfl ?_ _ _ (derivWF_hyp _)
          simp [logicalXSupportGuard, rowVar1, Formula.qVar, NatArithmetic.colOf,
            Term.instantiateTopNat, Term.instantiateNatAt, Term.weaken, Term.weakenVar,
            SC.closed]
      · -- range: `(weaken (SC.n dist)).eval = some dist ∧ FormulaDefined (eqNat …)`
        refine ⟨D.distance, by rw [sterm_eval_weaken_top]; exact scn_eval _ _ _ _ _,
          fun y hy => ?_⟩
        refine formulaDefined_eqNat ?_ ?_
        · -- `(lift 1 cover).eval` total — closed cover term, value `dist * y`
          exact ⟨D.distance * y + 0, by simp [logicalXSupportCover, SC.closed, STerm.lift,
            STerm.eval, Term.lift, NatArithmetic.gridIdxLeft, rowVar1, Term.eval,
            Term.weakenVar, Env.cons, bind, Option.bind]⟩
        · rw [sterm_eval_weaken_top]
          exact ⟨x, by simp [SFormula.boundNat, SC.closed, STerm.eval, Term.eval, Env.cons]⟩
    · refine derivWF_botElim (derivWF_notElim ?_ (derivWF_hyp _))
      -- `entryI = ⋯.mpr (⋯.mp h)`, `h = stabAtClosedIteLamEqElse …`.  Strip the
      -- two `simpa`-casts via `eq_mpr_eq_cast` then transport `DerivWF` through.
      simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
      refine derivWF_cast_type rfl ?_ _ _ (derivWF_cast_type rfl ?_ _ _
        (derivWF_stabAtClosedIteLamEqElse _ _ _ _ _ (derivWF_hyp _) ?_ ?_))
      · simp [logicalX, SC.closed, SC.p, STerm.weaken, STerm.lift, SFormula.boundNat,
          Formula.qVar, Term.lift, Term.weakenVar, rowVar1, Term.instantiateTopNat,
          Term.instantiateNatAt]
      · simp [logicalX, SC.closed, SC.p, STerm.weaken, STerm.lift, SFormula.boundNat,
          Formula.qVar, Term.lift, Term.weakenVar, rowVar1, Term.instantiateTopNat,
          Term.instantiateNatAt]
      · -- LHS eval `stabAt (stabLam (ite …)) (closed rowVar1)`
        obtain ⟨g, hg⟩ := logicalXBody_eval_total (arity := 1) Surface.code.body
          (D.distance + 1) D.distance (Env.cons x Env.empty)
        refine sterm_eval_stabAt (sv := fun q => some (g q)) (qv := x) ?_ ?_ ⟨g x, rfl⟩
        · simpa [SC.closed, STerm.eval, Formula.qVar] using hg
        · simp [SC.closed, STerm.eval, rowVar1, Term.eval, Env.cons]
      · -- RHS eval `instantiateTopNat rowVar1 (pauliLit I)` = `pauliLit I`
        exact ⟨Pauli.I, by simp [rowVar1, Term.instantiateTopNat, Term.instantiateNatAt,
          Term.eval]⟩

/-! ## Validated leaf: `DerivWF (logicalXSupportSurjectiveDeriv D)`

Structurally analogous to `logicalXSupportCoveredDeriv_WF` (an `allNatLtIntroBounded`
tree with an inner `existsNatLtIntroTerm` + `applyNatSubstitutionBeta` +
`stabAtClosedIteLamEqThen` + `andIntro` and the same `simpa`-cast pattern).  The
walk reuses exactly the combinator library + `derivWF_cast_type` validated above,
adding only the trivial slot `_wf` leaves and `derivWF_weakenContext` (the
`nonIOfEqPauliLit` arm contracts `weakenContext` to `.contextWeakening`). -/
/-- `DerivWF` is invariant under `weakenContext`: it is `.contextWeakening _ child`,
whose `DerivWF` clause is definitionally the child's. -/
theorem derivWF_weakenContext {arity : Nat} {Γ : List (SFormula arity)}
    {A B : SFormula arity} (d : SFormula.Deriv Γ A)
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (h : DerivWF d cb fuel rho E) :
    DerivWF (d.weakenContext (B := B)) cb fuel rho E := h

/-- WF of `logicalXSlotInRangeDeriv`: a `gridIdxLeftLtSquare` over two trivial
`hyp`/`closedNatLt` children. -/
theorem logicalXSlotInRangeDeriv_WF (D : OddSurfaceDistance) {fuel : Nat}
    {rho : Env 1} {E : PartialStabilizer} :
    DerivWF (logicalXSlotInRangeDeriv D) Surface.code.body fuel rho E :=
  ⟨True.intro, True.intro⟩

/-- WF of `logicalXSlotRowEqDeriv`: a `gridIdxLeftDivEq` over two trivial children. -/
theorem logicalXSlotRowEqDeriv_WF (D : OddSurfaceDistance) {fuel : Nat}
    {rho : Env 1} {E : PartialStabilizer} :
    DerivWF (logicalXSlotRowEqDeriv D) Surface.code.body fuel rho E :=
  ⟨True.intro, True.intro⟩

/-- WF of `logicalXSlotColEqDeriv`: a `gridIdxLeftModEq` over two trivial children. -/
theorem logicalXSlotColEqDeriv_WF (D : OddSurfaceDistance) {fuel : Nat}
    {rho : Env 1} {E : PartialStabilizer} :
    DerivWF (logicalXSlotColEqDeriv D) Surface.code.body fuel rho E :=
  ⟨True.intro, True.intro⟩

theorem logicalXSupportSurjectiveDeriv_WF (D : OddSurfaceDistance)
    (E : PartialStabilizer) :
    DerivWF (logicalXSupportSurjectiveDeriv D) Surface.code.body (D.distance + 2)
      Env.empty E := by
  unfold logicalXSupportSurjectiveDeriv
  refine derivWF_allNatLtIntroBounded _ _ ⟨D.distance, scn_eval _ _ _ _ _, ?_⟩
  intro x hx
  refine ⟨?_, by simp [SFormula.ContextHolds]⟩
  refine derivWF_existsNatLtIntroTerm _ _ _
    (logicalXSlotInRangeDeriv_WF D) ?_ ?_
  · -- body: applyNatSubstitutionBeta over the `simpa`-cast `andIntro hNonI hRowEq`
    refine derivWF_applyNatSubstitutionBeta ?_
    simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
    refine derivWF_cast_type rfl ?_ _ _ (derivWF_cast_type rfl ?_ _ _ ?_)
    · simp [SFormula.instantiateTopNat, SFormula.instantiateNatAt,
        SFormula.nonIAt, SFormula.boundNat, STerm.instantiateTopNat, STerm.instantiateNatAt,
        STerm.weaken, STerm.lift, Term.instantiateTopNat, Term.instantiateNatAt,
        Term.weaken, Term.lift, Term.weakenVar, SC.closed, SC.n, SC.p,
        gridRowOf, logicalXSlotWitness, rowVar1, NatArithmetic.rowOf,
        NatArithmetic.gridIdxLeft, logicalX, Formula.qVar]
    · simp [SFormula.instantiateTopNat, SFormula.instantiateNatAt,
        SFormula.nonIAt, SFormula.boundNat, STerm.instantiateTopNat, STerm.instantiateNatAt,
        STerm.weaken, STerm.lift, Term.instantiateTopNat, Term.instantiateNatAt,
        Term.weaken, Term.lift, Term.weakenVar, SC.closed, SC.n, SC.p,
        gridRowOf, logicalXSlotWitness, rowVar1, NatArithmetic.rowOf,
        NatArithmetic.gridIdxLeft, logicalX, Formula.qVar]
    refine derivWF_andIntro ?_ (logicalXSlotRowEqDeriv_WF D)
    -- left: `nonIOfEqPauliLit … (casts (stabAtClosedIteLamEqThen … (cast eqNatBoolTrue)))`
    unfold nonIOfEqPauliLit pauliNeqOfEqLeft
    -- `notIntro (notElim (eqPauliTrans (eqPauliSymm hab.weakenContext) assumption)
    --                    (pauliNeqLit …).weakenContext)`
    refine ⟨?_, ⟨⟨?_, True.intro⟩, derivWF_weakenContext _ True.intro⟩⟩
    · -- `FormulaDefined (eqPauli (stabAt (logicalX).weaken witness) (SC.p I))`
      refine formulaDefined_eqPauli ?_ (sterm_eval_p _)
      obtain ⟨g, hg⟩ := logicalXBody_eval_total (arity := 1) Surface.code.body (D.distance + 1)
        D.distance (Env.cons x Env.empty)
      refine sterm_eval_stabAt (sv := fun q => some (g q))
        (qv := D.distance * x) ?_ ?_ ⟨_, rfl⟩
      · simpa [SC.closed, logicalX, STerm.weaken, STerm.lift, STerm.eval, Term.weaken,
          Term.lift, Term.weakenVar] using hg
      · simp [logicalXSlotWitness, SC.closed, STerm.eval, NatArithmetic.gridIdxLeft, rowVar1,
          Term.eval, Term.weakenVar, Env.cons, bind, Option.bind]
    · -- `DerivWF (eqPauliSymm hEntry'_cast.weakenContext)` = `DerivWF hEntry'_cast`
      refine derivWF_weakenContext _ ?_
      -- `DerivWF (cast (cast (stabAtClosedIteLamEqThen … (cast eqNatBoolTrue))))`
      refine derivWF_cast_type rfl ?_ _ _ (derivWF_cast_type rfl ?_ _ _ ?_)
      · simp [logicalX, SC.closed, SC.p, STerm.weaken, STerm.lift, SFormula.boundNat,
          Formula.qVar, Term.lift, Term.weakenVar, rowVar1, Term.instantiateTopNat,
          Term.instantiateNatAt, logicalXSlotWitness, NatArithmetic.gridIdxLeft]
      · simp [logicalX, SC.closed, SC.p, STerm.weaken, STerm.lift, SFormula.boundNat,
          Formula.qVar, Term.lift, Term.weakenVar, rowVar1, Term.instantiateTopNat,
          Term.instantiateNatAt, logicalXSlotWitness, NatArithmetic.gridIdxLeft]
      -- `stabAtClosedIteLamEqThen … child`: child = `cast (eqNatBoolTrue … colEq)`
      refine derivWF_stabAtClosedIteLamEqThen _ _ _ _ _
        (derivWF_cast_type rfl ?_ _ _ (logicalXSlotColEqDeriv_WF D)) ?_ ?_
      · simp [logicalXSlotGuard, logicalXSlotWitness, Formula.qVar, NatArithmetic.colOf,
          Term.instantiateTopNat, Term.instantiateNatAt, Term.weaken, Term.lift,
          Term.weakenVar, SC.closed, SC.b, NatArithmetic.gridIdxLeft]
      · -- LHS eval `stabAt (closed (stabLam (ite …))) (closed witness)`
        obtain ⟨g, hg⟩ := logicalXBody_eval_total (arity := 1) Surface.code.body
          (D.distance + 1) D.distance (Env.cons x Env.empty)
        refine sterm_eval_stabAt (sv := fun q => some (g q)) (qv := D.distance * x) ?_ ?_ ⟨g _, rfl⟩
        · simpa [SC.closed, logicalX, STerm.eval] using hg
        · simp [logicalXSlotWitness, SC.closed, STerm.eval, NatArithmetic.gridIdxLeft, rowVar1,
            Term.eval, Term.weakenVar, Env.cons, bind, Option.bind]
      · -- RHS eval `instantiateTopNat witness (pauliLit X)` = `pauliLit X`
        exact ⟨Pauli.X, by simp [logicalXSlotWitness, Term.instantiateTopNat,
          Term.instantiateNatAt, Term.eval]⟩
  · -- range
    refine ⟨nQubits D.distance, by rw [sterm_eval_weaken_top]; exact scn_eval _ _ _ _ _,
      fun y hy => ?_⟩
    refine formulaDefined_and ?_ ?_
    · -- `nonIAt (logicalX).weaken.weaken boundNat` = not (eqPauli (stabAt … ) (SC.p I))
      refine formulaDefined_not (formulaDefined_eqPauli ?_ (sterm_eval_p _))
      obtain ⟨g, hg⟩ := logicalXBody_eval_total (arity := 2) Surface.code.body (D.distance + 1)
        D.distance (Env.cons y (Env.cons x Env.empty))
      refine sterm_eval_stabAt (sv := fun q => some (g q)) (qv := y) ?_ ?_ ⟨g y, rfl⟩
      · simpa [SC.closed, logicalX, STerm.weaken, STerm.lift, STerm.eval, Term.weaken,
          Term.lift, Term.weakenVar] using hg
      · simp [SFormula.boundNat, SC.closed, STerm.eval, Term.eval, Env.cons]
    · -- `eqNat (lift 1 (gridRowOf)) (boundNat.weaken)`
      refine formulaDefined_eqNat ?_ ?_
      · exact ⟨y / D.distance, by simp [gridRowOf, SC.closed, STerm.lift,
          STerm.eval, Term.lift, NatArithmetic.rowOf, rowVar1, Term.eval, Term.weakenVar,
          Env.cons, bind, Option.bind]⟩
      · exact ⟨x, by simp [SFormula.boundNat, SC.closed, STerm.weaken, STerm.lift,
          STerm.eval, Term.lift, Term.weakenVar, Term.eval, Env.cons]⟩

/-! ## Validation target: `logicalXWeightExactPure`

End-to-end `DerivWFA` for one of the 6 code-level sub-trees, assembled entirely
from the combinator library + leaf dischargers.  The only residual is the single
isolated WIP leaf `logicalXSupportSurjectiveDeriv_WF`. -/

theorem logicalXWeightExactPure_WF (D : OddSurfaceDistance) (E : PartialStabilizer) :
    DerivWFA (logicalXWeightExactPure D) Env.empty E := by
  refine derivWFA_cut2 (derivWF_andIntro_hyp_hyp (by simp) (by simp)) ?_ ?_
  · unfold logicalXWeightUpperPure
    obtain ⟨g, hg⟩ := logicalX_eval_total Surface.code.body (D.distance + 1) D.distance Env.empty
    refine derivWFA_weightLeBySupport (nv := nQubits D.distance) (wv := D.distance)
      (Ev := fun q => some (g q))
      (scn_eval _ _ _ _ _) ?_ (scn_eval _ _ _ _ _) StabTotalUpTo.ofTotal
      (derivWFA_core _ _ _ ?_)
    · simpa [SC.closed, STerm.eval] using hg
    · exact logicalXSupportCoveredDeriv_WF D E
  · refine derivWFA_core _ _ _ ?_
    unfold logicalXWeightLowerDeriv
    refine derivWF_finiteSurjectiveWeightLower _ _ _ _ _ ?_ True.intro ?_
    · -- `DerivWF (logicalXSupportSurjectiveDeriv D)` — another deep `allNatLt` tree
      -- with `simpa`-casts (analogous to `logicalXSupportCoveredDeriv_WF`).  WIP.
      exact logicalXSupportSurjectiveDeriv_WF D E
    · -- `FormulaDefined (weightLe n (closed logicalX) limit)`
      obtain ⟨g, hg⟩ := logicalX_eval_total Surface.code.body (D.distance + 1)
        D.distance Env.empty
      exact formulaDefined_weightLe (nv := nQubits D.distance)
        (Av := fun q => some (g q)) (wv := D.distance - 1)
        (scn_eval _ _ _ _ _) (by simpa [SC.closed, STerm.eval] using hg)
        (scn_eval _ _ _ _ _) StabTotalUpTo.ofTotal

/-! ## Z/col transpose of the `logicalX*` definedness witnesses

These mirror the `logicalX*_WF` proofs line-for-line under the Z/col swap:
`div`↔`mod`, `rowOf`↔`colOf`, `gridRowOf`↔`gridColOf`,
`gridIdxLeftDivModEqOfCol`↔`gridIdxLeftDivModEqOfRow`,
`divLtOfLtSquare`↔`modLtOfLtSquare`, `Pauli.X`↔`Pauli.Z`,
`logicalX*`↔`logicalZ*`. -/

/-- WF of `logicalZSlotInRangeDeriv`: a `gridIdxLeftLtSquare` over two trivial
children. -/
theorem logicalZSlotInRangeDeriv_WF (D : OddSurfaceDistance) {fuel : Nat}
    {rho : Env 1} {E : PartialStabilizer} :
    DerivWF (logicalZSlotInRangeDeriv D) Surface.code.body fuel rho E :=
  ⟨True.intro, True.intro⟩

/-- WF of `logicalZSlotRowEqDeriv`: a `gridIdxLeftDivEq` over two trivial children. -/
theorem logicalZSlotRowEqDeriv_WF (D : OddSurfaceDistance) {fuel : Nat}
    {rho : Env 1} {E : PartialStabilizer} :
    DerivWF (logicalZSlotRowEqDeriv D) Surface.code.body fuel rho E :=
  ⟨True.intro, True.intro⟩

/-- WF of `logicalZSlotColEqDeriv`: a `gridIdxLeftModEq` over two trivial children. -/
theorem logicalZSlotColEqDeriv_WF (D : OddSurfaceDistance) {fuel : Nat}
    {rho : Env 1} {E : PartialStabilizer} :
    DerivWF (logicalZSlotColEqDeriv D) Surface.code.body fuel rho E :=
  ⟨True.intro, True.intro⟩

/-- Z/row transpose of `logicalXSupportCoveredDeriv_WF`. -/
theorem logicalZSupportCoveredDeriv_WF (D : OddSurfaceDistance) (E : PartialStabilizer) :
    DerivWF (logicalZSupportCoveredDeriv D) Surface.code.body (D.distance + 2)
      Env.empty E := by
  unfold logicalZSupportCoveredDeriv
  refine derivWF_allNatLtIntroBounded _ _ ⟨nQubits D.distance, scn_eval _ _ _ _ _, ?_⟩
  intro x hx
  refine ⟨?_, by simp [SFormula.ContextHolds]⟩
  refine derivWF_impIntro ?_ ?_
  · -- `FormulaDefined (nonIAt (closed logicalZ).weaken boundNat)`
    refine formulaDefined_not (formulaDefined_eqPauli ?_ (sterm_eval_p _))
    obtain ⟨g, hg⟩ := logicalZ_eval_total Surface.code.body (D.distance + 1) D.distance
      Env.empty
    refine sterm_eval_stabAt (s := (SC.closed (logicalZ D.distance)).weaken)
      (sv := fun q => some (g q)) (qv := x) ?_ ?_ ⟨g x, rfl⟩
    · rw [sterm_eval_weaken_top]
      simpa [SC.closed, STerm.eval] using hg
    · simp [SFormula.boundNat, SC.closed, STerm.eval, Term.eval, Env.cons]
  · refine derivWF_boolCases _ _ ?_ ?_ ?_
    · refine ⟨decide (x / D.distance = 0), ?_⟩
      simp [SC.closed, STerm.eval, rowVar1, Formula.qVar, Term.instantiateTopNat,
        Term.instantiateNatAt, Term.eval, Env.cons, bind, Option.bind]
    · -- trueBranch: `existsNatLtIntroTerm … colLt (applyNatSubstitutionBeta … (⋯.mpr eqGrid))`
      refine derivWF_existsNatLtIntroTerm _ _ _
        (derivWF_modLtOfLtSquare _ _ (derivWF_hyp _)) ?_ ?_
      · -- bodyD: strip the `eqGrid` cast, then `gridIdxLeftDivModEqOfRow`
        refine derivWF_applyNatSubstitutionBeta ?_
        simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
        refine derivWF_cast_type rfl ?_ _ _
          (derivWF_gridIdxLeftDivModEqOfRow _ _ _ (derivWF_hyp _) ?_)
        · simp [SFormula.instantiateTopNat, SFormula.instantiateNatAt, STerm.instantiateNatAt,
            STerm.lift, STerm.weaken, SC.closed, logicalZSupportCover,
            NatArithmetic.gridIdxLeft, NatArithmetic.colOf, rowVar1, SFormula.boundNat,
            Term.instantiateNatAt, Term.lift, Term.weakenVar]
        · -- rowZero: `id (cast ⋯ assumption)`; `id` defeq, transport the cast
          show DerivWF (cast _ SFormula.Deriv.assumption) _ _ _ _
          refine derivWF_cast_type rfl ?_ _ _ (derivWF_hyp _)
          simp [logicalZSupportGuard, rowVar1, Formula.qVar, NatArithmetic.rowOf,
            Term.instantiateTopNat, Term.instantiateNatAt, Term.weaken, Term.weakenVar,
            SC.closed]
      · -- range: `(weaken (SC.n dist)).eval = some dist ∧ FormulaDefined (eqNat …)`
        refine ⟨D.distance, by rw [sterm_eval_weaken_top]; exact scn_eval _ _ _ _ _,
          fun y hy => ?_⟩
        refine formulaDefined_eqNat ?_ ?_
        · -- `(lift 1 cover).eval` total — closed cover term, value `0 * dist + y`
          exact ⟨0 + y, by simp [logicalZSupportCover, SC.closed, STerm.lift,
            STerm.eval, Term.lift, NatArithmetic.gridIdxLeft, rowVar1, Term.eval,
            Term.weakenVar, Env.cons, bind, Option.bind]⟩
        · rw [sterm_eval_weaken_top]
          exact ⟨x, by simp [SFormula.boundNat, SC.closed, STerm.eval, Term.eval, Env.cons]⟩
    · refine derivWF_botElim (derivWF_notElim ?_ (derivWF_hyp _))
      -- `entryI = ⋯.mpr (⋯.mp h)`, `h = stabAtClosedIteLamEqElse …`.  Strip the
      -- two `simpa`-casts via `eq_mpr_eq_cast` then transport `DerivWF` through.
      simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
      refine derivWF_cast_type rfl ?_ _ _ (derivWF_cast_type rfl ?_ _ _
        (derivWF_stabAtClosedIteLamEqElse _ _ _ _ _ (derivWF_hyp _) ?_ ?_))
      · simp [logicalZ, SC.closed, SC.p, STerm.weaken, STerm.lift, SFormula.boundNat,
          Formula.qVar, Term.lift, Term.weakenVar, rowVar1, Term.instantiateTopNat,
          Term.instantiateNatAt]
      · simp [logicalZ, SC.closed, SC.p, STerm.weaken, STerm.lift, SFormula.boundNat,
          Formula.qVar, Term.lift, Term.weakenVar, rowVar1, Term.instantiateTopNat,
          Term.instantiateNatAt]
      · -- LHS eval `stabAt (stabLam (ite …)) (closed rowVar1)`
        obtain ⟨g, hg⟩ := logicalZBody_eval_total (arity := 1) Surface.code.body
          (D.distance + 1) D.distance (Env.cons x Env.empty)
        refine sterm_eval_stabAt (sv := fun q => some (g q)) (qv := x) ?_ ?_ ⟨g x, rfl⟩
        · simpa [SC.closed, STerm.eval, Formula.qVar] using hg
        · simp [SC.closed, STerm.eval, rowVar1, Term.eval, Env.cons]
      · -- RHS eval `instantiateTopNat rowVar1 (pauliLit I)` = `pauliLit I`
        exact ⟨Pauli.I, by simp [rowVar1, Term.instantiateTopNat, Term.instantiateNatAt,
          Term.eval]⟩

/-- Z/col transpose of `logicalXSupportSurjectiveDeriv_WF`. -/
theorem logicalZSupportSurjectiveDeriv_WF (D : OddSurfaceDistance)
    (E : PartialStabilizer) :
    DerivWF (logicalZSupportSurjectiveDeriv D) Surface.code.body (D.distance + 2)
      Env.empty E := by
  unfold logicalZSupportSurjectiveDeriv
  refine derivWF_allNatLtIntroBounded _ _ ⟨D.distance, scn_eval _ _ _ _ _, ?_⟩
  intro x hx
  refine ⟨?_, by simp [SFormula.ContextHolds]⟩
  refine derivWF_existsNatLtIntroTerm _ _ _
    (logicalZSlotInRangeDeriv_WF D) ?_ ?_
  · -- body: applyNatSubstitutionBeta over the `simpa`-cast `andIntro hNonI hColEq`
    refine derivWF_applyNatSubstitutionBeta ?_
    simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
    refine derivWF_cast_type rfl ?_ _ _ (derivWF_cast_type rfl ?_ _ _ ?_)
    · simp [SFormula.instantiateTopNat, SFormula.instantiateNatAt,
        SFormula.nonIAt, SFormula.boundNat, STerm.instantiateTopNat, STerm.instantiateNatAt,
        STerm.weaken, STerm.lift, Term.instantiateTopNat, Term.instantiateNatAt,
        Term.weaken, Term.lift, Term.weakenVar, SC.closed, SC.n, SC.p,
        gridColOf, logicalZSlotWitness, rowVar1, NatArithmetic.colOf,
        NatArithmetic.gridIdxLeft, logicalZ, Formula.qVar]
    · simp [SFormula.instantiateTopNat, SFormula.instantiateNatAt,
        SFormula.nonIAt, SFormula.boundNat, STerm.instantiateTopNat, STerm.instantiateNatAt,
        STerm.weaken, STerm.lift, Term.instantiateTopNat, Term.instantiateNatAt,
        Term.weaken, Term.lift, Term.weakenVar, SC.closed, SC.n, SC.p,
        gridColOf, logicalZSlotWitness, rowVar1, NatArithmetic.colOf,
        NatArithmetic.gridIdxLeft, logicalZ, Formula.qVar]
    refine derivWF_andIntro ?_ (logicalZSlotColEqDeriv_WF D)
    -- left: `nonIOfEqPauliLit … (casts (stabAtClosedIteLamEqThen … (cast eqNatBoolTrue)))`
    unfold nonIOfEqPauliLit pauliNeqOfEqLeft
    refine ⟨?_, ⟨⟨?_, True.intro⟩, derivWF_weakenContext _ True.intro⟩⟩
    · -- `FormulaDefined (eqPauli (stabAt (logicalZ).weaken witness) (SC.p I))`
      refine formulaDefined_eqPauli ?_ (sterm_eval_p _)
      obtain ⟨g, hg⟩ := logicalZBody_eval_total (arity := 1) Surface.code.body (D.distance + 1)
        D.distance (Env.cons x Env.empty)
      refine sterm_eval_stabAt (sv := fun q => some (g q))
        (qv := 0 + x) ?_ ?_ ⟨_, rfl⟩
      · simpa [SC.closed, logicalZ, STerm.weaken, STerm.lift, STerm.eval, Term.weaken,
          Term.lift, Term.weakenVar] using hg
      · simp [logicalZSlotWitness, SC.closed, STerm.eval, NatArithmetic.gridIdxLeft, rowVar1,
          Term.eval, Term.weakenVar, Env.cons, bind, Option.bind]
    · -- `DerivWF (eqPauliSymm hEntry'_cast.weakenContext)` = `DerivWF hEntry'_cast`
      refine derivWF_weakenContext _ ?_
      refine derivWF_cast_type rfl ?_ _ _ (derivWF_cast_type rfl ?_ _ _ ?_)
      · simp [logicalZ, SC.closed, SC.p, STerm.weaken, STerm.lift, SFormula.boundNat,
          Formula.qVar, Term.lift, Term.weakenVar, rowVar1, Term.instantiateTopNat,
          Term.instantiateNatAt, logicalZSlotWitness, NatArithmetic.gridIdxLeft]
      · simp [logicalZ, SC.closed, SC.p, STerm.weaken, STerm.lift, SFormula.boundNat,
          Formula.qVar, Term.lift, Term.weakenVar, rowVar1, Term.instantiateTopNat,
          Term.instantiateNatAt, logicalZSlotWitness, NatArithmetic.gridIdxLeft]
      -- `stabAtClosedIteLamEqThen … child`: child = `cast (eqNatBoolTrue … rowEq)`
      refine derivWF_stabAtClosedIteLamEqThen _ _ _ _ _
        (derivWF_cast_type rfl ?_ _ _ (logicalZSlotRowEqDeriv_WF D)) ?_ ?_
      · simp [logicalZSlotGuard, logicalZSlotWitness, Formula.qVar, NatArithmetic.rowOf,
          Term.instantiateTopNat, Term.instantiateNatAt, Term.weaken, Term.lift,
          Term.weakenVar, SC.closed, SC.b, NatArithmetic.gridIdxLeft]
      · -- LHS eval `stabAt (closed (stabLam (ite …))) (closed witness)`
        obtain ⟨g, hg⟩ := logicalZBody_eval_total (arity := 1) Surface.code.body
          (D.distance + 1) D.distance (Env.cons x Env.empty)
        refine sterm_eval_stabAt (sv := fun q => some (g q)) (qv := 0 + x) ?_ ?_ ⟨g _, rfl⟩
        · simpa [SC.closed, logicalZ, STerm.eval] using hg
        · simp [logicalZSlotWitness, SC.closed, STerm.eval, NatArithmetic.gridIdxLeft, rowVar1,
            Term.eval, Term.weakenVar, Env.cons, bind, Option.bind]
      · -- RHS eval `instantiateTopNat witness (pauliLit Z)` = `pauliLit Z`
        exact ⟨Pauli.Z, by simp [logicalZSlotWitness, Term.instantiateTopNat,
          Term.instantiateNatAt, Term.eval]⟩
  · -- range
    refine ⟨nQubits D.distance, by rw [sterm_eval_weaken_top]; exact scn_eval _ _ _ _ _,
      fun y hy => ?_⟩
    refine formulaDefined_and ?_ ?_
    · -- `nonIAt (logicalZ).weaken.weaken boundNat` = not (eqPauli (stabAt … ) (SC.p I))
      refine formulaDefined_not (formulaDefined_eqPauli ?_ (sterm_eval_p _))
      obtain ⟨g, hg⟩ := logicalZBody_eval_total (arity := 2) Surface.code.body (D.distance + 1)
        D.distance (Env.cons y (Env.cons x Env.empty))
      refine sterm_eval_stabAt (sv := fun q => some (g q)) (qv := y) ?_ ?_ ⟨g y, rfl⟩
      · simpa [SC.closed, logicalZ, STerm.weaken, STerm.lift, STerm.eval, Term.weaken,
          Term.lift, Term.weakenVar] using hg
      · simp [SFormula.boundNat, SC.closed, STerm.eval, Term.eval, Env.cons]
    · -- `eqNat (lift 1 (gridColOf)) (boundNat.weaken)`
      refine formulaDefined_eqNat ?_ ?_
      · exact ⟨y % D.distance, by simp [gridColOf, SC.closed, STerm.lift,
          STerm.eval, Term.lift, NatArithmetic.colOf, rowVar1, Term.eval, Term.weakenVar,
          Env.cons, bind, Option.bind]⟩
      · exact ⟨x, by simp [SFormula.boundNat, SC.closed, STerm.weaken, STerm.lift,
          STerm.eval, Term.lift, Term.weakenVar, Term.eval, Env.cons]⟩

/-- Z/col transpose of `logicalXWeightExactPure_WF`. -/
theorem logicalZWeightExactPure_WF (D : OddSurfaceDistance) (E : PartialStabilizer) :
    DerivWFA (logicalZWeightExactPure D) Env.empty E := by
  refine derivWFA_cut2 (derivWF_andIntro_hyp_hyp (by simp) (by simp)) ?_ ?_
  · unfold logicalZWeightUpperPure
    obtain ⟨g, hg⟩ := logicalZ_eval_total Surface.code.body (D.distance + 1) D.distance Env.empty
    refine derivWFA_weightLeBySupport (nv := nQubits D.distance) (wv := D.distance)
      (Ev := fun q => some (g q))
      (scn_eval _ _ _ _ _) ?_ (scn_eval _ _ _ _ _) StabTotalUpTo.ofTotal
      (derivWFA_core _ _ _ ?_)
    · simpa [SC.closed, STerm.eval] using hg
    · exact logicalZSupportCoveredDeriv_WF D E
  · refine derivWFA_core _ _ _ ?_
    unfold logicalZWeightLowerDeriv
    refine derivWF_finiteSurjectiveWeightLower _ _ _ _ _ ?_ True.intro ?_
    · exact logicalZSupportSurjectiveDeriv_WF D E
    · -- `FormulaDefined (weightLe n (closed logicalZ) limit)`
      obtain ⟨g, hg⟩ := logicalZ_eval_total Surface.code.body (D.distance + 1)
        D.distance Env.empty
      exact formulaDefined_weightLe (nv := nQubits D.distance)
        (Av := fun q => some (g q)) (wv := D.distance - 1)
        (scn_eval _ _ _ _ _) (by simpa [SC.closed, STerm.eval] using hg)
        (scn_eval _ _ _ _ _) StabTotalUpTo.ofTotal

/-! ## Validated leaf: `DerivWF (logicalXZNoncommPure D)` — the anticommutation tree

A node-by-node walk of the logical-pair anticommutation tree:
`cut1` over `noncommutesOfSingleAnti` (3 children: in-range `gridIdxLeftLtSquare`,
the origin `anticommutesTransport`, and the deep `allNatLt` commutes-except-origin
tree with nested `boolCases`/`mp`/`allNatLtElim`/`applyNatBoundNatBeta`), with the
`arithBool` premise discharged trivially. -/

/-- WF of `logicalOriginInRangeDeriv`: `gridIdxLeftLtSquare` over two `closedNatLt`. -/
theorem logicalOriginInRangeDeriv_WF (D : OddSurfaceDistance) {fuel : Nat}
    {rho : Env 0} {E : PartialStabilizer} :
    DerivWF (logicalOriginInRangeDeriv D) Surface.code.body fuel rho E :=
  ⟨True.intro, True.intro⟩

/-- WF of `logicalXOriginEntryDeriv`: a `stabAtClosedIteLamEqThen` over an
`eqNatBoolTrue`/`gridIdxLeftModEq`, stripped of the two `simpa`-casts. -/
theorem logicalXOriginEntryDeriv_WF (D : OddSurfaceDistance)
    {rho : Env 0} {E : PartialStabilizer} :
    DerivWF (logicalXOriginEntryDeriv D) Surface.code.body (D.distance + 2) rho E := by
  unfold logicalXOriginEntryDeriv
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  refine derivWF_cast_type rfl ?_ _ _
    (derivWF_stabAtClosedIteLamEqThen _ _ _ _ _
      (derivWF_cast_type rfl ?_ _ _ (derivWF_eqNatBoolTrue _ _
        (derivWF_gridIdxLeftModEq _ _ _ True.intro True.intro))) ?_ ?_)
  · simp [logicalX, logicalOriginQ, Formula.qVar, SC.closed, SC.p,
      Term.instantiateTopNat, Term.instantiateNatAt, Term.weaken, Term.lift,
      Term.weakenVar, NatArithmetic.colOf]
  · simp [logicalOriginQ, Formula.qVar, NatArithmetic.colOf, Term.instantiateTopNat,
      Term.instantiateNatAt, Term.weaken, Term.lift, Term.weakenVar, SC.closed, SC.b]
  · -- LHS eval `stabAt (closed (stabLam (ite …))) (closed origin)`
    obtain ⟨g, hg⟩ := logicalXBody_eval_total (arity := 0) Surface.code.body
      (D.distance + 1) D.distance rho
    refine sterm_eval_stabAt (sv := fun q => some (g q)) (qv := D.distance * 0 + 0) ?_ ?_ ⟨g _, rfl⟩
    · simpa [SC.closed, logicalX, STerm.eval] using hg
    · simp [logicalOriginQ, SC.closed, STerm.eval, NatArithmetic.gridIdxLeft,
        Term.eval, Env.cons, bind, Option.bind]
  · -- RHS eval `instantiateTopNat origin (pauliLit X)` = `pauliLit X`
    exact ⟨Pauli.X, by simp [logicalOriginQ, Term.instantiateTopNat,
      Term.instantiateNatAt, Term.eval]⟩

/-- WF of `logicalZOriginEntryDeriv`: Z/row transpose of the X-origin entry. -/
theorem logicalZOriginEntryDeriv_WF (D : OddSurfaceDistance)
    {rho : Env 0} {E : PartialStabilizer} :
    DerivWF (logicalZOriginEntryDeriv D) Surface.code.body (D.distance + 2) rho E := by
  unfold logicalZOriginEntryDeriv
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  refine derivWF_cast_type rfl ?_ _ _
    (derivWF_stabAtClosedIteLamEqThen _ _ _ _ _
      (derivWF_cast_type rfl ?_ _ _ (derivWF_eqNatBoolTrue _ _
        (derivWF_gridIdxLeftDivEq _ _ _ True.intro True.intro))) ?_ ?_)
  · simp [logicalZ, logicalOriginQ, Formula.qVar, SC.closed, SC.p,
      Term.instantiateTopNat, Term.instantiateNatAt, Term.weaken, Term.lift,
      Term.weakenVar, NatArithmetic.rowOf]
  · simp [logicalOriginQ, Formula.qVar, NatArithmetic.rowOf, Term.instantiateTopNat,
      Term.instantiateNatAt, Term.weaken, Term.lift, Term.weakenVar, SC.closed, SC.b]
  · obtain ⟨g, hg⟩ := logicalZBody_eval_total (arity := 0) Surface.code.body
      (D.distance + 1) D.distance rho
    refine sterm_eval_stabAt (sv := fun q => some (g q)) (qv := D.distance * 0 + 0) ?_ ?_ ⟨g _, rfl⟩
    · simpa [SC.closed, logicalZ, STerm.eval] using hg
    · simp [logicalOriginQ, SC.closed, STerm.eval, NatArithmetic.gridIdxLeft,
        Term.eval, Env.cons, bind, Option.bind]
  · exact ⟨Pauli.Z, by simp [logicalOriginQ, Term.instantiateTopNat,
      Term.instantiateNatAt, Term.eval]⟩

/-- WF of `logicalXZOriginAnticommDeriv`: an `anticommutesTransport` over the two
origin-entry derivations and a `pauliAnticommutesLit`, stripped of the `simpa`-cast. -/
theorem logicalXZOriginAnticommDeriv_WF (D : OddSurfaceDistance)
    {rho : Env 0} {E : PartialStabilizer} :
    DerivWF (logicalXZOriginAnticommDeriv D) Surface.code.body (D.distance + 2) rho E := by
  unfold logicalXZOriginAnticommDeriv
  refine derivWF_anticommutesTransport _ _ _ _ _
    (logicalXOriginEntryDeriv_WF D) (logicalZOriginEntryDeriv_WF D)
    (derivWF_pauliAnticommutesLit _ _) ?_
  · -- FormulaDefined (eqBool (anticommutes x0 (SC.p X)) (SC.b true))
    refine formulaDefined_eqBool (sterm_eval_anticommutes ?_ (sterm_eval_p _)) (sterm_eval_b _)
    obtain ⟨g, hg⟩ := logicalXBody_eval_total (arity := 0) Surface.code.body
      (D.distance + 1) D.distance rho
    refine sterm_eval_stabAt (sv := fun q => some (g q)) (qv := D.distance * 0 + 0) ?_ ?_ ⟨g _, rfl⟩
    · simpa [SC.closed, logicalX, STerm.eval] using hg
    · simp [logicalOriginQ, SC.closed, STerm.eval, NatArithmetic.gridIdxLeft,
        Term.eval, Env.cons, bind, Option.bind]

/-- WF of `logicalXBoundEntryIDeriv D hFalse`: a `stabAtClosedIteLamEqElse` (with
the `rowVar1` bound-witness) over the `simpa`-cast `hFalse`, given the input's WF. -/
theorem logicalXBoundEntryIDeriv_WF {Γ : List (SFormula 1)} (D : OddSurfaceDistance)
    {rho : Env 1} {E : PartialStabilizer}
    (hFalse : SFormula.Deriv Γ (.eqBool (logicalXGuardAtBound D.distance) (SC.b false)))
    (hWF : DerivWF hFalse Surface.code.body (D.distance + 2) rho E) :
    DerivWF (logicalXBoundEntryIDeriv D hFalse) Surface.code.body (D.distance + 2) rho E := by
  unfold logicalXBoundEntryIDeriv
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  refine derivWF_cast_type rfl ?_ _ _ (derivWF_cast_type rfl ?_ _ _
    (derivWF_stabAtClosedIteLamEqElse _ _ _ _ _
      (derivWF_cast_type rfl ?_ _ _ hWF) ?_ ?_))
  · simp [logicalX, rowVar1, Formula.qVar, SFormula.boundNat, SC.closed, SC.p,
      STerm.weaken, STerm.lift, Term.instantiateTopNat, Term.instantiateNatAt,
      Term.weaken, Term.lift, Term.weakenVar, NatArithmetic.colOf]
  · simp [logicalX, rowVar1, Formula.qVar, SFormula.boundNat, SC.closed, SC.p,
      STerm.weaken, STerm.lift, Term.instantiateTopNat, Term.instantiateNatAt,
      Term.weaken, Term.lift, Term.weakenVar, NatArithmetic.colOf]
  · simp [logicalXGuardAtBound, rowVar1, Formula.qVar, NatArithmetic.colOf,
      Term.instantiateTopNat, Term.instantiateNatAt, Term.weaken, Term.weakenVar,
      SC.closed]
  · -- LHS eval `stabAt (closed (stabLam (ite …))) (closed rowVar1)`
    obtain ⟨g, hg⟩ := logicalXBody_eval_total (arity := 1) Surface.code.body
      (D.distance + 1) D.distance rho
    refine sterm_eval_stabAt (sv := fun q => some (g q)) (qv := rho ⟨0, by decide⟩) ?_ ?_ ⟨g _, rfl⟩
    · simpa [SC.closed, logicalX, STerm.eval] using hg
    · simp [rowVar1, SC.closed, STerm.eval, Formula.qVar, Term.eval, Env.cons]
  · -- RHS eval `instantiateTopNat rowVar1 (pauliLit I)` = `pauliLit I`
    exact ⟨Pauli.I, by simp [rowVar1, Term.instantiateTopNat, Term.instantiateNatAt,
      Term.eval]⟩

/-- WF of `logicalZBoundEntryIDeriv D hFalse`: Z/row transpose of the X version. -/
theorem logicalZBoundEntryIDeriv_WF {Γ : List (SFormula 1)} (D : OddSurfaceDistance)
    {rho : Env 1} {E : PartialStabilizer}
    (hFalse : SFormula.Deriv Γ (.eqBool (logicalZGuardAtBound D.distance) (SC.b false)))
    (hWF : DerivWF hFalse Surface.code.body (D.distance + 2) rho E) :
    DerivWF (logicalZBoundEntryIDeriv D hFalse) Surface.code.body (D.distance + 2) rho E := by
  unfold logicalZBoundEntryIDeriv
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  refine derivWF_cast_type rfl ?_ _ _ (derivWF_cast_type rfl ?_ _ _
    (derivWF_stabAtClosedIteLamEqElse _ _ _ _ _
      (derivWF_cast_type rfl ?_ _ _ hWF) ?_ ?_))
  · simp [logicalZ, rowVar1, Formula.qVar, SFormula.boundNat, SC.closed, SC.p,
      STerm.weaken, STerm.lift, Term.instantiateTopNat, Term.instantiateNatAt,
      Term.weaken, Term.lift, Term.weakenVar, NatArithmetic.rowOf]
  · simp [logicalZ, rowVar1, Formula.qVar, SFormula.boundNat, SC.closed, SC.p,
      STerm.weaken, STerm.lift, Term.instantiateTopNat, Term.instantiateNatAt,
      Term.weaken, Term.lift, Term.weakenVar, NatArithmetic.rowOf]
  · simp [logicalZGuardAtBound, rowVar1, Formula.qVar, NatArithmetic.rowOf,
      Term.instantiateTopNat, Term.instantiateNatAt, Term.weaken, Term.weakenVar,
      SC.closed]
  · obtain ⟨g, hg⟩ := logicalZBody_eval_total (arity := 1) Surface.code.body
      (D.distance + 1) D.distance rho
    refine sterm_eval_stabAt (sv := fun q => some (g q)) (qv := rho ⟨0, by decide⟩) ?_ ?_ ⟨g _, rfl⟩
    · simpa [SC.closed, logicalZ, STerm.eval] using hg
    · simp [rowVar1, SC.closed, STerm.eval, Formula.qVar, Term.eval, Env.cons]
  · exact ⟨Pauli.I, by simp [rowVar1, Term.instantiateTopNat, Term.instantiateNatAt,
      Term.eval]⟩

/-- WF of `logicalXZCommutesExceptOriginDeriv`: the deep `allNatLtIntroBounded`
tree whose body is `impIntro (boolCases xGuard … (boolCases zGuard …))` with the
nested `mp`/`allNatLtElim`/`applyNatBoundNatBeta` true-true arm.  Stripped of the
`simpa`-casts node by node. -/
theorem logicalXZCommutesExceptOriginDeriv_WF (D : OddSurfaceDistance)
    (E : PartialStabilizer) :
    DerivWF (logicalXZCommutesExceptOriginDeriv D) Surface.code.body (D.distance + 2)
      Env.empty E := by
  -- `localCommutesAt (logicalX).weaken (logicalZ).weaken boundNat` is defined at
  -- every in-range slot — the shared `FormulaDefined` for both `localCommutes`
  -- arms.
  have hLocComm : ∀ (y : Nat),
      SFormula.Deriv.FormulaDefined Surface.code.body (D.distance + 2)
        (Env.cons y Env.empty) E
        (SFormula.localCommutesAt (SC.closed (logicalX D.distance)).weaken
          (SC.closed (logicalZ D.distance)).weaken SFormula.boundNat) := by
    intro y
    obtain ⟨gx, hgx⟩ := logicalXBody_eval_total (arity := 1) Surface.code.body
      (D.distance + 1) D.distance (Env.cons y Env.empty)
    obtain ⟨gz, hgz⟩ := logicalZBody_eval_total (arity := 1) Surface.code.body
      (D.distance + 1) D.distance (Env.cons y Env.empty)
    refine formulaDefined_localCommutesAt ?_ ?_
    · refine sterm_eval_stabAt (sv := fun q => some (gx q)) (qv := y) ?_ ?_ ⟨gx y, rfl⟩
      · simpa [SC.closed, logicalX, STerm.weaken, STerm.lift, STerm.eval, Term.weaken,
          Term.lift, Term.weakenVar] using hgx
      · simp [SFormula.boundNat, SC.closed, STerm.eval, Term.eval, Env.cons]
    · refine sterm_eval_stabAt (sv := fun q => some (gz q)) (qv := y) ?_ ?_ ⟨gz y, rfl⟩
      · simpa [SC.closed, logicalZ, STerm.weaken, STerm.lift, STerm.eval, Term.weaken,
          Term.lift, Term.weakenVar] using hgz
      · simp [SFormula.boundNat, SC.closed, STerm.eval, Term.eval, Env.cons]
  unfold logicalXZCommutesExceptOriginDeriv
  refine derivWF_allNatLtIntroBounded _ _ ⟨nQubits D.distance, scn_eval _ _ _ _ _, ?_⟩
  intro x hx
  refine ⟨?_, fun A hA => ?_⟩
  swap
  · -- ContextHolds [logicalOriginOverlapF D]: discharged by `logicalOriginOverlap_valid`
    rcases List.mem_singleton.1 hA with rfl
    exact logicalOriginOverlap_valid D Env.empty E
  refine derivWF_impIntro ?_ ?_
  · -- FormulaDefined (not (eqNat boundNat q0.weaken))
    refine formulaDefined_not (formulaDefined_eqNat ?_ ?_)
    · exact ⟨x, by simp [SFormula.boundNat, SC.closed, STerm.eval, Term.eval, Env.cons]⟩
    · rw [sterm_eval_weaken_top]
      exact ⟨D.distance * 0 + 0, by simp [logicalOriginQ, SC.closed, STerm.eval,
        NatArithmetic.gridIdxLeft, Term.eval, Env.cons, bind, Option.bind]⟩
  · -- body: `id (boolCases xGuard target trueX falseX)` (`id` defeq)
    refine derivWF_boolCases _ _ ?_ ?_ ?_
    · -- xGuard bool eval
      refine ⟨decide (x % D.distance = 0), ?_⟩
      simp [logicalXGuardAtBound, SC.closed, STerm.eval, rowVar1, Formula.qVar,
        NatArithmetic.colOf, Term.eval, Env.cons, bind, Option.bind]
    · -- trueX: `boolCases zGuard target trueZ falseZ`
      refine derivWF_boolCases _ _ ?_ ?_ ?_
      · -- zGuard bool eval
        refine ⟨decide (x / D.distance = 0), ?_⟩
        simp [logicalZGuardAtBound, SC.closed, STerm.eval, rowVar1, Formula.qVar,
          NatArithmetic.rowOf, Term.eval, Env.cons, bind, Option.bind]
      · -- trueZ: `(hEq.notElim hNotEq).botElim`
        refine derivWF_botElim (derivWF_notElim ?_ (derivWF_hyp _))
        -- hEq = `hBody.mp (hX.andIntro hZ)`
        refine derivWF_mp ?_ (derivWF_andIntro (derivWF_hyp _) True.intro)
        -- hBody = `applyNatBoundNatBeta (...) hApply`
        refine derivWF_applyNatBoundNatBeta _ ?_
        -- hApply = `allNatLtElim … hAll hBoundLt`; hAll = `id hOverlap` (hyp), hBoundLt = hyp
        exact derivWF_allNatLtElim _ _ _ (derivWF_hyp _) (derivWF_hyp _)
      · -- falseZ: `id (localCommutesOfRightI … (logicalZBoundEntryIDeriv D assumption))`
        refine derivWF_localCommutesOfRightI _ _ _ ?_ (hLocComm x)
        exact logicalZBoundEntryIDeriv_WF D _ True.intro
    · -- falseX: `id (localCommutesOfLeftI … (logicalXBoundEntryIDeriv D assumption))`
      refine derivWF_localCommutesOfLeftI _ _ _ ?_ (hLocComm x)
      exact logicalXBoundEntryIDeriv_WF D _ True.intro

/-- WF of `logicalXZNoncommDeriv`: a `noncommutesOfSingleAnti` over the in-range
`weakenContext`, the origin-anticomm `weakenContext`, and the deep
commutes-except-origin tree. -/
theorem logicalXZNoncommDeriv_WF (D : OddSurfaceDistance) (E : PartialStabilizer) :
    DerivWF (logicalXZNoncommDeriv D) Surface.code.body (D.distance + 2)
      Env.empty E := by
  unfold logicalXZNoncommDeriv
  exact derivWF_noncommutesOfSingleAnti _ _ _ _
    (derivWF_weakenContext _ (logicalOriginInRangeDeriv_WF D))
    (derivWF_weakenContext _ (logicalXZOriginAnticommDeriv_WF D))
    (logicalXZCommutesExceptOriginDeriv_WF D E)

/-- End-to-end `DerivWFA` for the logical-pair anticommutation sub-tree:
`cut1` over `logicalXZNoncommDeriv` with the `arithBool` overlap premise. -/
theorem logicalXZNoncommPure_WF (D : OddSurfaceDistance) (E : PartialStabilizer) :
    DerivWFA (logicalXZNoncommPure D) Env.empty E := by
  unfold logicalXZNoncommPure
  exact derivWFA_cut1 (logicalXZNoncommDeriv_WF D E) (derivWFA_arithBool _ _)

/-! ## Axiom audit (all pieces — no new axioms, no `sorryAx`) -/

#print axioms logicalXSupportCoveredDeriv_WF
#print axioms logicalXSupportSurjectiveDeriv_WF
#print axioms logicalXWeightExactPure_WF
#print axioms logicalZSupportCoveredDeriv_WF
#print axioms logicalZSupportSurjectiveDeriv_WF
#print axioms logicalZWeightExactPure_WF
#print axioms logicalXZCommutesExceptOriginDeriv_WF
#print axioms logicalXZNoncommDeriv_WF
#print axioms logicalXZNoncommPure_WF
#print axioms derivWF_cast_type
#print axioms derivWFA_weightLeBySupport
#print axioms logicalXBody_eval_total

end QHL.CodeLang.Surface.Verify
