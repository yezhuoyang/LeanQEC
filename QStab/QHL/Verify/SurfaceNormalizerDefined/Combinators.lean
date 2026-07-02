import QStab.QHL.Verify.SurfaceCodeLevelDefined
import QStab.QHL.Verify.SurfaceNormalizers

/-!
# Normalizer sub-tree definedness — Combinators

The `DerivWFA` cast/binder combinators for the normalizer top nodes, and the extra trivial
`rfl`-transparent `DerivWF` node combinators.
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

set_option maxHeartbeats 1600000


/-! ## `DerivWFA` cast/binder combinators (new, for the normalizer top nodes) -/

/-- `DerivWFA` transports across a *type-level* `cast` of the `PureFamilyDerivA`,
given the type equality arises from a formula equality.  Punches through the
`Eq.mpr`/`cast` the `simpa` in `xNormCommuteSym`/`zNormCommuteSym` inserts. -/
theorem derivWFA_cast_type {cb : Term 2 .stab} {fuel arity : Nat} {A A' : SFormula arity}
    (hA : A = A') (d : PureFamilyDerivA cb fuel A)
    (htype : PureFamilyDerivA cb fuel A = PureFamilyDerivA cb fuel A')
    {rho : Env arity} {E : PartialStabilizer}
    (h : DerivWFA d rho E) :
    DerivWFA (cast htype d) rho E := by
  subst hA
  rw [cast_eq]
  exact h

/-- `DerivWFA (allNatLtIntro n child)` from the range eval plus the per-`x` child
`DerivWFA`. -/
theorem derivWFA_allNatLtIntro {cb : Term 2 .stab} {fuel arity : Nat}
    {A : SFormula (arity + 1)} (n : STerm arity .nat)
    {child : PureFamilyDerivA cb fuel A}
    {rho : Env arity} {E : PartialStabilizer}
    (hwf : ∃ bound, n.eval cb fuel rho E = some bound ∧
      ∀ x, x < bound → DerivWFA child (Env.cons x rho) E) :
    DerivWFA (PureFamilyDerivA.allNatLtIntro n child) rho E := hwf

/-- `DerivWFA (pfdaAnd hA hB)` from both children's `DerivWFA`.  The `andIntro`
core of two `hyp`s is trivially well-formed. -/
theorem pfdaAnd_WF {D : OddSurfaceDistance} {A B : SFormula 1}
    {hA : PureFamilyDerivA Surface.code.body (D.distance + 2) A}
    {hB : PureFamilyDerivA Surface.code.body (D.distance + 2) B}
    {x : Nat} {E : PartialStabilizer}
    (wA : DerivWFA hA (Env.cons x Env.empty) E)
    (wB : DerivWFA hB (Env.cons x Env.empty) E) :
    DerivWFA (pfdaAnd hA hB) (Env.cons x Env.empty) E :=
  ⟨⟨True.intro, True.intro⟩, wA, wB⟩

/-! ## Extra `DerivWF` node combinators (trivial, `rfl`-transparent)

These mirror the `DerivWF` clauses for the `eqPauli`/`pauliIteSelect`/`contextWeakening`
nodes the masters bottom out at.  Each unfolds definitionally to the children's
clause, so the proof is just the constructor. -/

theorem derivWF_eqPauliTrans' {arity : Nat} {Γ : List (SFormula arity)}
    {a b c : STerm arity .pauli}
    {left : SFormula.Deriv Γ (.eqPauli a b)} {right : SFormula.Deriv Γ (.eqPauli b c)}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (hl : DerivWF left cb fuel rho E) (hr : DerivWF right cb fuel rho E) :
    DerivWF (SFormula.Deriv.eqPauliTrans a b c left right) cb fuel rho E := ⟨hl, hr⟩

theorem derivWF_eqPauliSymm' {arity : Nat} {Γ : List (SFormula arity)}
    {a b : STerm arity .pauli} {child : SFormula.Deriv Γ (.eqPauli a b)}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (hchild : DerivWF child cb fuel rho E) :
    DerivWF (SFormula.Deriv.eqPauliSymm a b child) cb fuel rho E := hchild

theorem derivWF_pauliIteSelectThen' {arity : Nat} {Γ : List (SFormula arity)}
    (cond : Term arity .bool) (p1 p2 : Term arity .pauli)
    {child : SFormula.Deriv Γ (.eqBool (SC.closed cond) (SC.b true))}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (hchild : DerivWF child cb fuel rho E)
    (hfd : SFormula.Deriv.FormulaDefined cb fuel rho E
      (.eqPauli (SC.closed (.ite cond p1 p2)) (SC.closed p1))) :
    DerivWF (SFormula.Deriv.pauliIteSelectThen cond p1 p2 child) cb fuel rho E :=
  ⟨hchild, hfd⟩

theorem derivWF_pauliIteSelectElse' {arity : Nat} {Γ : List (SFormula arity)}
    (cond : Term arity .bool) (p1 p2 : Term arity .pauli)
    {child : SFormula.Deriv Γ (.eqBool (SC.closed cond) (SC.b false))}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (hchild : DerivWF child cb fuel rho E)
    (hfd : SFormula.Deriv.FormulaDefined cb fuel rho E
      (.eqPauli (SC.closed (.ite cond p1 p2)) (SC.closed p2))) :
    DerivWF (SFormula.Deriv.pauliIteSelectElse cond p1 p2 child) cb fuel rho E :=
  ⟨hchild, hfd⟩

/-- `DerivWF (stabAtClosedIteLamEqThen …)` from the guard child's WF and the
`stabAtClosedIteLam` FormulaDefined leaf. -/
theorem derivWF_stabAtClosedIteLamEqThen' {arity : Nat} {Γ : List (SFormula arity)}
    (cond : Term (arity + 1) .bool) (thenP elseP : Term (arity + 1) .pauli) (q : Term arity .nat)
    (hq : SFormula.PureNatTerm q)
    {child : SFormula.Deriv Γ (.eqBool (SC.closed (Term.instantiateTopNat q cond)) (SC.b true))}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (hchild : DerivWF child cb fuel rho E)
    (hfd : SFormula.Deriv.FormulaDefined cb fuel rho E
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (.ite cond thenP elseP))) (SC.closed q))
        (SC.closed (Term.instantiateTopNat q thenP)))) :
    DerivWF (SFormula.Deriv.stabAtClosedIteLamEqThen cond thenP elseP q hq child) cb fuel rho E :=
  ⟨hchild, hfd⟩

/-- `DerivWF (stabAtClosedIteLamEqElse …)` from the guard child's WF and the leaf. -/
theorem derivWF_stabAtClosedIteLamEqElse' {arity : Nat} {Γ : List (SFormula arity)}
    (cond : Term (arity + 1) .bool) (thenP elseP : Term (arity + 1) .pauli) (q : Term arity .nat)
    (hq : SFormula.PureNatTerm q)
    {child : SFormula.Deriv Γ (.eqBool (SC.closed (Term.instantiateTopNat q cond)) (SC.b false))}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (hchild : DerivWF child cb fuel rho E)
    (hfd : SFormula.Deriv.FormulaDefined cb fuel rho E
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (.ite cond thenP elseP))) (SC.closed q))
        (SC.closed (Term.instantiateTopNat q elseP)))) :
    DerivWF (SFormula.Deriv.stabAtClosedIteLamEqElse cond thenP elseP q hq child) cb fuel rho E :=
  ⟨hchild, hfd⟩

theorem derivWF_pauliEqLit' {arity : Nat} {Γ : List (SFormula arity)} (p : Pauli)
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer} :
    DerivWF (SFormula.Deriv.pauliEqLit (Γ := Γ) (arity := arity) p) cb fuel rho E :=
  True.intro

theorem derivWF_contextWeakening' {arity : Nat} {Γ Δ : List (SFormula arity)}
    {A : SFormula arity} (h : ∀ C ∈ Γ, C ∈ Δ) (child : SFormula.Deriv Γ A)
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (hchild : DerivWF child cb fuel rho E) :
    DerivWF (SFormula.Deriv.contextWeakening h child) cb fuel rho E := hchild

end QHL.CodeLang.Surface.Verify
