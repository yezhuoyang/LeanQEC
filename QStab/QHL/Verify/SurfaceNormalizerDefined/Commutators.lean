import QStab.QHL.Verify.SurfaceNormalizerDefined.FlatBridge

/-!
# Normalizer sub-tree definedness — Commutators

Residual leaf #2 (the commutator leaves), the bundle's `DerivWFA`, and the well-formedness
of the commutator leaves.
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

set_option maxHeartbeats 1600000

/-! ## Residual leaf #2: the commutator leaves (OPEN)

`commTwoAntiA` / `commTwoAntiB` / `commPointwiseSym` each emit a deep
`SFormula.Deriv` (`commutesOfTwoAnti` / `commutesOfPointwise` over
`colDispatchOnTrue` / `entryAtBound` / `logicalXOffColumnLocalCommutes`
sub-trees).  Their `DerivWF` is large but flat in `D.index`.  Stated here as the
named residuals the per-`k` boolCases tree bottoms out at. -/

/-! ## The bundle's `DerivWFA` (depends on residual #1)

`xBundle D = pfdaAnd … (pfdaAnd … …)`; the glue is discharged by `pfdaAnd_WF`,
the `arithBool`/`allNatLtIntro`-of-`arithBool` packs are trivial, and the five
`recCall`-entry packs reduce to `rowEntryFlatSym_WF` (residual #1). -/

/-- Shared discharger for the four `nQ1`-bound, `arithBool`-body packs
(`rightBandFalse`/`classABulkZPin`/`classBLeftZPin`/`bandImpCZero`): each is
`allNatLtIntro (nQ1 D) (arithBool …)`, range evals to `nQubits D.distance`, and
every body clause is trivially `True`. -/
theorem nQ1ArithBoolPack_WF {D : OddSurfaceDistance}
    {A : SFormula 2}
    {hfrag : arithBoolFragment A = true}
    {hvalid : ∀ (rho : Env 2) (E : PartialStabilizer),
      A.eval Surface.code.body (D.distance + 2) rho E = some true}
    {x : Nat} {E : PartialStabilizer} :
    DerivWFA (PureFamilyDerivA.allNatLtIntro (nQ1 D)
      (PureFamilyDerivA.arithBool A hfrag hvalid)) (Env.cons x Env.empty) E := by
  refine derivWFA_allNatLtIntro _ ⟨nQubits D.distance, ?_, fun y hy => True.intro⟩
  simp [nQ1, SC.closed, STerm.eval, Term.eval, Term.lift, Term.weakenVar]

theorem rightBandFalsePack_WF (D : OddSurfaceDistance) {x : Nat} {E : PartialStabilizer} :
    DerivWFA (rightBandFalsePack D) (Env.cons x Env.empty) E := by
  unfold rightBandFalsePack; exact nQ1ArithBoolPack_WF

theorem classABulkZPinPack_WF (D : OddSurfaceDistance) {x : Nat} {E : PartialStabilizer} :
    DerivWFA (classABulkZPinPack D) (Env.cons x Env.empty) E := by
  unfold classABulkZPinPack; exact nQ1ArithBoolPack_WF

theorem classBLeftZPinPack_WF (D : OddSurfaceDistance) {x : Nat} {E : PartialStabilizer} :
    DerivWFA (classBLeftZPinPack D) (Env.cons x Env.empty) E := by
  unfold classBLeftZPinPack; exact nQ1ArithBoolPack_WF

theorem bandImpCZeroPack_WF (D : OddSurfaceDistance) {x : Nat} {E : PartialStabilizer} :
    DerivWFA (bandImpCZeroPack D) (Env.cons x Env.empty) E := by
  unfold bandImpCZeroPack; exact nQ1ArithBoolPack_WF

/-- Each flat-entry pack `xEntryFlat1 D qT hqT` reduces to `rowEntryFlatSym_WF`. -/
theorem xEntryFlat1_WF (D : OddSurfaceDistance) (qT : Term 1 .nat)
    (hqT : SFormula.PureNatTerm qT) {x : Nat} {E : PartialStabilizer} :
    DerivWFA (xEntryFlat1 D qT hqT) (Env.cons x Env.empty) E := by
  unfold xEntryFlat1
  -- fuel bound `D.index + 2 ≤ D.distance + 2`; witness-free now (local projection width).
  exact rowEntryFlatSym_WF _ _ _ _ _ _ _ _
    (by simp only [OddSurfaceDistance.distance, oddDistance]; omega)

/-- `entryFlatPack D = allNatLtIntro (nQ1 D) (xEntryFlat2BoundW D)`; range evals to
`nQubits D.distance` and the body reduces (modulo the `rowK2_eq` cast) to
`rowEntryFlatSym_WF`. -/
theorem entryFlatPack_WF (D : OddSurfaceDistance) {x : Nat} {E : PartialStabilizer} :
    DerivWFA (entryFlatPack D) (Env.cons x Env.empty) E := by
  unfold entryFlatPack
  refine derivWFA_allNatLtIntro _ ⟨nQubits D.distance, ?_, fun y hy => ?_⟩
  · simp [SC.closed, STerm.eval, Term.eval, Term.lift, Term.weakenVar]
  · unfold xEntryFlat2BoundW
    simp only [eq_mpr_eq_cast]
    refine derivWFA_cast_type rfl _ _ ?_
    unfold xEntryFlat2Bound
    -- fuel bound `D.index + 2 ≤ D.distance + 2`; witness-free now (local projection width).
    exact rowEntryFlatSym_WF _ _ _ _ _ _ _ _
      (by simp only [OddSurfaceDistance.distance, oddDistance]; omega)

/-- `DerivWFA (xBundle D)`: the 14-pack conjunction.  Glue by `pfdaAnd_WF`; the
five `recCall`-entry packs (`entryFlatPack` + 4 × `xEntryFlat1`) bottom out at
`rowEntryFlatSym_WF` (residual #1); the four `nQ1`-`arithBool` packs by
`nQ1ArithBoolPack_WF`; the five plain `arithBool` packs are trivially `True`. -/
theorem xBundle_WF (D : OddSurfaceDistance) {x : Nat} {E : PartialStabilizer} :
    DerivWFA (xBundle D) (Env.cons x Env.empty) E := by
  unfold xBundle
  exact pfdaAnd_WF (entryFlatPack_WF D)
    (pfdaAnd_WF (rightBandFalsePack_WF D)
      (pfdaAnd_WF True.intro
        (pfdaAnd_WF True.intro
          (pfdaAnd_WF (classABulkZPinPack_WF D)
            (pfdaAnd_WF True.intro
              (pfdaAnd_WF True.intro
                (pfdaAnd_WF (classBLeftZPinPack_WF D)
                  (pfdaAnd_WF (xEntryFlat1_WF D (qa0 D) (qa0_pure D))
                    (pfdaAnd_WF (xEntryFlat1_WF D (qa1 D) (qa1_pure D))
                      (pfdaAnd_WF (xEntryFlat1_WF D (qb0 D) (qb0_pure D))
                        (pfdaAnd_WF (xEntryFlat1_WF D (qb1 D) (qb1_pure D))
                          (pfdaAnd_WF True.intro (bandImpCZeroPack_WF D)))))))))))))

/-! ## Well-formedness of the commutator leaves

Every commutator constructor (the four pointwise/two-anti `X` leaves and their
`Z`-transposes) carries a `DerivWF` definedness certificate, assembled bottom-up
from the leaf, dispatcher, and pin lemmas in this section. -/


/-- `DerivWF (weakenFresh child)` from the child at the tail env. -/
theorem derivWF_weakenFresh {arity : Nat} {Γ : List (SFormula arity)} {A : SFormula arity}
    {child : SFormula.Deriv Γ A} {cb : Term 2 .stab} {fuel : Nat} {rho : Env (arity + 1)}
    {E : PartialStabilizer} (h : DerivWF child cb fuel (envTail' rho) E) :
    DerivWF (SFormula.Deriv.weakenFresh (A := A) child) cb fuel rho E := h

/-- `DerivWF (notIntro child)` from `FormulaDefined A` + the child. -/
theorem derivWF_notIntro {arity : Nat} {Γ : List (SFormula arity)} {A : SFormula arity}
    {child : SFormula.Deriv (A :: Γ) .bot} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity}
    {E : PartialStabilizer} (hA : SFormula.Deriv.FormulaDefined cb fuel rho E A)
    (h : DerivWF child cb fuel rho E) :
    DerivWF (SFormula.Deriv.notIntro (A := A) child) cb fuel rho E := ⟨hA, h⟩

/-- `DerivWF (orElim disj left right)` from all three children. -/
theorem derivWF_orElim {arity : Nat} {Γ : List (SFormula arity)} {A B C : SFormula arity}
    {disj : SFormula.Deriv Γ (.or A B)} {left : SFormula.Deriv (A :: Γ) C}
    {right : SFormula.Deriv (B :: Γ) C} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity}
    {E : PartialStabilizer} (hd : DerivWF disj cb fuel rho E) (hl : DerivWF left cb fuel rho E)
    (hr : DerivWF right cb fuel rho E) :
    DerivWF (SFormula.Deriv.orElim disj left right) cb fuel rho E := ⟨hd, hl, hr⟩

/-- `DerivWF (eqBoolFalseNotTrue b child)` from the child (which proves `eqBool b false`). -/
theorem derivWF_eqBoolFalseNotTrue {arity : Nat} {Γ : List (SFormula arity)}
    {b : STerm arity .bool} {child : SFormula.Deriv Γ (.eqBool b (SC.b false))}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (h : DerivWF child cb fuel rho E) :
    DerivWF (SFormula.Deriv.eqBoolFalseNotTrue b child) cb fuel rho E := h

/-- `DerivWF (commutesOfTwoAnti …)` from its six children. -/
theorem derivWF_commutesOfTwoAnti {arity : Nat} {Γ : List (SFormula arity)}
    {n A B : _} {q0 q1 : STerm arity .nat}
    {lt0D : SFormula.Deriv Γ (SFormula.witnessLt q0 n)}
    {lt1D : SFormula.Deriv Γ (SFormula.witnessLt q1 n)}
    {neD : SFormula.Deriv Γ (.not (.eqNat q0 q1))}
    {anti0D : SFormula.Deriv Γ (.eqBool (.anticommutes (.stabAt A q0) (.stabAt B q0)) (SC.b true))}
    {anti1D : SFormula.Deriv Γ (.eqBool (.anticommutes (.stabAt A q1) (.stabAt B q1)) (SC.b true))}
    {restD : _}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (h0 : DerivWF lt0D cb fuel rho E) (h1 : DerivWF lt1D cb fuel rho E)
    (hne : DerivWF neD cb fuel rho E) (ha0 : DerivWF anti0D cb fuel rho E)
    (ha1 : DerivWF anti1D cb fuel rho E) (hr : DerivWF restD cb fuel rho E) :
    DerivWF (SFormula.Deriv.commutesOfTwoAnti n A B q0 q1 lt0D lt1D neD anti0D anti1D restD)
      cb fuel rho E :=
  ⟨h0, h1, hne, ha0, ha1, hr⟩

/-- `DerivWF (commutesOfPointwise n A B child)` from the child + the `commutesUpTo`
formula's definedness. -/
theorem derivWF_commutesOfPointwise {arity : Nat} {Γ : List (SFormula arity)}
    {n : STerm arity .nat} {A B : STerm arity .stab}
    {child : SFormula.Deriv Γ (SFormula.pointwiseCommutesUpTo n A B)}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (h : DerivWF child cb fuel rho E)
    (hFD : SFormula.Deriv.FormulaDefined cb fuel rho E (.commutesUpTo n A B)) :
    DerivWF (SFormula.Deriv.commutesOfPointwise n A B child) cb fuel rho E := ⟨h, hFD⟩

/-- `DerivWF (localCommutesOfLeftEqNoAntiRight …)` — the 7th constructor combinator
(the `colCommFromEntry` geometric leaf). -/
theorem derivWF_localCommutesOfLeftEqNoAntiRight {arity : Nat} {Γ : List (SFormula arity)}
    (A B : STerm arity .stab) (q : STerm arity .nat) (p : STerm arity .pauli)
    {eqD : SFormula.Deriv Γ (.eqPauli (.stabAt A q) p)}
    {noAntiD : SFormula.Deriv Γ (.not (.eqBool (.anticommutes (.stabAt B q) p) (SC.b true)))}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (heq : DerivWF eqD cb fuel rho E) (hnoAnti : DerivWF noAntiD cb fuel rho E)
    (hfd : SFormula.Deriv.FormulaDefined cb fuel rho E (SFormula.localCommutesAt A B q)) :
    DerivWF (SFormula.Deriv.localCommutesOfLeftEqNoAntiRight A B q p eqD noAntiD) cb fuel rho E :=
  ⟨heq, hnoAnti, hfd⟩

/-- Uniform commutator-`DerivWF` walker: `flat_deriv_wf`'s pure-leaf alternatives + every
constructor combinator (the 7 new + the existing geometric ones) + the geometric
`FormulaDefined` dischargers (`localCommutesAt`/`commutesUpTo`).  Sub-helper `DerivWF`s and
`stabAt`-eval side-conditions are found by `assumption`. -/
macro "comm_deriv_wf" : tactic =>
  `(tactic|
    repeat first
      | exact True.intro
      | assumption
      | refine derivWF_eqPauliTrans' ?_ ?_
      | refine derivWF_eqPauliSymm' ?_
      | refine derivWF_mp ?_ ?_
      | refine derivWF_andIntro ?_ ?_
      | refine derivWF_andElimLeft' ?_
      | refine derivWF_andElimRight' ?_
      | refine derivWF_contextWeakening' _ _ ?_
      | refine derivWF_weakenFresh ?_
      | refine derivWF_notIntro ?_ ?_
      | refine derivWF_notElim ?_ ?_
      | refine derivWF_orElim ?_ ?_ ?_
      | refine derivWF_botElim ?_
      | refine derivWF_impIntro ?_ ?_
      | refine derivWF_eqBoolFalseNotTrue ?_
      | refine derivWF_eqNatBoolTrue _ _ ?_
      | refine derivWF_commutesOfTwoAnti ?_ ?_ ?_ ?_ ?_ ?_
      | refine derivWF_commutesOfPointwise ?_ ?_
      | refine derivWF_localCommutesOfLeftEqNoAntiRight _ _ _ _ ?_ ?_ ?_
      | refine derivWF_localCommutesOfLeftI _ _ _ ?_ ?_
      | refine derivWF_localCommutesOfRightI _ _ _ ?_ ?_
      | refine derivWF_anticommutesTransport _ _ _ _ _ ?_ ?_ ?_ ?_
      | refine derivWF_allNatLtElim _ _ _ ?_ ?_
      | refine derivWF_allNatLtIntroBounded _ _ ?_
      | refine derivWF_applyNatBoundNatBeta _ ?_
      | refine derivWF_pauliIteSelectThen' _ _ _ ?_ ?_
      | refine derivWF_pauliIteSelectElse' _ _ _ ?_ ?_
      | refine derivWF_boolCases _ _
          (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?_ ?_
      | exact derivWF_pauliAnticommutesLit _ _
      | apply derivWF_pauliEqLit'
      | apply formulaDefined_localCommutesAt
      | apply formulaDefined_commutesUpTo
      | apply formulaDefined_eqPauli_purePauli
      | leaf_pp)

end QHL.CodeLang.Surface.Verify
