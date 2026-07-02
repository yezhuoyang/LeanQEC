import QStab.QHL.Verify.SurfaceNormalizerDefined.Combinators

/-!
# Normalizer sub-tree definedness — PurePauliCerts

PurePauli certificates for the leaf trees.
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

set_option maxHeartbeats 1600000

/-! ## PurePauli certificates for the leaf trees

`baseLeafTreeTA` / `recLeafTreeTA` are `pauliLit`-`ite` trees over pure-bool guards
(no `recCall`/`stabAt`/`stabFold`), hence `PurePauli`.  These certificates feed the
uniform `PurePauli.eval_total` discharger at every `pauliIteSelect*` /
`stabAtClosedIteLam` FormulaDefined leaf the masters bottom out at. -/

open QHL.CodeLang.Surface.Verify in
/-- `baseLeafTreeTA dT kT qT` is a `PurePauli` tree when the index terms are pure. -/
theorem baseLeafTreeTA_purePauli {arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    PurePauli (baseLeafTreeTA dT kT qT) := by
  simp only [baseLeafTreeTA, bulkGuardTA, bulkCountTA, dm1TA, baseBulkBandGuardTA,
    baseKindGuardTA, rTA, cTA, gridIdx, topClassGuardTA, baseBTA, baseHalfTA,
    topBandGuardTA, rightClassGuardTA, rightBandGuardTA, leftClassGuardTA, leftBandGuardTA,
    bottomBandGuardTA, lastCellTA, band3, orEqSucc, orEqPair, le]
  pure_tree <;> assumption

/-- `FormulaDefined (.eqPauli (closed a) (closed b))` for two `PurePauli` terms —
the uniform discharger for every `pauliIteSelect*` leaf the masters bottom out at.
(Both sides are recursion-free, so `PurePauli.eval_total` supplies totality.) -/
theorem formulaDefined_eqPauli_purePauli {arity : Nat} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer} {a b : Term arity .pauli}
    (ha : PurePauli a) (hb : PurePauli b) :
    SFormula.Deriv.FormulaDefined cb fuel rho E (.eqPauli (SC.closed a) (SC.closed b)) :=
  formulaDefined_eqPauli_closed (ha.eval_total cb fuel rho) (hb.eval_total cb fuel rho)

/-- Discharge a `PurePauli` goal for a subtree of a leaf tree: unfold guard sugar,
run the structural `pure_tree` walker, finish abstract index leaves by assumption. -/
macro "leaf_pp" : tactic =>
  `(tactic|
    (try simp only [baseLeafTreeTA, recLeafTreeTA, bulkGuardTA, bulkCountTA, dm1TA,
        baseBulkBandGuardTA, baseKindGuardTA, rTA, cTA, gridIdx, topClassGuardTA, baseBTA,
        baseHalfTA, topBandGuardTA, rightClassGuardTA, rightBandGuardTA, leftClassGuardTA,
        leftBandGuardTA, bottomBandGuardTA, lastCellTA, interiorCellGuardTA, insideGuardTA,
        topCellGuardTA, rightCellGuardTA, leftCellGuardTA, bottomCellGuardTA, rowTA, colTA,
        topOuterGuardTA, rightOuterGuardTA, leftOuterGuardTA, bottomOuterGuardTA,
        band3, band4, orEqSucc, orEqPair, le]
     pure_tree <;> assumption))

/-- `recLeafTreeTA` is a `PurePauli` tree when the index terms and the five resolved
cell paulis are pure (the inner cells are opaque `PurePauli` leaves, closed by assumption). -/
theorem recLeafTreeTA_purePauli {arity : Nat} {dT kT qT : Term arity .nat}
    {pInt pTop pRight pLeft pBottom : Term arity .pauli}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpi : PurePauli pInt) (hpt : PurePauli pTop) (hpr : PurePauli pRight)
    (hpl : PurePauli pLeft) (hpb : PurePauli pBottom) :
    PurePauli (recLeafTreeTA dT kT qT pInt pTop pRight pLeft pBottom) := by
  leaf_pp

/-- The fully-resolved row tree `rowSymTreeA m` is `PurePauli` for every depth `m` (induction:
base = `baseLeafTreeTA`, step = `recLeafTreeTA` with the five inner trees pure by IH). -/
theorem rowSymTreeA_purePauli {arity : Nat} (m : Nat) {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    PurePauli (rowSymTreeA m dT kT qT) := by
  induction m generalizing dT kT qT hd hk hq with
  | zero => exact baseLeafTreeTA_purePauli hd hk hq
  | succ m ih =>
      exact recLeafTreeTA_purePauli hd hk hq
        (ih (innerDTA_pure hd) (interiorKTA_pure hd hk) (innerQTA_pure hd hq))
        (ih (innerDTA_pure hd) (topKTA_pure hd hk) (innerQTA_pure hd hq))
        (ih (innerDTA_pure hd) (rightKTA_pure hd hk) (innerQTA_pure hd hq))
        (ih (innerDTA_pure hd) (leftKTA_pure hd hk) (innerQTA_pure hd hq))
        (ih (innerDTA_pure hd) (bottomKTA_pure hd hk) (innerQTA_pure hd hq))

theorem leafZ_WF {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hBand hKind} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wBand : DerivWF hBand cb fuel rho E)
    (wKind : DerivWF hKind cb fuel rho E) :
    DerivWF (leafZ (Γ := Γ) dT kT qT hBulk hBand hKind) cb fuel rho E := by
  unfold leafZ
  refine derivWF_eqPauliTrans'
    (derivWF_pauliIteSelectThen' _ _ _ wBulk ?_)
    (derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectThen' _ _ _ wBand ?_)
      (derivWF_pauliIteSelectThen' _ _ _ wKind ?_)) <;>
    exact formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)

/-- `baseBulkSelectTrueD`/`baseBulkSelectFalseD` are `rw`-of-`hBulk`; their WF is the
guard's WF transported across the type rewrite. -/
theorem baseBulkSelectTrueD_WF {arity : Nat} {Γ : List (SFormula arity)}
    (dT kT qT : Term arity .nat) {hBulk} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) :
    DerivWF (baseBulkSelectTrueD (Γ := Γ) dT kT qT hBulk) cb fuel rho E := by
  unfold baseBulkSelectTrueD
  exact derivWF_cast_type rfl (by simp only [bulkGuardTA, bulkCountTA, dm1TA,
    Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]) _ _ wBulk

theorem baseBulkSelectFalseD_WF {arity : Nat} {Γ : List (SFormula arity)}
    (dT kT qT : Term arity .nat) {hBulk} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) :
    DerivWF (baseBulkSelectFalseD (Γ := Γ) dT kT qT hBulk) cb fuel rho E := by
  unfold baseBulkSelectFalseD
  exact derivWF_cast_type rfl (by simp only [bulkGuardTA, bulkCountTA, dm1TA,
    Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]) _ _ wBulk

/-- Discharge a `∃ v, Term.eval cb fuel t rho = some v` goal for a recursion-free
`t` (the lam-body / instantiateTopNat RHS shapes the keystone leaves emit).  All such
terms are `codeSubstAt`-of-`PurePauli` or `instantiateTopNat`-of-`PurePauli`, so the
banked totality closures apply; the residual abstract index leaves close by the
`hd`/`hk`/`hq` purity assumptions. -/
macro "eval_tot" : tactic =>
  `(tactic|
    first
      | exact purePauli_codeSubstAt_one_eval_total ‹SFormula.PureNatTerm _› ‹SFormula.PureNatTerm _›
          baseEntry_purePauli _ _ _
      | exact purePauli_instantiateTopNat_eval_total ‹SFormula.PureNatTerm _› (by leaf_pp) _ _ _)

/-- The structural well-formedness walk for the keystone leaf trees / peels / masters.
Repeatedly: peels `Eq.mpr`/`cast` shells (`derivWF_cast_type rfl rfl _ rfl`), applies
the node combinators (`eqPauliTrans`/`eqPauliSymm`/`pauliIteSelect`/`stabAtClosedIteLam`/
`boolCases`/`contextWeakening`/`pauliEqLit`), and discharges leaves (`True`, the
`hyp`/guard WF assumptions, the `pauliIteSelect`/`stabAtClosedIteLam` FormulaDefined
obligations via the `PurePauli` totality bank). -/
macro "wf_walk" : tactic =>
  `(tactic|
    repeat first
      | assumption
      | exact True.intro
      | exact derivWF_cast_type rfl rfl _ rfl (by assumption)
      | apply derivWF_cast_type rfl rfl _ rfl
      | apply derivWF_eqPauliTrans'
      | apply derivWF_eqPauliSymm'
      | apply derivWF_stabAtClosedIteLamEqThen' _ _ _ _ ‹SFormula.PureNatTerm _›
      | apply derivWF_stabAtClosedIteLamEqElse' _ _ _ _ ‹SFormula.PureNatTerm _›
      | apply derivWF_pauliIteSelectThen'
      | apply derivWF_pauliIteSelectElse'
      | apply derivWF_pauliEqLit'
      | apply derivWF_contextWeakening'
      | exact formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)
      | exact formulaDefined_stabAtClosedIteLam ‹SFormula.PureNatTerm _›
          (fun _ => by eval_tot) (by eval_tot))

/-- Strip ONE `cast`/`Eq.mpr` shell whose formula equality is closed by the peels' own
`simp only` normal form (OBSTACLE A fix): walking the giant substituted-baseEntry
formula equalities with `rfl` whnf-times-out, but the *explicit* simp set proves the
equality cheaply.  Covers both base (`baseEntry`) and rec (`recursiveEntry`) peels. -/
macro "peel_cast" : tactic =>
  `(tactic|
    first
      | apply derivWF_cast_type rfl (by
          simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]) _ rfl
      | apply derivWF_cast_type rfl (by
          simp only [codeSubstAt, liftTopN, Term.weaken, reduceDIte,
            Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]) _ rfl
      | apply derivWF_cast_type rfl (by
          simp only [SurfaceASTPublic.baseEntry, SurfaceASTPublic.recursiveEntry,
            SurfaceASTPublic.promotedBoundaryEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
            SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN,
            Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte, eq_mp_eq_cast,
            eq_mpr_eq_cast, cast_eq, band3, band4, le, orEqSucc, orEqPair,
            Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift,
            Nat.lt_irrefl, dite_false, dite_true,
            topOuterGuardTA, rightOuterGuardTA, leftOuterGuardTA, bottomOuterGuardTA,
            rowTA, colTA, cTA, rTA, dm1TA]) _ rfl
      | exact derivWF_cast_type rfl (by
          simp only [Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]) _ rfl
          (by assumption)
      | exact derivWF_cast_type rfl (by
          simp only [SurfaceASTPublic.baseEntry, SurfaceASTPublic.recursiveEntry,
            SurfaceASTPublic.promotedBoundaryEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
            SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN,
            Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte, eq_mp_eq_cast,
            eq_mpr_eq_cast, cast_eq, band3, band4, le, orEqSucc, orEqPair,
            Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift,
            Nat.lt_irrefl, dite_false, dite_true,
            topOuterGuardTA, rightOuterGuardTA, leftOuterGuardTA, bottomOuterGuardTA,
            rowTA, colTA, cTA, rTA, dm1TA]) _ rfl (by assumption))

/-- The OBSTACLE-A-aware structural walk: like `wf_walk` but strips `cast` shells via
the explicit-simp `peel_cast` (avoiding the `rfl`-whnf blow-up).  Discharges the
`PurePauli`-lam-body leaf shapes (base peels); for the *recursive* peels the lam-body
leaf is supplied separately (see `recPeel_walk`). -/
macro "peel_walk" : tactic =>
  `(tactic|
    repeat first
      | assumption
      | exact True.intro
      | apply derivWF_eqPauliTrans'
      | apply derivWF_eqPauliSymm'
      | apply derivWF_stabAtClosedIteLamEqThen' _ _ _ _ ‹SFormula.PureNatTerm _›
      | apply derivWF_stabAtClosedIteLamEqElse' _ _ _ _ ‹SFormula.PureNatTerm _›
      | apply derivWF_pauliIteSelectThen'
      | apply derivWF_pauliIteSelectElse'
      | apply derivWF_pauliEqLit'
      | apply derivWF_contextWeakening'
      | refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?_ ?_
      | exact formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)
      | exact formulaDefined_stabAtClosedIteLam ‹SFormula.PureNatTerm _›
          (fun _ => by eval_tot) (by eval_tot)
      | peel_cast)

end QHL.CodeLang.Surface.Verify
