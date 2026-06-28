import QStab.QHL.Verify.SurfaceCodeLevelDefined
import QStab.QHL.Verify.SurfaceNormalizers

/-!
# `DerivWFA` for the two NORMALIZER code-level sub-trees (GROUP 2)

This file works towards `xNormScaffold_WF` / `zNormScaffold_WF`, the definedness
well-formedness witnesses for the symbolic `logicalX`/`logicalZ` normalizers
(`xNormCommuteSym` / `zNormCommuteSym`).  These are 2 of the 6 `codeLevel`
sub-trees consumed by the `codeLevelDefined` discharger through
`pfd_defined`/`pfda_defined`.

## Status (HONEST)

The reusable `DerivWFA`-combinator scaffolding is in place and the top-level walk
is reduced via the combinators to exactly two genuinely deep residuals:

* `rowEntryFlatSym_WF` — the flat row-entry totality.  `rowEntryFlatSym` composes
  `surfaceRowEntryCharSymbolicA` (recurses on `D.index`!) with
  `rowSymTreeFlatBridgeSym`.

  ### `m`-induction COLLAPSE (PROVEN)
  `surfaceRowEntryCharSymbolicA_WF` is the keystone's first conjunct.  Its `DerivWFA`
  is proved by a single `induction m` whose BODY IS SORRY-FREE: the BASE relays
  `baseRowConvergeA_WF`, the STEP relays the IH (the five inner sub-derivations'
  `DerivWFA`) through `recRowConvergeA_WF`.  No per-level multiplication of the leaf
  grind — the entire `m`-family reduces to the two FLAT (non-`m`-recursing) master
  helpers.  `recRowConvergeA_WF`'s `cut1`/`cut2` glue (relaying the five IH sub-
  derivations + the row-projection structure) is ALSO sorry-free.
  REMAINING (the genuine grind, flat in `m`): the two master cores'
  `DerivWF`/`DerivWFA` — `baseEntryMasterD` (base 7-level boolCases tree),
  `recEntryMasterD` (rec 7-level boolCases tree), and the `surfaceCodeRowSelectBase`
  / `surfaceCodeRowSelectRecursive` row-select sub-trees; plus the parallel
  `rowSymTreeFlatBridgeSym` / `recFlatMasterD` bridge induction.  Each is hundreds of
  LOC of bespoke closed-`Term.eval` discharge (the `baseLeafTreeTA` pauli-literal
  `ite`-trees are NOT `PureTerm`, so the uniform `…_closedPure` dischargers do not
  apply).  `rowEntryFlatSym_WF` now takes the row-projection witnesses (`hproj`,
  `hwit`) — the qubit-in-range side-data the binder range supplies in the consumers.
* the commutator leaves `commTwoAntiA` / `commTwoAntiB` / `commPointwiseSym` —
  each a deep `SFormula.Deriv` (with `colDispatchOnTrue` / `entryAtBound` /
  `logicalXOffColumnLocalCommutes` sub-trees).  Their `DerivWF` is large but does
  NOT recurse on `D.index`.  OPEN (residual #2).

Everything *between* these residuals (the cast/`allNatLtIntro`/`cut1`/`boolCases`
structure, the `pfdaAnd` bundle glue, AND the entire `m`-induction collapse) is
proved sorry-free below.
-/

namespace QHL.CodeLang.Surface.Verify

open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

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

/-! ## Per-peel / per-leaf `DerivWF` lemmas (BASE master leaves)

Each base peel/leaf is proved in ISOLATION (so the explicit-simp `peel_cast` runs once
per peel, not multiplied across the master's `repeat`).  The master then wires them with
explicit `boolCases` + `eqPauliTrans`/`eqPauliSymm` nodes — no global backtracking. -/

set_option maxHeartbeats 800000

/-! ### `baseEntry` head-`ite` definedness bridge (NO `codeSubstAt` whnf)

The base peels' stated type carries `codeSubstAt dT kT 1 baseEntry`.  Their
`DerivWF` leaf obligation is the `FormulaDefined` of the lam-body `ite`, and the
straightforward `formulaDefined_stabAtClosedIteLam … (by eval_tot)` forces the
elaborator to whnf-reduce `codeSubstAt … baseEntry` to expose its top `ite` — a
`WellFounded.fix` deep-unfold that blows up memory.

We avoid the whnf entirely: extract the three head children of `baseEntry` by a
cheap literal match, expose the head `ite` of `codeSubstAt … baseEntry` with the
single-step `codeSubstAt_ite` equation lemma, and discharge totality of the
*explicit head form* by rewriting it back to the `codeSubstAt` form (where the
banked `purePauli_codeSubstAt_one_eval_total` applies).  Every step is bounded;
no `codeSubstAt … baseEntry` is ever whnf-reduced. -/

-- NOTE: `codeSubstAt_ite`, `baseEntryCond`/`Then`/`Else`, `baseEntry_head_eq`, and
-- `codeSubstAt_one_baseEntry_head` are defined in `SurfaceRowCharacterizationSymbolic`
-- and imported here (not re-declared, to avoid duplicate-definition clashes).

/-- `baseEntry` (public-name view) is a pure Pauli tree. -/
theorem baseEntry_purePauli_public : PurePauli SurfaceASTPublic.baseEntry := by
  rw [← SurfaceASTPublic.baseEntry_eq_public]; exact baseEntry_purePauli

/-- Totality of the explicit head form of `codeSubstAt dT kT 1 baseEntry` at every
extended environment.  Proved by rewriting back to the `codeSubstAt` form (NO whnf)
and invoking the banked pure-Pauli totality closure. -/
theorem baseEntry_headForm_eval_total {arity : Nat} {dT kT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT)
    (cb : Term 2 .stab) (fuel : Nat) (rho : Env arity) (qv : Nat) :
    ∃ p, Term.eval cb fuel
        (Term.ite (codeSubstAt dT kT 1 baseEntryCond)
          (codeSubstAt dT kT 1 baseEntryThen) (codeSubstAt dT kT 1 baseEntryElse))
        (Env.cons qv rho) = some p := by
  rw [← codeSubstAt_one_baseEntry_head]
  exact purePauli_codeSubstAt_one_eval_total hd hk baseEntry_purePauli_public cb fuel
    (Env.cons qv rho)

/-- `FormulaDefined` of the `baseEntry` lam-body leaf, stated over the *explicit head
form* so it matches the base peels' unfolded goal **without** any `codeSubstAt` whnf.
This is the reusable leaf the base peels' `_WF` lemmas consume. -/
theorem formulaDefined_baseEntry_lam {arity : Nat} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    {dT kT qT : Term arity .nat} {rhs : Term arity .pauli}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hrhs : ∃ v, Term.eval cb fuel rhs rho = some v) :
    SFormula.Deriv.FormulaDefined cb fuel rho E
      (.eqPauli
        (.stabAt (SC.closed (.stabLam
          (Term.ite (codeSubstAt dT kT 1 baseEntryCond)
            (codeSubstAt dT kT 1 baseEntryThen) (codeSubstAt dT kT 1 baseEntryElse))))
          (SC.closed qT))
        (SC.closed rhs)) :=
  formulaDefined_stabAtClosedIteLam hq
    (fun qv => baseEntry_headForm_eval_total hd hk cb fuel rho qv) hrhs

/-- `baseEntryThen` (the bulk then-branch of `baseEntry`) is a pure Pauli tree —
extracted from `baseEntry`'s head `ite` purity (no re-derivation). -/
theorem baseEntryThen_purePauli : PurePauli baseEntryThen := by
  have h : PurePauli (Term.ite baseEntryCond baseEntryThen baseEntryElse) := by
    rw [← baseEntry_head_eq]; exact baseEntry_purePauli_public
  cases h with | ite _ ht _ => exact ht

/-- Totality of the selected then-branch RHS `instantiateTopNat qT (codeSubstAt 1 baseEntryThen)`
of the base bulk peels (`recBasePeelD_{Z,X,I}`).  Cheap: the instantiate-eval bridge to the
extended env, then the banked pure-Pauli `codeSubstAt` totality — never a deep `codeSubstAt`
whnf.  (Reusable `hrhs` discharger; replaces the `eval_tot` first-branch heavy failing match.) -/
theorem baseEntryThen_inst_eval_total {arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (cb : Term 2 .stab) (fuel : Nat) (rho : Env arity) :
    ∃ v, Term.eval cb fuel
        (Term.instantiateTopNat qT (codeSubstAt dT kT 1 baseEntryThen)) rho = some v := by
  obtain ⟨qv, hq0⟩ := hq.eval_total cb 0 rho
  have hqAll : ∀ f', Term.eval cb f' qT rho = some qv := fun f' => by
    rw [SFormula.PureNatTerm.eval_stable hq cb cb f' 0 rho]; exact hq0
  rw [Term.eval_instantiateTopNat (codeSubstAt dT kT 1 baseEntryThen) cb fuel hqAll]
  exact purePauli_codeSubstAt_one_eval_total hd hk baseEntryThen_purePauli cb fuel (Env.cons qv rho)

/-- `baseEntryElse` (the boundary else-branch of `baseEntry`) is a pure Pauli tree. -/
theorem baseEntryElse_purePauli : PurePauli baseEntryElse := by
  have h : PurePauli (Term.ite baseEntryCond baseEntryThen baseEntryElse) := by
    rw [← baseEntry_head_eq]; exact baseEntry_purePauli_public
  cases h with | ite _ _ he => exact he

/-- Totality of the selected else-branch RHS `instantiateTopNat qT (codeSubstAt 1 baseEntryElse)`
of the boundary peels (`recTop/Right/Left/Bottom*PeelD`).  Same cheap instantiate-eval bridge +
banked pure-Pauli totality as the then-branch version; never a deep `codeSubstAt` whnf. -/
theorem baseEntryElse_inst_eval_total {arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (cb : Term 2 .stab) (fuel : Nat) (rho : Env arity) :
    ∃ v, Term.eval cb fuel
        (Term.instantiateTopNat qT (codeSubstAt dT kT 1 baseEntryElse)) rho = some v := by
  obtain ⟨qv, hq0⟩ := hq.eval_total cb 0 rho
  have hqAll : ∀ f', Term.eval cb f' qT rho = some qv := fun f' => by
    rw [SFormula.PureNatTerm.eval_stable hq cb cb f' 0 rho]; exact hq0
  rw [Term.eval_instantiateTopNat (codeSubstAt dT kT 1 baseEntryElse) cb fuel hqAll]
  exact purePauli_codeSubstAt_one_eval_total hd hk baseEntryElse_purePauli cb fuel (Env.cons qv rho)

theorem recBasePeelD_Z_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hBand hKind} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wBand : DerivWF hBand cb fuel rho E)
    (wKind : DerivWF hKind cb fuel rho E) :
    DerivWF (recBasePeelD_Z (Γ := Γ) dT kT qT hq hBulk hBand hKind) cb fuel rho E := by
  -- The head-form `recBasePeelD_Z` keeps the lam body as
  -- `ite (codeSubstAt 1 baseEntryCond) (codeSubstAt 1 baseEntryThen) (codeSubstAt 1 baseEntryElse)`,
  -- so the combinator chain matches WITHOUT whnf-reducing `codeSubstAt … baseEntry`.  The
  -- `stabAtClosedIteLam` leaf is the reusable head-form bridge `formulaDefined_baseEntry_lam`
  -- (its body totality goes through `baseEntry_headForm_eval_total`, never a deep unfold);
  -- the selected then-branch totality (`hrhs`) is the bounded `eval_tot` discharger.
  -- Three `Eq.mpr` casts (head from `rw [codeSubstAt_one_baseEntry_head]`, the guard, the
  -- per-branch expansion), each peeled via `derivWF_cast_type` whose `A = A'` side-goal is the
  -- SAME bounded equation lemma the def used — so `codeSubstAt … baseEntry` is never whnf-reduced.
  unfold recBasePeelD_Z
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  refine derivWF_cast_type rfl (by rw [codeSubstAt_one_baseEntry_head]) _ _ ?_
  refine derivWF_eqPauliTrans'
    (derivWF_stabAtClosedIteLamEqThen' _ _ _ _ hq
      (derivWF_cast_type rfl (by rw [instantiateTopNat_codeSubstAt_one_baseEntryCond]) _ _ wBulk)
      (formulaDefined_baseEntry_lam hd hk hq (baseEntryThen_inst_eval_total hd hk hq cb fuel rho)))
    ?rest
  refine derivWF_cast_type rfl ?_ _ _ ?_
  · simp only [baseEntryThen, SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
      SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN, Term.weaken,
      Nat.reduceLT, Nat.reduceEqDiff, reduceDIte, eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq,
      band3, orEqSucc, orEqPair, Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]
  · exact derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectThen' _ _ _ wBand
        (formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)))
      (derivWF_pauliIteSelectThen' _ _ _ wKind
        (formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)))

theorem recBasePeelD_X_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hBand hKind} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wBand : DerivWF hBand cb fuel rho E)
    (wKind : DerivWF hKind cb fuel rho E) :
    DerivWF (recBasePeelD_X (Γ := Γ) dT kT qT hq hBulk hBand hKind) cb fuel rho E := by
  -- Same head-form bridge pattern as `recBasePeelD_Z_WF`; X selects the *else* kind branch.
  unfold recBasePeelD_X
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  refine derivWF_cast_type rfl (by rw [codeSubstAt_one_baseEntry_head]) _ _ ?_
  refine derivWF_eqPauliTrans'
    (derivWF_stabAtClosedIteLamEqThen' _ _ _ _ hq
      (derivWF_cast_type rfl (by rw [instantiateTopNat_codeSubstAt_one_baseEntryCond]) _ _ wBulk)
      (formulaDefined_baseEntry_lam hd hk hq (baseEntryThen_inst_eval_total hd hk hq cb fuel rho)))
    ?rest
  refine derivWF_cast_type rfl ?_ _ _ ?_
  · simp only [baseEntryThen, SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
      SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN, Term.weaken,
      Nat.reduceLT, Nat.reduceEqDiff, reduceDIte, eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq,
      band3, orEqSucc, orEqPair, Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]
  · exact derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectThen' _ _ _ wBand
        (formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)))
      (derivWF_pauliIteSelectElse' _ _ _ wKind
        (formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)))

theorem recBasePeelD_I_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hBand} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wBand : DerivWF hBand cb fuel rho E) :
    DerivWF (recBasePeelD_I (Γ := Γ) dT kT qT hq hBulk hBand) cb fuel rho E := by
  -- Same head-form bridge pattern; `→I` second part is a single `pauliIteSelectElse`.
  unfold recBasePeelD_I
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  refine derivWF_cast_type rfl (by rw [codeSubstAt_one_baseEntry_head]) _ _ ?_
  refine derivWF_eqPauliTrans'
    (derivWF_stabAtClosedIteLamEqThen' _ _ _ _ hq
      (derivWF_cast_type rfl (by rw [instantiateTopNat_codeSubstAt_one_baseEntryCond]) _ _ wBulk)
      (formulaDefined_baseEntry_lam hd hk hq (baseEntryThen_inst_eval_total hd hk hq cb fuel rho)))
    ?rest
  refine derivWF_cast_type rfl ?_ _ _ ?_
  · simp only [baseEntryThen, SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
      SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN, Term.weaken,
      Nat.reduceLT, Nat.reduceEqDiff, reduceDIte, eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq,
      band3, orEqSucc, orEqPair, Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]
  · exact derivWF_pauliIteSelectElse' _ _ _ wBand
      (formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp))

theorem recTopXPeelD_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hTopClass hTopBand} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity}
    {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wTopBand : DerivWF hTopBand cb fuel rho E) :
    DerivWF (recTopXPeelD (Γ := Γ) dT kT qT hq hBulk hTopClass hTopBand) cb fuel rho E := by
  -- EqElse head-form bridge: `else` branch (`baseEntryElse`), bulk=false guard, deeper chain.
  unfold recTopXPeelD
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  refine derivWF_cast_type rfl (by rw [codeSubstAt_one_baseEntry_head]) _ _ ?_
  refine derivWF_eqPauliTrans'
    (derivWF_stabAtClosedIteLamEqElse' _ _ _ _ hq
      (derivWF_cast_type rfl (by rw [instantiateTopNat_codeSubstAt_one_baseEntryCond]) _ _ wBulk)
      (formulaDefined_baseEntry_lam hd hk hq (baseEntryElse_inst_eval_total hd hk hq cb fuel rho)))
    ?rest
  refine derivWF_cast_type rfl ?_ _ _ ?_
  · simp only [baseEntryElse, SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
      SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN, Term.weaken,
      Nat.reduceLT, Nat.reduceEqDiff, reduceDIte, eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq,
      band3, orEqSucc, orEqPair, Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift,
      Nat.lt_irrefl, dite_false, dite_true]
  · exact derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectThen' _ _ _ wTopClass
        (formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)))
      (derivWF_eqPauliTrans'
        (derivWF_pauliIteSelectThen' _ _ _ wTopBand
          (formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)))
        (derivWF_pauliEqLit' _))

theorem recTopIPeelD_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hTopClass hTopBand} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity}
    {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wTopBand : DerivWF hTopBand cb fuel rho E) :
    DerivWF (recTopIPeelD (Γ := Γ) dT kT qT hq hBulk hTopClass hTopBand) cb fuel rho E := by
  -- EqElse head-form bridge; TopI chain: topClass(then) → topBand(else) → I.
  unfold recTopIPeelD
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  refine derivWF_cast_type rfl (by rw [codeSubstAt_one_baseEntry_head]) _ _ ?_
  refine derivWF_eqPauliTrans'
    (derivWF_stabAtClosedIteLamEqElse' _ _ _ _ hq
      (derivWF_cast_type rfl (by rw [instantiateTopNat_codeSubstAt_one_baseEntryCond]) _ _ wBulk)
      (formulaDefined_baseEntry_lam hd hk hq (baseEntryElse_inst_eval_total hd hk hq cb fuel rho)))
    ?rest
  refine derivWF_cast_type rfl ?_ _ _ ?_
  · simp only [baseEntryElse, SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
      SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN, Term.weaken,
      Nat.reduceLT, Nat.reduceEqDiff, reduceDIte, eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq,
      band3, orEqSucc, orEqPair, Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift,
      Nat.lt_irrefl, dite_false, dite_true]
  · exact derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectThen' _ _ _ wTopClass
        (formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)))
      (derivWF_pauliIteSelectElse' _ _ _ wTopBand
        (formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)))

theorem recRightZPeelD_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hTopClass hRightClass hRightBand} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity}
    {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wRightBand : DerivWF hRightBand cb fuel rho E) :
    DerivWF (recRightZPeelD (Γ := Γ) dT kT qT hq hBulk hTopClass hRightClass hRightBand)
      cb fuel rho E := by
  -- EqElse head-form bridge; RightZ chain: skip top(else) → right(then) → rightBand(then) → Z.
  unfold recRightZPeelD
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  refine derivWF_cast_type rfl (by rw [codeSubstAt_one_baseEntry_head]) _ _ ?_
  refine derivWF_eqPauliTrans'
    (derivWF_stabAtClosedIteLamEqElse' _ _ _ _ hq
      (derivWF_cast_type rfl (by rw [instantiateTopNat_codeSubstAt_one_baseEntryCond]) _ _ wBulk)
      (formulaDefined_baseEntry_lam hd hk hq (baseEntryElse_inst_eval_total hd hk hq cb fuel rho)))
    ?rest
  refine derivWF_cast_type rfl ?_ _ _ ?_
  · simp only [baseEntryElse, SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
      SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN, Term.weaken,
      Nat.reduceLT, Nat.reduceEqDiff, reduceDIte, eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq,
      band3, orEqSucc, orEqPair, Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift,
      Nat.lt_irrefl, dite_false, dite_true]
  · exact derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectElse' _ _ _ wTopClass
        (formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)))
      (derivWF_eqPauliTrans'
        (derivWF_pauliIteSelectThen' _ _ _ wRightClass
          (formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)))
        (derivWF_eqPauliTrans'
          (derivWF_pauliIteSelectThen' _ _ _ wRightBand
            (formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)))
          (derivWF_pauliEqLit' _)))

theorem recRightIPeelD_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hTopClass hRightClass hRightBand} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity}
    {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wRightBand : DerivWF hRightBand cb fuel rho E) :
    DerivWF (recRightIPeelD (Γ := Γ) dT kT qT hq hBulk hTopClass hRightClass hRightBand)
      cb fuel rho E := by
  -- EqElse head-form bridge; RightI chain: skip top(else) → right(then) → rightBand(else) → I.
  unfold recRightIPeelD
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  refine derivWF_cast_type rfl (by rw [codeSubstAt_one_baseEntry_head]) _ _ ?_
  refine derivWF_eqPauliTrans'
    (derivWF_stabAtClosedIteLamEqElse' _ _ _ _ hq
      (derivWF_cast_type rfl (by rw [instantiateTopNat_codeSubstAt_one_baseEntryCond]) _ _ wBulk)
      (formulaDefined_baseEntry_lam hd hk hq (baseEntryElse_inst_eval_total hd hk hq cb fuel rho)))
    ?rest
  refine derivWF_cast_type rfl ?_ _ _ ?_
  · simp only [baseEntryElse, SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
      SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN, Term.weaken,
      Nat.reduceLT, Nat.reduceEqDiff, reduceDIte, eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq,
      band3, orEqSucc, orEqPair, Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift,
      Nat.lt_irrefl, dite_false, dite_true]
  · exact derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectElse' _ _ _ wTopClass
        (formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)))
      (derivWF_eqPauliTrans'
        (derivWF_pauliIteSelectThen' _ _ _ wRightClass
          (formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)))
        (derivWF_pauliIteSelectElse' _ _ _ wRightBand
          (formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp))))

theorem recLeftZPeelD_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hTopClass hRightClass hLeftClass hLeftBand} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wLeftClass : DerivWF hLeftClass cb fuel rho E)
    (wLeftBand : DerivWF hLeftBand cb fuel rho E) :
    DerivWF (recLeftZPeelD (Γ := Γ) dT kT qT hq hBulk hTopClass hRightClass hLeftClass hLeftBand)
      cb fuel rho E := by
  -- EqElse head-form bridge; LeftZ chain: skip top,right(else) → left(then) → leftBand(then) → Z.
  unfold recLeftZPeelD
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  refine derivWF_cast_type rfl (by rw [codeSubstAt_one_baseEntry_head]) _ _ ?_
  refine derivWF_eqPauliTrans'
    (derivWF_stabAtClosedIteLamEqElse' _ _ _ _ hq
      (derivWF_cast_type rfl (by rw [instantiateTopNat_codeSubstAt_one_baseEntryCond]) _ _ wBulk)
      (formulaDefined_baseEntry_lam hd hk hq (baseEntryElse_inst_eval_total hd hk hq cb fuel rho)))
    ?rest
  refine derivWF_cast_type rfl ?_ _ _ ?_
  · simp only [baseEntryElse, SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
      SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN, Term.weaken,
      Nat.reduceLT, Nat.reduceEqDiff, reduceDIte, eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq,
      band3, orEqSucc, orEqPair, Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift,
      Nat.lt_irrefl, dite_false, dite_true]
  · exact derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectElse' _ _ _ wTopClass
        (formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)))
      (derivWF_eqPauliTrans'
        (derivWF_pauliIteSelectElse' _ _ _ wRightClass
          (formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)))
        (derivWF_eqPauliTrans'
          (derivWF_pauliIteSelectThen' _ _ _ wLeftClass
            (formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)))
          (derivWF_eqPauliTrans'
            (derivWF_pauliIteSelectThen' _ _ _ wLeftBand
              (formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)))
            (derivWF_pauliEqLit' _))))

theorem recLeftIPeelD_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hTopClass hRightClass hLeftClass hLeftBand} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wLeftClass : DerivWF hLeftClass cb fuel rho E)
    (wLeftBand : DerivWF hLeftBand cb fuel rho E) :
    DerivWF (recLeftIPeelD (Γ := Γ) dT kT qT hq hBulk hTopClass hRightClass hLeftClass hLeftBand)
      cb fuel rho E := by
  -- EqElse head-form bridge; LeftI chain: skip top,right(else) → left(then) → leftBand(else) → I.
  unfold recLeftIPeelD
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  refine derivWF_cast_type rfl (by rw [codeSubstAt_one_baseEntry_head]) _ _ ?_
  refine derivWF_eqPauliTrans'
    (derivWF_stabAtClosedIteLamEqElse' _ _ _ _ hq
      (derivWF_cast_type rfl (by rw [instantiateTopNat_codeSubstAt_one_baseEntryCond]) _ _ wBulk)
      (formulaDefined_baseEntry_lam hd hk hq (baseEntryElse_inst_eval_total hd hk hq cb fuel rho)))
    ?rest
  refine derivWF_cast_type rfl ?_ _ _ ?_
  · simp only [baseEntryElse, SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
      SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN, Term.weaken,
      Nat.reduceLT, Nat.reduceEqDiff, reduceDIte, eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq,
      band3, orEqSucc, orEqPair, Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift,
      Nat.lt_irrefl, dite_false, dite_true]
  · exact derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectElse' _ _ _ wTopClass
        (formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)))
      (derivWF_eqPauliTrans'
        (derivWF_pauliIteSelectElse' _ _ _ wRightClass
          (formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)))
        (derivWF_eqPauliTrans'
          (derivWF_pauliIteSelectThen' _ _ _ wLeftClass
            (formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)))
          (derivWF_pauliIteSelectElse' _ _ _ wLeftBand
            (formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)))))

theorem recBottomXPeelD_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hTopClass hRightClass hLeftClass hBottomBand} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wLeftClass : DerivWF hLeftClass cb fuel rho E)
    (wBottomBand : DerivWF hBottomBand cb fuel rho E) :
    DerivWF (recBottomXPeelD (Γ := Γ) dT kT qT hq hBulk hTopClass hRightClass hLeftClass hBottomBand)
      cb fuel rho E := by
  -- EqElse head-form bridge; BottomX chain: skip top,right,left(else) → bottomBand(then) → X.
  unfold recBottomXPeelD
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  refine derivWF_cast_type rfl (by rw [codeSubstAt_one_baseEntry_head]) _ _ ?_
  refine derivWF_eqPauliTrans'
    (derivWF_stabAtClosedIteLamEqElse' _ _ _ _ hq
      (derivWF_cast_type rfl (by rw [instantiateTopNat_codeSubstAt_one_baseEntryCond]) _ _ wBulk)
      (formulaDefined_baseEntry_lam hd hk hq (baseEntryElse_inst_eval_total hd hk hq cb fuel rho)))
    ?rest
  refine derivWF_cast_type rfl ?_ _ _ ?_
  · simp only [baseEntryElse, SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
      SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN, Term.weaken,
      Nat.reduceLT, Nat.reduceEqDiff, reduceDIte, eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq,
      band3, orEqSucc, orEqPair, Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift,
      Nat.lt_irrefl, dite_false, dite_true]
  · exact derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectElse' _ _ _ wTopClass
        (formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)))
      (derivWF_eqPauliTrans'
        (derivWF_pauliIteSelectElse' _ _ _ wRightClass
          (formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)))
        (derivWF_eqPauliTrans'
          (derivWF_pauliIteSelectElse' _ _ _ wLeftClass
            (formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)))
          (derivWF_eqPauliTrans'
            (derivWF_pauliIteSelectThen' _ _ _ wBottomBand
              (formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)))
            (derivWF_pauliEqLit' _))))

theorem recBottomIPeelD_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hTopClass hRightClass hLeftClass hBottomBand} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wLeftClass : DerivWF hLeftClass cb fuel rho E)
    (wBottomBand : DerivWF hBottomBand cb fuel rho E) :
    DerivWF (recBottomIPeelD (Γ := Γ) dT kT qT hq hBulk hTopClass hRightClass hLeftClass hBottomBand)
      cb fuel rho E := by
  -- EqElse head-form bridge; BottomI chain: skip top,right,left(else) → bottomBand(else) → I.
  unfold recBottomIPeelD
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  refine derivWF_cast_type rfl (by rw [codeSubstAt_one_baseEntry_head]) _ _ ?_
  refine derivWF_eqPauliTrans'
    (derivWF_stabAtClosedIteLamEqElse' _ _ _ _ hq
      (derivWF_cast_type rfl (by rw [instantiateTopNat_codeSubstAt_one_baseEntryCond]) _ _ wBulk)
      (formulaDefined_baseEntry_lam hd hk hq (baseEntryElse_inst_eval_total hd hk hq cb fuel rho)))
    ?rest
  refine derivWF_cast_type rfl ?_ _ _ ?_
  · simp only [baseEntryElse, SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
      SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN, Term.weaken,
      Nat.reduceLT, Nat.reduceEqDiff, reduceDIte, eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq,
      band3, orEqSucc, orEqPair, Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift,
      Nat.lt_irrefl, dite_false, dite_true]
  · exact derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectElse' _ _ _ wTopClass
        (formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)))
      (derivWF_eqPauliTrans'
        (derivWF_pauliIteSelectElse' _ _ _ wRightClass
          (formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)))
        (derivWF_eqPauliTrans'
          (derivWF_pauliIteSelectElse' _ _ _ wLeftClass
            (formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)))
          (derivWF_pauliIteSelectElse' _ _ _ wBottomBand
            (formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)))))

/-! ### Base-leaf `DerivWF` lemmas (pure `pauliIteSelect` chains over `baseLeafTreeTA`) -/

theorem leafBulkX_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hBand hKind} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wBand : DerivWF hBand cb fuel rho E)
    (wKind : DerivWF hKind cb fuel rho E) :
    DerivWF (leafBulkX (Γ := Γ) dT kT qT hBulk hBand hKind) cb fuel rho E := by
  unfold leafBulkX
  refine derivWF_eqPauliTrans'
    (derivWF_pauliIteSelectThen' _ _ _ wBulk ?_)
    (derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectThen' _ _ _ wBand ?_)
      (derivWF_pauliIteSelectElse' _ _ _ wKind ?_)) <;>
    exact formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)

theorem leafBulkI_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hBand} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wBand : DerivWF hBand cb fuel rho E) :
    DerivWF (leafBulkI (Γ := Γ) dT kT qT hBulk hBand) cb fuel rho E := by
  unfold leafBulkI
  refine derivWF_eqPauliTrans'
    (derivWF_pauliIteSelectThen' _ _ _ wBulk ?_)
    (derivWF_pauliIteSelectElse' _ _ _ wBand ?_) <;>
    exact formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)

theorem leafTopX_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hTopClass hTopBand} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity}
    {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wTopBand : DerivWF hTopBand cb fuel rho E) :
    DerivWF (leafTopX (Γ := Γ) dT kT qT hBulk hTopClass hTopBand) cb fuel rho E := by
  unfold leafTopX
  refine derivWF_eqPauliTrans'
    (derivWF_pauliIteSelectElse' _ _ _ wBulk ?_)
    (derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectThen' _ _ _ wTopClass ?_)
      (derivWF_pauliIteSelectThen' _ _ _ wTopBand ?_)) <;>
    exact formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)

theorem leafTopI_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hTopClass hTopBand} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity}
    {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wTopBand : DerivWF hTopBand cb fuel rho E) :
    DerivWF (leafTopI (Γ := Γ) dT kT qT hBulk hTopClass hTopBand) cb fuel rho E := by
  unfold leafTopI
  refine derivWF_eqPauliTrans'
    (derivWF_pauliIteSelectElse' _ _ _ wBulk ?_)
    (derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectThen' _ _ _ wTopClass ?_)
      (derivWF_pauliIteSelectElse' _ _ _ wTopBand ?_)) <;>
    exact formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)

theorem leafRightZ_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hTopClass hRightClass hRightBand} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity}
    {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wRightBand : DerivWF hRightBand cb fuel rho E) :
    DerivWF (leafRightZ (Γ := Γ) dT kT qT hBulk hTopClass hRightClass hRightBand) cb fuel rho E := by
  unfold leafRightZ
  refine derivWF_eqPauliTrans'
    (derivWF_pauliIteSelectElse' _ _ _ wBulk ?_)
    (derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectElse' _ _ _ wTopClass ?_)
      (derivWF_eqPauliTrans'
        (derivWF_pauliIteSelectThen' _ _ _ wRightClass ?_)
        (derivWF_pauliIteSelectThen' _ _ _ wRightBand ?_))) <;>
    exact formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)

theorem leafRightI_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hTopClass hRightClass hRightBand} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity}
    {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wRightBand : DerivWF hRightBand cb fuel rho E) :
    DerivWF (leafRightI (Γ := Γ) dT kT qT hBulk hTopClass hRightClass hRightBand) cb fuel rho E := by
  unfold leafRightI
  refine derivWF_eqPauliTrans'
    (derivWF_pauliIteSelectElse' _ _ _ wBulk ?_)
    (derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectElse' _ _ _ wTopClass ?_)
      (derivWF_eqPauliTrans'
        (derivWF_pauliIteSelectThen' _ _ _ wRightClass ?_)
        (derivWF_pauliIteSelectElse' _ _ _ wRightBand ?_))) <;>
    exact formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)

theorem leafLeftZ_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hTopClass hRightClass hLeftClass hLeftBand} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wLeftClass : DerivWF hLeftClass cb fuel rho E)
    (wLeftBand : DerivWF hLeftBand cb fuel rho E) :
    DerivWF (leafLeftZ (Γ := Γ) dT kT qT hBulk hTopClass hRightClass hLeftClass hLeftBand)
      cb fuel rho E := by
  unfold leafLeftZ
  refine derivWF_eqPauliTrans'
    (derivWF_pauliIteSelectElse' _ _ _ wBulk ?_)
    (derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectElse' _ _ _ wTopClass ?_)
      (derivWF_eqPauliTrans'
        (derivWF_pauliIteSelectElse' _ _ _ wRightClass ?_)
        (derivWF_eqPauliTrans'
          (derivWF_pauliIteSelectThen' _ _ _ wLeftClass ?_)
          (derivWF_pauliIteSelectThen' _ _ _ wLeftBand ?_)))) <;>
    exact formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)

theorem leafLeftI_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hTopClass hRightClass hLeftClass hLeftBand} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wLeftClass : DerivWF hLeftClass cb fuel rho E)
    (wLeftBand : DerivWF hLeftBand cb fuel rho E) :
    DerivWF (leafLeftI (Γ := Γ) dT kT qT hBulk hTopClass hRightClass hLeftClass hLeftBand)
      cb fuel rho E := by
  unfold leafLeftI
  refine derivWF_eqPauliTrans'
    (derivWF_pauliIteSelectElse' _ _ _ wBulk ?_)
    (derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectElse' _ _ _ wTopClass ?_)
      (derivWF_eqPauliTrans'
        (derivWF_pauliIteSelectElse' _ _ _ wRightClass ?_)
        (derivWF_eqPauliTrans'
          (derivWF_pauliIteSelectThen' _ _ _ wLeftClass ?_)
          (derivWF_pauliIteSelectElse' _ _ _ wLeftBand ?_)))) <;>
    exact formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)

theorem leafBottomX_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hTopClass hRightClass hLeftClass hBottomBand} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wLeftClass : DerivWF hLeftClass cb fuel rho E)
    (wBottomBand : DerivWF hBottomBand cb fuel rho E) :
    DerivWF (leafBottomX (Γ := Γ) dT kT qT hBulk hTopClass hRightClass hLeftClass hBottomBand)
      cb fuel rho E := by
  unfold leafBottomX
  refine derivWF_eqPauliTrans'
    (derivWF_pauliIteSelectElse' _ _ _ wBulk ?_)
    (derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectElse' _ _ _ wTopClass ?_)
      (derivWF_eqPauliTrans'
        (derivWF_pauliIteSelectElse' _ _ _ wRightClass ?_)
        (derivWF_eqPauliTrans'
          (derivWF_pauliIteSelectElse' _ _ _ wLeftClass ?_)
          (derivWF_pauliIteSelectThen' _ _ _ wBottomBand ?_)))) <;>
    exact formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)

theorem leafBottomI_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hTopClass hRightClass hLeftClass hBottomBand} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wLeftClass : DerivWF hLeftClass cb fuel rho E)
    (wBottomBand : DerivWF hBottomBand cb fuel rho E) :
    DerivWF (leafBottomI (Γ := Γ) dT kT qT hBulk hTopClass hRightClass hLeftClass hBottomBand)
      cb fuel rho E := by
  unfold leafBottomI
  refine derivWF_eqPauliTrans'
    (derivWF_pauliIteSelectElse' _ _ _ wBulk ?_)
    (derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectElse' _ _ _ wTopClass ?_)
      (derivWF_eqPauliTrans'
        (derivWF_pauliIteSelectElse' _ _ _ wRightClass ?_)
        (derivWF_eqPauliTrans'
          (derivWF_pauliIteSelectElse' _ _ _ wLeftClass ?_)
          (derivWF_pauliIteSelectElse' _ _ _ wBottomBand ?_)))) <;>
    exact formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)

/-! ## Base master `DerivWF` — assembled from the per-peel/per-leaf lemmas

The master's 5-deep `boolCases` tree is wired explicitly (each guard bool-eval is total,
`sterm_eval_closedPure`); every leaf is `eqPauliTrans (peel) (eqPauliSymm (leaf))`, whose
`DerivWF` is `⟨peel_WF, leaf_WF⟩`.  The peels/leaves carry `.hyp` guard children, whose
`DerivWF` is `True.intro`.  Built from the isolated lemmas — NO global `peel_walk` over
the whole master (that re-runs the explicit-simp cast strip per node and blows up). -/
theorem baseEntryMasterD_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer} :
    DerivWF (baseEntryMasterD (Γ := Γ) dT kT qT hq) cb fuel rho E := by
  unfold baseEntryMasterD
  refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?bulkT ?bulkF
  case bulkT =>
    refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?bandT ?bandF
    case bandT =>
      refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?kindT ?kindF
      case kindT =>
        exact derivWF_eqPauliTrans' (recBasePeelD_Z_WF _ _ _ _ hd hk hq True.intro True.intro True.intro)
          (derivWF_eqPauliSymm' (leafZ_WF _ _ _ hd hk hq True.intro True.intro True.intro))
      case kindF =>
        exact derivWF_eqPauliTrans' (recBasePeelD_X_WF _ _ _ _ hd hk hq True.intro True.intro True.intro)
          (derivWF_eqPauliSymm' (leafBulkX_WF _ _ _ _ hd hk hq True.intro True.intro True.intro))
    case bandF =>
      exact derivWF_eqPauliTrans' (recBasePeelD_I_WF _ _ _ _ hd hk hq True.intro True.intro)
        (derivWF_eqPauliSymm' (leafBulkI_WF _ _ _ _ hd hk hq True.intro True.intro))
  case bulkF =>
    refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?tcT ?tcF
    case tcT =>
      refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?tbT ?tbF
      case tbT =>
        exact derivWF_eqPauliTrans' (recTopXPeelD_WF _ _ _ _ hd hk hq True.intro True.intro True.intro)
          (derivWF_eqPauliSymm' (leafTopX_WF _ _ _ _ hd hk hq True.intro True.intro True.intro))
      case tbF =>
        exact derivWF_eqPauliTrans' (recTopIPeelD_WF _ _ _ _ hd hk hq True.intro True.intro True.intro)
          (derivWF_eqPauliSymm' (leafTopI_WF _ _ _ _ hd hk hq True.intro True.intro True.intro))
    case tcF =>
      refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?rcT ?rcF
      case rcT =>
        refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?rbT ?rbF
        case rbT =>
          exact derivWF_eqPauliTrans'
            (recRightZPeelD_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro)
            (derivWF_eqPauliSymm'
              (leafRightZ_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro))
        case rbF =>
          exact derivWF_eqPauliTrans'
            (recRightIPeelD_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro)
            (derivWF_eqPauliSymm'
              (leafRightI_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro))
      case rcF =>
        refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?lcT ?lcF
        case lcT =>
          refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?lbT ?lbF
          case lbT =>
            exact derivWF_eqPauliTrans'
              (recLeftZPeelD_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro True.intro)
              (derivWF_eqPauliSymm'
                (leafLeftZ_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro True.intro))
          case lbF =>
            exact derivWF_eqPauliTrans'
              (recLeftIPeelD_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro True.intro)
              (derivWF_eqPauliSymm'
                (leafLeftI_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro True.intro))
        case lcF =>
          refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?bbT ?bbF
          case bbT =>
            exact derivWF_eqPauliTrans'
              (recBottomXPeelD_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro True.intro)
              (derivWF_eqPauliSymm'
                (leafBottomX_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro True.intro))
          case bbF =>
            exact derivWF_eqPauliTrans'
              (recBottomIPeelD_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro True.intro)
              (derivWF_eqPauliSymm'
                (leafBottomI_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro True.intro))

/-- `DerivWF` of `baseLeafSelfEq` (the roundabout reflexivity `baseLeafTreeTA = baseLeafTreeTA`):
same 7-level boolCases structure as `baseEntryMasterD_WF`, but each leaf is `leafX / leafX`
(no peel side).  Consumed by `recFallbackPeelD_WF` / `baseBoundaryStripD_WF`. -/
theorem baseLeafSelfEq_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer} :
    DerivWF (baseLeafSelfEq (Γ := Γ) dT kT qT) cb fuel rho E := by
  unfold baseLeafSelfEq
  refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?bulkT ?bulkF
  case bulkT =>
    refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?bandT ?bandF
    case bandT =>
      refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?kindT ?kindF
      case kindT =>
        exact derivWF_eqPauliTrans' (leafZ_WF _ _ _ hd hk hq True.intro True.intro True.intro)
          (derivWF_eqPauliSymm' (leafZ_WF _ _ _ hd hk hq True.intro True.intro True.intro))
      case kindF =>
        exact derivWF_eqPauliTrans' (leafBulkX_WF _ _ _ _ hd hk hq True.intro True.intro True.intro)
          (derivWF_eqPauliSymm' (leafBulkX_WF _ _ _ _ hd hk hq True.intro True.intro True.intro))
    case bandF =>
      exact derivWF_eqPauliTrans' (leafBulkI_WF _ _ _ _ hd hk hq True.intro True.intro)
        (derivWF_eqPauliSymm' (leafBulkI_WF _ _ _ _ hd hk hq True.intro True.intro))
  case bulkF =>
    refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?tcT ?tcF
    case tcT =>
      refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?tbT ?tbF
      case tbT =>
        exact derivWF_eqPauliTrans' (leafTopX_WF _ _ _ _ hd hk hq True.intro True.intro True.intro)
          (derivWF_eqPauliSymm' (leafTopX_WF _ _ _ _ hd hk hq True.intro True.intro True.intro))
      case tbF =>
        exact derivWF_eqPauliTrans' (leafTopI_WF _ _ _ _ hd hk hq True.intro True.intro True.intro)
          (derivWF_eqPauliSymm' (leafTopI_WF _ _ _ _ hd hk hq True.intro True.intro True.intro))
    case tcF =>
      refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?rcT ?rcF
      case rcT =>
        refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?rbT ?rbF
        case rbT =>
          exact derivWF_eqPauliTrans'
            (leafRightZ_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro)
            (derivWF_eqPauliSymm'
              (leafRightZ_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro))
        case rbF =>
          exact derivWF_eqPauliTrans'
            (leafRightI_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro)
            (derivWF_eqPauliSymm'
              (leafRightI_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro))
      case rcF =>
        refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?lcT ?lcF
        case lcT =>
          refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?lbT ?lbF
          case lbT =>
            exact derivWF_eqPauliTrans'
              (leafLeftZ_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro True.intro)
              (derivWF_eqPauliSymm'
                (leafLeftZ_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro True.intro))
          case lbF =>
            exact derivWF_eqPauliTrans'
              (leafLeftI_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro True.intro)
              (derivWF_eqPauliSymm'
                (leafLeftI_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro True.intro))
        case lcF =>
          refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?bbT ?bbF
          case bbT =>
            exact derivWF_eqPauliTrans'
              (leafBottomX_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro True.intro)
              (derivWF_eqPauliSymm'
                (leafBottomX_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro True.intro))
          case bbF =>
            exact derivWF_eqPauliTrans'
              (leafBottomI_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro True.intro)
              (derivWF_eqPauliSymm'
                (leafBottomI_WF _ _ _ _ hd hk hq True.intro True.intro True.intro True.intro True.intro))

set_option maxHeartbeats 400000

/-! ## STEP 0 — `RecEvalData`: the per-level rec-eval side-data bundle

The recursive peels (`recInteriorPeelD` / `rec*PromotedPeelD` / …) bottom out at a
`stabAtClosedIteLam` node whose lam body is `codeSubstAt dT kT 1 recursiveEntry` —
the recursive entry with the *symbolic* distance/index `dT`/`kT` substituted.  This
body is NOT `PurePauli` (it contains `recCall`), so the uniform `eval_tot` discharger
does not apply.  Its totality is supplied by `recPeelLamBody_eval_total`
(SurfaceRecConvergence), which needs: `dT`/`kT` evaluate to constants `dv`/`kv` at
*every* fuel, `2 ≤ dv`, and `InnerTotal f' dv` (the inner code converges).  We bundle
exactly these facts in `RecEvalData`. -/

/-- A pure nat term evaluates to the *same* value at every fuel (pure terms ignore
fuel — they contain no `recCall`).  The "all-fuel" form of `PureNatTerm.eval_total`,
needed for the `hdAll`/`hkAll` hypotheses of `recPeelLamBody_eval_total`. -/
theorem pureNatTerm_eval_total_allFuel {arity : Nat} {x : Term arity .nat}
    (hx : SFormula.PureNatTerm x) (cb : Term 2 .stab) (rho : Env arity) :
    ∃ xv, ∀ fuel, Term.eval cb fuel x rho = some xv := by
  obtain ⟨xv, hxv⟩ := hx.eval_total cb 0 rho
  exact ⟨xv, fun fuel => by rw [SFormula.PureNatTerm.eval_stable hx cb cb fuel 0 rho]; exact hxv⟩

/-- The per-level recursive-eval side-data, at the rec master's fuel `f' + 1`.

Bundles everything `recPeelLamBody_eval_total` and `RecOk.eval_total` need to
discharge the `stabAtClosedIteLam` lam-body and the substituted-recursiveEntry RHS:

* `dv`/`kv` — the constant values `dT`/`kT` evaluate to (`hdAll`/`hkAll`, all fuel);
* `2 ≤ dv` — the recursion's distance floor;
* `InnerTotal f' dv` — the inner code converges up to `nQubits (dv-2)`.

`dv = oddDistance m = 2m+3` and `InnerTotal f' (2m+3)` are supplied automatically by
the `DistAtA` structure + `codeEntry_total`; `kv` from any pure `kT`. -/
structure RecEvalData {arity : Nat} (dT kT : Term arity .nat) (f' : Nat)
    (rho : Env arity) where
  dv : Nat
  kv : Nat
  hdAll : ∀ fuel, Term.eval Surface.code.body fuel dT rho = some dv
  hkAll : ∀ fuel, Term.eval Surface.code.body fuel kT rho = some kv
  hd2 : 2 ≤ dv
  hinner : InnerTotal f' dv

/-- The keystone lam-body totality, repackaged from a `RecEvalData`.  Discharges the
`hbody` premise of `formulaDefined_stabAtClosedIteLam` for the recursive peels (the
non-`PurePauli` lam body `codeSubstAt dT kT 1 recursiveEntry`). -/
theorem RecEvalData.lamBody_total {arity : Nat} {dT kT : Term arity .nat} {f' : Nat}
    {rho : Env arity} (R : RecEvalData dT kT f' rho) (qv : Nat) :
    ∃ p, Term.eval Surface.code.body (f' + 1)
        (QHL.CodeLang.Verify.codeSubstAt dT kT 1 Surface.recursiveEntry)
        (Env.cons qv rho) = some p :=
  recPeelLamBody_eval_total R.hd2 R.hdAll R.hkAll R.hinner qv

/-- The substituted-recursiveEntry term `codeSubstAt dT kT 1 recursiveEntry` evaluates
to `some` at `Env.cons qv rho` (the `stabAt`-applied form of the lam-body totality).
This is `RecOk.codeSubstAt_one_eval_eq` + `RecOk.eval_total`, repackaged. -/
theorem RecEvalData.recEntrySubst_total {arity : Nat} {dT kT : Term arity .nat} {f' : Nat}
    {rho : Env arity} (R : RecEvalData dT kT f' rho) (fuel qv : Nat) :
    ∃ p, Term.eval Surface.code.body (f' + 1)
        (QHL.CodeLang.Verify.codeSubstAt dT kT 1 Surface.recursiveEntry)
        (Env.cons qv rho) = some p :=
  R.lamBody_total qv

/-- **STEP 2 core (generalized totality).**  For *any* `RecOk`-certified subtree `t'`
of the recursive entry, `codeSubstAt dT kT 1 t'` is eval-total at `Env.cons qv rho`.
Generalizes `recPeelLamBody_eval_total` from `recursiveEntry` to its `RecOk` subtrees
(needed for the rec peels' RHS / `pauliIteSelect` branch obligations, which select
sub-`ite`s of the recursive entry).  The reusable rec-side analogue of
`purePauli_codeSubstAt_one_eval_total`. -/
theorem RecEvalData.recOkSubst_total {arity : Nat} {dT kT : Term arity .nat} {f' : Nat}
    {rho : Env arity} (R : RecEvalData dT kT f' rho)
    {t' : Term 3 .pauli} (ht' : RecOk t') (qv : Nat) :
    ∃ p, Term.eval Surface.code.body (f' + 1)
        (QHL.CodeLang.Verify.codeSubstAt dT kT 1 t') (Env.cons qv rho) = some p := by
  rw [ht'.codeSubstAt_one_eval_eq Surface.code.body (f' + 1) R.hdAll R.hkAll (qv := qv)]
  exact ht'.eval_total (k := R.kv) (q := qv) R.hd2 R.hinner

/-- **STEP 2 core (instantiated form).**  `instantiateTopNat qT (codeSubstAt dT kT 1 t')`
evaluates at `rho`, for any `RecOk` subtree `t'`, given `qT` evaluates to `qv` at every
fuel.  By the public eval-bridge `Term.eval_instantiateTopNat`, this equals the opened
substituted subtree, total by `recOkSubst_total`.  This discharges the rec peels'
`instantiateTopNat`-RHS `FormulaDefined` obligations. -/
theorem RecEvalData.instRecOkSubst_total {arity : Nat} {dT kT qT : Term arity .nat} {f' : Nat}
    {rho : Env arity} (R : RecEvalData dT kT f' rho)
    {qv : Nat} (hqAll : ∀ fuel, Term.eval Surface.code.body fuel qT rho = some qv)
    {t' : Term 3 .pauli} (ht' : RecOk t') :
    ∃ p, Term.eval Surface.code.body (f' + 1)
        (Term.instantiateTopNat qT (QHL.CodeLang.Verify.codeSubstAt dT kT 1 t')) rho = some p := by
  rw [Term.eval_instantiateTopNat _ Surface.code.body (f' + 1) hqAll]
  exact R.recOkSubst_total ht' qv

/-- Build a `RecEvalData` at the rec master's distance index, from a `DistAtA arity (m+1)`
(supplying `dT` → `oddDistance (m+1)` at all fuels) and any pure `kT`.  The
`InnerTotal` and `2 ≤ dv` facts come from `codeEntry_total` / the `oddDistance`
definition; the rec master runs at fuel `f' + 1` with `f' = 2*(m+1)+3` (`= bridge
fuel - 1`), comfortably covering the recursion depth `m+1`. -/
noncomputable def recEvalData_of_DistAtA {arity : Nat} {m : Nat} (DD : DistAtA arity (m + 1))
    {kT : Term arity .nat} (hk : SFormula.PureNatTerm kT) (rho : Env arity) {f' : Nat}
    (hf' : m + 1 ≤ f') :
    RecEvalData DD.dT kT f' rho := by
  have h := pureNatTerm_eval_total_allFuel hk Surface.code.body rho
  refine
    { dv := oddDistance (m + 1)
      kv := h.choose
      hdAll := fun fuel => DD.evalsTo rho
      hkAll := h.choose_spec
      hd2 := by simp only [oddDistance]; omega
      hinner := ?_ }
  -- `InnerTotal f' (oddDistance (m+1))`: the inner code at distance `oddDistance(m+1)-2`
  -- converges up to `nQubits` via `codeEntry_total`.
  intro Kv qv hqv
  have hd2 : oddDistance (m + 1) - 2 = 2 * m + 3 := by simp only [oddDistance]; omega
  rw [hd2] at hqv ⊢
  exact codeEntry_total m Kv f' hf' qv hqv

/-! ## STEP 2 — the rec-peel lam-node FormulaDefined discharger

The recursive peels' first node is `stabAtClosedIteLamEqThen cond thenP elseP qT`
whose `DerivWF` carries a `FormulaDefined` obligation of the shape
`eqPauli (stabAt (closed (stabLam (ite cond thenP elseP))) (closed qT))
        (closed (instantiateTopNat qT thenP))`,
where `ite cond thenP elseP` is the unfolded `codeSubstAt dT kT 1 recursiveEntry`
(the peel's `simp only` unfolds it definitionally).  Both totality premises of
`formulaDefined_stabAtClosedIteLam` are discharged from a `RecEvalData`:

* `hbody`  — the lam body `codeSubstAt dT kT 1 recursiveEntry` is total at every
  extended env, via `RecEvalData.lamBody_total` (defeq to the unfolded body);
* `hrhs`  — `instantiateTopNat qT thenP` evaluates: by the public eval-bridge
  `Term.eval_instantiateTopNat`, it equals the lam body opened at `qv = eval qT`,
  hence total by `RecEvalData.lamBody_total`. -/

/-- `FormulaDefined` for a rec-peel `stabAtClosedIteLam` node whose lam body is
(definitionally) `codeSubstAt dT kT 1 recursiveEntry`.  Both sides total via
`RecEvalData`.  `hbodyEq`/`hrhsEq` are the (peel-supplied) definitional identities
identifying the normalized `ite cond thenP elseP` body with `codeSubstAt …
recursiveEntry`, and the normalized RHS `instantiateTopNat qT thenP` with the
opened lam body. -/
theorem recPeel_lamFD {arity : Nat} {cb : Term 2 .stab} {f' : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    {cond : Term (arity + 1) .bool} {thenP elseP : Term (arity + 1) .pauli}
    {qT : Term arity .nat} {rhs : Term arity .pauli}
    (hq : SFormula.PureNatTerm qT)
    (hbody : ∀ qv, ∃ p, Term.eval Surface.code.body (f' + 1)
      (.ite cond thenP elseP) (Env.cons qv rho) = some p)
    (hrhs : ∃ v, Term.eval Surface.code.body (f' + 1) rhs rho = some v) :
    SFormula.Deriv.FormulaDefined Surface.code.body (f' + 1) rho E
      (.eqPauli (.stabAt (SC.closed (.stabLam (.ite cond thenP elseP))) (SC.closed qT))
        (SC.closed rhs)) :=
  formulaDefined_stabAtClosedIteLam hq hbody hrhs

/-! ## STEP 3 — rec-leaf `pauliIteSelect` dischargers (over `recLeafTreeTA`)

The rec leaves (`recLeafInt`/…/`recLeafBoundary`) are pure `pauliIteSelect` chains
over `recLeafTreeTA dT kT qT pInt pTop pRight pLeft pBottom`, whose *recursing* leaves
are the free IH paulis `pInt…pBottom`.  Each `pauliIteSelectThen/Else cond p1 p2` node
needs `FormulaDefined (eqPauli (ite cond p1 p2) p1/p2)`, i.e. totality of the `ite`
branches.  The pure branches close by `leaf_pp`; the `pInt…pBottom` branches need their
totality supplied (from the IH `DerivWFA` in the master).  The helpers below build the
`ite`-eval totality from the branch totalities. -/

/-- `eval (ite cond p1 p2)` is total from totality of the (pure-bool) guard and both
branches. -/
theorem eval_ite_pauli_total {arity : Nat} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {cond : Term arity .bool} {p1 p2 : Term arity .pauli}
    (hc : ∃ cv, Term.eval cb fuel cond rho = some cv)
    (h1 : ∃ v, Term.eval cb fuel p1 rho = some v)
    (h2 : ∃ v, Term.eval cb fuel p2 rho = some v) :
    ∃ v, Term.eval cb fuel (.ite cond p1 p2) rho = some v := by
  obtain ⟨cv, hcv⟩ := hc; obtain ⟨v1, hv1⟩ := h1; obtain ⟨v2, hv2⟩ := h2
  cases cv with
  | false => exact ⟨v2, by simp [Term.eval, hcv, hv2]⟩
  | true => exact ⟨v1, by simp [Term.eval, hcv, hv1]⟩

/-- `FormulaDefined (eqPauli (ite cond p1 p2) p1)` (the `pauliIteSelectThen` obligation)
from totality of guard + both branches. -/
theorem formulaDefined_iteSelectThen {arity : Nat} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    {cond : Term arity .bool} {p1 p2 : Term arity .pauli}
    (hc : ∃ cv, Term.eval cb fuel cond rho = some cv)
    (h1 : ∃ v, Term.eval cb fuel p1 rho = some v)
    (h2 : ∃ v, Term.eval cb fuel p2 rho = some v) :
    SFormula.Deriv.FormulaDefined cb fuel rho E
      (.eqPauli (SC.closed (.ite cond p1 p2)) (SC.closed p1)) :=
  formulaDefined_eqPauli_closed (eval_ite_pauli_total hc h1 h2) h1

/-- `FormulaDefined (eqPauli (ite cond p1 p2) p2)` (the `pauliIteSelectElse` obligation). -/
theorem formulaDefined_iteSelectElse {arity : Nat} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    {cond : Term arity .bool} {p1 p2 : Term arity .pauli}
    (hc : ∃ cv, Term.eval cb fuel cond rho = some cv)
    (h1 : ∃ v, Term.eval cb fuel p1 rho = some v)
    (h2 : ∃ v, Term.eval cb fuel p2 rho = some v) :
    SFormula.Deriv.FormulaDefined cb fuel rho E
      (.eqPauli (SC.closed (.ite cond p1 p2)) (SC.closed p2)) :=
  formulaDefined_eqPauli_closed (eval_ite_pauli_total hc h1 h2) h2

/-- Totality of `baseLeafTreeTA` (a `PurePauli` tree) at any env. -/
theorem baseLeafTreeTA_eval_total {arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (cb : Term 2 .stab) (fuel : Nat) (rho : Env arity) :
    ∃ v, Term.eval cb fuel (baseLeafTreeTA dT kT qT) rho = some v :=
  (baseLeafTreeTA_purePauli hd hk hq).eval_total cb fuel rho

/-- A `recLeafTreeTA`-guard / cell-guard is a `PureBoolTerm` when the index terms are
pure.  Discharged by unfolding the guard sugar and running `pure_tree`. -/
theorem recLeafGuard_eval_total {arity : Nat} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {cond : Term arity .bool} (hc : SFormula.PureBoolTerm cond) :
    ∃ cv, Term.eval cb fuel cond rho = some cv :=
  hc.eval_total cb fuel rho

/-- Lean guard/pauli-leaf purity prover for `rec_leaf_tot`: identical to `leaf_pp` but
WITHOUT the two giant tree defs `baseLeafTreeTA`/`recLeafTreeTA` in the simp set.  The
cell/outer guards never mention those trees, so unfolding them at every one of the
~20-40 `ite` nodes per rec leaf is pure waste — and `simp only [recLeafTreeTA]` building
the giant equational lemma at each node is exactly the >12 GB blowup.  Dropping them
keeps each per-node purity proof bounded. -/
macro "guard_pp" : tactic =>
  `(tactic|
    (try simp only [bulkGuardTA, bulkCountTA, dm1TA,
        baseBulkBandGuardTA, baseKindGuardTA, rTA, cTA, gridIdx, topClassGuardTA, baseBTA,
        baseHalfTA, topBandGuardTA, rightClassGuardTA, rightBandGuardTA, leftClassGuardTA,
        leftBandGuardTA, bottomBandGuardTA, lastCellTA, interiorCellGuardTA, insideGuardTA,
        topCellGuardTA, rightCellGuardTA, leftCellGuardTA, bottomCellGuardTA, rowTA, colTA,
        topOuterGuardTA, rightOuterGuardTA, leftOuterGuardTA, bottomOuterGuardTA,
        band3, band4, orEqSucc, orEqPair, le]
     pure_tree <;> assumption))

/-- Structural totality witness for a pauli term (cf. `PurePauli` / `RecOk`): built from
pure subterms (`pure`), arbitrary already-total leaves (`atom` — e.g. the IH paulis
`pInt…pBottom`), and `ite` nodes over total guards.  Crucially it is recursed via `apply`
(head-constructor match), so building it over the giant `recLeafTreeTA` is bounded —
unlike a direct `eval_ite_pauli_total` recursion, whose `refine`-unification whnf-reduces
`Term.eval` over the whole subtree (the >12 GB interpreter blowup). -/
inductive EvalTotalTree {arity : Nat} (cb : Term 2 .stab) (fuel : Nat) (rho : Env arity) :
    Term arity .pauli → Prop where
  | pure {x : Term arity .pauli} : PurePauli x → EvalTotalTree cb fuel rho x
  | atom {x : Term arity .pauli} :
      (∃ v, Term.eval cb fuel x rho = some v) → EvalTotalTree cb fuel rho x
  | ite {c : Term arity .bool} {a b : Term arity .pauli} :
      (∃ cv, Term.eval cb fuel c rho = some cv) →
      EvalTotalTree cb fuel rho a → EvalTotalTree cb fuel rho b →
      EvalTotalTree cb fuel rho (.ite c a b)

/-- Convert a structural witness to an actual eval-totality, by induction on the WITNESS
(not the term): each node discharges once via `eval_ite_pauli_total` on already-decomposed
pieces, so the single `eval`-reduction never traverses the giant folded tree. -/
theorem EvalTotalTree.eval_total {arity : Nat} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {x : Term arity .pauli} (h : EvalTotalTree cb fuel rho x) :
    ∃ v, Term.eval cb fuel x rho = some v := by
  induction h with
  | pure hp => exact hp.eval_total cb fuel rho
  | atom ht => exact ht
  | ite hc _ _ iha ihb => exact eval_ite_pauli_total hc iha ihb

/-- Build an `EvalTotalTree` for a `recLeafTreeTA` (sub)tree by head-match recursion:
`ite` nodes recurse (guard discharged by the lean `guard_pp`), IH-pauli leaves close by
`atom` + `assumption`, pure leaves by `pure`.  No `eval` whnf over the giant tree. -/
macro "rec_tree" : tactic =>
  `(tactic|
    (try simp only [recLeafTreeTA, bulkGuardTA, bulkCountTA, dm1TA,
        baseBulkBandGuardTA, baseKindGuardTA, rTA, cTA, gridIdx, topClassGuardTA, baseBTA,
        baseHalfTA, topBandGuardTA, rightClassGuardTA, rightBandGuardTA, leftClassGuardTA,
        leftBandGuardTA, bottomBandGuardTA, lastCellTA, interiorCellGuardTA, insideGuardTA,
        topCellGuardTA, rightCellGuardTA, leftCellGuardTA, bottomCellGuardTA, rowTA, colTA,
        topOuterGuardTA, rightOuterGuardTA, leftOuterGuardTA, bottomOuterGuardTA,
        band3, band4, orEqSucc, orEqPair, le]
     repeat'
      first
        | exact EvalTotalTree.pure (baseLeafTreeTA_purePauli (by assumption) (by assumption)
            (by assumption))
        | apply EvalTotalTree.ite
        | exact EvalTotalTree.atom (by assumption)
        | apply EvalTotalTree.pure
        | apply recLeafGuard_eval_total
        | exact SFormula.PureNatTerm.var _
        | exact SFormula.PureNatTerm.natLit _
        | exact SFormula.PureBoolTerm.boolLit _
        | exact PurePauli.lit _
        | apply PurePauli.ite
        | apply SFormula.PureBoolTerm.eqNat
        | apply SFormula.PureBoolTerm.ltNat
        | apply SFormula.PureBoolTerm.leNat
        | apply SFormula.PureBoolTerm.not
        | apply SFormula.PureBoolTerm.and
        | apply SFormula.PureBoolTerm.or
        | apply SFormula.PureNatTerm.add
        | apply SFormula.PureNatTerm.sub
        | apply SFormula.PureNatTerm.mul
        | apply SFormula.PureNatTerm.div
        | apply SFormula.PureNatTerm.mod
        | apply SFormula.PureNatTerm.ite
        | assumption))

/-- Totality discharger for rec-leaf `FormulaDefined` obligations: pauli-subtree
totalities via the bounded `EvalTotalTree` witness; bool-guard totalities via
`recLeafGuard_eval_total`. -/
macro "rec_leaf_tot" : tactic =>
  `(tactic| first
      | (refine EvalTotalTree.eval_total ?_ <;> rec_tree)
      | (refine recLeafGuard_eval_total ?_ <;> guard_pp))

/-! ### Rec-leaf `DerivWF` lemmas (explicit-combinator chains over `recLeafTreeTA`)

Each rec leaf is an `eqPauliTrans`-chain of `pauliIteSelect*` nodes; its `DerivWF` is
built with the explicit node combinators (`derivWF_eqPauliTrans'` /
`derivWF_pauliIteSelect*'`) — NOT a raw `refine ⟨⟩`, which would force the slow
`recLeafTreeTA` defeq (OBSTACLE A).  Each `pauliIteSelect` `FormulaDefined` obligation
is discharged by `formulaDefined_iteSelect{Then,Else}` with the branch totalities
(`rec_leaf_tot`).  The IH paulis `pInt…pBottom` enter as totality hypotheses.

The deeper leaves (`…NI` / `Left` / `Bottom`) recurse through the full
`recLeafTreeTA` `ite` chain via `rec_leaf_tot`, which exceeds the section's
`400000` heartbeat budget; raise it for the rec-leaf walks. -/

/-- Expand `recLeafTreeTA`'s cell/outer guards once (NOT `baseLeafTreeTA`, which is caught
by name).  Run once per leaf so the per-node walk needs no further `simp` (the per-node
`simp` was the cumulative-memory blowup). -/
macro "rec_simp" : tactic =>
  `(tactic|
    try simp only [recLeafTreeTA, bulkGuardTA, bulkCountTA, dm1TA,
        baseBulkBandGuardTA, baseKindGuardTA, rTA, cTA, gridIdx, topClassGuardTA, baseBTA,
        baseHalfTA, topBandGuardTA, rightClassGuardTA, rightBandGuardTA, leftClassGuardTA,
        leftBandGuardTA, bottomBandGuardTA, lastCellTA, interiorCellGuardTA, insideGuardTA,
        topCellGuardTA, rightCellGuardTA, leftCellGuardTA, bottomCellGuardTA, rowTA, colTA,
        topOuterGuardTA, rightOuterGuardTA, leftOuterGuardTA, bottomOuterGuardTA,
        band3, band4, orEqSucc, orEqPair, le])

/-- **Chain-free base walker.**  `rec_simp` (expand guards once) then one bounded `repeat'`
that walks the `eqPauliTrans` / `pauliIteSelect` `DerivWF` chain, discharges each
`FormulaDefined` via `formulaDefined_iteSelect{Then,Else}`, and proves every `∃ v, eval …`
totality through the structural `EvalTotalTree` witness (head-match `apply` — never reduces
`eval`).  Used for the per-cell pieces (interior/inside/outer/guards) where the *deeper*
cell totality is supplied explicitly.  `rec_leaf_wf` below extends this to cite the named
cell-chain lemmas, so a full leaf never re-derives the nested cell chain. -/
macro "rec_inside" : tactic =>
  `(tactic|
    (rec_simp
     repeat' first
       | apply derivWF_eqPauliTrans'
       | apply derivWF_pauliIteSelectThen'
       | apply derivWF_pauliIteSelectElse'
       | apply formulaDefined_iteSelectThen
       | apply formulaDefined_iteSelectElse
       | exact baseLeafTreeTA_eval_total (by assumption) (by assumption) (by assumption) _ _ _
       | apply recLeafGuard_eval_total
       | apply EvalTotalTree.eval_total
       | exact EvalTotalTree.pure (baseLeafTreeTA_purePauli (by assumption) (by assumption)
           (by assumption))
       | apply EvalTotalTree.ite
       | exact EvalTotalTree.atom (by assumption)
       | apply EvalTotalTree.pure
       | exact SFormula.PureNatTerm.var _
       | exact SFormula.PureNatTerm.natLit _
       | exact SFormula.PureBoolTerm.boolLit _
       | exact PurePauli.lit _
       | apply PurePauli.ite
       | apply SFormula.PureBoolTerm.eqNat
       | apply SFormula.PureBoolTerm.ltNat
       | apply SFormula.PureBoolTerm.leNat
       | apply SFormula.PureBoolTerm.not
       | apply SFormula.PureBoolTerm.and
       | apply SFormula.PureBoolTerm.or
       | apply SFormula.PureNatTerm.add
       | apply SFormula.PureNatTerm.sub
       | apply SFormula.PureNatTerm.mul
       | apply SFormula.PureNatTerm.div
       | apply SFormula.PureNatTerm.mod
       | apply SFormula.PureNatTerm.ite
       | assumption))

set_option maxHeartbeats 1600000

/-! ### Named guard-purity lemmas (each proved ONCE; cited by name in `rec_leaf_wf`, so the
expanded guard arithmetic is built once here instead of re-expanded in every leaf — the
cumulative-memory fix). -/

def bulkGuard_pure {arity : Nat} {dT kT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureBoolTerm (bulkGuardTA dT kT) := by guard_pp

def interiorCell_pure {arity : Nat} {dT kT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureBoolTerm (interiorCellGuardTA dT kT) := by guard_pp

def inside_pure {arity : Nat} {dT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hq : SFormula.PureNatTerm qT) :
    SFormula.PureBoolTerm (insideGuardTA dT qT) := by guard_pp

def topCell_pure {arity : Nat} {dT kT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureBoolTerm (topCellGuardTA dT kT) := by guard_pp

def topOuter_pure {arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    SFormula.PureBoolTerm (topOuterGuardTA dT kT qT) := by guard_pp

def rightCell_pure {arity : Nat} {dT kT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureBoolTerm (rightCellGuardTA dT kT) := by guard_pp

def rightOuter_pure {arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    SFormula.PureBoolTerm (rightOuterGuardTA dT kT qT) := by guard_pp

def leftCell_pure {arity : Nat} {dT kT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureBoolTerm (leftCellGuardTA dT kT) := by guard_pp

def leftOuter_pure {arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    SFormula.PureBoolTerm (leftOuterGuardTA dT kT qT) := by guard_pp

def bottomCell_pure {arity : Nat} {dT kT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) :
    SFormula.PureBoolTerm (bottomCellGuardTA dT kT) := by guard_pp

def bottomOuter_pure {arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT) :
    SFormula.PureBoolTerm (bottomOuterGuardTA dT kT qT) := by guard_pp

/-- **Generic cell-totality — the single pattern reused by all five cells.**  A cell chain
`ite cellGuard (ite insideGuard pX outer) next` is total iff its cell guard, inside guard,
inside pauli `pX`, outer pauli, and the rest `next` are all total.  (Two nested
`eval_ite_pauli_total`s.)  Each `recCell*Chain_total` below is one application of this. -/
theorem recCell_total {arity : Nat} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity}
    {cellGuard insideGuard : Term arity .bool} {pX outer next : Term arity .pauli}
    (hcg : ∃ cv, Term.eval cb fuel cellGuard rho = some cv)
    (hig : ∃ cv, Term.eval cb fuel insideGuard rho = some cv)
    (hpX : ∃ v, Term.eval cb fuel pX rho = some v)
    (hout : ∃ v, Term.eval cb fuel outer rho = some v)
    (hnext : ∃ v, Term.eval cb fuel next rho = some v) :
    ∃ v, Term.eval cb fuel (.ite cellGuard (.ite insideGuard pX outer) next) rho = some v :=
  eval_ite_pauli_total hcg (eval_ite_pauli_total hig hpX hout) hnext

/-! ### Per-cell totality lemmas (proved ONCE each, bottom-up; cited by `rec_leaf_wf`)

Each says "this cell chain evaluates everywhere" given the IH paulis below it are total.
The local cell (guard + inside/outer pauli) is discharged by `rec_inside`; the rest of the
chain is the previous lemma, cited by name — so no re-derivation. -/

theorem recBottomChain_total {arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {pBottom : Term arity .pauli}
    (hpBottom : ∃ v, Term.eval cb fuel pBottom rho = some v) :
    ∃ v, Term.eval cb fuel (recBottomChainTA dT kT qT pBottom) rho = some v := by
  unfold recBottomChainTA
  exact recCell_total (by rec_inside) (by rec_inside) (by rec_inside) (by rec_inside)
    (baseLeafTreeTA_eval_total hd hk hq cb fuel rho)

theorem recLeftChain_total {arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {pLeft pBottom : Term arity .pauli}
    (hpLeft : ∃ v, Term.eval cb fuel pLeft rho = some v)
    (hpBottom : ∃ v, Term.eval cb fuel pBottom rho = some v) :
    ∃ v, Term.eval cb fuel (recLeftChainTA dT kT qT pLeft pBottom) rho = some v := by
  unfold recLeftChainTA
  exact recCell_total (by rec_inside) (by rec_inside) (by rec_inside) (by rec_inside)
    (recBottomChain_total hd hk hq hpBottom)

theorem recRightChain_total {arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {pRight pLeft pBottom : Term arity .pauli}
    (hpRight : ∃ v, Term.eval cb fuel pRight rho = some v)
    (hpLeft : ∃ v, Term.eval cb fuel pLeft rho = some v)
    (hpBottom : ∃ v, Term.eval cb fuel pBottom rho = some v) :
    ∃ v, Term.eval cb fuel (recRightChainTA dT kT qT pRight pLeft pBottom) rho = some v := by
  unfold recRightChainTA
  exact recCell_total (by rec_inside) (by rec_inside) (by rec_inside) (by rec_inside)
    (recLeftChain_total hd hk hq hpLeft hpBottom)

theorem recTopChain_total {arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity}
    {pTop pRight pLeft pBottom : Term arity .pauli}
    (hpTop : ∃ v, Term.eval cb fuel pTop rho = some v)
    (hpRight : ∃ v, Term.eval cb fuel pRight rho = some v)
    (hpLeft : ∃ v, Term.eval cb fuel pLeft rho = some v)
    (hpBottom : ∃ v, Term.eval cb fuel pBottom rho = some v) :
    ∃ v, Term.eval cb fuel (recTopChainTA dT kT qT pTop pRight pLeft pBottom) rho = some v := by
  unfold recTopChainTA
  exact recCell_total (by rec_inside) (by rec_inside) (by rec_inside) (by rec_inside)
    (recRightChain_total hd hk hq hpRight hpLeft hpBottom)

theorem recInteriorChain_total {arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity}
    {pInt pTop pRight pLeft pBottom : Term arity .pauli}
    (hpInt : ∃ v, Term.eval cb fuel pInt rho = some v)
    (hpTop : ∃ v, Term.eval cb fuel pTop rho = some v)
    (hpRight : ∃ v, Term.eval cb fuel pRight rho = some v)
    (hpLeft : ∃ v, Term.eval cb fuel pLeft rho = some v)
    (hpBottom : ∃ v, Term.eval cb fuel pBottom rho = some v) :
    ∃ v, Term.eval cb fuel (recInteriorChainTA dT kT qT pInt pTop pRight pLeft pBottom) rho
      = some v := by
  unfold recInteriorChainTA
  exact recCell_total (by rec_inside) (by rec_inside) (by rec_inside) (by rec_inside)
    (recTopChain_total hd hk hq hpTop hpRight hpLeft hpBottom)

/-- **Uniform rec-leaf / whole-tree prover.**  `rec_inside`'s walk, plus branches that cite
the per-cell totality lemmas by name (matched up to defeq against `recLeafTreeTA`'s subtrees)
— so a leaf's else-branch cell chains are taken wholesale, never re-derived.  Every rec leaf
is now the one-liner `rec_leaf_wf`, at any cell depth, bounded. -/
macro "rec_leaf_wf" : tactic =>
  `(tactic|
    (repeat' first
       | apply derivWF_eqPauliTrans'
       | apply derivWF_pauliIteSelectThen'
       | apply derivWF_pauliIteSelectElse'
       | apply formulaDefined_iteSelectThen
       | apply formulaDefined_iteSelectElse
       | exact recInteriorChain_total (by assumption) (by assumption) (by assumption)
           (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
       | exact recTopChain_total (by assumption) (by assumption) (by assumption)
           (by assumption) (by assumption) (by assumption) (by assumption)
       | exact recRightChain_total (by assumption) (by assumption) (by assumption)
           (by assumption) (by assumption) (by assumption)
       | exact recLeftChain_total (by assumption) (by assumption) (by assumption)
           (by assumption) (by assumption)
       | exact recBottomChain_total (by assumption) (by assumption) (by assumption)
           (by assumption)
       | exact EvalTotalTree.atom (recInteriorChain_total (by assumption) (by assumption)
           (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
           (by assumption))
       | exact EvalTotalTree.atom (recTopChain_total (by assumption) (by assumption)
           (by assumption) (by assumption) (by assumption) (by assumption) (by assumption))
       | exact EvalTotalTree.atom (recRightChain_total (by assumption) (by assumption)
           (by assumption) (by assumption) (by assumption) (by assumption))
       | exact EvalTotalTree.atom (recLeftChain_total (by assumption) (by assumption)
           (by assumption) (by assumption) (by assumption))
       | exact EvalTotalTree.atom (recBottomChain_total (by assumption) (by assumption)
           (by assumption) (by assumption))
       | exact baseLeafTreeTA_eval_total (by assumption) (by assumption) (by assumption) _ _ _
       | exact EvalTotalTree.atom (baseLeafTreeTA_eval_total (by assumption) (by assumption)
           (by assumption) _ _ _)
       | exact EvalTotalTree.pure (baseLeafTreeTA_purePauli (by assumption) (by assumption)
           (by assumption))
       | exact recLeafGuard_eval_total (bulkGuard_pure (by assumption) (by assumption))
       | exact recLeafGuard_eval_total (interiorCell_pure (by assumption) (by assumption))
       | exact recLeafGuard_eval_total (inside_pure (by assumption) (by assumption))
       | exact recLeafGuard_eval_total (topCell_pure (by assumption) (by assumption))
       | exact recLeafGuard_eval_total (topOuter_pure (by assumption) (by assumption) (by assumption))
       | exact recLeafGuard_eval_total (rightCell_pure (by assumption) (by assumption))
       | exact recLeafGuard_eval_total (rightOuter_pure (by assumption) (by assumption) (by assumption))
       | exact recLeafGuard_eval_total (leftCell_pure (by assumption) (by assumption))
       | exact recLeafGuard_eval_total (leftOuter_pure (by assumption) (by assumption) (by assumption))
       | exact recLeafGuard_eval_total (bottomCell_pure (by assumption) (by assumption))
       | exact recLeafGuard_eval_total (bottomOuter_pure (by assumption) (by assumption) (by assumption))
       | apply EvalTotalTree.eval_total
       | apply EvalTotalTree.ite
       | exact EvalTotalTree.atom (by assumption)
       | exact EvalTotalTree.pure (PurePauli.lit _)
       | assumption))

/-- **Reusable whole-tree totality.**  `recLeafTreeTA` evaluates to `some` at any env,
given index purities + the five IH-pauli totalities.  Proved ONCE via `rec_leaf_tot`
(the per-node `eval_ite_pauli_total` recursion runs a single time here, not 9× per
rec-leaf × 12 leaves).  Every rec-leaf `_WF` draws its branch totalities from this. -/
theorem recLeafTreeTA_eval_total {arity : Nat} {dT kT qT : Term arity .nat}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity}
    {pInt pTop pRight pLeft pBottom : Term arity .pauli}
    (hpInt : ∃ v, Term.eval cb fuel pInt rho = some v)
    (hpTop : ∃ v, Term.eval cb fuel pTop rho = some v)
    (hpRight : ∃ v, Term.eval cb fuel pRight rho = some v)
    (hpLeft : ∃ v, Term.eval cb fuel pLeft rho = some v)
    (hpBottom : ∃ v, Term.eval cb fuel pBottom rho = some v) :
    EvalTotalTree cb fuel rho (recLeafTreeTA dT kT qT pInt pTop pRight pLeft pBottom) := by
  rec_leaf_wf

theorem recLeafInt_WF {arity : Nat} (Γ : List (SFormula arity))
    (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    {hBulk hInterior hInside} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E) (wInside : DerivWF hInside cb fuel rho E)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpInt : ∃ v, Term.eval cb fuel pInt rho = some v)
    (hpTop : ∃ v, Term.eval cb fuel pTop rho = some v)
    (hpRight : ∃ v, Term.eval cb fuel pRight rho = some v)
    (hpLeft : ∃ v, Term.eval cb fuel pLeft rho = some v)
    (hpBottom : ∃ v, Term.eval cb fuel pBottom rho = some v) :
    DerivWF (recLeafInt (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom hBulk hInterior hInside)
      cb fuel rho E := by
  unfold recLeafInt
  rec_leaf_wf

/-- The shared per-leaf hypotheses: index purities + the five IH-pauli totalities. -/
theorem recLeafIntI_WF {arity : Nat} (Γ : List (SFormula arity))
    (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    {hBulk hInterior hInside} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E) (wInside : DerivWF hInside cb fuel rho E)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpInt : ∃ v, Term.eval cb fuel pInt rho = some v)
    (hpTop : ∃ v, Term.eval cb fuel pTop rho = some v)
    (hpRight : ∃ v, Term.eval cb fuel pRight rho = some v)
    (hpLeft : ∃ v, Term.eval cb fuel pLeft rho = some v)
    (hpBottom : ∃ v, Term.eval cb fuel pBottom rho = some v) :
    DerivWF (recLeafIntI (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom hBulk hInterior hInside)
      cb fuel rho E := by
  unfold recLeafIntI
  rec_leaf_wf

theorem recLeafTop_WF {arity : Nat} (Γ : List (SFormula arity))
    (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    {hBulk hInterior hTop hInside} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E) (wTop : DerivWF hTop cb fuel rho E) (wInside : DerivWF hInside cb fuel rho E)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpInt : ∃ v, Term.eval cb fuel pInt rho = some v)
    (hpTop : ∃ v, Term.eval cb fuel pTop rho = some v)
    (hpRight : ∃ v, Term.eval cb fuel pRight rho = some v)
    (hpLeft : ∃ v, Term.eval cb fuel pLeft rho = some v)
    (hpBottom : ∃ v, Term.eval cb fuel pBottom rho = some v) :
    DerivWF (recLeafTop (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom hBulk hInterior hTop hInside)
      cb fuel rho E := by
  unfold recLeafTop
  rec_leaf_wf

theorem recLeafTopNI_WF {arity : Nat} (Γ : List (SFormula arity))
    (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    {hBulk hInterior hTop hInside} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E) (wTop : DerivWF hTop cb fuel rho E) (wInside : DerivWF hInside cb fuel rho E)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpInt : ∃ v, Term.eval cb fuel pInt rho = some v)
    (hpTop : ∃ v, Term.eval cb fuel pTop rho = some v)
    (hpRight : ∃ v, Term.eval cb fuel pRight rho = some v)
    (hpLeft : ∃ v, Term.eval cb fuel pLeft rho = some v)
    (hpBottom : ∃ v, Term.eval cb fuel pBottom rho = some v) :
    DerivWF (recLeafTopNI (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom hBulk hInterior hTop hInside)
      cb fuel rho E := by
  unfold recLeafTopNI
  rec_leaf_wf

theorem recLeafRight_WF {arity : Nat} (Γ : List (SFormula arity))
    (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    {hBulk hInterior hTop hRight hInside} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E) (wTop : DerivWF hTop cb fuel rho E) (wRight : DerivWF hRight cb fuel rho E) (wInside : DerivWF hInside cb fuel rho E)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpInt : ∃ v, Term.eval cb fuel pInt rho = some v)
    (hpTop : ∃ v, Term.eval cb fuel pTop rho = some v)
    (hpRight : ∃ v, Term.eval cb fuel pRight rho = some v)
    (hpLeft : ∃ v, Term.eval cb fuel pLeft rho = some v)
    (hpBottom : ∃ v, Term.eval cb fuel pBottom rho = some v) :
    DerivWF (recLeafRight (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom
      hBulk hInterior hTop hRight hInside) cb fuel rho E := by
  unfold recLeafRight
  rec_leaf_wf

theorem recLeafRightNI_WF {arity : Nat} (Γ : List (SFormula arity))
    (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    {hBulk hInterior hTop hRight hInside} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E) (wTop : DerivWF hTop cb fuel rho E) (wRight : DerivWF hRight cb fuel rho E) (wInside : DerivWF hInside cb fuel rho E)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpInt : ∃ v, Term.eval cb fuel pInt rho = some v)
    (hpTop : ∃ v, Term.eval cb fuel pTop rho = some v)
    (hpRight : ∃ v, Term.eval cb fuel pRight rho = some v)
    (hpLeft : ∃ v, Term.eval cb fuel pLeft rho = some v)
    (hpBottom : ∃ v, Term.eval cb fuel pBottom rho = some v) :
    DerivWF (recLeafRightNI (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom
      hBulk hInterior hTop hRight hInside) cb fuel rho E := by
  unfold recLeafRightNI
  rec_leaf_wf

theorem recLeafLeft_WF {arity : Nat} (Γ : List (SFormula arity))
    (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    {hBulk hInterior hTop hRight hLeft hInside} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E) (wTop : DerivWF hTop cb fuel rho E) (wRight : DerivWF hRight cb fuel rho E) (wLeft : DerivWF hLeft cb fuel rho E) (wInside : DerivWF hInside cb fuel rho E)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpInt : ∃ v, Term.eval cb fuel pInt rho = some v)
    (hpTop : ∃ v, Term.eval cb fuel pTop rho = some v)
    (hpRight : ∃ v, Term.eval cb fuel pRight rho = some v)
    (hpLeft : ∃ v, Term.eval cb fuel pLeft rho = some v)
    (hpBottom : ∃ v, Term.eval cb fuel pBottom rho = some v) :
    DerivWF (recLeafLeft (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom
      hBulk hInterior hTop hRight hLeft hInside) cb fuel rho E := by
  unfold recLeafLeft
  rec_leaf_wf

theorem recLeafLeftNI_WF {arity : Nat} (Γ : List (SFormula arity))
    (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    {hBulk hInterior hTop hRight hLeft hInside} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E) (wTop : DerivWF hTop cb fuel rho E) (wRight : DerivWF hRight cb fuel rho E) (wLeft : DerivWF hLeft cb fuel rho E) (wInside : DerivWF hInside cb fuel rho E)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpInt : ∃ v, Term.eval cb fuel pInt rho = some v)
    (hpTop : ∃ v, Term.eval cb fuel pTop rho = some v)
    (hpRight : ∃ v, Term.eval cb fuel pRight rho = some v)
    (hpLeft : ∃ v, Term.eval cb fuel pLeft rho = some v)
    (hpBottom : ∃ v, Term.eval cb fuel pBottom rho = some v) :
    DerivWF (recLeafLeftNI (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom
      hBulk hInterior hTop hRight hLeft hInside) cb fuel rho E := by
  unfold recLeafLeftNI
  rec_leaf_wf

theorem recLeafBottom_WF {arity : Nat} (Γ : List (SFormula arity))
    (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    {hBulk hInterior hTop hRight hLeft hBottom hInside} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E) (wTop : DerivWF hTop cb fuel rho E) (wRight : DerivWF hRight cb fuel rho E) (wLeft : DerivWF hLeft cb fuel rho E) (wBottom : DerivWF hBottom cb fuel rho E) (wInside : DerivWF hInside cb fuel rho E)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpInt : ∃ v, Term.eval cb fuel pInt rho = some v)
    (hpTop : ∃ v, Term.eval cb fuel pTop rho = some v)
    (hpRight : ∃ v, Term.eval cb fuel pRight rho = some v)
    (hpLeft : ∃ v, Term.eval cb fuel pLeft rho = some v)
    (hpBottom : ∃ v, Term.eval cb fuel pBottom rho = some v) :
    DerivWF (recLeafBottom (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom
      hBulk hInterior hTop hRight hLeft hBottom hInside) cb fuel rho E := by
  unfold recLeafBottom
  rec_leaf_wf

theorem recLeafBottomNI_WF {arity : Nat} (Γ : List (SFormula arity))
    (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    {hBulk hInterior hTop hRight hLeft hBottom hInside} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E) (wTop : DerivWF hTop cb fuel rho E) (wRight : DerivWF hRight cb fuel rho E) (wLeft : DerivWF hLeft cb fuel rho E) (wBottom : DerivWF hBottom cb fuel rho E) (wInside : DerivWF hInside cb fuel rho E)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpInt : ∃ v, Term.eval cb fuel pInt rho = some v)
    (hpTop : ∃ v, Term.eval cb fuel pTop rho = some v)
    (hpRight : ∃ v, Term.eval cb fuel pRight rho = some v)
    (hpLeft : ∃ v, Term.eval cb fuel pLeft rho = some v)
    (hpBottom : ∃ v, Term.eval cb fuel pBottom rho = some v) :
    DerivWF (recLeafBottomNI (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom
      hBulk hInterior hTop hRight hLeft hBottom hInside) cb fuel rho E := by
  unfold recLeafBottomNI
  rec_leaf_wf

theorem recLeafFallback_WF {arity : Nat} (Γ : List (SFormula arity))
    (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    {hBulk hInterior hTop hRight hLeft hBottom} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E) (wTop : DerivWF hTop cb fuel rho E) (wRight : DerivWF hRight cb fuel rho E) (wLeft : DerivWF hLeft cb fuel rho E) (wBottom : DerivWF hBottom cb fuel rho E)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpInt : ∃ v, Term.eval cb fuel pInt rho = some v)
    (hpTop : ∃ v, Term.eval cb fuel pTop rho = some v)
    (hpRight : ∃ v, Term.eval cb fuel pRight rho = some v)
    (hpLeft : ∃ v, Term.eval cb fuel pLeft rho = some v)
    (hpBottom : ∃ v, Term.eval cb fuel pBottom rho = some v) :
    DerivWF (recLeafFallback (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom
      hBulk hInterior hTop hRight hLeft hBottom) cb fuel rho E := by
  unfold recLeafFallback
  rec_leaf_wf

theorem recLeafBoundary_WF {arity : Nat} (Γ : List (SFormula arity))
    (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    {hBulk} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpInt : ∃ v, Term.eval cb fuel pInt rho = some v)
    (hpTop : ∃ v, Term.eval cb fuel pTop rho = some v)
    (hpRight : ∃ v, Term.eval cb fuel pRight rho = some v)
    (hpLeft : ∃ v, Term.eval cb fuel pLeft rho = some v)
    (hpBottom : ∃ v, Term.eval cb fuel pBottom rho = some v) :
    DerivWF (recLeafBoundary (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom hBulk)
      cb fuel rho E := by
  unfold recLeafBoundary
  rec_leaf_wf

/-! ## STEP A — the recursive-peel `DerivWF` lemmas

Each recursive peel (`recInteriorPeelD` / `rec*PromotedPeelD` / `recFallbackPeelD` /
`baseBoundaryStripD`) is an `eqPauliTrans`-chain whose head is a `stabAtClosedIteLam`
node over the *recursive* lam body `codeSubstAt dT kT 1 recursiveEntry` (NOT
`PurePauli`), followed by `pauliIteSelect*` selections that bottom out at the inner
recursing cell (whose RHS is the `recCall`-containing `centerInnerRefA` /
`promotedInnerRefA`).

Unlike the base peels, the FormulaDefined leaves are discharged from a `RecEvalData`
(the lam-body / instantiate-RHS totalities, `recPeel_lamFD`) and from the *supplied*
inner-ref totality (`hpInt …`/the `closedStabAtSplit` eval the row-witness carries) —
these are the recursing leaves' totalities the master/witness threads in.  The peels
run at `cb = Surface.code.body`, `fuel = f' + 1` (the rec master's fixed fuel). -/

set_option maxHeartbeats 1600000

/-! ### STEP A.0 — head-form rec-peel infrastructure (RecOk leaf totality + lam-body FD)

Mirrors the base-side `baseEntryThen_inst_eval_total` / `formulaDefined_baseEntry_lam`, but
the recursive bulk-then `recEntryThen` is a `RecOk` tree (NOT `PurePauli`), so leaf totality
goes through `RecEvalData.instRecOkSubst_total` (never a `codeSubstAt` whnf).  The head-form
lemmas (`codeSubstAt_one_recursiveEntry_head` etc.) live in `SurfaceRowCharacterizationSymbolic`. -/

/-- `RecOk` of `recursiveEntry`'s bulk-then subtree, extracted from `recursiveEntry_recOk`.
The spurious `pure` case is closed constructively (`PurePauli (ite …) → PurePauli then`). -/
theorem recEntryThen_recOk : RecOk recEntryThen := by
  have h : RecOk (Term.ite recEntryCond recEntryThen recEntryElse) := by
    rw [← recursiveEntry_head_eq, ← SurfaceASTPublic.recursiveEntry_eq_public]
    exact recursiveEntry_recOk
  cases h with
  | ite _ ht _ => exact ht
  | pure hp => cases hp with | ite _ ht _ => exact RecOk.pure ht

/-- Head children of `recEntryThen` (the interior cell's guard / then / else). -/
def recEntryThenCond : Term 3 .bool :=
  match recEntryThen with | .ite c _ _ => c | _ => .boolLit true
def recEntryThenThen : Term 3 .pauli :=
  match recEntryThen with | .ite _ t _ => t | _ => .pauliLit Pauli.I
def recEntryThenElse : Term 3 .pauli :=
  match recEntryThen with | .ite _ _ e => e | _ => .pauliLit Pauli.I
theorem recEntryThen_head_eq :
    recEntryThen = Term.ite recEntryThenCond recEntryThenThen recEntryThenElse := rfl
/-- `RecOk` of the interior cell's then-branch (the inside guarded leaf), by sub-extraction. -/
theorem recEntryThenThen_recOk : RecOk recEntryThenThen := by
  have h : RecOk recEntryThen := recEntryThen_recOk
  rw [recEntryThen_head_eq] at h
  cases h with
  | ite _ ht _ => exact ht
  | pure hp => cases hp with | ite _ ht _ => exact RecOk.pure ht

/-! Top-cell (and the rest of the promoted-cell chain): `recEntryThenElse` = the 4-cell
`else` of `recEntryThen`.  Its head children give the top cell; deeper cells extract from its
`else`.  The outer cell guards (`topCell`/…) ≠ `insideGuard`, so `cases` on these concrete
`RecOk`s yields only `ite`/`pure` (no `guarded`) — abstract `RecOk.of_ite_then` is NOT provable. -/
def recEntryThenElseCond : Term 3 .bool :=
  match recEntryThenElse with | .ite c _ _ => c | _ => .boolLit true
def recEntryThenElseThen : Term 3 .pauli :=
  match recEntryThenElse with | .ite _ t _ => t | _ => .pauliLit Pauli.I
def recEntryThenElseElse : Term 3 .pauli :=
  match recEntryThenElse with | .ite _ _ e => e | _ => .pauliLit Pauli.I
theorem recEntryThenElse_head_eq :
    recEntryThenElse = Term.ite recEntryThenElseCond recEntryThenElseThen recEntryThenElseElse := rfl
theorem recEntryThenElse_recOk : RecOk recEntryThenElse := by
  have h : RecOk recEntryThen := recEntryThen_recOk
  rw [recEntryThen_head_eq] at h
  cases h with
  | ite _ _ he => exact he
  | pure hp => cases hp with | ite _ _ he => exact RecOk.pure he
theorem recEntryThenElseThen_recOk : RecOk recEntryThenElseThen := by
  have h : RecOk recEntryThenElse := recEntryThenElse_recOk
  rw [recEntryThenElse_head_eq] at h
  cases h with
  | ite _ ht _ => exact ht
  | pure hp => cases hp with | ite _ ht _ => exact RecOk.pure ht

/-- Totality of any `RecOk` subtree under `codeSubstAt`+`instantiateTopNat` (FOLDED form, no
whnf).  The reusable rec-side leaf-totality discharger (analogue of `baseEntryThen_inst_eval_total`,
but `RecOk` rather than `PurePauli`). -/
theorem subtree_inst_eval_total {arity : Nat} {dT kT qT : Term arity .nat} {f' : Nat}
    {rho : Env arity} (R : RecEvalData dT kT f' rho)
    (hq : SFormula.PureNatTerm qT) {t' : Term 3 .pauli} (ht' : RecOk t') :
    ∃ v, Term.eval Surface.code.body (f' + 1)
        (Term.instantiateTopNat qT (codeSubstAt dT kT 1 t')) rho = some v := by
  obtain ⟨qv, hq0⟩ := hq.eval_total Surface.code.body 0 rho
  have hqAll : ∀ f, Term.eval Surface.code.body f qT rho = some qv := fun f => by
    rw [SFormula.PureNatTerm.eval_stable hq Surface.code.body Surface.code.body f 0 rho]; exact hq0
  exact R.instRecOkSubst_total hqAll ht'

theorem recEntryThen_inst_eval_total {arity : Nat} {dT kT qT : Term arity .nat} {f' : Nat}
    {rho : Env arity} (R : RecEvalData dT kT f' rho) (hq : SFormula.PureNatTerm qT) :
    ∃ v, Term.eval Surface.code.body (f' + 1)
        (Term.instantiateTopNat qT (codeSubstAt dT kT 1 recEntryThen)) rho = some v :=
  subtree_inst_eval_total R hq recEntryThen_recOk

theorem interiorBranch_inst_eval_total {arity : Nat} {dT kT qT : Term arity .nat} {f' : Nat}
    {rho : Env arity} (R : RecEvalData dT kT f' rho) (hq : SFormula.PureNatTerm qT) :
    ∃ v, Term.eval Surface.code.body (f' + 1)
        (Term.instantiateTopNat qT (codeSubstAt dT kT 1 recEntryThenThen)) rho = some v :=
  subtree_inst_eval_total R hq recEntryThenThen_recOk

/-- Totality of `rest` (the 4 promoted cells, `recEntryThen`'s else). -/
theorem rest_inst_eval_total {arity : Nat} {dT kT qT : Term arity .nat} {f' : Nat}
    {rho : Env arity} (R : RecEvalData dT kT f' rho) (hq : SFormula.PureNatTerm qT) :
    ∃ v, Term.eval Surface.code.body (f' + 1)
        (Term.instantiateTopNat qT (codeSubstAt dT kT 1 recEntryThenElse)) rho = some v :=
  subtree_inst_eval_total R hq recEntryThenElse_recOk

/-- Totality of the top cell's branch (`rest`'s then = the top `promotedBoundaryEntry`). -/
theorem topBranch_inst_eval_total {arity : Nat} {dT kT qT : Term arity .nat} {f' : Nat}
    {rho : Env arity} (R : RecEvalData dT kT f' rho) (hq : SFormula.PureNatTerm qT) :
    ∃ v, Term.eval Surface.code.body (f' + 1)
        (Term.instantiateTopNat qT (codeSubstAt dT kT 1 recEntryThenElseThen)) rho = some v :=
  subtree_inst_eval_total R hq recEntryThenElseThen_recOk

/-! Deeper promoted cells: `rest2` (right), `rest3` (left), `rest4` (bottom) along
`recEntryThen`'s else chain; each `restₖ`'s then-branch is that cell's `promotedBoundaryEntry`.
Same inline `cases`-extraction (cell guards ≠ `insideGuard` ⇒ only ite/pure). -/
def recEntryThenElseElseCond : Term 3 .bool :=
  match recEntryThenElseElse with | .ite c _ _ => c | _ => .boolLit true
def recEntryThenElseElseThen : Term 3 .pauli :=
  match recEntryThenElseElse with | .ite _ t _ => t | _ => .pauliLit Pauli.I
def recEntryThenElseElseElse : Term 3 .pauli :=
  match recEntryThenElseElse with | .ite _ _ e => e | _ => .pauliLit Pauli.I
theorem recEntryThenElseElse_head_eq :
    recEntryThenElseElse = Term.ite recEntryThenElseElseCond recEntryThenElseElseThen recEntryThenElseElseElse := rfl
theorem recEntryThenElseElse_recOk : RecOk recEntryThenElseElse := by
  have h : RecOk recEntryThenElse := recEntryThenElse_recOk
  rw [recEntryThenElse_head_eq] at h
  cases h with
  | ite _ _ he => exact he
  | pure hp => cases hp with | ite _ _ he => exact RecOk.pure he
theorem recEntryThenElseElseThen_recOk : RecOk recEntryThenElseElseThen := by
  have h : RecOk recEntryThenElseElse := recEntryThenElseElse_recOk
  rw [recEntryThenElseElse_head_eq] at h
  cases h with
  | ite _ ht _ => exact ht
  | pure hp => cases hp with | ite _ ht _ => exact RecOk.pure ht
def recEntryThenElseElseElseCond : Term 3 .bool :=
  match recEntryThenElseElseElse with | .ite c _ _ => c | _ => .boolLit true
def recEntryThenElseElseElseThen : Term 3 .pauli :=
  match recEntryThenElseElseElse with | .ite _ t _ => t | _ => .pauliLit Pauli.I
def recEntryThenElseElseElseElse : Term 3 .pauli :=
  match recEntryThenElseElseElse with | .ite _ _ e => e | _ => .pauliLit Pauli.I
theorem recEntryThenElseElseElse_head_eq :
    recEntryThenElseElseElse = Term.ite recEntryThenElseElseElseCond recEntryThenElseElseElseThen recEntryThenElseElseElseElse := rfl
theorem recEntryThenElseElseElse_recOk : RecOk recEntryThenElseElseElse := by
  have h : RecOk recEntryThenElseElse := recEntryThenElseElse_recOk
  rw [recEntryThenElseElse_head_eq] at h
  cases h with
  | ite _ _ he => exact he
  | pure hp => cases hp with | ite _ _ he => exact RecOk.pure he
theorem recEntryThenElseElseElseThen_recOk : RecOk recEntryThenElseElseElseThen := by
  have h : RecOk recEntryThenElseElseElse := recEntryThenElseElseElse_recOk
  rw [recEntryThenElseElseElse_head_eq] at h
  cases h with
  | ite _ ht _ => exact ht
  | pure hp => cases hp with | ite _ ht _ => exact RecOk.pure ht
def recEntryThenElseElseElseElseCond : Term 3 .bool :=
  match recEntryThenElseElseElseElse with | .ite c _ _ => c | _ => .boolLit true
def recEntryThenElseElseElseElseThen : Term 3 .pauli :=
  match recEntryThenElseElseElseElse with | .ite _ t _ => t | _ => .pauliLit Pauli.I
def recEntryThenElseElseElseElseElse : Term 3 .pauli :=
  match recEntryThenElseElseElseElse with | .ite _ _ e => e | _ => .pauliLit Pauli.I
theorem recEntryThenElseElseElseElse_head_eq :
    recEntryThenElseElseElseElse = Term.ite recEntryThenElseElseElseElseCond recEntryThenElseElseElseElseThen recEntryThenElseElseElseElseElse := rfl
theorem recEntryThenElseElseElseElse_recOk : RecOk recEntryThenElseElseElseElse := by
  have h : RecOk recEntryThenElseElseElse := recEntryThenElseElseElse_recOk
  rw [recEntryThenElseElseElse_head_eq] at h
  cases h with
  | ite _ _ he => exact he
  | pure hp => cases hp with | ite _ _ he => exact RecOk.pure he
theorem recEntryThenElseElseElseElseThen_recOk : RecOk recEntryThenElseElseElseElseThen := by
  have h : RecOk recEntryThenElseElseElseElse := recEntryThenElseElseElseElse_recOk
  rw [recEntryThenElseElseElseElse_head_eq] at h
  cases h with
  | ite _ ht _ => exact ht
  | pure hp => cases hp with | ite _ ht _ => exact RecOk.pure ht
/-- Totality of `rest2` (right cell's else-context). -/
theorem rest2_inst_eval_total {arity : Nat} {dT kT qT : Term arity .nat} {f' : Nat}
    {rho : Env arity} (R : RecEvalData dT kT f' rho) (hq : SFormula.PureNatTerm qT) :
    ∃ v, Term.eval Surface.code.body (f' + 1)
        (Term.instantiateTopNat qT (codeSubstAt dT kT 1 recEntryThenElseElse)) rho = some v :=
  subtree_inst_eval_total R hq recEntryThenElseElse_recOk
/-- Totality of the right cell's branch. -/
theorem rightBranch_inst_eval_total {arity : Nat} {dT kT qT : Term arity .nat} {f' : Nat}
    {rho : Env arity} (R : RecEvalData dT kT f' rho) (hq : SFormula.PureNatTerm qT) :
    ∃ v, Term.eval Surface.code.body (f' + 1)
        (Term.instantiateTopNat qT (codeSubstAt dT kT 1 recEntryThenElseElseThen)) rho = some v :=
  subtree_inst_eval_total R hq recEntryThenElseElseThen_recOk
/-- Totality of `rest3` (left cell's else-context). -/
theorem rest3_inst_eval_total {arity : Nat} {dT kT qT : Term arity .nat} {f' : Nat}
    {rho : Env arity} (R : RecEvalData dT kT f' rho) (hq : SFormula.PureNatTerm qT) :
    ∃ v, Term.eval Surface.code.body (f' + 1)
        (Term.instantiateTopNat qT (codeSubstAt dT kT 1 recEntryThenElseElseElse)) rho = some v :=
  subtree_inst_eval_total R hq recEntryThenElseElseElse_recOk
/-- Totality of the left cell's branch. -/
theorem leftBranch_inst_eval_total {arity : Nat} {dT kT qT : Term arity .nat} {f' : Nat}
    {rho : Env arity} (R : RecEvalData dT kT f' rho) (hq : SFormula.PureNatTerm qT) :
    ∃ v, Term.eval Surface.code.body (f' + 1)
        (Term.instantiateTopNat qT (codeSubstAt dT kT 1 recEntryThenElseElseElseThen)) rho = some v :=
  subtree_inst_eval_total R hq recEntryThenElseElseElseThen_recOk
/-- Totality of `rest4` (bottom cell's else-context). -/
theorem rest4_inst_eval_total {arity : Nat} {dT kT qT : Term arity .nat} {f' : Nat}
    {rho : Env arity} (R : RecEvalData dT kT f' rho) (hq : SFormula.PureNatTerm qT) :
    ∃ v, Term.eval Surface.code.body (f' + 1)
        (Term.instantiateTopNat qT (codeSubstAt dT kT 1 recEntryThenElseElseElseElse)) rho = some v :=
  subtree_inst_eval_total R hq recEntryThenElseElseElseElse_recOk
/-- Totality of the bottom cell's branch. -/
theorem bottomBranch_inst_eval_total {arity : Nat} {dT kT qT : Term arity .nat} {f' : Nat}
    {rho : Env arity} (R : RecEvalData dT kT f' rho) (hq : SFormula.PureNatTerm qT) :
    ∃ v, Term.eval Surface.code.body (f' + 1)
        (Term.instantiateTopNat qT (codeSubstAt dT kT 1 recEntryThenElseElseElseElseThen)) rho = some v :=
  subtree_inst_eval_total R hq recEntryThenElseElseElseElseThen_recOk

/-! Fallback / boundary base leaves: `rest5` = `recEntryThen`'s deepest else (= baseEntry),
and `recEntryElse` = `recursiveEntry`'s else (= baseEntry).  Both are `RecOk.pure`. -/
theorem recEntryThenElseElseElseElseElse_recOk : RecOk recEntryThenElseElseElseElseElse := by
  have h : RecOk recEntryThenElseElseElseElse := recEntryThenElseElseElseElse_recOk
  rw [recEntryThenElseElseElseElse_head_eq] at h
  cases h with
  | ite _ _ he => exact he
  | pure hp => cases hp with | ite _ _ he => exact RecOk.pure he
theorem recEntryElse_recOk : RecOk recEntryElse := by
  have h : RecOk (Term.ite recEntryCond recEntryThen recEntryElse) := by
    rw [← recursiveEntry_head_eq, ← SurfaceASTPublic.recursiveEntry_eq_public]
    exact recursiveEntry_recOk
  cases h with
  | ite _ _ he => exact he
  | pure hp => cases hp with | ite _ _ he => exact RecOk.pure he
/-- Totality of the deepest base leaf `rest5` (fallback peel). -/
theorem rest5_inst_eval_total {arity : Nat} {dT kT qT : Term arity .nat} {f' : Nat}
    {rho : Env arity} (R : RecEvalData dT kT f' rho) (hq : SFormula.PureNatTerm qT) :
    ∃ v, Term.eval Surface.code.body (f' + 1)
        (Term.instantiateTopNat qT (codeSubstAt dT kT 1 recEntryThenElseElseElseElseElse)) rho = some v :=
  subtree_inst_eval_total R hq recEntryThenElseElseElseElseElse_recOk
/-- Totality of `recEntryElse` (= baseEntry; boundary strip). -/
theorem recEntryElse_inst_eval_total {arity : Nat} {dT kT qT : Term arity .nat} {f' : Nat}
    {rho : Env arity} (R : RecEvalData dT kT f' rho) (hq : SFormula.PureNatTerm qT) :
    ∃ v, Term.eval Surface.code.body (f' + 1)
        (Term.instantiateTopNat qT (codeSubstAt dT kT 1 recEntryElse)) rho = some v :=
  subtree_inst_eval_total R hq recEntryElse_recOk

/-- `instantiateTopNat qT (codeSubstAt 1 recEntryElse)` IS `baseLeafTreeTA` (recEntryElse =
baseEntry; same identity the `baseBoundaryStripD` def uses).  Reused by the boundary `_WF`. -/
theorem recEntryElse_inst_eq_baseLeaf {arity : Nat} (dT kT qT : Term arity .nat) :
    Term.instantiateTopNat qT (codeSubstAt dT kT 1 recEntryElse) = baseLeafTreeTA dT kT qT := by
  simp only [recEntryElse, SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.baseEntry,
    SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q,
    codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4, orEqSucc, le,
    Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift,
    baseLeafTreeTA, bulkGuardTA, bulkCountTA, dm1TA, baseBulkBandGuardTA,
    baseKindGuardTA, topClassGuardTA, baseBTA, baseHalfTA, topBandGuardTA, rightClassGuardTA,
    rightBandGuardTA, leftClassGuardTA, leftBandGuardTA, orEqPair, bottomBandGuardTA]

/-- Same identity for the fallback peel's deepest else `rest5` (= baseEntry). -/
theorem rest5_inst_eq_baseLeaf {arity : Nat} (dT kT qT : Term arity .nat) :
    Term.instantiateTopNat qT (codeSubstAt dT kT 1 recEntryThenElseElseElseElseElse)
      = baseLeafTreeTA dT kT qT := by
  simp only [recEntryThenElseElseElseElseElse, recEntryThenElseElseElseElse, recEntryThenElseElseElse,
    recEntryThenElseElse, recEntryThenElse, recEntryThen,
    SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry, SurfaceASTPublic.baseEntry,
    SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q,
    codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4, orEqSucc, le,
    Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift,
    baseLeafTreeTA, bulkGuardTA, bulkCountTA, dm1TA, baseBulkBandGuardTA,
    baseKindGuardTA, topClassGuardTA, baseBTA, baseHalfTA, topBandGuardTA, rightClassGuardTA,
    rightBandGuardTA, leftClassGuardTA, leftBandGuardTA, orEqPair, bottomBandGuardTA]

/-- Head-form lam-body totality (mirror of `baseEntry_headForm_eval_total`); bridges
`RecEvalData.lamBody_total` to the head form via `codeSubstAt_one_recursiveEntry_head`. -/
theorem recEntry_headForm_eval_total {arity : Nat} {dT kT : Term arity .nat} {f' : Nat}
    {rho : Env arity} (R : RecEvalData dT kT f' rho) (qv : Nat) :
    ∃ p, Term.eval Surface.code.body (f' + 1)
        (Term.ite (codeSubstAt dT kT 1 recEntryCond)
          (codeSubstAt dT kT 1 recEntryThen) (codeSubstAt dT kT 1 recEntryElse))
        (Env.cons qv rho) = some p := by
  rw [← codeSubstAt_one_recursiveEntry_head, ← SurfaceASTPublic.recursiveEntry_eq_public]
  exact R.lamBody_total qv

/-- `FormulaDefined` of the rec lam-body leaf over the explicit head form (mirror of
`formulaDefined_baseEntry_lam`). -/
theorem formulaDefined_recEntry_lam {arity : Nat} {f' : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    {dT kT qT : Term arity .nat} {rhs : Term arity .pauli}
    (hq : SFormula.PureNatTerm qT) (R : RecEvalData dT kT f' rho)
    (hrhs : ∃ v, Term.eval Surface.code.body (f' + 1) rhs rho = some v) :
    SFormula.Deriv.FormulaDefined Surface.code.body (f' + 1) rho E
      (.eqPauli
        (.stabAt (SC.closed (.stabLam
          (Term.ite (codeSubstAt dT kT 1 recEntryCond)
            (codeSubstAt dT kT 1 recEntryThen) (codeSubstAt dT kT 1 recEntryElse))))
          (SC.closed qT))
        (SC.closed rhs)) :=
  formulaDefined_stabAtClosedIteLam hq (fun qv => recEntry_headForm_eval_total R qv) hrhs

/-- Fast FOLDED→expanded simp bridge: rewrites a `subtree_inst_eval_total` (folded) to the
peel `def`'s expanded form.  Same simp set the `def` uses; bounded, never whnf-blows-up. -/
macro "rec_exp_bridge" t:term : tactic =>
  `(tactic|
    (have hbr := $t
     simp only [recEntryThen, recEntryThenThen, recEntryThenCond, recEntryThenElse,
       recEntryThenElseThen, recEntryThenElseCond, recEntryThenElseElse,
       recEntryThenElseElseCond, recEntryThenElseElseThen, recEntryThenElseElseElse,
       recEntryThenElseElseElseCond, recEntryThenElseElseElseThen, recEntryThenElseElseElseElse,
       recEntryThenElseElseElseElseCond, recEntryThenElseElseElseElseThen, recEntryThenElseElseElseElseElse,
       recEntryCond, recEntryElse,
       SurfaceASTPublic.recursiveEntry,
       SurfaceASTPublic.promotedBoundaryEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
       SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN, Term.weaken,
       Nat.reduceLT, Nat.reduceEqDiff, reduceDIte, eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq,
       band3, band4, orEqSucc, le, Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift] at hbr
     exact hbr))

/-- **Rec interior-not-inside peel `DerivWF`** — the head-form mirror of `recBasePeelD_Z_WF`.
Three `derivWF_cast_type` peels (head / guard / branch); the lam-body leaf via
`formulaDefined_recEntry_lam`; the two `pauliIteSelect` leaves via `RecOk` subtree totalities
bridged to the expanded goal by `rec_exp_bridge` (the recursing leaf is NOT `PurePauli`). -/
theorem recInteriorIPeelD_WF {arity : Nat} {Γ : List (SFormula arity)}
    (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hInterior hInside} {f' : Nat} {rho : Env arity} {E : PartialStabilizer}
    (R : RecEvalData dT kT f' rho)
    (wBulk : DerivWF hBulk Surface.code.body (f' + 1) rho E)
    (wInterior : DerivWF hInterior Surface.code.body (f' + 1) rho E)
    (wInside : DerivWF hInside Surface.code.body (f' + 1) rho E) :
    DerivWF (recInteriorIPeelD (Γ := Γ) dT kT qT hq hBulk hInterior hInside)
      Surface.code.body (f' + 1) rho E := by
  unfold recInteriorIPeelD
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  refine derivWF_cast_type rfl (by rw [codeSubstAt_one_recursiveEntry_head]) _ _ ?_
  refine derivWF_eqPauliTrans'
    (derivWF_stabAtClosedIteLamEqThen' _ _ _ _ hq
      (derivWF_cast_type rfl (by rw [instantiateTopNat_codeSubstAt_one_recEntryCond]) _ _ wBulk)
      (formulaDefined_recEntry_lam hq R (recEntryThen_inst_eval_total R hq)))
    ?rest
  refine derivWF_cast_type rfl ?_ _ _ ?_
  · simp only [recEntryThen, SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
      SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q,
      codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
      eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4, orEqSucc, le,
      Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]
  · exact derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectThen' _ _ _ wInterior
        (formulaDefined_eqPauli_closed
          (by rec_exp_bridge (recEntryThen_inst_eval_total R hq))
          (by rec_exp_bridge (interiorBranch_inst_eval_total R hq))))
      (derivWF_pauliIteSelectElse' _ _ _ wInside
        (formulaDefined_eqPauli_closed
          (by rec_exp_bridge (interiorBranch_inst_eval_total R hq))
          ((PurePauli.lit Pauli.I).eval_total Surface.code.body (f' + 1) rho)))

/-- **Rec interior-inside peel `DerivWF`** (the IH variant): interior → inside → the recursing
inner-cell stab → IH `pInt`.  Same head-form mirror as `recInteriorIPeelD_WF`, but the inside
node selects the recursing leaf `centerInnerRefA` (its totality `hStab` is the
`closedStabAtSplit` eval the master threads), and the chain bottoms at the IH derivation
`ih` (its `DerivWF` is `wIh`). -/
theorem recInteriorPeelD_WF {arity : Nat} {Γ : List (SFormula arity)}
    (dT kT qT : Term arity .nat) (pInt : Term arity .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hInterior hInside}
    {ih : SFormula.Deriv Γ (.eqPauli (SC.closed (centerInnerRefA dT kT qT)) (SC.closed pInt))}
    {f' : Nat} {rho : Env arity} {E : PartialStabilizer}
    (R : RecEvalData dT kT f' rho)
    (wBulk : DerivWF hBulk Surface.code.body (f' + 1) rho E)
    (wInterior : DerivWF hInterior Surface.code.body (f' + 1) rho E)
    (wInside : DerivWF hInside Surface.code.body (f' + 1) rho E)
    (wIh : DerivWF ih Surface.code.body (f' + 1) rho E)
    (hStab : ∃ v, Term.eval Surface.code.body (f' + 1) (centerInnerRefA dT kT qT) rho = some v) :
    DerivWF (recInteriorPeelD (Γ := Γ) dT kT qT pInt hq hBulk hInterior hInside ih)
      Surface.code.body (f' + 1) rho E := by
  unfold recInteriorPeelD
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  refine derivWF_cast_type rfl (by rw [codeSubstAt_one_recursiveEntry_head]) _ _ ?_
  refine derivWF_eqPauliTrans'
    (derivWF_stabAtClosedIteLamEqThen' _ _ _ _ hq
      (derivWF_cast_type rfl (by rw [instantiateTopNat_codeSubstAt_one_recEntryCond]) _ _ wBulk)
      (formulaDefined_recEntry_lam hq R (recEntryThen_inst_eval_total R hq)))
    ?rest
  refine derivWF_cast_type rfl ?_ _ _ ?_
  · simp only [recEntryThen, SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
      SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q,
      codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
      eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4, orEqSucc, le,
      Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]
  · exact derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectThen' _ _ _ wInterior
        (formulaDefined_eqPauli_closed
          (by rec_exp_bridge (recEntryThen_inst_eval_total R hq))
          (by rec_exp_bridge (interiorBranch_inst_eval_total R hq))))
      (derivWF_eqPauliTrans'
        (derivWF_pauliIteSelectThen' _ _ _ wInside
          (formulaDefined_eqPauli_closed
            (by rec_exp_bridge (interiorBranch_inst_eval_total R hq))
            hStab))
        wIh)

/-- **Rec top-promoted-inside peel `DerivWF`** (IH variant, top cell): interior(else) →
top(then) → inside(then → stab) → IH `pTop`.  Navigates `recEntryThen`'s else (`rest`) then the
top branch; leaf totalities via `rest_inst_eval_total`/`topBranch_inst_eval_total`; `hStab` is
the promoted stab `promotedInnerRefA … topKTA` the master threads. -/
theorem recTopPromotedPeelD_WF {arity : Nat} {Γ : List (SFormula arity)}
    (dT kT qT : Term arity .nat) (pTop : Term arity .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hInterior hTop hInside}
    {ih : SFormula.Deriv Γ (.eqPauli (SC.closed (promotedInnerRefA dT qT (topKTA dT kT))) (SC.closed pTop))}
    {f' : Nat} {rho : Env arity} {E : PartialStabilizer}
    (R : RecEvalData dT kT f' rho)
    (wBulk : DerivWF hBulk Surface.code.body (f' + 1) rho E)
    (wInterior : DerivWF hInterior Surface.code.body (f' + 1) rho E)
    (wTop : DerivWF hTop Surface.code.body (f' + 1) rho E)
    (wInside : DerivWF hInside Surface.code.body (f' + 1) rho E)
    (wIh : DerivWF ih Surface.code.body (f' + 1) rho E)
    (hStab : ∃ v, Term.eval Surface.code.body (f' + 1)
      (promotedInnerRefA dT qT (topKTA dT kT)) rho = some v) :
    DerivWF (recTopPromotedPeelD (Γ := Γ) dT kT qT pTop hq hBulk hInterior hTop hInside ih)
      Surface.code.body (f' + 1) rho E := by
  unfold recTopPromotedPeelD
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  refine derivWF_cast_type rfl (by rw [codeSubstAt_one_recursiveEntry_head]) _ _ ?_
  refine derivWF_eqPauliTrans'
    (derivWF_stabAtClosedIteLamEqThen' _ _ _ _ hq
      (derivWF_cast_type rfl (by rw [instantiateTopNat_codeSubstAt_one_recEntryCond]) _ _ wBulk)
      (formulaDefined_recEntry_lam hq R (recEntryThen_inst_eval_total R hq)))
    ?rest
  refine derivWF_cast_type rfl ?_ _ _ ?_
  · simp only [recEntryThen, SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
      SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q,
      codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
      eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4, orEqSucc, le,
      Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift]
  · exact derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectElse' _ _ _ wInterior
        (formulaDefined_eqPauli_closed
          (by rec_exp_bridge (recEntryThen_inst_eval_total R hq))
          (by rec_exp_bridge (rest_inst_eval_total R hq))))
      (derivWF_eqPauliTrans'
        (derivWF_pauliIteSelectThen' _ _ _ wTop
          (formulaDefined_eqPauli_closed
            (by rec_exp_bridge (rest_inst_eval_total R hq))
            (by rec_exp_bridge (topBranch_inst_eval_total R hq))))
        (derivWF_eqPauliTrans'
          (derivWF_pauliIteSelectThen' _ _ _ wInside
            (formulaDefined_eqPauli_closed
              (by rec_exp_bridge (topBranch_inst_eval_total R hq))
              hStab))
          wIh))

/-- **Rec top-promoted-not-inside peel `DerivWF`** (pure variant, top cell): interior(else) →
top(then) → inside(else) → the pure outer `ite topOuter X I`.  No IH/stab; the final leaf is
`PurePauli` (discharged by `leaf_pp`). -/
theorem recTopPromotedNotInsidePeelD_WF {arity : Nat} {Γ : List (SFormula arity)}
    (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hInterior hTop hInside}
    {f' : Nat} {rho : Env arity} {E : PartialStabilizer}
    (R : RecEvalData dT kT f' rho)
    (wBulk : DerivWF hBulk Surface.code.body (f' + 1) rho E)
    (wInterior : DerivWF hInterior Surface.code.body (f' + 1) rho E)
    (wTop : DerivWF hTop Surface.code.body (f' + 1) rho E)
    (wInside : DerivWF hInside Surface.code.body (f' + 1) rho E) :
    DerivWF (recTopPromotedNotInsidePeelD (Γ := Γ) dT kT qT hq hBulk hInterior hTop hInside)
      Surface.code.body (f' + 1) rho E := by
  unfold recTopPromotedNotInsidePeelD
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  refine derivWF_cast_type rfl (by rw [codeSubstAt_one_recursiveEntry_head]) _ _ ?_
  refine derivWF_eqPauliTrans'
    (derivWF_stabAtClosedIteLamEqThen' _ _ _ _ hq
      (derivWF_cast_type rfl (by rw [instantiateTopNat_codeSubstAt_one_recEntryCond]) _ _ wBulk)
      (formulaDefined_recEntry_lam hq R (recEntryThen_inst_eval_total R hq)))
    ?rest
  refine derivWF_cast_type rfl ?_ _ _ ?_
  · simp only [recEntryThen, SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
      SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q,
      codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
      eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4, orEqSucc, le,
      topOuterGuardTA, rowTA, colTA, cTA, dm1TA,
      Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift, Nat.lt_irrefl, dite_false, dite_true]
  · exact derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectElse' _ _ _ wInterior
        (formulaDefined_eqPauli_closed
          (by rec_exp_bridge (recEntryThen_inst_eval_total R hq))
          (by rec_exp_bridge (rest_inst_eval_total R hq))))
      (derivWF_eqPauliTrans'
        (derivWF_pauliIteSelectThen' _ _ _ wTop
          (formulaDefined_eqPauli_closed
            (by rec_exp_bridge (rest_inst_eval_total R hq))
            (by rec_exp_bridge (topBranch_inst_eval_total R hq))))
        (derivWF_pauliIteSelectElse' _ _ _ wInside
          (formulaDefined_eqPauli_closed
            (by rec_exp_bridge (topBranch_inst_eval_total R hq))
            (PurePauli.eval_total (by leaf_pp) Surface.code.body (f' + 1) rho))))

/-- **Rec right-promoted-inside peel `DerivWF`** (IH variant). -/
theorem recRightPromotedPeelD_WF {arity : Nat} {Γ : List (SFormula arity)}
    (dT kT qT : Term arity .nat) (pRight : Term arity .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hInterior hTop hRight hInside}
    {ih : SFormula.Deriv Γ (.eqPauli (SC.closed (promotedInnerRefA dT qT (rightKTA dT kT))) (SC.closed pRight))}
    {f' : Nat} {rho : Env arity} {E : PartialStabilizer}
    (R : RecEvalData dT kT f' rho)
    (wBulk : DerivWF hBulk Surface.code.body (f' + 1) rho E)
    (wInterior : DerivWF hInterior Surface.code.body (f' + 1) rho E)
    (wTop : DerivWF hTop Surface.code.body (f' + 1) rho E)
    (wRight : DerivWF hRight Surface.code.body (f' + 1) rho E)
    (wInside : DerivWF hInside Surface.code.body (f' + 1) rho E)
    (wIh : DerivWF ih Surface.code.body (f' + 1) rho E)
    (hStab : ∃ v, Term.eval Surface.code.body (f' + 1)
      (promotedInnerRefA dT qT (rightKTA dT kT)) rho = some v) :
    DerivWF (recRightPromotedPeelD (Γ := Γ) dT kT qT pRight hq hBulk hInterior hTop hRight hInside ih)
      Surface.code.body (f' + 1) rho E := by
  unfold recRightPromotedPeelD
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  refine derivWF_cast_type rfl (by rw [codeSubstAt_one_recursiveEntry_head]) _ _ ?_
  refine derivWF_eqPauliTrans'
    (derivWF_stabAtClosedIteLamEqThen' _ _ _ _ hq
      (derivWF_cast_type rfl (by rw [instantiateTopNat_codeSubstAt_one_recEntryCond]) _ _ wBulk)
      (formulaDefined_recEntry_lam hq R (recEntryThen_inst_eval_total R hq)))
    ?rest
  refine derivWF_cast_type rfl ?_ _ _ ?_
  · simp only [recEntryThen, SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
      SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q,
      codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
      eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4, orEqSucc, le,
      Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift, Nat.lt_irrefl, dite_false, dite_true]
  · exact derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectElse' _ _ _ wInterior
        (formulaDefined_eqPauli_closed (by rec_exp_bridge (recEntryThen_inst_eval_total R hq))
          (by rec_exp_bridge (rest_inst_eval_total R hq))))
      (derivWF_eqPauliTrans'
        (derivWF_pauliIteSelectElse' _ _ _ wTop
          (formulaDefined_eqPauli_closed (by rec_exp_bridge (rest_inst_eval_total R hq))
            (by rec_exp_bridge (rest2_inst_eval_total R hq))))
        (derivWF_eqPauliTrans'
          (derivWF_pauliIteSelectThen' _ _ _ wRight
            (formulaDefined_eqPauli_closed (by rec_exp_bridge (rest2_inst_eval_total R hq))
              (by rec_exp_bridge (rightBranch_inst_eval_total R hq))))
          (derivWF_eqPauliTrans'
            (derivWF_pauliIteSelectThen' _ _ _ wInside
              (formulaDefined_eqPauli_closed (by rec_exp_bridge (rightBranch_inst_eval_total R hq)) hStab))
            wIh)))

/-- **Rec right-promoted-not-inside peel `DerivWF`** (pure variant). -/
theorem recRightPromotedNotInsidePeelD_WF {arity : Nat} {Γ : List (SFormula arity)}
    (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hInterior hTop hRight hInside}
    {f' : Nat} {rho : Env arity} {E : PartialStabilizer}
    (R : RecEvalData dT kT f' rho)
    (wBulk : DerivWF hBulk Surface.code.body (f' + 1) rho E)
    (wInterior : DerivWF hInterior Surface.code.body (f' + 1) rho E)
    (wTop : DerivWF hTop Surface.code.body (f' + 1) rho E)
    (wRight : DerivWF hRight Surface.code.body (f' + 1) rho E)
    (wInside : DerivWF hInside Surface.code.body (f' + 1) rho E) :
    DerivWF (recRightPromotedNotInsidePeelD (Γ := Γ) dT kT qT hq hBulk hInterior hTop hRight hInside)
      Surface.code.body (f' + 1) rho E := by
  unfold recRightPromotedNotInsidePeelD
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  refine derivWF_cast_type rfl (by rw [codeSubstAt_one_recursiveEntry_head]) _ _ ?_
  refine derivWF_eqPauliTrans'
    (derivWF_stabAtClosedIteLamEqThen' _ _ _ _ hq
      (derivWF_cast_type rfl (by rw [instantiateTopNat_codeSubstAt_one_recEntryCond]) _ _ wBulk)
      (formulaDefined_recEntry_lam hq R (recEntryThen_inst_eval_total R hq)))
    ?rest
  refine derivWF_cast_type rfl ?_ _ _ ?_
  · simp only [recEntryThen, SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
      SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q,
      codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
      eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4, orEqSucc, le,
      rightOuterGuardTA, rowTA, colTA, rTA, dm1TA,
      Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift, Nat.lt_irrefl, dite_false, dite_true]
  · exact derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectElse' _ _ _ wInterior
        (formulaDefined_eqPauli_closed (by rec_exp_bridge (recEntryThen_inst_eval_total R hq))
          (by rec_exp_bridge (rest_inst_eval_total R hq))))
      (derivWF_eqPauliTrans'
        (derivWF_pauliIteSelectElse' _ _ _ wTop
          (formulaDefined_eqPauli_closed (by rec_exp_bridge (rest_inst_eval_total R hq))
            (by rec_exp_bridge (rest2_inst_eval_total R hq))))
        (derivWF_eqPauliTrans'
          (derivWF_pauliIteSelectThen' _ _ _ wRight
            (formulaDefined_eqPauli_closed (by rec_exp_bridge (rest2_inst_eval_total R hq))
              (by rec_exp_bridge (rightBranch_inst_eval_total R hq))))
          (derivWF_pauliIteSelectElse' _ _ _ wInside
            (formulaDefined_eqPauli_closed (by rec_exp_bridge (rightBranch_inst_eval_total R hq))
              (PurePauli.eval_total (by leaf_pp) Surface.code.body (f' + 1) rho)))))

/-- **Rec left-promoted-inside peel `DerivWF`** (IH variant). -/
theorem recLeftPromotedPeelD_WF {arity : Nat} {Γ : List (SFormula arity)}
    (dT kT qT : Term arity .nat) (pLeft : Term arity .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hInterior hTop hRight hLeft hInside}
    {ih : SFormula.Deriv Γ (.eqPauli (SC.closed (promotedInnerRefA dT qT (leftKTA dT kT))) (SC.closed pLeft))}
    {f' : Nat} {rho : Env arity} {E : PartialStabilizer}
    (R : RecEvalData dT kT f' rho)
    (wBulk : DerivWF hBulk Surface.code.body (f' + 1) rho E)
    (wInterior : DerivWF hInterior Surface.code.body (f' + 1) rho E)
    (wTop : DerivWF hTop Surface.code.body (f' + 1) rho E)
    (wRight : DerivWF hRight Surface.code.body (f' + 1) rho E)
    (wLeft : DerivWF hLeft Surface.code.body (f' + 1) rho E)
    (wInside : DerivWF hInside Surface.code.body (f' + 1) rho E)
    (wIh : DerivWF ih Surface.code.body (f' + 1) rho E)
    (hStab : ∃ v, Term.eval Surface.code.body (f' + 1)
      (promotedInnerRefA dT qT (leftKTA dT kT)) rho = some v) :
    DerivWF (recLeftPromotedPeelD (Γ := Γ) dT kT qT pLeft hq hBulk hInterior hTop hRight hLeft hInside ih)
      Surface.code.body (f' + 1) rho E := by
  unfold recLeftPromotedPeelD
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  refine derivWF_cast_type rfl (by rw [codeSubstAt_one_recursiveEntry_head]) _ _ ?_
  refine derivWF_eqPauliTrans'
    (derivWF_stabAtClosedIteLamEqThen' _ _ _ _ hq
      (derivWF_cast_type rfl (by rw [instantiateTopNat_codeSubstAt_one_recEntryCond]) _ _ wBulk)
      (formulaDefined_recEntry_lam hq R (recEntryThen_inst_eval_total R hq)))
    ?rest
  refine derivWF_cast_type rfl ?_ _ _ ?_
  · simp only [recEntryThen, SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
      SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q,
      codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
      eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4, orEqSucc, le,
      Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift, Nat.lt_irrefl, dite_false, dite_true]
  · exact derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectElse' _ _ _ wInterior
        (formulaDefined_eqPauli_closed (by rec_exp_bridge (recEntryThen_inst_eval_total R hq))
          (by rec_exp_bridge (rest_inst_eval_total R hq))))
      (derivWF_eqPauliTrans'
        (derivWF_pauliIteSelectElse' _ _ _ wTop
          (formulaDefined_eqPauli_closed (by rec_exp_bridge (rest_inst_eval_total R hq))
            (by rec_exp_bridge (rest2_inst_eval_total R hq))))
        (derivWF_eqPauliTrans'
          (derivWF_pauliIteSelectElse' _ _ _ wRight
            (formulaDefined_eqPauli_closed (by rec_exp_bridge (rest2_inst_eval_total R hq))
              (by rec_exp_bridge (rest3_inst_eval_total R hq))))
          (derivWF_eqPauliTrans'
            (derivWF_pauliIteSelectThen' _ _ _ wLeft
              (formulaDefined_eqPauli_closed (by rec_exp_bridge (rest3_inst_eval_total R hq))
                (by rec_exp_bridge (leftBranch_inst_eval_total R hq))))
            (derivWF_eqPauliTrans'
              (derivWF_pauliIteSelectThen' _ _ _ wInside
                (formulaDefined_eqPauli_closed (by rec_exp_bridge (leftBranch_inst_eval_total R hq)) hStab))
              wIh))))

/-- **Rec left-promoted-not-inside peel `DerivWF`** (pure variant). -/
theorem recLeftPromotedNotInsidePeelD_WF {arity : Nat} {Γ : List (SFormula arity)}
    (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hInterior hTop hRight hLeft hInside}
    {f' : Nat} {rho : Env arity} {E : PartialStabilizer}
    (R : RecEvalData dT kT f' rho)
    (wBulk : DerivWF hBulk Surface.code.body (f' + 1) rho E)
    (wInterior : DerivWF hInterior Surface.code.body (f' + 1) rho E)
    (wTop : DerivWF hTop Surface.code.body (f' + 1) rho E)
    (wRight : DerivWF hRight Surface.code.body (f' + 1) rho E)
    (wLeft : DerivWF hLeft Surface.code.body (f' + 1) rho E)
    (wInside : DerivWF hInside Surface.code.body (f' + 1) rho E) :
    DerivWF (recLeftPromotedNotInsidePeelD (Γ := Γ) dT kT qT hq hBulk hInterior hTop hRight hLeft hInside)
      Surface.code.body (f' + 1) rho E := by
  unfold recLeftPromotedNotInsidePeelD
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  refine derivWF_cast_type rfl (by rw [codeSubstAt_one_recursiveEntry_head]) _ _ ?_
  refine derivWF_eqPauliTrans'
    (derivWF_stabAtClosedIteLamEqThen' _ _ _ _ hq
      (derivWF_cast_type rfl (by rw [instantiateTopNat_codeSubstAt_one_recEntryCond]) _ _ wBulk)
      (formulaDefined_recEntry_lam hq R (recEntryThen_inst_eval_total R hq)))
    ?rest
  refine derivWF_cast_type rfl ?_ _ _ ?_
  · simp only [recEntryThen, SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
      SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q,
      codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
      eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4, orEqSucc, le,
      leftOuterGuardTA, rowTA, colTA, rTA, dm1TA,
      Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift, Nat.lt_irrefl, dite_false, dite_true]
  · exact derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectElse' _ _ _ wInterior
        (formulaDefined_eqPauli_closed (by rec_exp_bridge (recEntryThen_inst_eval_total R hq))
          (by rec_exp_bridge (rest_inst_eval_total R hq))))
      (derivWF_eqPauliTrans'
        (derivWF_pauliIteSelectElse' _ _ _ wTop
          (formulaDefined_eqPauli_closed (by rec_exp_bridge (rest_inst_eval_total R hq))
            (by rec_exp_bridge (rest2_inst_eval_total R hq))))
        (derivWF_eqPauliTrans'
          (derivWF_pauliIteSelectElse' _ _ _ wRight
            (formulaDefined_eqPauli_closed (by rec_exp_bridge (rest2_inst_eval_total R hq))
              (by rec_exp_bridge (rest3_inst_eval_total R hq))))
          (derivWF_eqPauliTrans'
            (derivWF_pauliIteSelectThen' _ _ _ wLeft
              (formulaDefined_eqPauli_closed (by rec_exp_bridge (rest3_inst_eval_total R hq))
                (by rec_exp_bridge (leftBranch_inst_eval_total R hq))))
            (derivWF_pauliIteSelectElse' _ _ _ wInside
              (formulaDefined_eqPauli_closed (by rec_exp_bridge (leftBranch_inst_eval_total R hq))
                (PurePauli.eval_total (by leaf_pp) Surface.code.body (f' + 1) rho))))))

/-- **Rec bottom-promoted-inside peel `DerivWF`** (IH variant). -/
theorem recBottomPromotedPeelD_WF {arity : Nat} {Γ : List (SFormula arity)}
    (dT kT qT : Term arity .nat) (pBottom : Term arity .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hInterior hTop hRight hLeft hBottom hInside}
    {ih : SFormula.Deriv Γ (.eqPauli (SC.closed (promotedInnerRefA dT qT (bottomKTA dT kT))) (SC.closed pBottom))}
    {f' : Nat} {rho : Env arity} {E : PartialStabilizer}
    (R : RecEvalData dT kT f' rho)
    (wBulk : DerivWF hBulk Surface.code.body (f' + 1) rho E)
    (wInterior : DerivWF hInterior Surface.code.body (f' + 1) rho E)
    (wTop : DerivWF hTop Surface.code.body (f' + 1) rho E)
    (wRight : DerivWF hRight Surface.code.body (f' + 1) rho E)
    (wLeft : DerivWF hLeft Surface.code.body (f' + 1) rho E)
    (wBottom : DerivWF hBottom Surface.code.body (f' + 1) rho E)
    (wInside : DerivWF hInside Surface.code.body (f' + 1) rho E)
    (wIh : DerivWF ih Surface.code.body (f' + 1) rho E)
    (hStab : ∃ v, Term.eval Surface.code.body (f' + 1)
      (promotedInnerRefA dT qT (bottomKTA dT kT)) rho = some v) :
    DerivWF (recBottomPromotedPeelD (Γ := Γ) dT kT qT pBottom hq hBulk hInterior hTop hRight hLeft hBottom hInside ih)
      Surface.code.body (f' + 1) rho E := by
  unfold recBottomPromotedPeelD
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  refine derivWF_cast_type rfl (by rw [codeSubstAt_one_recursiveEntry_head]) _ _ ?_
  refine derivWF_eqPauliTrans'
    (derivWF_stabAtClosedIteLamEqThen' _ _ _ _ hq
      (derivWF_cast_type rfl (by rw [instantiateTopNat_codeSubstAt_one_recEntryCond]) _ _ wBulk)
      (formulaDefined_recEntry_lam hq R (recEntryThen_inst_eval_total R hq)))
    ?rest
  refine derivWF_cast_type rfl ?_ _ _ ?_
  · simp only [recEntryThen, SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
      SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q,
      codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
      eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4, orEqSucc, le,
      Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift, Nat.lt_irrefl, dite_false, dite_true]
  · exact derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectElse' _ _ _ wInterior
        (formulaDefined_eqPauli_closed (by rec_exp_bridge (recEntryThen_inst_eval_total R hq))
          (by rec_exp_bridge (rest_inst_eval_total R hq))))
      (derivWF_eqPauliTrans'
        (derivWF_pauliIteSelectElse' _ _ _ wTop
          (formulaDefined_eqPauli_closed (by rec_exp_bridge (rest_inst_eval_total R hq))
            (by rec_exp_bridge (rest2_inst_eval_total R hq))))
        (derivWF_eqPauliTrans'
          (derivWF_pauliIteSelectElse' _ _ _ wRight
            (formulaDefined_eqPauli_closed (by rec_exp_bridge (rest2_inst_eval_total R hq))
              (by rec_exp_bridge (rest3_inst_eval_total R hq))))
          (derivWF_eqPauliTrans'
            (derivWF_pauliIteSelectElse' _ _ _ wLeft
              (formulaDefined_eqPauli_closed (by rec_exp_bridge (rest3_inst_eval_total R hq))
                (by rec_exp_bridge (rest4_inst_eval_total R hq))))
            (derivWF_eqPauliTrans'
              (derivWF_pauliIteSelectThen' _ _ _ wBottom
                (formulaDefined_eqPauli_closed (by rec_exp_bridge (rest4_inst_eval_total R hq))
                  (by rec_exp_bridge (bottomBranch_inst_eval_total R hq))))
              (derivWF_eqPauliTrans'
                (derivWF_pauliIteSelectThen' _ _ _ wInside
                  (formulaDefined_eqPauli_closed (by rec_exp_bridge (bottomBranch_inst_eval_total R hq)) hStab))
                wIh)))))

/-- **Rec bottom-promoted-not-inside peel `DerivWF`** (pure variant). -/
theorem recBottomPromotedNotInsidePeelD_WF {arity : Nat} {Γ : List (SFormula arity)}
    (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hInterior hTop hRight hLeft hBottom hInside}
    {f' : Nat} {rho : Env arity} {E : PartialStabilizer}
    (R : RecEvalData dT kT f' rho)
    (wBulk : DerivWF hBulk Surface.code.body (f' + 1) rho E)
    (wInterior : DerivWF hInterior Surface.code.body (f' + 1) rho E)
    (wTop : DerivWF hTop Surface.code.body (f' + 1) rho E)
    (wRight : DerivWF hRight Surface.code.body (f' + 1) rho E)
    (wLeft : DerivWF hLeft Surface.code.body (f' + 1) rho E)
    (wBottom : DerivWF hBottom Surface.code.body (f' + 1) rho E)
    (wInside : DerivWF hInside Surface.code.body (f' + 1) rho E) :
    DerivWF (recBottomPromotedNotInsidePeelD (Γ := Γ) dT kT qT hq hBulk hInterior hTop hRight hLeft hBottom hInside)
      Surface.code.body (f' + 1) rho E := by
  unfold recBottomPromotedNotInsidePeelD
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  refine derivWF_cast_type rfl (by rw [codeSubstAt_one_recursiveEntry_head]) _ _ ?_
  refine derivWF_eqPauliTrans'
    (derivWF_stabAtClosedIteLamEqThen' _ _ _ _ hq
      (derivWF_cast_type rfl (by rw [instantiateTopNat_codeSubstAt_one_recEntryCond]) _ _ wBulk)
      (formulaDefined_recEntry_lam hq R (recEntryThen_inst_eval_total R hq)))
    ?rest
  refine derivWF_cast_type rfl ?_ _ _ ?_
  · simp only [recEntryThen, SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
      SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q,
      codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
      eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4, orEqSucc, le,
      bottomOuterGuardTA, rowTA, colTA, cTA, dm1TA,
      Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift, Nat.lt_irrefl, dite_false, dite_true]
  · exact derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectElse' _ _ _ wInterior
        (formulaDefined_eqPauli_closed (by rec_exp_bridge (recEntryThen_inst_eval_total R hq))
          (by rec_exp_bridge (rest_inst_eval_total R hq))))
      (derivWF_eqPauliTrans'
        (derivWF_pauliIteSelectElse' _ _ _ wTop
          (formulaDefined_eqPauli_closed (by rec_exp_bridge (rest_inst_eval_total R hq))
            (by rec_exp_bridge (rest2_inst_eval_total R hq))))
        (derivWF_eqPauliTrans'
          (derivWF_pauliIteSelectElse' _ _ _ wRight
            (formulaDefined_eqPauli_closed (by rec_exp_bridge (rest2_inst_eval_total R hq))
              (by rec_exp_bridge (rest3_inst_eval_total R hq))))
          (derivWF_eqPauliTrans'
            (derivWF_pauliIteSelectElse' _ _ _ wLeft
              (formulaDefined_eqPauli_closed (by rec_exp_bridge (rest3_inst_eval_total R hq))
                (by rec_exp_bridge (rest4_inst_eval_total R hq))))
            (derivWF_eqPauliTrans'
              (derivWF_pauliIteSelectThen' _ _ _ wBottom
                (formulaDefined_eqPauli_closed (by rec_exp_bridge (rest4_inst_eval_total R hq))
                  (by rec_exp_bridge (bottomBranch_inst_eval_total R hq))))
              (derivWF_pauliIteSelectElse' _ _ _ wInside
                (formulaDefined_eqPauli_closed (by rec_exp_bridge (bottomBranch_inst_eval_total R hq))
                  (PurePauli.eval_total (by leaf_pp) Surface.code.body (f' + 1) rho)))))))

/-- **Rec fallback peel `DerivWF`** (bulk true, all cells false → baseEntry → baseLeafTreeTA).
Five `pauliIteSelectElse` selections down the cell chain, bottoming at `baseLeafSelfEq`. -/
theorem recFallbackPeelD_WF {arity : Nat} {Γ : List (SFormula arity)}
    (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hInterior hTop hRight hLeft hBottom}
    {f' : Nat} {rho : Env arity} {E : PartialStabilizer}
    (R : RecEvalData dT kT f' rho)
    (wBulk : DerivWF hBulk Surface.code.body (f' + 1) rho E)
    (wInterior : DerivWF hInterior Surface.code.body (f' + 1) rho E)
    (wTop : DerivWF hTop Surface.code.body (f' + 1) rho E)
    (wRight : DerivWF hRight Surface.code.body (f' + 1) rho E)
    (wLeft : DerivWF hLeft Surface.code.body (f' + 1) rho E)
    (wBottom : DerivWF hBottom Surface.code.body (f' + 1) rho E) :
    DerivWF (recFallbackPeelD (Γ := Γ) dT kT qT hq hBulk hInterior hTop hRight hLeft hBottom)
      Surface.code.body (f' + 1) rho E := by
  unfold recFallbackPeelD
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  refine derivWF_cast_type rfl (by rw [codeSubstAt_one_recursiveEntry_head]) _ _ ?_
  refine derivWF_eqPauliTrans'
    (derivWF_stabAtClosedIteLamEqThen' _ _ _ _ hq
      (derivWF_cast_type rfl (by rw [instantiateTopNat_codeSubstAt_one_recEntryCond]) _ _ wBulk)
      (formulaDefined_recEntry_lam hq R (recEntryThen_inst_eval_total R hq)))
    ?rest
  refine derivWF_cast_type rfl ?_ _ _ ?_
  · simp only [recEntryThen, SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
      SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q,
      codeSubstAt, liftTopN, Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
      eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4, orEqSucc, le,
      Term.instantiateTopNat, Term.instantiateNatAt, instTop_lift, Nat.lt_irrefl, dite_false, dite_true]
  · exact derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectElse' _ _ _ wInterior
        (formulaDefined_eqPauli_closed (by rec_exp_bridge (recEntryThen_inst_eval_total R hq))
          (by rec_exp_bridge (rest_inst_eval_total R hq))))
      (derivWF_eqPauliTrans'
        (derivWF_pauliIteSelectElse' _ _ _ wTop
          (formulaDefined_eqPauli_closed (by rec_exp_bridge (rest_inst_eval_total R hq))
            (by rec_exp_bridge (rest2_inst_eval_total R hq))))
        (derivWF_eqPauliTrans'
          (derivWF_pauliIteSelectElse' _ _ _ wRight
            (formulaDefined_eqPauli_closed (by rec_exp_bridge (rest2_inst_eval_total R hq))
              (by rec_exp_bridge (rest3_inst_eval_total R hq))))
          (derivWF_eqPauliTrans'
            (derivWF_pauliIteSelectElse' _ _ _ wLeft
              (formulaDefined_eqPauli_closed (by rec_exp_bridge (rest3_inst_eval_total R hq))
                (by rec_exp_bridge (rest4_inst_eval_total R hq))))
            (derivWF_eqPauliTrans'
              (derivWF_pauliIteSelectElse' _ _ _ wBottom
                (formulaDefined_eqPauli_closed (by rec_exp_bridge (rest4_inst_eval_total R hq))
                  (by rec_exp_bridge (rest5_inst_eval_total R hq))))
              (derivWF_cast_type rfl
                (by simp only [SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
                  SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN,
                  Term.weaken, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte, eq_mp_eq_cast,
                  eq_mpr_eq_cast, cast_eq, Term.instantiateNatAt, instTop_lift,
                  baseLeafTreeTA, bulkGuardTA, bulkCountTA, dm1TA, baseBulkBandGuardTA, band3,
                  orEqSucc, baseKindGuardTA, topClassGuardTA, baseBTA, baseHalfTA, topBandGuardTA,
                  rightClassGuardTA, rightBandGuardTA, leftClassGuardTA, leftBandGuardTA, orEqPair,
                  bottomBandGuardTA]) _ _
                (baseLeafSelfEq_WF Γ dT kT qT hd hk hq))))))

/-- **Boundary strip `DerivWF`** (bulk false → baseEntry → baseLeafTreeTA), EqElse head. -/
theorem baseBoundaryStripD_WF {arity : Nat} {Γ : List (SFormula arity)}
    (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk}
    {f' : Nat} {rho : Env arity} {E : PartialStabilizer}
    (R : RecEvalData dT kT f' rho)
    (wBulk : DerivWF hBulk Surface.code.body (f' + 1) rho E) :
    DerivWF (baseBoundaryStripD (Γ := Γ) dT kT qT hq hBulk)
      Surface.code.body (f' + 1) rho E := by
  unfold baseBoundaryStripD
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  refine derivWF_cast_type rfl (by rw [codeSubstAt_one_recursiveEntry_head]) _ _ ?_
  refine derivWF_eqPauliTrans'
    (derivWF_stabAtClosedIteLamEqElse' _ _ _ _ hq
      (derivWF_cast_type rfl (by rw [instantiateTopNat_codeSubstAt_one_recEntryCond]) _ _ wBulk)
      (formulaDefined_recEntry_lam hq R (recEntryElse_inst_eval_total R hq)))
    ?rest
  refine derivWF_cast_type rfl (by rw [recEntryElse_inst_eq_baseLeaf]) _ _
    (baseLeafSelfEq_WF Γ dT kT qT hd hk hq)

/-- **Rec entry master `DerivWF`** — the 12-leaf boolCases tree.  Mirrors `recEntryMasterD`
exactly: each leaf is `eqPauliTrans (peel) (eqPauliSymm (recLeaf))`; the five `inside`-true
leaves thread the recursive IH (`derivWF_contextWeakening' wpXD` + `hStabX`); guards are all
`.hyp`/`.assumption` so their `DerivWF` is `True.intro`. -/
theorem recEntryMasterD_WF {arity : Nat} {Γ : List (SFormula arity)}
    (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {pIntD : SFormula.Deriv Γ (.eqPauli (SC.closed (centerInnerRefA dT kT qT)) (SC.closed pInt))}
    {pTopD : SFormula.Deriv Γ (.eqPauli (SC.closed (promotedInnerRefA dT qT (topKTA dT kT))) (SC.closed pTop))}
    {pRightD : SFormula.Deriv Γ (.eqPauli (SC.closed (promotedInnerRefA dT qT (rightKTA dT kT))) (SC.closed pRight))}
    {pLeftD : SFormula.Deriv Γ (.eqPauli (SC.closed (promotedInnerRefA dT qT (leftKTA dT kT))) (SC.closed pLeft))}
    {pBottomD : SFormula.Deriv Γ (.eqPauli (SC.closed (promotedInnerRefA dT qT (bottomKTA dT kT))) (SC.closed pBottom))}
    {f' : Nat} {rho : Env arity} {E : PartialStabilizer}
    (R : RecEvalData dT kT f' rho)
    (wpIntD : DerivWF pIntD Surface.code.body (f' + 1) rho E)
    (wpTopD : DerivWF pTopD Surface.code.body (f' + 1) rho E)
    (wpRightD : DerivWF pRightD Surface.code.body (f' + 1) rho E)
    (wpLeftD : DerivWF pLeftD Surface.code.body (f' + 1) rho E)
    (wpBottomD : DerivWF pBottomD Surface.code.body (f' + 1) rho E)
    (hpInt : ∃ v, Term.eval Surface.code.body (f' + 1) pInt rho = some v)
    (hpTop : ∃ v, Term.eval Surface.code.body (f' + 1) pTop rho = some v)
    (hpRight : ∃ v, Term.eval Surface.code.body (f' + 1) pRight rho = some v)
    (hpLeft : ∃ v, Term.eval Surface.code.body (f' + 1) pLeft rho = some v)
    (hpBottom : ∃ v, Term.eval Surface.code.body (f' + 1) pBottom rho = some v)
    (hStabInt : ∃ v, Term.eval Surface.code.body (f' + 1) (centerInnerRefA dT kT qT) rho = some v)
    (hStabTop : ∃ v, Term.eval Surface.code.body (f' + 1) (promotedInnerRefA dT qT (topKTA dT kT)) rho = some v)
    (hStabRight : ∃ v, Term.eval Surface.code.body (f' + 1) (promotedInnerRefA dT qT (rightKTA dT kT)) rho = some v)
    (hStabLeft : ∃ v, Term.eval Surface.code.body (f' + 1) (promotedInnerRefA dT qT (leftKTA dT kT)) rho = some v)
    (hStabBottom : ∃ v, Term.eval Surface.code.body (f' + 1) (promotedInnerRefA dT qT (bottomKTA dT kT)) rho = some v) :
    DerivWF (recEntryMasterD dT kT qT pInt pTop pRight pLeft pBottom hq pIntD pTopD pRightD pLeftD pBottomD)
      Surface.code.body (f' + 1) rho E := by
  unfold recEntryMasterD
  refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?bulkT ?bulkF
  case bulkT =>
    refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?intT ?intF
    case intT =>
      refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?iInside ?iI
      case iInside =>
        refine derivWF_eqPauliTrans'
          (recInteriorPeelD_WF dT kT qT pInt hd hk hq R True.intro True.intro True.intro
            (derivWF_contextWeakening' _ _ wpIntD) hStabInt)
          (derivWF_eqPauliSymm' ?_)
        refine recLeafInt_WF _ dT kT qT pInt pTop pRight pLeft pBottom
          ?_ ?_ ?_ hd hk hq hpInt hpTop hpRight hpLeft hpBottom <;> exact True.intro
      case iI =>
        refine derivWF_eqPauliTrans'
          (recInteriorIPeelD_WF dT kT qT hd hk hq R True.intro True.intro True.intro)
          (derivWF_eqPauliSymm' ?_)
        refine recLeafIntI_WF _ dT kT qT pInt pTop pRight pLeft pBottom
          ?_ ?_ ?_ hd hk hq hpInt hpTop hpRight hpLeft hpBottom <;> exact True.intro
    case intF =>
      refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?topT ?topF
      case topT =>
        refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?tInside ?tNI
        case tInside =>
          refine derivWF_eqPauliTrans'
            (recTopPromotedPeelD_WF dT kT qT pTop hd hk hq R True.intro True.intro True.intro True.intro
              (derivWF_contextWeakening' _ _ wpTopD) hStabTop)
            (derivWF_eqPauliSymm' ?_)
          refine recLeafTop_WF _ dT kT qT pInt pTop pRight pLeft pBottom
            ?_ ?_ ?_ ?_ hd hk hq hpInt hpTop hpRight hpLeft hpBottom <;> exact True.intro
        case tNI =>
          refine derivWF_eqPauliTrans'
            (recTopPromotedNotInsidePeelD_WF dT kT qT hd hk hq R True.intro True.intro True.intro True.intro)
            (derivWF_eqPauliSymm' ?_)
          refine recLeafTopNI_WF _ dT kT qT pInt pTop pRight pLeft pBottom
            ?_ ?_ ?_ ?_ hd hk hq hpInt hpTop hpRight hpLeft hpBottom <;> exact True.intro
      case topF =>
        refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?rightT ?rightF
        case rightT =>
          refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?rInside ?rNI
          case rInside =>
            refine derivWF_eqPauliTrans'
              (recRightPromotedPeelD_WF dT kT qT pRight hd hk hq R True.intro True.intro True.intro True.intro True.intro
                (derivWF_contextWeakening' _ _ wpRightD) hStabRight)
              (derivWF_eqPauliSymm' ?_)
            refine recLeafRight_WF _ dT kT qT pInt pTop pRight pLeft pBottom
              ?_ ?_ ?_ ?_ ?_ hd hk hq hpInt hpTop hpRight hpLeft hpBottom <;> exact True.intro
          case rNI =>
            refine derivWF_eqPauliTrans'
              (recRightPromotedNotInsidePeelD_WF dT kT qT hd hk hq R True.intro True.intro True.intro True.intro True.intro)
              (derivWF_eqPauliSymm' ?_)
            refine recLeafRightNI_WF _ dT kT qT pInt pTop pRight pLeft pBottom
              ?_ ?_ ?_ ?_ ?_ hd hk hq hpInt hpTop hpRight hpLeft hpBottom <;> exact True.intro
        case rightF =>
          refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?leftT ?leftF
          case leftT =>
            refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?lInside ?lNI
            case lInside =>
              refine derivWF_eqPauliTrans'
                (recLeftPromotedPeelD_WF dT kT qT pLeft hd hk hq R True.intro True.intro True.intro True.intro True.intro True.intro
                  (derivWF_contextWeakening' _ _ wpLeftD) hStabLeft)
                (derivWF_eqPauliSymm' ?_)
              refine recLeafLeft_WF _ dT kT qT pInt pTop pRight pLeft pBottom
                ?_ ?_ ?_ ?_ ?_ ?_ hd hk hq hpInt hpTop hpRight hpLeft hpBottom <;> exact True.intro
            case lNI =>
              refine derivWF_eqPauliTrans'
                (recLeftPromotedNotInsidePeelD_WF dT kT qT hd hk hq R True.intro True.intro True.intro True.intro True.intro True.intro)
                (derivWF_eqPauliSymm' ?_)
              refine recLeafLeftNI_WF _ dT kT qT pInt pTop pRight pLeft pBottom
                ?_ ?_ ?_ ?_ ?_ ?_ hd hk hq hpInt hpTop hpRight hpLeft hpBottom <;> exact True.intro
          case leftF =>
            refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?bottomT ?bottomF
            case bottomT =>
              refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?bInside ?bNI
              case bInside =>
                refine derivWF_eqPauliTrans'
                  (recBottomPromotedPeelD_WF dT kT qT pBottom hd hk hq R True.intro True.intro True.intro True.intro True.intro True.intro True.intro
                    (derivWF_contextWeakening' _ _ wpBottomD) hStabBottom)
                  (derivWF_eqPauliSymm' ?_)
                refine recLeafBottom_WF _ dT kT qT pInt pTop pRight pLeft pBottom
                  ?_ ?_ ?_ ?_ ?_ ?_ ?_ hd hk hq hpInt hpTop hpRight hpLeft hpBottom <;> exact True.intro
              case bNI =>
                refine derivWF_eqPauliTrans'
                  (recBottomPromotedNotInsidePeelD_WF dT kT qT hd hk hq R True.intro True.intro True.intro True.intro True.intro True.intro True.intro)
                  (derivWF_eqPauliSymm' ?_)
                refine recLeafBottomNI_WF _ dT kT qT pInt pTop pRight pLeft pBottom
                  ?_ ?_ ?_ ?_ ?_ ?_ ?_ hd hk hq hpInt hpTop hpRight hpLeft hpBottom <;> exact True.intro
            case bottomF =>
              refine derivWF_eqPauliTrans'
                (recFallbackPeelD_WF dT kT qT hd hk hq R True.intro True.intro True.intro True.intro True.intro True.intro)
                (derivWF_eqPauliSymm' ?_)
              refine recLeafFallback_WF _ dT kT qT pInt pTop pRight pLeft pBottom
                ?_ ?_ ?_ ?_ ?_ ?_ hd hk hq hpInt hpTop hpRight hpLeft hpBottom <;> exact True.intro
  case bulkF =>
    refine derivWF_eqPauliTrans'
      (baseBoundaryStripD_WF dT kT qT hd hk hq R True.intro)
      (derivWF_eqPauliSymm' ?_)
    refine recLeafBoundary_WF _ dT kT qT pInt pTop pRight pLeft pBottom
      ?_ hd hk hq hpInt hpTop hpRight hpLeft hpBottom <;> exact True.intro

/-! ## Residual leaf #1: the flat row-entry totality (OPEN)

`rowEntryFlatSym = eqPauliTrans (surfaceRowEntryCharSymbolicA …) (rowSymTreeFlatBridgeSym …)`.
`surfaceRowEntryCharSymbolicA` recurses on `m = D.index`; closing its `DerivWFA`
re-runs that recursion (`recRowConvergeA` / `recEntryMasterD` boolCases masters at
every depth, plus the `rowSymTreeFlatBridgeSym` / `recFlatMasterD` bridge).  This
is the genuinely deep, ∀-D residual flagged in `SurfaceNormalizers.lean`. -/
/-! ### The `m`-induction skeleton for the symbolic row-entry characterization

`surfaceRowEntryCharSymbolicA` recurses on `m = D.index`: base `m = 0` dispatches
via `baseRowConvergeA` (the base master), and step `m + 1` builds five IH-resolved
sub-derivations `pIntA … pBottomA` (each `eqPauliTrans (closedStabAtSplit …) (IH …)`)
and dispatches via `recRowConvergeA` (the rec master).  Its `DerivWFA` is therefore
proved by induction on `m` with **one** base + **one** step: the step relays the IH
(the five sub-derivations' `DerivWFA`) and discharges this level's nodes.  The
per-level cost does NOT multiply — the entire `m`-family is covered by the two
master `_WF` helpers below.

The two master `_WF` helpers (`baseRowConvergeA_WF`, `recRowConvergeA_WF`) are the
genuine residual: each is a flat (non-`m`-recursing) `boolCases` tree over ~13 leaf
peels, each leaf needing bespoke closed-`Term.eval` discharge (the `baseLeafTreeTA`
pauli-literal `ite`-trees are NOT `PureTerm`, so the uniform `…_closedPure`
dischargers do not apply).  Stated with the purity hypotheses the recursion supplies. -/

/-! ### STEP C — the row-select `DerivWFA` helpers

`surfaceCodeRowSelectBase/Recursive` = `pureEqStabTrans n (recCall dT kT)
(codeSubstTerm …) (stabLam …-subst) (surfaceCodeRowUnfold …) (surfaceCodeSubstBody…)`,
and `pureEqStabTrans = cut2 (eqStabTrans-node) hUnfold hSubst`.  So its `DerivWFA`
is `⟨DerivWF (eqStabTrans node), DerivWFA (surfaceCodeRowUnfold …),
DerivWFA (surfaceCodeSubstBody… )⟩`.  The `recUnfold`/`iteSelect` side-data is the
row-projection eval data (`n`/`dT`/`kT`/`recCall` evals + range), supplied by the
`DistAtA` distance fact and `recCall_total_symbolicDK` at the call site. -/

/-- The `recUnfold` leaf's eval side-data: `n`/`dT`/`kT`/`recCall` all evaluate, and
the `recCall` stabilizer is total up to `nv`.  This is `DerivWFA (surfaceCodeRowUnfold
…)` packaged. -/
def RowUnfoldData {arity fuel : Nat} (n : STerm arity .nat) (dT kT : Term arity .nat)
    (rho : Env arity) (E : PartialStabilizer) : Prop :=
  ∃ nv dv kv sa,
    n.eval Surface.code.body fuel rho E = some nv ∧
      Term.eval Surface.code.body fuel dT rho = some dv ∧
        Term.eval Surface.code.body fuel kT rho = some kv ∧
          Term.eval Surface.code.body fuel (.recCall dT kT) rho = some sa ∧
            ∀ q, q < nv → ∃ p, sa q = some p

theorem surfaceCodeRowUnfold_WF {arity fuel : Nat} (n : STerm arity .nat)
    (dT kT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT)
    (rho : Env arity) (E : PartialStabilizer)
    (hData : RowUnfoldData (fuel := fuel) n dT kT rho E) :
    DerivWFA (surfaceCodeRowUnfold (fuel := fuel) n dT kT hd hk) rho E := by
  unfold surfaceCodeRowUnfold
  exact hData

theorem surfaceCodeSubstBodyBase_WF {arity fuel : Nat} (n : STerm arity .nat)
    (dT kT : Term arity .nat)
    (hGuard : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat dT (n5 : Term arity .nat))) (SC.b true)))
    (rho : Env arity) (E : PartialStabilizer)
    (hGuardWF : DerivWFA hGuard rho E)
    {nv : Nat} (hn : n.eval Surface.code.body fuel rho E = some nv)
    (hS1 : ∃ s1, Term.eval Surface.code.body fuel
        (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.baseEntry)) rho = some s1 ∧
      ∀ q, q < nv → ∃ p, s1 q = some p) :
    DerivWFA (surfaceCodeSubstBodyBase (fuel := fuel) n dT kT hGuard) rho E := by
  unfold surfaceCodeSubstBodyBase
  simp only [eq_mpr_eq_cast]
  obtain ⟨s1, hs1, hs1def⟩ := hS1
  refine derivWFA_cast_type (by rw [surfaceCodeSubstBody_eq]) _ _ ?_
  exact ⟨nv, s1, hn, hGuardWF, hs1, hs1def⟩

theorem surfaceCodeSubstBodyRecursive_WF {arity fuel : Nat} (n : STerm arity .nat)
    (dT kT : Term arity .nat)
    (hGuard : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat dT (n5 : Term arity .nat))) (SC.b false)))
    (rho : Env arity) (E : PartialStabilizer)
    (hGuardWF : DerivWFA hGuard rho E)
    {nv : Nat} (hn : n.eval Surface.code.body fuel rho E = some nv)
    (hS2 : ∃ s2, Term.eval Surface.code.body fuel
        (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)) rho = some s2 ∧
      ∀ q, q < nv → ∃ p, s2 q = some p) :
    DerivWFA (surfaceCodeSubstBodyRecursive (fuel := fuel) n dT kT hGuard) rho E := by
  unfold surfaceCodeSubstBodyRecursive
  simp only [eq_mpr_eq_cast]
  obtain ⟨s2, hs2, hs2def⟩ := hS2
  refine derivWFA_cast_type (by rw [surfaceCodeSubstBody_eq]) _ _ ?_
  exact ⟨nv, s2, hn, hGuardWF, hs2, hs2def⟩

theorem surfaceCodeRowSelectBase_WF {arity fuel : Nat} (n : STerm arity .nat)
    (dT kT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT)
    (hGuard : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat dT (n5 : Term arity .nat))) (SC.b true)))
    (rho : Env arity) (E : PartialStabilizer)
    (hGuardWF : DerivWFA hGuard rho E)
    (hUnfold : DerivWFA (surfaceCodeRowUnfold (fuel := fuel) n dT kT hd hk) rho E)
    (hSubst : DerivWFA (surfaceCodeSubstBodyBase (fuel := fuel) n dT kT hGuard) rho E) :
    DerivWFA (surfaceCodeRowSelectBase (fuel := fuel) n dT kT hd hk hGuard) rho E := by
  unfold surfaceCodeRowSelectBase pureEqStabTrans
  exact ⟨⟨True.intro, True.intro⟩, hUnfold, hSubst⟩

theorem surfaceCodeRowSelectRecursive_WF {arity fuel : Nat} (n : STerm arity .nat)
    (dT kT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT)
    (hGuard : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat dT (n5 : Term arity .nat))) (SC.b false)))
    (rho : Env arity) (E : PartialStabilizer)
    (hGuardWF : DerivWFA hGuard rho E)
    (hUnfold : DerivWFA (surfaceCodeRowUnfold (fuel := fuel) n dT kT hd hk) rho E)
    (hSubst : DerivWFA (surfaceCodeSubstBodyRecursive (fuel := fuel) n dT kT hGuard) rho E) :
    DerivWFA (surfaceCodeRowSelectRecursive (fuel := fuel) n dT kT hd hk hGuard) rho E := by
  unfold surfaceCodeRowSelectRecursive pureEqStabTrans
  exact ⟨⟨True.intro, True.intro⟩, hUnfold, hSubst⟩

/-! ### STEP D — row-select WF providers from a `DistAtA` + fuel bound

The two providers below assemble the STEP-C row-select WFs at the *symbolic distance*
`DD.dT` (evaluating to `oddDistance m = 2m+3`), the canonical range `n =
SC.n (nQubits (oddDistance m)) = (2m+3)²`, and any pure index `kT`.  All eval
side-data is mechanical: `n.eval` via `scn_eval`, `dT.eval` via `DD.evalsTo`,
`kT.eval` via purity, the `recCall` totality via `recCall_total_symbolicDK`
(needing `m + 2 ≤ fuel`), and the `stabLam` body totality via the `PurePauli`
substitution bank.  These discharge the `hRowSel` hypotheses of
`baseRowConvergeA_WF` / `recRowConvergeA_WF`. -/

/-- `RowUnfoldData` at the canonical range `nQubits (oddDistance m)`, from `DistAtA`
+ fuel bound. -/
theorem rowUnfoldData_of_DistAtA {arity fuel m : Nat} (DD : DistAtA arity m)
    {kT : Term arity .nat} (hk : SFormula.PureNatTerm kT) (rho : Env arity)
    (E : PartialStabilizer) (hfuel : m + 2 ≤ fuel) :
    RowUnfoldData (fuel := fuel) (SC.n (nQubits (oddDistance m))) DD.dT kT rho E := by
  obtain ⟨kv, hkv⟩ := hk.eval_total Surface.code.body fuel rho
  have hdv : Term.eval Surface.code.body fuel DD.dT rho = some (2 * m + 3) := by
    have := DD.evalsTo (fuel := fuel) rho
    simpa only [oddDistance] using this
  obtain ⟨sa, hsa, hsadef⟩ := recCall_total_symbolicDK m fuel hfuel rho
    (fun fuel' => by simpa only [oddDistance] using DD.evalsTo (fuel := fuel') rho) hk
  refine ⟨nQubits (oddDistance m), 2 * m + 3, kv, sa, scn_eval _ _ _ _ _, hdv, hkv, hsa, ?_⟩
  intro q hq
  exact hsadef q (by simpa only [nQubits, oddDistance] using hq)

/-- The `stabLam`-of-substituted-`PurePauli` totality (`hS1`/`hS2`): the lam body
`codeSubstAt DD.dT kT 1 entry` (with `entry` a `PurePauli`) is total at every opened
env, so the `stabLam` evaluates to a partial stabilizer total up to any bound. -/
theorem stabLamSubst_total {arity fuel m : Nat} (DD : DistAtA arity m)
    {kT : Term arity .nat} (hk : SFormula.PureNatTerm kT) (rho : Env arity)
    {entry : Term (1 + 2) .pauli} (hentry : PurePauli entry) :
    ∃ s1, Term.eval Surface.code.body fuel
        (.stabLam (QHL.CodeLang.Verify.codeSubstAt DD.dT kT 1 entry)) rho = some s1 ∧
      ∀ q, q < nQubits (oddDistance m) → ∃ p, s1 q = some p := by
  refine ⟨fun q => Term.eval Surface.code.body fuel
      (QHL.CodeLang.Verify.codeSubstAt DD.dT kT 1 entry) (Env.cons q rho),
      by simp only [Term.eval], ?_⟩
  intro q _
  exact purePauli_codeSubstAt_one_eval_total DD.pure hk hentry Surface.code.body fuel
    (Env.cons q rho)

/-- The BASE row-select WF at the canonical range, from `DistAtA` + fuel bound. -/
theorem surfaceCodeRowSelectBase_WF_of_DistAtA {arity fuel m : Nat} (DD : DistAtA arity m)
    {kT : Term arity .nat} (hk : SFormula.PureNatTerm kT) (rho : Env arity)
    (E : PartialStabilizer) (hfuel : m + 2 ≤ fuel)
    (hGuard : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat DD.dT (n5 : Term arity .nat))) (SC.b true)))
    (hGuardWF : DerivWFA hGuard rho E) :
    DerivWFA (surfaceCodeRowSelectBase (fuel := fuel) (SC.n (nQubits (oddDistance m)))
      DD.dT kT DD.pure hk hGuard) rho E := by
  refine surfaceCodeRowSelectBase_WF _ DD.dT kT DD.pure hk hGuard rho E hGuardWF
    (surfaceCodeRowUnfold_WF _ DD.dT kT DD.pure hk rho E
      (rowUnfoldData_of_DistAtA DD hk rho E hfuel))
    (surfaceCodeSubstBodyBase_WF _ DD.dT kT hGuard rho E hGuardWF (scn_eval _ _ _ _ _)
      (stabLamSubst_total DD hk rho
        (SurfaceASTPublic.baseEntry_eq_public ▸ baseEntry_purePauli)))

/-- The `stabLam`-of-substituted-`recursiveEntry` totality (`hS2`): the recursive lam
body `codeSubstAt DD.dT kT 1 recursiveEntry` is NOT `PurePauli`; its per-`q` totality
comes from `RecEvalData.lamBody_total` (the keystone recursive-entry convergence). -/
theorem stabLamSubstRec_total {arity m f' : Nat} {rho : Env arity} (DD : DistAtA arity (m + 1))
    {kT : Term arity .nat} (R : RecEvalData DD.dT kT f' rho) :
    ∃ s2, Term.eval Surface.code.body (f' + 1)
        (.stabLam (QHL.CodeLang.Verify.codeSubstAt DD.dT kT 1 SurfaceASTPublic.recursiveEntry))
          rho = some s2 ∧
      ∀ q, q < nQubits (oddDistance (m + 1)) → ∃ p, s2 q = some p := by
  -- `RecEvalData.lamBody_total` totalizes `codeSubstAt … Surface.recursiveEntry`;
  -- bridge to the `SurfaceASTPublic.recursiveEntry` public mirror.
  rw [← SurfaceASTPublic.recursiveEntry_eq_public]
  refine ⟨fun q => Term.eval Surface.code.body (f' + 1)
      (QHL.CodeLang.Verify.codeSubstAt DD.dT kT 1 Surface.recursiveEntry)
        (Env.cons q rho), by simp only [Term.eval], ?_⟩
  intro q _
  exact R.lamBody_total q

/-- The RECURSIVE row-select WF at the canonical range, at the rec-master fuel `f'+1`,
from `DistAtA (m+1)` + a `RecEvalData`. -/
theorem surfaceCodeRowSelectRecursive_WF_of_DistAtA {arity m f' : Nat} {rho : Env arity}
    (DD : DistAtA arity (m + 1))
    {kT : Term arity .nat} (hk : SFormula.PureNatTerm kT)
    (E : PartialStabilizer) (hfuel : (m + 1) + 2 ≤ f' + 1)
    (R : RecEvalData DD.dT kT f' rho) :
    DerivWFA (surfaceCodeRowSelectRecursive (fuel := f' + 1)
      (SC.n (nQubits (oddDistance (m + 1)))) DD.dT kT DD.pure hk
      (distLtFiveFalse_of_DistAtA DD)) rho E := by
  refine surfaceCodeRowSelectRecursive_WF _ DD.dT kT DD.pure hk (distLtFiveFalse_of_DistAtA DD)
      rho E True.intro
    (surfaceCodeRowUnfold_WF _ DD.dT kT DD.pure hk rho E
      (rowUnfoldData_of_DistAtA DD hk rho E hfuel))
    (surfaceCodeSubstBodyRecursive_WF _ DD.dT kT (distLtFiveFalse_of_DistAtA DD) rho E True.intro
      (scn_eval _ _ _ _ _)
      (stabLamSubstRec_total DD R))

/-! ### STEP D' — ALL-WIDTH row-select WF providers (local projection width)

The providers above fix the projection width to the global stabilizer width
`SC.n (nQubits (oddDistance m))`.  The refactored `surfaceRowEntryCharSymbolicA` instead
uses the **local** width `SC.succClosed qT = qT + 1`, so the `eqPauliProj` side-condition
`qv < nv` becomes `qv < qv + 1` — trivially true for *every* qubit (boundary/corner
included), with no global range / descent witness.  These mirrors take an arbitrary
evaluated width `n`/`nv`; the row totality is the *unbounded* `recCall_total_symbolicDK_all`
/ `*_total_all` (rows total at every `q`, `Pauli.I` out of range — `codeEntry_total_all`). -/

/-- All-width `RowUnfoldData`: `recCall DD.dT kT` is total at *every* `q` (hence `< nv` for
any evaluated width `nv`), from `recCall_total_symbolicDK_all`. -/
theorem rowUnfoldData_of_DistAtA_all {arity fuel m : Nat} (DD : DistAtA arity m)
    {kT : Term arity .nat} (hk : SFormula.PureNatTerm kT) (rho : Env arity)
    (E : PartialStabilizer) (hfuel : m + 2 ≤ fuel)
    (n : STerm arity .nat) {nv : Nat}
    (hn : n.eval Surface.code.body fuel rho E = some nv) :
    RowUnfoldData (fuel := fuel) n DD.dT kT rho E := by
  obtain ⟨kv, hkv⟩ := hk.eval_total Surface.code.body fuel rho
  have hdv : Term.eval Surface.code.body fuel DD.dT rho = some (2 * m + 3) := by
    have := DD.evalsTo (fuel := fuel) rho
    simpa only [oddDistance] using this
  have hdAll : ∀ fuel', Term.eval Surface.code.body fuel' DD.dT rho = some (2 * m + 3) :=
    fun fuel' => by simpa only [oddDistance] using DD.evalsTo (fuel := fuel') rho
  obtain ⟨sa, hsa, hsadef⟩ := recCall_total_symbolicDK_all m fuel hfuel rho hdAll hk
  exact ⟨nv, 2 * m + 3, kv, sa, hn, hdv, hkv, hsa, fun q _ => hsadef q⟩

/-- All-`q` `stabLam`-of-`PurePauli` totality (the `nQubits` bound in `stabLamSubst_total`
is unused — its proof already does `intro q _`). -/
theorem stabLamSubst_total_all {arity fuel m : Nat} (DD : DistAtA arity m)
    {kT : Term arity .nat} (hk : SFormula.PureNatTerm kT) (rho : Env arity)
    {entry : Term (1 + 2) .pauli} (hentry : PurePauli entry) :
    ∃ s1, Term.eval Surface.code.body fuel
        (.stabLam (QHL.CodeLang.Verify.codeSubstAt DD.dT kT 1 entry)) rho = some s1 ∧
      ∀ q, ∃ p, s1 q = some p := by
  refine ⟨fun q => Term.eval Surface.code.body fuel
      (QHL.CodeLang.Verify.codeSubstAt DD.dT kT 1 entry) (Env.cons q rho),
      by simp only [Term.eval], ?_⟩
  intro q
  exact purePauli_codeSubstAt_one_eval_total DD.pure hk hentry Surface.code.body fuel
    (Env.cons q rho)

/-- All-`q` `stabLam`-of-`recursiveEntry` totality (companion to `stabLamSubstRec_total`). -/
theorem stabLamSubstRec_total_all {arity m f' : Nat} {rho : Env arity} (DD : DistAtA arity (m + 1))
    {kT : Term arity .nat} (R : RecEvalData DD.dT kT f' rho) :
    ∃ s2, Term.eval Surface.code.body (f' + 1)
        (.stabLam (QHL.CodeLang.Verify.codeSubstAt DD.dT kT 1 SurfaceASTPublic.recursiveEntry))
          rho = some s2 ∧
      ∀ q, ∃ p, s2 q = some p := by
  rw [← SurfaceASTPublic.recursiveEntry_eq_public]
  refine ⟨fun q => Term.eval Surface.code.body (f' + 1)
      (QHL.CodeLang.Verify.codeSubstAt DD.dT kT 1 Surface.recursiveEntry)
        (Env.cons q rho), by simp only [Term.eval], ?_⟩
  intro q
  exact R.lamBody_total q

/-- All-width BASE row-select WF (local projection width `n`). -/
theorem surfaceCodeRowSelectBase_WF_of_DistAtA_all {arity fuel m : Nat} (DD : DistAtA arity m)
    {kT : Term arity .nat} (hk : SFormula.PureNatTerm kT) (rho : Env arity)
    (E : PartialStabilizer) (hfuel : m + 2 ≤ fuel)
    (hGuard : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat DD.dT (n5 : Term arity .nat))) (SC.b true)))
    (hGuardWF : DerivWFA hGuard rho E)
    (n : STerm arity .nat) {nv : Nat}
    (hn : n.eval Surface.code.body fuel rho E = some nv) :
    DerivWFA (surfaceCodeRowSelectBase (fuel := fuel) n DD.dT kT DD.pure hk hGuard) rho E := by
  refine surfaceCodeRowSelectBase_WF _ DD.dT kT DD.pure hk hGuard rho E hGuardWF
    (surfaceCodeRowUnfold_WF _ DD.dT kT DD.pure hk rho E
      (rowUnfoldData_of_DistAtA_all DD hk rho E hfuel n hn))
    (surfaceCodeSubstBodyBase_WF _ DD.dT kT hGuard rho E hGuardWF hn
      (let ⟨s1, hs1, hs1all⟩ := stabLamSubst_total_all DD hk rho
        (SurfaceASTPublic.baseEntry_eq_public ▸ baseEntry_purePauli)
       ⟨s1, hs1, fun q _ => hs1all q⟩))

/-- All-width RECURSIVE row-select WF (local projection width `n`). -/
theorem surfaceCodeRowSelectRecursive_WF_of_DistAtA_all {arity m f' : Nat} {rho : Env arity}
    (DD : DistAtA arity (m + 1))
    {kT : Term arity .nat} (hk : SFormula.PureNatTerm kT)
    (E : PartialStabilizer) (hfuel : (m + 1) + 2 ≤ f' + 1)
    (R : RecEvalData DD.dT kT f' rho)
    (n : STerm arity .nat) {nv : Nat}
    (hn : n.eval Surface.code.body (f' + 1) rho E = some nv) :
    DerivWFA (surfaceCodeRowSelectRecursive (fuel := f' + 1)
      n DD.dT kT DD.pure hk
      (distLtFiveFalse_of_DistAtA DD)) rho E := by
  refine surfaceCodeRowSelectRecursive_WF _ DD.dT kT DD.pure hk (distLtFiveFalse_of_DistAtA DD)
      rho E True.intro
    (surfaceCodeRowUnfold_WF _ DD.dT kT DD.pure hk rho E
      (rowUnfoldData_of_DistAtA_all DD hk rho E hfuel n hn))
    (surfaceCodeSubstBodyRecursive_WF _ DD.dT kT (distLtFiveFalse_of_DistAtA DD) rho E True.intro
      hn
      (let ⟨s2, hs2, hs2all⟩ := stabLamSubstRec_total_all DD R
       ⟨s2, hs2, fun q _ => hs2all q⟩))

/-- `DerivWFA` of the BASE master `baseRowConvergeA`.  Flat in `m`; the `cut1` head's
`SFormula.Deriv` core (`eqPauliTrans (hyp) (baseEntryMasterD …)`) is the leaf grind,
the `eqPauliProj`-of-`surfaceCodeRowSelectBase` premise carries the row-projection
eval side-data. -/
theorem baseRowConvergeA_WF {arity fuel : Nat} (n : STerm arity .nat)
    (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hBaseDist : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat dT (n5 : Term arity .nat))) (SC.b true)))
    (rho : Env arity) (E : PartialStabilizer)
    (hBaseDistWF : DerivWFA hBaseDist rho E)
    (hRowSel : DerivWFA (surfaceCodeRowSelectBase (fuel := fuel) n dT kT hd hk hBaseDist) rho E)
    (hproj : ∃ nv qv, n.eval Surface.code.body fuel rho E = some nv ∧
      (SC.closed qT).eval Surface.code.body fuel rho E = some qv ∧ qv < nv) :
    DerivWFA (baseRowConvergeA (fuel := fuel) n dT kT qT hd hk hq hBaseDist) rho E := by
  unfold baseRowConvergeA
  refine derivWFA_cut1 ?_ ?_
  · -- core: `eqPauliTrans (hyp) (baseEntryMasterD …)` — the base leaf grind,
    -- discharged by the fully-proven `baseEntryMasterD_WF`.
    exact derivWF_eqPauliTrans' True.intro (baseEntryMasterD_WF _ dT kT qT hd hk hq)
  · -- premise: `eqPauliProj n (recCall dT kT) (stabLam …) qT (surfaceCodeRowSelectBase …)`,
    -- whose `DerivWFA` is the supplied row-select WF (`hRowSel`, via STEP C helpers).
    obtain ⟨nv, qv, hn, hq', hqlt⟩ := hproj
    exact ⟨nv, qv, hn, hq', hqlt, hRowSel⟩

/-- `DerivWFA` of the REC master `recRowConvergeA`, **relaying** the five IH-supplied
sub-derivations' `DerivWFA` (`hInt … hBottom`).  Flat in `m` apart from those relays;
the `cut1`/`cut2` glue + the `recEntryMasterD` core are the leaf grind, the
`eqPauliProj`-of-`surfaceCodeRowSelectRecursive` premise carries the row-projection
eval side-data. -/
theorem recRowConvergeA_WF {arity fuel : Nat} (n : STerm arity .nat)
    (dT kT qT : Term arity .nat) (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hDist : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat dT (n5 : Term arity .nat))) (SC.b false)))
    (pIntA : PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (SC.closed (centerInnerRefA dT kT qT)) (SC.closed pInt)))
    (pTopA : PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (SC.closed (promotedInnerRefA dT qT (topKTA dT kT))) (SC.closed pTop)))
    (pRightA : PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (SC.closed (promotedInnerRefA dT qT (rightKTA dT kT))) (SC.closed pRight)))
    (pLeftA : PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (SC.closed (promotedInnerRefA dT qT (leftKTA dT kT))) (SC.closed pLeft)))
    (pBottomA : PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (SC.closed (promotedInnerRefA dT qT (bottomKTA dT kT))) (SC.closed pBottom)))
    (rho : Env arity) (E : PartialStabilizer)
    (hDistWF : DerivWFA hDist rho E)
    (hRowSel : DerivWFA (surfaceCodeRowSelectRecursive (fuel := fuel) n dT kT hd hk hDist) rho E)
    (hInt : DerivWFA pIntA rho E) (hTop : DerivWFA pTopA rho E)
    (hRight : DerivWFA pRightA rho E) (hLeft : DerivWFA pLeftA rho E)
    (hBottom : DerivWFA pBottomA rho E)
    (hproj : ∃ nv qv, n.eval Surface.code.body fuel rho E = some nv ∧
      (SC.closed qT).eval Surface.code.body fuel rho E = some qv ∧ qv < nv)
    -- The rec-master `DerivWF` inputs threaded into the `recEntryMasterD` core: the
    -- `RecEvalData` (lam-body totality, at `fuel = f' + 1`), the five resolved-cell pauli
    -- totalities (`hp*`), and the five recursing-stab totalities (`hStab*`, = the consumer's
    -- `closedStabAtSplit` evals / `RowStepWitness` splits).
    {f' : Nat} (R : RecEvalData dT kT f' rho) (hfe : fuel = f' + 1)
    (hpInt : ∃ v, Term.eval Surface.code.body fuel pInt rho = some v)
    (hpTop : ∃ v, Term.eval Surface.code.body fuel pTop rho = some v)
    (hpRight : ∃ v, Term.eval Surface.code.body fuel pRight rho = some v)
    (hpLeft : ∃ v, Term.eval Surface.code.body fuel pLeft rho = some v)
    (hpBottom : ∃ v, Term.eval Surface.code.body fuel pBottom rho = some v)
    (hStabInt : ∃ v, Term.eval Surface.code.body fuel (centerInnerRefA dT kT qT) rho = some v)
    (hStabTop : ∃ v, Term.eval Surface.code.body fuel (promotedInnerRefA dT qT (topKTA dT kT)) rho = some v)
    (hStabRight : ∃ v, Term.eval Surface.code.body fuel (promotedInnerRefA dT qT (rightKTA dT kT)) rho = some v)
    (hStabLeft : ∃ v, Term.eval Surface.code.body fuel (promotedInnerRefA dT qT (leftKTA dT kT)) rho = some v)
    (hStabBottom : ∃ v, Term.eval Surface.code.body fuel (promotedInnerRefA dT qT (bottomKTA dT kT)) rho = some v) :
    DerivWFA (recRowConvergeA (fuel := fuel) n dT kT qT pInt pTop pRight pLeft pBottom
      hd hk hq hDist pIntA pTopA pRightA pLeftA pBottomA) rho E := by
  subst hfe
  unfold recRowConvergeA
  -- The rec master is `cut1 (recEntryMasterD core) (cut2 … cut2 … hProj pIntA … pBottomA)`.
  -- The cut1/cut2 glue relays the five IH-supplied sub-derivations' `DerivWFA`
  -- (`hInt … hBottom`) and the row-projection premise (`eqPauliProj`-of-
  -- `surfaceCodeRowSelectRecursive`, the supplied `hRowSel`) sorry-free; the
  -- `recEntryMasterD` core's `DerivWF` is discharged by the fully-proven `recEntryMasterD_WF`
  -- (the andElim-projected IH derivations have trivial `DerivWF`, hence `True.intro`).
  refine derivWFA_cut1 ?core ?conj
  case core =>
    exact derivWF_eqPauliTrans' True.intro
      (recEntryMasterD_WF dT kT qT pInt pTop pRight pLeft pBottom hd hk hq R
        True.intro True.intro True.intro True.intro True.intro
        hpInt hpTop hpRight hpLeft hpBottom
        hStabInt hStabTop hStabRight hStabLeft hStabBottom)
  case conj =>
    -- the folded conjunction of the 6 facts, via nested `cut2`s:
    -- hProj (eqPauliProj), then pIntA, pTopA, pRightA, pLeftA, pBottomA.
    obtain ⟨nv, qv, hn, hq', hqlt⟩ := hproj
    refine derivWFA_cut2 (derivWF_andIntro_hyp_hyp (by simp) (by simp)) ?_ ?_
    · -- hProj : `eqPauliProj n (recCall dT kT) (stabLam …) qT (surfaceCodeRowSelectRecursive …)`,
      -- whose `DerivWFA` is the supplied row-select WF (`hRowSel`, via STEP C helpers).
      exact ⟨nv, qv, hn, hq', hqlt, hRowSel⟩
    · refine derivWFA_cut2 (derivWF_andIntro_hyp_hyp (by simp) (by simp)) hInt ?_
      refine derivWFA_cut2 (derivWF_andIntro_hyp_hyp (by simp) (by simp)) hTop ?_
      refine derivWFA_cut2 (derivWF_andIntro_hyp_hyp (by simp) (by simp)) hRight ?_
      refine derivWFA_cut2 (derivWF_andIntro_hyp_hyp (by simp) (by simp)) hLeft hBottom

/-- All-`q` recCall-stab split: `stabAt (recCall dInner kInner) qInner` evaluates for ANY
qubit value `qv`, from the unbounded `codeEntry_total_all` — no `qv < nQubits` range
side-condition.  This discharges the five `closedStabAtSplit` obligations of
`recRowConvergeA_WF` directly, with no descending row witness. -/
theorem innerStabSplit_all {arity m : Nat} {dInner kInner qInner : Term arity .nat}
    {rho : Env arity} {f' kv qv : Nat}
    (hd : Term.eval Surface.code.body f' dInner rho = some (2 * m + 3))
    (hkv : Term.eval Surface.code.body f' kInner rho = some kv)
    (hqv : Term.eval Surface.code.body (f' + 1) qInner rho = some qv)
    (hf' : m + 1 ≤ f') :
    ∃ v, Term.eval Surface.code.body (f' + 1)
        (.stabAt (.recCall dInner kInner) qInner) rho = some v := by
  obtain ⟨p, hp⟩ := codeEntry_total_all m kv f' hf' qv
  refine ⟨p, ?_⟩
  rw [QHL.CodeLang.Verify.CodeEvalHelpers.eval_stabAt_recCall Surface.code hd hkv hqv]
  exact hp

/-- **Definedness of the symbolic row-entry characterization** — refactored to use the
*local* projection width `SC.succClosed qT = qT + 1`.  The `eqPauliProj` side-condition is
then `qv < qv + 1` (trivial, `Nat.lt_succ_self`), so no `RowProjWitness` / `DescendingRowWitness`
side-data is needed: every qubit (boundary/corner included) is handled, with the recCall
totality (`recCall_total_symbolicDK_all`) and split evals (`innerStabSplit_all`) coming from
the unbounded `codeEntry_total_all`. -/
theorem surfaceRowEntryCharSymbolicA_WF {arity fuel : Nat} (m : Nat) (DD : DistAtA arity m)
    (kT qT : Term arity .nat)
    (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (rho : Env arity) (E : PartialStabilizer)
    (hfuel : m + 2 ≤ fuel) :
    DerivWFA (surfaceRowEntryCharSymbolicA (fuel := fuel) m DD kT qT hk hq) rho E := by
  induction m generalizing kT qT with
  | zero =>
      -- BASE: `surfaceRowEntryCharSymbolicA 0 DD kT qT = baseRowConvergeA (SC.succClosed qT) …`.
      rw [surfaceRowEntryCharSymbolicA]
      simp only [id]
      obtain ⟨qv, hqv⟩ := hq.eval_total Surface.code.body fuel rho
      have hsucc : (SC.succClosed qT).eval Surface.code.body fuel rho E = some (qv + 1) := by
        simp [SC.succClosed, SC.closed, STerm.eval, Term.eval, hqv]
      refine baseRowConvergeA_WF _ DD.dT kT qT DD.pure hk hq _ rho E ?_ ?_ ?_
      · -- `DerivWFA (distLtFiveTrue_of_DistAtA DD)` — an `arithBool`, trivially `True`.
        exact True.intro
      · -- `hRowSel`: the BASE row-select WF at the *local* width `SC.succClosed qT`.
        exact surfaceCodeRowSelectBase_WF_of_DistAtA_all DD hk rho E hfuel
          (distLtFiveTrue_of_DistAtA DD) True.intro (SC.succClosed qT) hsucc
      · -- row-projection witness `qv < qv + 1` (trivial — local width)
        exact ⟨qv + 1, qv, hsucc, (by simpa only [SC.closed, STerm.eval] using hqv), Nat.lt_succ_self qv⟩
  | succ m ih =>
      -- STEP: `surfaceRowEntryCharSymbolicA (m+1) DD kT qT` builds the five IH-resolved
      -- sub-derivations and dispatches via `recRowConvergeA` at the *local* width
      -- `SC.succClosed qT`.  The five `closedStabAtSplit` obligations are now discharged
      -- directly by `innerStabSplit_all` (all-`q` recCall totality), and the IH `ih` is
      -- witness-free.
      rw [surfaceRowEntryCharSymbolicA]
      simp only [id]
      have hfuel' : m + 2 ≤ fuel := by omega
      -- the rec-master `RecEvalData` at fuel `fuel = f' + 1` with `f' = fuel - 1`.
      obtain ⟨f', hfeq⟩ : ∃ f', fuel = f' + 1 := ⟨fuel - 1, by omega⟩
      subst hfeq
      have hf'm : m + 1 ≤ f' := by omega
      have R : RecEvalData DD.dT kT f' rho :=
        recEvalData_of_DistAtA DD hk rho (by omega)
      obtain ⟨qv, hqv⟩ := hq.eval_total Surface.code.body (f' + 1) rho
      have hsucc : (SC.succClosed qT).eval Surface.code.body (f' + 1) rho E = some (qv + 1) := by
        simp [SC.succClosed, SC.closed, STerm.eval, Term.eval, hqv]
      -- shared inner-distance eval (`innerDTA DD.dT = 2m+3`) + index/qubit evals for the
      -- five split obligations (all `Pauli.I`-total out of range via `codeEntry_total_all`).
      have hdInner : Term.eval Surface.code.body f' (innerDTA DD.dT) rho = some (2 * m + 3) := by
        rw [innerDTA, Term.eval, Term.eval, DD.evalsTo (fuel := f') rho]
        simp [Option.bind, Option.bind_eq_bind, Option.some.injEq, oddDistance]
        omega
      obtain ⟨qInnerV, hqInnerV⟩ :=
        (innerQTA_pure DD.pure hq).eval_total Surface.code.body (f' + 1) rho
      obtain ⟨kIntV, hkIntV⟩ := (interiorKTA_pure DD.pure hk).eval_total Surface.code.body f' rho
      obtain ⟨kTopV, hkTopV⟩ := (topKTA_pure DD.pure hk).eval_total Surface.code.body f' rho
      obtain ⟨kRightV, hkRightV⟩ := (rightKTA_pure DD.pure hk).eval_total Surface.code.body f' rho
      obtain ⟨kLeftV, hkLeftV⟩ := (leftKTA_pure DD.pure hk).eval_total Surface.code.body f' rho
      obtain ⟨kBottomV, hkBottomV⟩ := (bottomKTA_pure DD.pure hk).eval_total Surface.code.body f' rho
      have hStabInt : ∃ v, Term.eval Surface.code.body (f' + 1)
          (centerInnerRefA DD.dT kT qT) rho = some v :=
        innerStabSplit_all hdInner hkIntV hqInnerV hf'm
      have hStabTop : ∃ v, Term.eval Surface.code.body (f' + 1)
          (promotedInnerRefA DD.dT qT (topKTA DD.dT kT)) rho = some v :=
        innerStabSplit_all hdInner hkTopV hqInnerV hf'm
      have hStabRight : ∃ v, Term.eval Surface.code.body (f' + 1)
          (promotedInnerRefA DD.dT qT (rightKTA DD.dT kT)) rho = some v :=
        innerStabSplit_all hdInner hkRightV hqInnerV hf'm
      have hStabLeft : ∃ v, Term.eval Surface.code.body (f' + 1)
          (promotedInnerRefA DD.dT qT (leftKTA DD.dT kT)) rho = some v :=
        innerStabSplit_all hdInner hkLeftV hqInnerV hf'm
      have hStabBottom : ∃ v, Term.eval Surface.code.body (f' + 1)
          (promotedInnerRefA DD.dT qT (bottomKTA DD.dT kT)) rho = some v :=
        innerStabSplit_all hdInner hkBottomV hqInnerV hf'm
      refine recRowConvergeA_WF _ DD.dT kT qT _ _ _ _ _ DD.pure hk hq _ _ _ _ _ _ rho E
        True.intro
        (surfaceCodeRowSelectRecursive_WF_of_DistAtA_all DD hk E (by omega) R (SC.succClosed qT)
          hsucc)
        ?hInt ?hTop ?hRight ?hLeft ?hBottom
        ⟨qv + 1, qv, hsucc, (by simpa only [SC.closed, STerm.eval] using hqv), Nat.lt_succ_self qv⟩
        R rfl
        ((rowSymTreeA_purePauli m (innerDTA_pure DD.pure) (interiorKTA_pure DD.pure hk)
          (innerQTA_pure DD.pure hq)).eval_total Surface.code.body (f' + 1) rho)
        ((rowSymTreeA_purePauli m (innerDTA_pure DD.pure) (topKTA_pure DD.pure hk)
          (innerQTA_pure DD.pure hq)).eval_total Surface.code.body (f' + 1) rho)
        ((rowSymTreeA_purePauli m (innerDTA_pure DD.pure) (rightKTA_pure DD.pure hk)
          (innerQTA_pure DD.pure hq)).eval_total Surface.code.body (f' + 1) rho)
        ((rowSymTreeA_purePauli m (innerDTA_pure DD.pure) (leftKTA_pure DD.pure hk)
          (innerQTA_pure DD.pure hq)).eval_total Surface.code.body (f' + 1) rho)
        ((rowSymTreeA_purePauli m (innerDTA_pure DD.pure) (bottomKTA_pure DD.pure hk)
          (innerQTA_pure DD.pure hq)).eval_total Surface.code.body (f' + 1) rho)
        hStabInt hStabTop hStabRight hStabLeft hStabBottom
      case hInt =>
        exact ⟨hStabInt,
          ih DD.pred (interiorKTA DD.dT kT) (innerQTA DD.dT qT)
            (interiorKTA_pure DD.pure hk) (innerQTA_pure DD.pure hq) hfuel'⟩
      case hTop =>
        exact ⟨hStabTop,
          ih DD.pred (topKTA DD.dT kT) (innerQTA DD.dT qT)
            (topKTA_pure DD.pure hk) (innerQTA_pure DD.pure hq) hfuel'⟩
      case hRight =>
        exact ⟨hStabRight,
          ih DD.pred (rightKTA DD.dT kT) (innerQTA DD.dT qT)
            (rightKTA_pure DD.pure hk) (innerQTA_pure DD.pure hq) hfuel'⟩
      case hLeft =>
        exact ⟨hStabLeft,
          ih DD.pred (leftKTA DD.dT kT) (innerQTA DD.dT qT)
            (leftKTA_pure DD.pure hk) (innerQTA_pure DD.pure hq) hfuel'⟩
      case hBottom =>
        exact ⟨hStabBottom,
          ih DD.pred (bottomKTA DD.dT kT) (innerQTA DD.dT qT)
            (bottomKTA_pure DD.pure hk) (innerQTA_pure DD.pure hq) hfuel'⟩

/-! ## Flat-bridge `DerivWF` infrastructure

The flat bridge `rowSymTreeFlatBridgeSym` and its master `recFlatMasterD` are
**pure-formula** derivations (every node is `eqPauli`/`eqBool`/`imp`/`and`/`mp`/
`boolCases`/`pauliIteSelect`/`contextWeakening` over PurePauli/PureBool/PureNat
terms — NO `recCall`/`stabAt`/`recUnfold`).  So every `DerivWF` obligation is either
trivial (`hyp`/`assumption`/imp-arg → `True`) or `FormulaDefined` of a pure formula
(dischargeable by `formulaDefined_eqPauli_purePauli (by leaf_pp) (by leaf_pp)` /
`sterm_eval_closedPure`).  The uniform `flat_deriv_wf` tactic walks any such
derivation. -/

/-- `DerivWF (andElimLeft child) = DerivWF child` (definedness only recurses). -/
theorem derivWF_andElimLeft' {arity : Nat} {Γ : List (SFormula arity)} {A B : SFormula arity}
    {child : SFormula.Deriv Γ (.and A B)} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer} (h : DerivWF child cb fuel rho E) :
    DerivWF (SFormula.Deriv.andElimLeft child) cb fuel rho E := h

/-- `DerivWF (andElimRight child) = DerivWF child`. -/
theorem derivWF_andElimRight' {arity : Nat} {Γ : List (SFormula arity)} {A B : SFormula arity}
    {child : SFormula.Deriv Γ (.and A B)} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer} (h : DerivWF child cb fuel rho E) :
    DerivWF (SFormula.Deriv.andElimRight child) cb fuel rho E := h

/-- Uniform `DerivWF` discharger for a pure-formula derivation: applies the structural
`derivWF_*` combinators head-first, closes guard/imp child WFs by `assumption`/`True.intro`,
and every `FormulaDefined` leaf via the `PurePauli` route. -/
macro "flat_deriv_wf" : tactic =>
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
      | refine derivWF_pauliIteSelectThen' _ _ _ ?_ ?_
      | refine derivWF_pauliIteSelectElse' _ _ _ ?_ ?_
      | refine derivWF_boolCases _ _
          (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?_ ?_
      | apply formulaDefined_eqPauli_purePauli
      | leaf_pp)

/-! ### `baseLeaf*S` flat-leaf navigation `DerivWF` lemmas (resolve `baseLeafTreeTA` to the
selected `pauliLit` from the cell-class/band guards).  Proved once each, cited by the
`flatStep*` `DerivWF` proofs so the big leaf trees are never re-walked. -/

theorem baseLeafZS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hBand hKind} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wBand : DerivWF hBand cb fuel rho E)
    (wKind : DerivWF hKind cb fuel rho E) :
    DerivWF (baseLeafZS (Γ := Γ) dT kT qT hBulk hBand hKind) cb fuel rho E := by
  unfold baseLeafZS; flat_deriv_wf

theorem baseLeafXS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hBand hKind} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wBand : DerivWF hBand cb fuel rho E)
    (wKind : DerivWF hKind cb fuel rho E) :
    DerivWF (baseLeafXS (Γ := Γ) dT kT qT hBulk hBand hKind) cb fuel rho E := by
  unfold baseLeafXS; flat_deriv_wf

theorem baseLeafBulkIS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hBand} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wBand : DerivWF hBand cb fuel rho E) :
    DerivWF (baseLeafBulkIS (Γ := Γ) dT kT qT hBulk hBand) cb fuel rho E := by
  unfold baseLeafBulkIS; flat_deriv_wf

theorem baseLeafTopXS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hTopClass hTopBand} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wTopBand : DerivWF hTopBand cb fuel rho E) :
    DerivWF (baseLeafTopXS (Γ := Γ) dT kT qT hBulk hTopClass hTopBand) cb fuel rho E := by
  unfold baseLeafTopXS; flat_deriv_wf

theorem baseLeafTopIS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hTopClass hTopBand} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wTopBand : DerivWF hTopBand cb fuel rho E) :
    DerivWF (baseLeafTopIS (Γ := Γ) dT kT qT hBulk hTopClass hTopBand) cb fuel rho E := by
  unfold baseLeafTopIS; flat_deriv_wf

theorem baseLeafRightZS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hTopClass hRightClass hRightBand}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wRightBand : DerivWF hRightBand cb fuel rho E) :
    DerivWF (baseLeafRightZS (Γ := Γ) dT kT qT hBulk hTopClass hRightClass hRightBand) cb fuel rho E := by
  unfold baseLeafRightZS; flat_deriv_wf

theorem baseLeafRightIS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hTopClass hRightClass hRightBand}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wRightBand : DerivWF hRightBand cb fuel rho E) :
    DerivWF (baseLeafRightIS (Γ := Γ) dT kT qT hBulk hTopClass hRightClass hRightBand) cb fuel rho E := by
  unfold baseLeafRightIS; flat_deriv_wf

theorem baseLeafLeftZS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hTopClass hRightClass hLeftClass hLeftBand}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wLeftClass : DerivWF hLeftClass cb fuel rho E)
    (wLeftBand : DerivWF hLeftBand cb fuel rho E) :
    DerivWF (baseLeafLeftZS (Γ := Γ) dT kT qT hBulk hTopClass hRightClass hLeftClass hLeftBand) cb fuel rho E := by
  unfold baseLeafLeftZS; flat_deriv_wf

theorem baseLeafLeftIS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hTopClass hRightClass hLeftClass hLeftBand}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wLeftClass : DerivWF hLeftClass cb fuel rho E)
    (wLeftBand : DerivWF hLeftBand cb fuel rho E) :
    DerivWF (baseLeafLeftIS (Γ := Γ) dT kT qT hBulk hTopClass hRightClass hLeftClass hLeftBand) cb fuel rho E := by
  unfold baseLeafLeftIS; flat_deriv_wf

theorem baseLeafBottomXS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hTopClass hRightClass hLeftClass hBottomBand}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wLeftClass : DerivWF hLeftClass cb fuel rho E)
    (wBottomBand : DerivWF hBottomBand cb fuel rho E) :
    DerivWF (baseLeafBottomXS (Γ := Γ) dT kT qT hBulk hTopClass hRightClass hLeftClass hBottomBand) cb fuel rho E := by
  unfold baseLeafBottomXS; flat_deriv_wf

theorem baseLeafBottomIS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hTopClass hRightClass hLeftClass hBottomBand}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wLeftClass : DerivWF hLeftClass cb fuel rho E)
    (wBottomBand : DerivWF hBottomBand cb fuel rho E) :
    DerivWF (baseLeafBottomIS (Γ := Γ) dT kT qT hBulk hTopClass hRightClass hLeftClass hBottomBand) cb fuel rho E := by
  unfold baseLeafBottomIS; flat_deriv_wf

/-- `flat_step_wf`: like `flat_deriv_wf` but discharges `baseLeaf*S` leaves by CITING their
proved WF lemmas (no re-unfolding/re-walking of `baseLeafTreeTA`), keeping `flatStep*` terms
small. -/
macro "flat_step_wf" : tactic =>
  `(tactic|
    repeat first
      | exact True.intro
      | assumption
      | refine innerDTA_pure ?_
      | refine interiorKTA_pure ?_ ?_
      | refine topKTA_pure ?_ ?_
      | refine rightKTA_pure ?_ ?_
      | refine leftKTA_pure ?_ ?_
      | refine bottomKTA_pure ?_ ?_
      | refine innerQTA_pure ?_ ?_
      | refine baseLeafZS_WF _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
      | refine baseLeafXS_WF _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
      | refine baseLeafBulkIS_WF _ _ _ _ ?_ ?_ ?_ ?_ ?_
      | refine baseLeafTopXS_WF _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
      | refine baseLeafTopIS_WF _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
      | refine baseLeafRightZS_WF _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      | refine baseLeafRightIS_WF _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      | refine baseLeafLeftZS_WF _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      | refine baseLeafLeftIS_WF _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      | refine baseLeafBottomXS_WF _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      | refine baseLeafBottomIS_WF _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      | refine derivWF_eqPauliTrans' ?_ ?_
      | refine derivWF_eqPauliSymm' ?_
      | refine derivWF_mp ?_ ?_
      | refine derivWF_andIntro ?_ ?_
      | refine derivWF_andElimLeft' ?_
      | refine derivWF_andElimRight' ?_
      | refine derivWF_contextWeakening' _ _ ?_
      | refine derivWF_pauliIteSelectThen' _ _ _ ?_ ?_
      | refine derivWF_pauliIteSelectElse' _ _ _ ?_ ?_
      | refine derivWF_boolCases _ _
          (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?_ ?_
      | apply formulaDefined_eqPauli_purePauli
      | leaf_pp)

/-! ### `recLeaf*S` self-sim navigation `DerivWF` lemmas (resolve `recLeafTreeTA` to the
selected cell; need `PurePauli` of the five resolved cells for the `pauliIteSelect` leaves). -/

theorem recLeafIntS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpi : PurePauli pInt) (hpt : PurePauli pTop) (hpr : PurePauli pRight)
    (hpl : PurePauli pLeft) (hpb : PurePauli pBottom)
    {hBulk hInterior hInside} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wInside : DerivWF hInside cb fuel rho E) :
    DerivWF (recLeafIntS (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom hBulk hInterior hInside) cb fuel rho E := by
  unfold recLeafIntS; flat_deriv_wf

theorem recLeafIntIS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpi : PurePauli pInt) (hpt : PurePauli pTop) (hpr : PurePauli pRight)
    (hpl : PurePauli pLeft) (hpb : PurePauli pBottom)
    {hBulk hInterior hInside} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wInside : DerivWF hInside cb fuel rho E) :
    DerivWF (recLeafIntIS (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom hBulk hInterior hInside) cb fuel rho E := by
  unfold recLeafIntIS; flat_deriv_wf

theorem recLeafTopS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpi : PurePauli pInt) (hpt : PurePauli pTop) (hpr : PurePauli pRight)
    (hpl : PurePauli pLeft) (hpb : PurePauli pBottom)
    {hBulk hInterior hTop hInside} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wTop : DerivWF hTop cb fuel rho E) (wInside : DerivWF hInside cb fuel rho E) :
    DerivWF (recLeafTopS (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom hBulk hInterior hTop hInside) cb fuel rho E := by
  unfold recLeafTopS; flat_deriv_wf

theorem recLeafTopNIS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpi : PurePauli pInt) (hpt : PurePauli pTop) (hpr : PurePauli pRight)
    (hpl : PurePauli pLeft) (hpb : PurePauli pBottom)
    {hBulk hInterior hTop hInside} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wTop : DerivWF hTop cb fuel rho E) (wInside : DerivWF hInside cb fuel rho E) :
    DerivWF (recLeafTopNIS (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom hBulk hInterior hTop hInside) cb fuel rho E := by
  unfold recLeafTopNIS; flat_deriv_wf

theorem recLeafRightS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpi : PurePauli pInt) (hpt : PurePauli pTop) (hpr : PurePauli pRight)
    (hpl : PurePauli pLeft) (hpb : PurePauli pBottom)
    {hBulk hInterior hTop hRight hInside} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wTop : DerivWF hTop cb fuel rho E) (wRight : DerivWF hRight cb fuel rho E)
    (wInside : DerivWF hInside cb fuel rho E) :
    DerivWF (recLeafRightS (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom hBulk hInterior hTop hRight hInside) cb fuel rho E := by
  unfold recLeafRightS; flat_deriv_wf

theorem recLeafRightNIS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpi : PurePauli pInt) (hpt : PurePauli pTop) (hpr : PurePauli pRight)
    (hpl : PurePauli pLeft) (hpb : PurePauli pBottom)
    {hBulk hInterior hTop hRight hInside} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wTop : DerivWF hTop cb fuel rho E) (wRight : DerivWF hRight cb fuel rho E)
    (wInside : DerivWF hInside cb fuel rho E) :
    DerivWF (recLeafRightNIS (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom hBulk hInterior hTop hRight hInside) cb fuel rho E := by
  unfold recLeafRightNIS; flat_deriv_wf

theorem recLeafLeftS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpi : PurePauli pInt) (hpt : PurePauli pTop) (hpr : PurePauli pRight)
    (hpl : PurePauli pLeft) (hpb : PurePauli pBottom)
    {hBulk hInterior hTop hRight hLeft hInside} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wTop : DerivWF hTop cb fuel rho E) (wRight : DerivWF hRight cb fuel rho E)
    (wLeft : DerivWF hLeft cb fuel rho E) (wInside : DerivWF hInside cb fuel rho E) :
    DerivWF (recLeafLeftS (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom hBulk hInterior hTop hRight hLeft hInside) cb fuel rho E := by
  unfold recLeafLeftS; flat_deriv_wf

theorem recLeafLeftNIS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpi : PurePauli pInt) (hpt : PurePauli pTop) (hpr : PurePauli pRight)
    (hpl : PurePauli pLeft) (hpb : PurePauli pBottom)
    {hBulk hInterior hTop hRight hLeft hInside} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wTop : DerivWF hTop cb fuel rho E) (wRight : DerivWF hRight cb fuel rho E)
    (wLeft : DerivWF hLeft cb fuel rho E) (wInside : DerivWF hInside cb fuel rho E) :
    DerivWF (recLeafLeftNIS (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom hBulk hInterior hTop hRight hLeft hInside) cb fuel rho E := by
  unfold recLeafLeftNIS; flat_deriv_wf

theorem recLeafBottomS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpi : PurePauli pInt) (hpt : PurePauli pTop) (hpr : PurePauli pRight)
    (hpl : PurePauli pLeft) (hpb : PurePauli pBottom)
    {hBulk hInterior hTop hRight hLeft hBottom hInside} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wTop : DerivWF hTop cb fuel rho E) (wRight : DerivWF hRight cb fuel rho E)
    (wLeft : DerivWF hLeft cb fuel rho E) (wBottom : DerivWF hBottom cb fuel rho E)
    (wInside : DerivWF hInside cb fuel rho E) :
    DerivWF (recLeafBottomS (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom hBulk hInterior hTop hRight hLeft hBottom hInside) cb fuel rho E := by
  unfold recLeafBottomS; flat_deriv_wf

theorem recLeafBottomNIS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpi : PurePauli pInt) (hpt : PurePauli pTop) (hpr : PurePauli pRight)
    (hpl : PurePauli pLeft) (hpb : PurePauli pBottom)
    {hBulk hInterior hTop hRight hLeft hBottom hInside} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wTop : DerivWF hTop cb fuel rho E) (wRight : DerivWF hRight cb fuel rho E)
    (wLeft : DerivWF hLeft cb fuel rho E) (wBottom : DerivWF hBottom cb fuel rho E)
    (wInside : DerivWF hInside cb fuel rho E) :
    DerivWF (recLeafBottomNIS (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom hBulk hInterior hTop hRight hLeft hBottom hInside) cb fuel rho E := by
  unfold recLeafBottomNIS; flat_deriv_wf

theorem recLeafFallbackS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpi : PurePauli pInt) (hpt : PurePauli pTop) (hpr : PurePauli pRight)
    (hpl : PurePauli pLeft) (hpb : PurePauli pBottom)
    {hBulk hInterior hTop hRight hLeft hBottom} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wTop : DerivWF hTop cb fuel rho E) (wRight : DerivWF hRight cb fuel rho E)
    (wLeft : DerivWF hLeft cb fuel rho E) (wBottom : DerivWF hBottom cb fuel rho E) :
    DerivWF (recLeafFallbackS (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom hBulk hInterior hTop hRight hLeft hBottom) cb fuel rho E := by
  unfold recLeafFallbackS; flat_deriv_wf

theorem recLeafBoundaryS_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpi : PurePauli pInt) (hpt : PurePauli pTop) (hpr : PurePauli pRight)
    (hpl : PurePauli pLeft) (hpb : PurePauli pBottom)
    {hBulk} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) :
    DerivWF (recLeafBoundaryS (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom hBulk) cb fuel rho E := by
  unfold recLeafBoundaryS; flat_deriv_wf

/-! ### `flatStep*` `DerivWF` lemmas (the inner↔outer flat-tree equality at each cell; pure
boolCases over outer band/kind, `mp` on the correspondence implications, `baseLeaf*S` leaves). -/

theorem flatStepInterior_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hInterior hInside hImpBulk hImpBandT hImpBandF hImpKindT hImpKindF}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wInside : DerivWF hInside cb fuel rho E)
    (wImpBulk : DerivWF hImpBulk cb fuel rho E) (wImpBandT : DerivWF hImpBandT cb fuel rho E)
    (wImpBandF : DerivWF hImpBandF cb fuel rho E) (wImpKindT : DerivWF hImpKindT cb fuel rho E)
    (wImpKindF : DerivWF hImpKindF cb fuel rho E) :
    DerivWF (flatStepInterior (Γ := Γ) dT kT qT hBulk hInterior hInside hImpBulk hImpBandT hImpBandF hImpKindT hImpKindF) cb fuel rho E := by
  unfold flatStepInterior; flat_step_wf

theorem flatStepInteriorNI_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hInterior hInside hImpBandF}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wInside : DerivWF hInside cb fuel rho E) (wImpBandF : DerivWF hImpBandF cb fuel rho E) :
    DerivWF (flatStepInteriorNI (Γ := Γ) dT kT qT hBulk hInterior hInside hImpBandF) cb fuel rho E := by
  unfold flatStepInteriorNI; flat_step_wf

theorem flatStepTop_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hInterior hTop hInside hImpCtx hImpBandT hImpBandF}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wTop : DerivWF hTop cb fuel rho E) (wInside : DerivWF hInside cb fuel rho E)
    (wImpCtx : DerivWF hImpCtx cb fuel rho E) (wImpBandT : DerivWF hImpBandT cb fuel rho E)
    (wImpBandF : DerivWF hImpBandF cb fuel rho E) :
    DerivWF (flatStepTop (Γ := Γ) dT kT qT hBulk hInterior hTop hInside hImpCtx hImpBandT hImpBandF) cb fuel rho E := by
  unfold flatStepTop; flat_step_wf

theorem flatStepTopNI_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hInterior hTop hInside hImpCtx hImpBandT hImpBandF}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wTop : DerivWF hTop cb fuel rho E) (wInside : DerivWF hInside cb fuel rho E)
    (wImpCtx : DerivWF hImpCtx cb fuel rho E) (wImpBandT : DerivWF hImpBandT cb fuel rho E)
    (wImpBandF : DerivWF hImpBandF cb fuel rho E) :
    DerivWF (flatStepTopNI (Γ := Γ) dT kT qT hBulk hInterior hTop hInside hImpCtx hImpBandT hImpBandF) cb fuel rho E := by
  unfold flatStepTopNI; flat_step_wf

theorem flatStepRight_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hInterior hTop hRight hInside hImpCtx hImpBandT hImpBandF}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wTop : DerivWF hTop cb fuel rho E) (wRight : DerivWF hRight cb fuel rho E)
    (wInside : DerivWF hInside cb fuel rho E) (wImpCtx : DerivWF hImpCtx cb fuel rho E)
    (wImpBandT : DerivWF hImpBandT cb fuel rho E) (wImpBandF : DerivWF hImpBandF cb fuel rho E) :
    DerivWF (flatStepRight (Γ := Γ) dT kT qT hBulk hInterior hTop hRight hInside hImpCtx hImpBandT hImpBandF) cb fuel rho E := by
  unfold flatStepRight; flat_step_wf

theorem flatStepRightNI_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hInterior hTop hRight hInside hImpCtx hImpBandT hImpBandF}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wTop : DerivWF hTop cb fuel rho E) (wRight : DerivWF hRight cb fuel rho E)
    (wInside : DerivWF hInside cb fuel rho E) (wImpCtx : DerivWF hImpCtx cb fuel rho E)
    (wImpBandT : DerivWF hImpBandT cb fuel rho E) (wImpBandF : DerivWF hImpBandF cb fuel rho E) :
    DerivWF (flatStepRightNI (Γ := Γ) dT kT qT hBulk hInterior hTop hRight hInside hImpCtx hImpBandT hImpBandF) cb fuel rho E := by
  unfold flatStepRightNI; flat_step_wf

theorem flatStepLeft_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hInterior hTop hRight hLeft hInside hImpCtx hImpBandT hImpBandF}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wTop : DerivWF hTop cb fuel rho E) (wRight : DerivWF hRight cb fuel rho E)
    (wLeft : DerivWF hLeft cb fuel rho E) (wInside : DerivWF hInside cb fuel rho E)
    (wImpCtx : DerivWF hImpCtx cb fuel rho E) (wImpBandT : DerivWF hImpBandT cb fuel rho E)
    (wImpBandF : DerivWF hImpBandF cb fuel rho E) :
    DerivWF (flatStepLeft (Γ := Γ) dT kT qT hBulk hInterior hTop hRight hLeft hInside hImpCtx hImpBandT hImpBandF) cb fuel rho E := by
  unfold flatStepLeft; flat_step_wf

theorem flatStepLeftNI_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hInterior hTop hRight hLeft hInside hImpCtx hImpBandT hImpBandF}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wTop : DerivWF hTop cb fuel rho E) (wRight : DerivWF hRight cb fuel rho E)
    (wLeft : DerivWF hLeft cb fuel rho E) (wInside : DerivWF hInside cb fuel rho E)
    (wImpCtx : DerivWF hImpCtx cb fuel rho E) (wImpBandT : DerivWF hImpBandT cb fuel rho E)
    (wImpBandF : DerivWF hImpBandF cb fuel rho E) :
    DerivWF (flatStepLeftNI (Γ := Γ) dT kT qT hBulk hInterior hTop hRight hLeft hInside hImpCtx hImpBandT hImpBandF) cb fuel rho E := by
  unfold flatStepLeftNI; flat_step_wf

theorem flatStepBottom_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hInterior hTop hRight hLeft hBottom hInside hImpCtx hImpBandT hImpBandF}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wTop : DerivWF hTop cb fuel rho E) (wRight : DerivWF hRight cb fuel rho E)
    (wLeft : DerivWF hLeft cb fuel rho E) (wBottom : DerivWF hBottom cb fuel rho E)
    (wInside : DerivWF hInside cb fuel rho E) (wImpCtx : DerivWF hImpCtx cb fuel rho E)
    (wImpBandT : DerivWF hImpBandT cb fuel rho E) (wImpBandF : DerivWF hImpBandF cb fuel rho E) :
    DerivWF (flatStepBottom (Γ := Γ) dT kT qT hBulk hInterior hTop hRight hLeft hBottom hInside hImpCtx hImpBandT hImpBandF) cb fuel rho E := by
  unfold flatStepBottom; flat_step_wf

theorem flatStepBottomNI_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk hInterior hTop hRight hLeft hBottom hInside hImpCtx hImpBandT hImpBandF}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wInterior : DerivWF hInterior cb fuel rho E)
    (wTop : DerivWF hTop cb fuel rho E) (wRight : DerivWF hRight cb fuel rho E)
    (wLeft : DerivWF hLeft cb fuel rho E) (wBottom : DerivWF hBottom cb fuel rho E)
    (wInside : DerivWF hInside cb fuel rho E) (wImpCtx : DerivWF hImpCtx cb fuel rho E)
    (wImpBandT : DerivWF hImpBandT cb fuel rho E) (wImpBandF : DerivWF hImpBandF cb fuel rho E) :
    DerivWF (flatStepBottomNI (Γ := Γ) dT kT qT hBulk hInterior hTop hRight hLeft hBottom hInside hImpCtx hImpBandT hImpBandF) cb fuel rho E := by
  unfold flatStepBottomNI; flat_step_wf

/-- `flat_master_wf`: the master discharger — `flat_step_wf` plus `apply`-citations of the
proved `recLeaf*S_WF` / `flatStep*_WF` / `baseLeaf*S_WF` (so each navigation/step is reused,
never re-walked).  `apply` infers the index/cell args from the goal, leaving `hd/hk/hq`,
`PurePauli` (hp), and guard/imp WF goals to `assumption`/`True.intro`/combinators. -/
macro "flat_master_wf" : tactic =>
  `(tactic|
    repeat first
      | exact True.intro
      | assumption
      | refine innerDTA_pure ?_
      | refine interiorKTA_pure ?_ ?_
      | refine topKTA_pure ?_ ?_
      | refine rightKTA_pure ?_ ?_
      | refine leftKTA_pure ?_ ?_
      | refine bottomKTA_pure ?_ ?_
      | refine innerQTA_pure ?_ ?_
      | apply recLeafIntS_WF
      | apply recLeafIntIS_WF
      | apply recLeafTopS_WF
      | apply recLeafTopNIS_WF
      | apply recLeafRightS_WF
      | apply recLeafRightNIS_WF
      | apply recLeafLeftS_WF
      | apply recLeafLeftNIS_WF
      | apply recLeafBottomS_WF
      | apply recLeafBottomNIS_WF
      | apply recLeafFallbackS_WF
      | apply recLeafBoundaryS_WF
      | apply flatStepInterior_WF
      | apply flatStepInteriorNI_WF
      | apply flatStepTop_WF
      | apply flatStepTopNI_WF
      | apply flatStepRight_WF
      | apply flatStepRightNI_WF
      | apply flatStepLeft_WF
      | apply flatStepLeftNI_WF
      | apply flatStepBottom_WF
      | apply flatStepBottomNI_WF
      | apply baseLeafZS_WF
      | apply baseLeafXS_WF
      | apply baseLeafBulkIS_WF
      | apply baseLeafTopXS_WF
      | apply baseLeafTopIS_WF
      | apply baseLeafRightZS_WF
      | apply baseLeafRightIS_WF
      | apply baseLeafLeftZS_WF
      | apply baseLeafLeftIS_WF
      | apply baseLeafBottomXS_WF
      | apply baseLeafBottomIS_WF
      | refine derivWF_eqPauliTrans' ?_ ?_
      | refine derivWF_eqPauliSymm' ?_
      | refine derivWF_mp ?_ ?_
      | refine derivWF_andIntro ?_ ?_
      | refine derivWF_andElimLeft' ?_
      | refine derivWF_andElimRight' ?_
      | refine derivWF_contextWeakening' _ _ ?_
      | refine derivWF_pauliIteSelectThen' _ _ _ ?_ ?_
      | refine derivWF_pauliIteSelectElse' _ _ _ ?_ ?_
      | refine derivWF_boolCases _ _
          (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?_ ?_
      | apply formulaDefined_eqPauli_purePauli
      | leaf_pp)

/-- **`recFlatMasterD_WF`** — `DerivWF` of the flat-bridge master boolCases tree.  Mirrors
`recFlatMasterD` (each leaf `eqPauliTrans (recLeaf*S) (eqPauliTrans (contextWeakening hLeq*)
(flatStep*))`); the five resolved cells need `PurePauli`, and the IH-leaf equalities + the
~30 correspondence implications enter as `DerivWF` hyps (all `True.intro` at the bridge call,
where they are `andElim` projections of the cut hypothesis). -/
theorem recFlatMasterD_WF {arity : Nat} {Γ : List (SFormula arity)}
    (dT kT qT : Term arity .nat) (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpi : PurePauli pInt) (hpt : PurePauli pTop) (hpr : PurePauli pRight)
    (hpl : PurePauli pLeft) (hpb : PurePauli pBottom)
    {hLeqInt hLeqTop hLeqRight hLeqLeft hLeqBottom
      hImpBulk hImpBandT hImpBandF hImpKindT hImpKindF hImpBandFNI
      hTopImpCtx hTopImpBandT hTopImpBandF hRightImpCtx hRightImpBandT hRightImpBandF
      hLeftImpCtx hLeftImpBandT hLeftImpBandF hBottomImpCtx hBottomImpBandT hBottomImpBandF
      hTopNIImpCtx hTopNIImpBandT hTopNIImpBandF hRightNIImpCtx hRightNIImpBandT hRightNIImpBandF
      hLeftNIImpCtx hLeftNIImpBandT hLeftNIImpBandF hBottomNIImpCtx hBottomNIImpBandT hBottomNIImpBandF}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wLeqInt : DerivWF hLeqInt cb fuel rho E) (wLeqTop : DerivWF hLeqTop cb fuel rho E)
    (wLeqRight : DerivWF hLeqRight cb fuel rho E) (wLeqLeft : DerivWF hLeqLeft cb fuel rho E)
    (wLeqBottom : DerivWF hLeqBottom cb fuel rho E) (wImpBulk : DerivWF hImpBulk cb fuel rho E)
    (wImpBandT : DerivWF hImpBandT cb fuel rho E) (wImpBandF : DerivWF hImpBandF cb fuel rho E)
    (wImpKindT : DerivWF hImpKindT cb fuel rho E) (wImpKindF : DerivWF hImpKindF cb fuel rho E)
    (wImpBandFNI : DerivWF hImpBandFNI cb fuel rho E) (wTopImpCtx : DerivWF hTopImpCtx cb fuel rho E)
    (wTopImpBandT : DerivWF hTopImpBandT cb fuel rho E) (wTopImpBandF : DerivWF hTopImpBandF cb fuel rho E)
    (wRightImpCtx : DerivWF hRightImpCtx cb fuel rho E) (wRightImpBandT : DerivWF hRightImpBandT cb fuel rho E)
    (wRightImpBandF : DerivWF hRightImpBandF cb fuel rho E) (wLeftImpCtx : DerivWF hLeftImpCtx cb fuel rho E)
    (wLeftImpBandT : DerivWF hLeftImpBandT cb fuel rho E) (wLeftImpBandF : DerivWF hLeftImpBandF cb fuel rho E)
    (wBottomImpCtx : DerivWF hBottomImpCtx cb fuel rho E) (wBottomImpBandT : DerivWF hBottomImpBandT cb fuel rho E)
    (wBottomImpBandF : DerivWF hBottomImpBandF cb fuel rho E) (wTopNIImpCtx : DerivWF hTopNIImpCtx cb fuel rho E)
    (wTopNIImpBandT : DerivWF hTopNIImpBandT cb fuel rho E) (wTopNIImpBandF : DerivWF hTopNIImpBandF cb fuel rho E)
    (wRightNIImpCtx : DerivWF hRightNIImpCtx cb fuel rho E) (wRightNIImpBandT : DerivWF hRightNIImpBandT cb fuel rho E)
    (wRightNIImpBandF : DerivWF hRightNIImpBandF cb fuel rho E) (wLeftNIImpCtx : DerivWF hLeftNIImpCtx cb fuel rho E)
    (wLeftNIImpBandT : DerivWF hLeftNIImpBandT cb fuel rho E) (wLeftNIImpBandF : DerivWF hLeftNIImpBandF cb fuel rho E)
    (wBottomNIImpCtx : DerivWF hBottomNIImpCtx cb fuel rho E) (wBottomNIImpBandT : DerivWF hBottomNIImpBandT cb fuel rho E)
    (wBottomNIImpBandF : DerivWF hBottomNIImpBandF cb fuel rho E) :
    DerivWF (recFlatMasterD (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom
        hLeqInt hLeqTop hLeqRight hLeqLeft hLeqBottom
        hImpBulk hImpBandT hImpBandF hImpKindT hImpKindF hImpBandFNI
        hTopImpCtx hTopImpBandT hTopImpBandF hRightImpCtx hRightImpBandT hRightImpBandF
        hLeftImpCtx hLeftImpBandT hLeftImpBandF hBottomImpCtx hBottomImpBandT hBottomImpBandF
        hTopNIImpCtx hTopNIImpBandT hTopNIImpBandF hRightNIImpCtx hRightNIImpBandT hRightNIImpBandF
        hLeftNIImpCtx hLeftNIImpBandT hLeftNIImpBandF hBottomNIImpCtx hBottomNIImpBandT hBottomNIImpBandF)
      cb fuel rho E := by
  unfold recFlatMasterD
  flat_master_wf

/-- The flat-bridge analogue of the descending witness for `rowSymTreeFlatBridgeSym`.
Placeholder name capturing the parallel `m`-induction's per-level eval side-data;
the bridge's `recFlatMasterD` boolCases tree consumes the same kind of inner-cell
witnesses as `recRowConvergeA`. -/
def RowFlatWitness {arity : Nat} (qT : Term arity .nat) (m : Nat)
    (rho : Env arity) (E : PartialStabilizer) : Prop := True

/-- **`rowSymTreeFlatBridgeSym_WF`** — `DerivWFA` of the symbolic flat bridge, by induction
on `m` (parallel to the bridge's own recursion).  Base: `core (baseLeafSelfEq)`.  Step:
`cut1 (recFlatMasterD …) hConj` — master via `recFlatMasterD_WF`, `hConj` cut2-chain relays
the five IH facts (induction IH) + the ~30 `arithBool` correspondence implications
(`DerivWFA = True`).  No row-projection witnesses needed (the bridge has no `recCall`). -/
theorem rowSymTreeFlatBridgeSym_WF {arity fuel : Nat} (m : Nat) (D : DistAtA arity m)
    (kT qT : Term arity .nat) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (rho : Env arity) (E : PartialStabilizer) :
    DerivWFA (rowSymTreeFlatBridgeSym (fuel := fuel) m D kT qT hk hq) rho E := by
  induction m generalizing kT qT hk hq with
  | zero =>
      exact baseLeafSelfEq_WF [] D.dT kT qT D.pure hk hq
  | succ m ih =>
      have hd : SFormula.PureNatTerm D.dT := D.pure
      have hpi : PurePauli (rowSymTreeA m (innerDTA D.dT) (interiorKTA D.dT kT) (innerQTA D.dT qT)) :=
        rowSymTreeA_purePauli m (innerDTA_pure D.pure) (interiorKTA_pure D.pure hk) (innerQTA_pure D.pure hq)
      have hpt : PurePauli (rowSymTreeA m (recInnerDTA D.dT) (topKTA D.dT kT) (innerQTA D.dT qT)) :=
        rowSymTreeA_purePauli m (innerDTA_pure D.pure) (topKTA_pure D.pure hk) (innerQTA_pure D.pure hq)
      have hpr : PurePauli (rowSymTreeA m (recInnerDTA D.dT) (rightKTA D.dT kT) (innerQTA D.dT qT)) :=
        rowSymTreeA_purePauli m (innerDTA_pure D.pure) (rightKTA_pure D.pure hk) (innerQTA_pure D.pure hq)
      have hpl : PurePauli (rowSymTreeA m (recInnerDTA D.dT) (leftKTA D.dT kT) (innerQTA D.dT qT)) :=
        rowSymTreeA_purePauli m (innerDTA_pure D.pure) (leftKTA_pure D.pure hk) (innerQTA_pure D.pure hq)
      have hpb : PurePauli (rowSymTreeA m (recInnerDTA D.dT) (bottomKTA D.dT kT) (innerQTA D.dT qT)) :=
        rowSymTreeA_purePauli m (innerDTA_pure D.pure) (bottomKTA_pure D.pure hk) (innerQTA_pure D.pure hq)
      unfold rowSymTreeFlatBridgeSym
      refine ⟨?_, ?_⟩
      · -- master core: `recFlatMasterD` over the resolved cells (`hpi…hpb`); andElim arg WFs auto.
        unfold recFlatMasterD
        flat_master_wf
      · -- `hConj`: the 34-deep cut2 chain — 5 IH facts (induction IH at the inner indices) +
        -- ~30 `arithBool` imps (`DerivWFA = True`); cores are `andIntro` of two `hyp`s.
        repeat first
          | exact True.intro
          | assumption
          | apply ih
          | refine interiorKTA_pure ?_ ?_
          | refine topKTA_pure ?_ ?_
          | refine rightKTA_pure ?_ ?_
          | refine leftKTA_pure ?_ ?_
          | refine bottomKTA_pure ?_ ?_
          | refine innerQTA_pure ?_ ?_
          | refine ⟨⟨True.intro, True.intro⟩, ?_, ?_⟩

/-- `DerivWFA` of the symbolic flat row entry — the KEYSTONE.  `rowEntryFlatSym =
eqPauliTrans (surfaceRowEntryCharSymbolicA …) (rowSymTreeFlatBridgeSym …)`, so its
`DerivWFA` is the pair of the two sub-derivations' `DerivWFA`.  The first conjunct is
exactly `surfaceRowEntryCharSymbolicA_WF` (the proven `m`-induction, depending only on
the two flat master helpers); the second is the parallel flat-bridge induction.

Requires the row-projection witnesses (`hproj` at this level, `hwit` descending) — the
qubit-in-range side-data the binder range supplies in the real consumers. -/
theorem rowEntryFlatSym_WF {arity fuel : Nat} (m : Nat) (DD : DistAtA arity m)
    (kT qT : Term arity .nat)
    (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (rho : Env arity) (E : PartialStabilizer)
    (hfuel : m + 2 ≤ fuel) :
    DerivWFA (rowEntryFlatSym (fuel := fuel) m DD kT qT hk hq) rho E := by
  -- `eqPauliTrans` splits into the two sub-derivations' `DerivWFA`.
  refine ⟨?_, ?_⟩
  · -- `surfaceRowEntryCharSymbolicA m DD kT qT` — now **witness-free** (local projection
    -- width `SC.succClosed qT`, so `qv < qv + 1` is trivial).
    exact surfaceRowEntryCharSymbolicA_WF m DD kT qT hk hq rho E hfuel
  · -- `rowSymTreeFlatBridgeSym m DD kT qT` — the flat bridge (parallel `m`-induction, STEP E).
    exact rowSymTreeFlatBridgeSym_WF m DD kT qT hk hq rho E

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

/-! ## Leaf helper WFs (shared across all commutators, X and Z) -/

/-- WF of `entryAtBound`: `applyNatBoundNatBeta` over `allNatLtElim`. -/
theorem entryAtBound_WF (D : OddSurfaceDistance) {Δ : List (SFormula 2)}
    {hW : SFormula.Deriv Δ (entryFlatF1 D).weaken}
    {hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nQ1 D).weaken)}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env 2} {E : PartialStabilizer}
    (wW : DerivWF hW cb fuel rho E) (wq : DerivWF hq cb fuel rho E) :
    DerivWF (entryAtBound D hW hq) cb fuel rho E := by
  unfold entryAtBound
  exact derivWF_applyNatBoundNatBeta _ (derivWF_allNatLtElim _ _ _ wW wq)

/-- WF of `antiXX` / `antiXI` (pure `pauliAnticommutesLit` leaves). -/
theorem antiXX_WF {Δ : List (SFormula 2)} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env 2} {E : PartialStabilizer} :
    DerivWF (antiXX (Δ := Δ)) cb fuel rho E := by
  unfold antiXX; exact derivWF_pauliAnticommutesLit _ _

theorem antiXI_WF {Δ : List (SFormula 2)} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env 2} {E : PartialStabilizer} :
    DerivWF (antiXI (Δ := Δ)) cb fuel rho E := by
  unfold antiXI; exact derivWF_pauliAnticommutesLit _ _

/-- WF of `baseLeafBulkX` — a pure `eqPauliTrans`/`pauliIteSelect` tree; `flat_deriv_wf`
walks it, the three guard `DerivWF`s come by `assumption`. -/
theorem baseLeafBulkX_WF {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true))}
    {hBand : SFormula.Deriv Γ (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true))}
    {hKind : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b false))}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wBand : DerivWF hBand cb fuel rho E)
    (wKind : DerivWF hKind cb fuel rho E) :
    DerivWF (baseLeafBulkX dT kT qT hBulk hBand hKind) cb fuel rho E := by
  unfold baseLeafBulkX
  flat_deriv_wf

/-- WF of `rbfAtBound`: `mp` over `applyNatBoundNatBeta` over `allNatLtElim`. -/
theorem rbfAtBound_WF (D : OddSurfaceDistance) {Δ : List (SFormula 2)}
    {hW : SFormula.Deriv Δ (rightBandFalseF D).weaken}
    {hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nQ1 D).weaken)}
    {hcol : SFormula.Deriv Δ (colGuardRaw2 D)}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env 2} {E : PartialStabilizer}
    (wW : DerivWF hW cb fuel rho E) (wq : DerivWF hq cb fuel rho E)
    (wcol : DerivWF hcol cb fuel rho E) :
    DerivWF (rbfAtBound D hW hq hcol) cb fuel rho E := by
  unfold rbfAtBound
  exact derivWF_mp (derivWF_applyNatBoundNatBeta _ (derivWF_allNatLtElim _ _ _ wW wq)) wcol

/-- WF of `cw1` (= `contextWeakening`). -/
theorem cw1_WF {arity : Nat} {Δ : List (SFormula arity)} {A B : SFormula arity}
    {h : SFormula.Deriv Δ A} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity}
    {E : PartialStabilizer} (w : DerivWF h cb fuel rho E) :
    DerivWF (cw1 (B := B) h) cb fuel rho E := by
  unfold cw1
  exact derivWF_contextWeakening' _ _ w

/-- WF of `cw2`/`cw3`/`cw4`/`cw5` — nested `cw1`. -/
theorem cw2_WF {arity : Nat} {Δ : List (SFormula arity)} {A B C : SFormula arity}
    {h : SFormula.Deriv Δ A} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity}
    {E : PartialStabilizer} (w : DerivWF h cb fuel rho E) :
    DerivWF (cw2 (B := B) (C := C) h) cb fuel rho E := by
  unfold cw2; exact cw1_WF (cw1_WF w)

theorem cw3_WF {arity : Nat} {Δ : List (SFormula arity)} {A B C F : SFormula arity}
    {h : SFormula.Deriv Δ A} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity}
    {E : PartialStabilizer} (w : DerivWF h cb fuel rho E) :
    DerivWF (cw3 (B := B) (C := C) (E := F) h) cb fuel rho E := by
  unfold cw3; exact cw1_WF (cw2_WF w)

theorem cw4_WF {arity : Nat} {Δ : List (SFormula arity)} {A B C F G : SFormula arity}
    {h : SFormula.Deriv Δ A} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity}
    {E : PartialStabilizer} (w : DerivWF h cb fuel rho E) :
    DerivWF (cw4 (B := B) (C := C) (E := F) (F := G) h) cb fuel rho E := by
  unfold cw4; exact cw1_WF (cw3_WF w)

theorem cw5_WF {arity : Nat} {Δ : List (SFormula arity)} {A B C F G H : SFormula arity}
    {h : SFormula.Deriv Δ A} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity}
    {E : PartialStabilizer} (w : DerivWF h cb fuel rho E) :
    DerivWF (cw5 (B := B) (C := C) (E := F) (F := G) (G := H) h) cb fuel rho E := by
  unfold cw5; exact cw1_WF (cw4_WF w)

/-- WF of `eqBoolContra` (guard true∧false contradiction) — `botElim/notElim/eqBoolFalseNotTrue`. -/
theorem eqBoolContra_WF {arity : Nat} {Δ : List (SFormula arity)} {C : SFormula arity}
    (b : STerm arity .bool) {hT : SFormula.Deriv Δ (.eqBool b (SC.b true))}
    {hF : SFormula.Deriv Δ (.eqBool b (SC.b false))}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wT : DerivWF hT cb fuel rho E) (wF : DerivWF hF cb fuel rho E) :
    DerivWF (eqBoolContra (C := C) b hT hF) cb fuel rho E := by
  unfold eqBoolContra; comm_deriv_wf

/-- WF of `baseLeafZ` (pure ite tree; flat). -/
theorem baseLeafZ_WF {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true))}
    {hBand : SFormula.Deriv Γ (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true))}
    {hKind : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b true))}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wBand : DerivWF hBand cb fuel rho E)
    (wKind : DerivWF hKind cb fuel rho E) :
    DerivWF (baseLeafZ dT kT qT hBulk hBand hKind) cb fuel rho E := by
  unfold baseLeafZ; flat_deriv_wf

/- The deep `baseLeaf*` trees walk the giant nested-ite `baseLeafTreeTA`; the project
runs the analogous `baseLeaf*S_WF` block at `maxHeartbeats 1600000` (SurfaceNormalizerDefined,
file-level from line 1939).  Match that here; on migration these sit under the same setting. -/
set_option maxHeartbeats 1600000

theorem baseLeafBulkI_WF {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true))}
    {hBand : SFormula.Deriv Γ (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false))}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wBand : DerivWF hBand cb fuel rho E) :
    DerivWF (baseLeafBulkI dT kT qT hBulk hBand) cb fuel rho E := by
  unfold baseLeafBulkI; flat_deriv_wf

theorem baseLeafTopX_WF {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false))}
    {hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b true))}
    {hTopBand : SFormula.Deriv Γ (.eqBool (SC.closed (topBandGuardTA dT kT qT)) (SC.b true))}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wTopBand : DerivWF hTopBand cb fuel rho E) :
    DerivWF (baseLeafTopX dT kT qT hBulk hTopClass hTopBand) cb fuel rho E := by
  unfold baseLeafTopX; flat_deriv_wf

theorem baseLeafTopI_WF {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false))}
    {hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b true))}
    {hTopBand : SFormula.Deriv Γ (.eqBool (SC.closed (topBandGuardTA dT kT qT)) (SC.b false))}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wTopBand : DerivWF hTopBand cb fuel rho E) :
    DerivWF (baseLeafTopI dT kT qT hBulk hTopClass hTopBand) cb fuel rho E := by
  unfold baseLeafTopI; flat_deriv_wf

theorem baseLeafRightI_WF {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false))}
    {hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false))}
    {hRightClass : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b true))}
    {hRightBand : SFormula.Deriv Γ (.eqBool (SC.closed (rightBandGuardTA dT kT qT)) (SC.b false))}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wRightBand : DerivWF hRightBand cb fuel rho E) :
    DerivWF (baseLeafRightI dT kT qT hBulk hTopClass hRightClass hRightBand) cb fuel rho E := by
  unfold baseLeafRightI; flat_deriv_wf

theorem baseLeafLeftI_WF {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false))}
    {hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false))}
    {hRightClass : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b false))}
    {hLeftClass : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA dT kT)) (SC.b true))}
    {hLeftBand : SFormula.Deriv Γ (.eqBool (SC.closed (leftBandGuardTA dT kT qT)) (SC.b false))}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wLeftClass : DerivWF hLeftClass cb fuel rho E)
    (wLeftBand : DerivWF hLeftBand cb fuel rho E) :
    DerivWF (baseLeafLeftI dT kT qT hBulk hTopClass hRightClass hLeftClass hLeftBand) cb fuel rho E := by
  unfold baseLeafLeftI; flat_deriv_wf

theorem baseLeafBottomX_WF {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false))}
    {hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false))}
    {hRightClass : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b false))}
    {hLeftClass : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA dT kT)) (SC.b false))}
    {hBottomBand : SFormula.Deriv Γ (.eqBool (SC.closed (bottomBandGuardTA dT kT qT)) (SC.b true))}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wLeftClass : DerivWF hLeftClass cb fuel rho E)
    (wBottomBand : DerivWF hBottomBand cb fuel rho E) :
    DerivWF (baseLeafBottomX dT kT qT hBulk hTopClass hRightClass hLeftClass hBottomBand) cb fuel rho E := by
  unfold baseLeafBottomX; flat_deriv_wf

theorem baseLeafBottomI_WF {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false))}
    {hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false))}
    {hRightClass : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b false))}
    {hLeftClass : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA dT kT)) (SC.b false))}
    {hBottomBand : SFormula.Deriv Γ (.eqBool (SC.closed (bottomBandGuardTA dT kT qT)) (SC.b false))}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wLeftClass : DerivWF hLeftClass cb fuel rho E)
    (wBottomBand : DerivWF hBottomBand cb fuel rho E) :
    DerivWF (baseLeafBottomI dT kT qT hBulk hTopClass hRightClass hLeftClass hBottomBand) cb fuel rho E := by
  unfold baseLeafBottomI; flat_deriv_wf

/-- WF of `antiZAtA` (`eqPauliTrans` of the recCall row entry and `baseLeafZ`). -/
theorem antiZAtA_WF (D : OddSurfaceDistance) {Γ : List (SFormula 1)} (qT : Term 1 .nat)
    (hqpure : SFormula.PureNatTerm qT)
    {hEntry : SFormula.Deriv Γ
      (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed qT))
        (SC.closed (baseLeafTreeTA (dX1 D) kX1 qT)))}
    {hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dX1 D) kX1)) (SC.b true))}
    {hBand : SFormula.Deriv Γ (.eqBool (SC.closed (baseBulkBandGuardTA (dX1 D) kX1 qT)) (SC.b true))}
    {hKind : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dX1 D) kX1)) (SC.b true))}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env 1} {E : PartialStabilizer}
    (wEntry : DerivWF hEntry cb fuel rho E) (wBulk : DerivWF hBulk cb fuel rho E)
    (wBand : DerivWF hBand cb fuel rho E) (wKind : DerivWF hKind cb fuel rho E) :
    DerivWF (antiZAtA D qT hqpure hEntry hBulk hBand hKind) cb fuel rho E := by
  have hd : SFormula.PureNatTerm (dX1 D) := dX1_pure D
  have hk : SFormula.PureNatTerm kX1 := SFormula.PureNatTerm.var _
  unfold antiZAtA baseLeafZ
  comm_deriv_wf

/-- WF of `lxOnColEntryX` (logicalX entry = X on column 0), arity-2/boundNat adaptation of
`logicalXOriginEntryDeriv_WF`: targeted `derivWF_cast_type`/`stabAtClosedIteLamEqThen` (NON-'
to avoid the giant-term whnf), explicit `logicalXBody_eval_total` for the LHS eval. -/
theorem lxOnColEntryX_WF (D : OddSurfaceDistance) {Δ : List (SFormula 2)}
    {hTrue : SFormula.Deriv Δ (.eqBool (logicalXColGuardAt2 D) (SC.b true))}
    {fuel : Nat} {rho : Env 2} {E : PartialStabilizer}
    (wTrue : DerivWF hTrue Surface.code.body fuel rho E) :
    DerivWF (lxOnColEntryX D hTrue) Surface.code.body fuel rho E := by
  unfold lxOnColEntryX
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  refine derivWF_cast_type rfl ?_ _ _
    (derivWF_cast_type rfl ?_ _ _
      (derivWF_stabAtClosedIteLamEqThen _ _ _ _ _ wTrue ?lhs ?rhs))
  · simp only [liftedLX2, logicalXOdd, logicalX, Formula.qVar, SC.closed, SC.p,
      OddSurfaceDistance.distance, oddDistance, STerm.weaken, STerm.lift,
      Term.lift, Term.weaken, Term.weakenVar]
    first | rfl | simp [Term.instantiateTopNat, Term.instantiateNatAt, Term.weakenVar]
  · simp only [liftedLX2, logicalXOdd, logicalX, Formula.qVar, SC.closed, SC.p,
      OddSurfaceDistance.distance, oddDistance, STerm.weaken, STerm.lift,
      Term.lift, Term.weaken, Term.weakenVar]
    first | rfl | simp [Term.instantiateTopNat, Term.instantiateNatAt, Term.weakenVar]
  case lhs =>
    exact ⟨(if rho 0 % D.distance = 0 then Pauli.X else Pauli.I),
      by simp [SC.closed, STerm.eval, Term.eval, Formula.qVar, Env.cons, bind, Option.bind];
         split <;> rfl⟩
  case rhs =>
    exact ⟨Pauli.X, by simp [Term.instantiateTopNat, Term.instantiateNatAt, Term.eval]⟩

/-- WF of `lxPureEntryX` (logicalX entry = X at a pure column-0 qubit `qT`),
arity-1/pure-qubit analogue of `lxOnColEntryX_WF`.  Same `simp only`/double-cast
recipe; the guard child is the `simpa`-cast of `hguardq` (one inner cast), and the
LHS eval pivots on `PureNatTerm.eval_total` for the pure qubit. -/
theorem lxPureEntryX_WF (D : OddSurfaceDistance) {Γ : List (SFormula 1)}
    (qT : Term 1 .nat) (hq : SFormula.PureNatTerm qT)
    {hguardq : SFormula.Deriv Γ (colGuardPure1 D qT)}
    {fuel : Nat} {rho : Env 1} {E : PartialStabilizer}
    (wguardq : DerivWF hguardq Surface.code.body fuel rho E) :
    DerivWF (lxPureEntryX D qT hq hguardq) Surface.code.body fuel rho E := by
  unfold lxPureEntryX
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  refine derivWF_cast_type rfl ?_ _ _
    (derivWF_cast_type rfl ?_ _ _
      (derivWF_stabAtClosedIteLamEqThen _ _ _ _ _
        (derivWF_cast_type rfl ?_ _ _ wguardq) ?lhs ?rhs))
  · simp only [liftedLX1, logicalXOdd, logicalX, Formula.qVar, SC.closed, SC.p, Term.lift]
    first | rfl | simp [Term.instantiateTopNat, Term.instantiateNatAt, Term.weakenVar]
  · simp only [liftedLX1, logicalXOdd, logicalX, Formula.qVar, SC.closed, SC.p, Term.lift]
    first | rfl | simp [Term.instantiateTopNat, Term.instantiateNatAt, Term.weakenVar]
  · simp only [liftedLX1, logicalXOdd, logicalX, Formula.qVar, SC.closed, SC.p, Term.lift]
    first | rfl | simp [Term.instantiateTopNat, Term.instantiateNatAt, Term.weakenVar]
  case lhs =>
    obtain ⟨qv, hqv⟩ := SFormula.PureNatTerm.eval_total hq Surface.code.body fuel (rho := rho)
    exact ⟨if qv % D.distance = 0 then Pauli.X else Pauli.I,
      by simp [SC.closed, STerm.eval, Term.eval, Formula.qVar, Env.cons, bind, Option.bind, hqv];
         split <;> rfl⟩
  case rhs =>
    exact ⟨Pauli.X, by simp [Term.instantiateTopNat, Term.instantiateNatAt, Term.eval]⟩

/-- WF of `logicalXOffColumnLocalCommutes` (off-column ⇒ logicalX entry is `I`,
hence `A` commutes there).  `localCommutesOfRightI` over the Else-branch entry deriv,
with the `localCommutesAt` `FormulaDefined` from the caller's left-stab eval `hA`
and the (reduced) lifted-logicalX eval. -/
theorem logicalXOffColumnLocalCommutes_WF (D : OddSurfaceDistance) {Γ : List (SFormula 2)}
    (A : STerm 2 .stab)
    {hFalse : SFormula.Deriv Γ (.eqBool (logicalXColGuardAt2 D) (SC.b false))}
    {fuel : Nat} {rho : Env 2} {E : PartialStabilizer}
    (wFalse : DerivWF hFalse Surface.code.body fuel rho E)
    (hA : ∃ v, (STerm.stabAt A SFormula.boundNat).eval Surface.code.body fuel rho E = some v) :
    DerivWF (logicalXOffColumnLocalCommutes D A hFalse) Surface.code.body fuel rho E := by
  unfold logicalXOffColumnLocalCommutes
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  refine derivWF_localCommutesOfRightI _ _ _
    (derivWF_cast_type rfl ?_ _ _ (derivWF_cast_type rfl ?_ _ _
      (derivWF_stabAtClosedIteLamEqElse _ _ _ _ _ wFalse ?lhs ?rhs)))
    ?fd
  · simp only [logicalXOdd, logicalX, Formula.qVar, SC.closed, SC.p, OddSurfaceDistance.distance,
      oddDistance, STerm.weaken, STerm.lift, Term.lift, Term.weaken, Term.weakenVar]
    first | rfl | simp [Term.instantiateTopNat, Term.instantiateNatAt, Term.weakenVar]
  · simp only [logicalXOdd, logicalX, Formula.qVar, SC.closed, SC.p, OddSurfaceDistance.distance,
      oddDistance, STerm.weaken, STerm.lift, Term.lift, Term.weaken, Term.weakenVar]
    first | rfl | simp [Term.instantiateTopNat, Term.instantiateNatAt, Term.weakenVar]
  case lhs =>
    exact ⟨(if rho 0 % D.distance = 0 then Pauli.X else Pauli.I),
      by simp [SC.closed, STerm.eval, Term.eval, Formula.qVar, Env.cons, bind, Option.bind];
         split <;> rfl⟩
  case rhs =>
    exact ⟨Pauli.I, by simp [Term.instantiateTopNat, Term.instantiateNatAt, Term.eval]⟩
  case fd =>
    refine formulaDefined_localCommutesAt hA ?_
    exact ⟨if rho 0 % D.distance = 0 then Pauli.X else Pauli.I,
      by simp only [logicalXOdd, logicalX, SC.closed, SC.p, OddSurfaceDistance.distance, oddDistance,
            STerm.weaken, STerm.lift, Term.lift, Term.weaken, Term.weakenVar, SFormula.boundNat];
         simp [STerm.eval, Term.eval, Formula.qVar, Env.cons, bind, Option.bind,
            Term.lift, Term.weakenVar];
         split <;> rfl⟩

/-- WF of `lzOnRowEntryZ` (logicalZ entry = Z on row 0).  Z/`div`/row transpose of
`lxOnColEntryX_WF`. -/
theorem lzOnRowEntryZ_WF (D : OddSurfaceDistance) {Δ : List (SFormula 2)}
    {hTrue : SFormula.Deriv Δ (.eqBool (logicalZRowGuardAt2 D) (SC.b true))}
    {fuel : Nat} {rho : Env 2} {E : PartialStabilizer}
    (wTrue : DerivWF hTrue Surface.code.body fuel rho E) :
    DerivWF (lzOnRowEntryZ D hTrue) Surface.code.body fuel rho E := by
  unfold lzOnRowEntryZ
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  refine derivWF_cast_type rfl ?_ _ _
    (derivWF_cast_type rfl ?_ _ _
      (derivWF_stabAtClosedIteLamEqThen _ _ _ _ _ wTrue ?lhs ?rhs))
  · simp only [liftedLZ2, logicalZOdd, logicalZ, Formula.qVar, SC.closed, SC.p,
      OddSurfaceDistance.distance, oddDistance, STerm.weaken, STerm.lift,
      Term.lift, Term.weaken, Term.weakenVar]
    first | rfl | simp [Term.instantiateTopNat, Term.instantiateNatAt, Term.weakenVar]
  · simp only [liftedLZ2, logicalZOdd, logicalZ, Formula.qVar, SC.closed, SC.p,
      OddSurfaceDistance.distance, oddDistance, STerm.weaken, STerm.lift,
      Term.lift, Term.weaken, Term.weakenVar]
    first | rfl | simp [Term.instantiateTopNat, Term.instantiateNatAt, Term.weakenVar]
  case lhs =>
    exact ⟨(if rho 0 / D.distance = 0 then Pauli.Z else Pauli.I),
      by simp [SC.closed, STerm.eval, Term.eval, Formula.qVar, Env.cons, bind, Option.bind];
         split <;> rfl⟩
  case rhs =>
    exact ⟨Pauli.Z, by simp [Term.instantiateTopNat, Term.instantiateNatAt, Term.eval]⟩

/-- WF of `lzPureEntryZ`.  Z/`div`/row/pure-qubit transpose of `lxPureEntryX_WF`. -/
theorem lzPureEntryZ_WF (D : OddSurfaceDistance) {Γ : List (SFormula 1)}
    (qT : Term 1 .nat) (hq : SFormula.PureNatTerm qT)
    {hguardq : SFormula.Deriv Γ (rowGuardPure1 D qT)}
    {fuel : Nat} {rho : Env 1} {E : PartialStabilizer}
    (wguardq : DerivWF hguardq Surface.code.body fuel rho E) :
    DerivWF (lzPureEntryZ D qT hq hguardq) Surface.code.body fuel rho E := by
  unfold lzPureEntryZ
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  refine derivWF_cast_type rfl ?_ _ _
    (derivWF_cast_type rfl ?_ _ _
      (derivWF_stabAtClosedIteLamEqThen _ _ _ _ _
        (derivWF_cast_type rfl ?_ _ _ wguardq) ?lhs ?rhs))
  · simp only [liftedLZ1, logicalZOdd, logicalZ, Formula.qVar, SC.closed, SC.p, Term.lift]
    first | rfl | simp [Term.instantiateTopNat, Term.instantiateNatAt, Term.weakenVar]
  · simp only [liftedLZ1, logicalZOdd, logicalZ, Formula.qVar, SC.closed, SC.p, Term.lift]
    first | rfl | simp [Term.instantiateTopNat, Term.instantiateNatAt, Term.weakenVar]
  · simp only [liftedLZ1, logicalZOdd, logicalZ, Formula.qVar, SC.closed, SC.p, Term.lift]
    first | rfl | simp [Term.instantiateTopNat, Term.instantiateNatAt, Term.weakenVar]
  case lhs =>
    obtain ⟨qv, hqv⟩ := SFormula.PureNatTerm.eval_total hq Surface.code.body fuel (rho := rho)
    exact ⟨if qv / D.distance = 0 then Pauli.Z else Pauli.I,
      by simp [SC.closed, STerm.eval, Term.eval, Formula.qVar, Env.cons, bind, Option.bind, hqv];
         split <;> rfl⟩
  case rhs =>
    exact ⟨Pauli.Z, by simp [Term.instantiateTopNat, Term.instantiateNatAt, Term.eval]⟩

/-- WF of `logicalZOffRowLocalCommutes`.  Z/`div`/row transpose of
`logicalXOffColumnLocalCommutes_WF`. -/
theorem logicalZOffRowLocalCommutes_WF (D : OddSurfaceDistance) {Γ : List (SFormula 2)}
    (A : STerm 2 .stab)
    {hFalse : SFormula.Deriv Γ (.eqBool (logicalZRowGuardAt2 D) (SC.b false))}
    {fuel : Nat} {rho : Env 2} {E : PartialStabilizer}
    (wFalse : DerivWF hFalse Surface.code.body fuel rho E)
    (hA : ∃ v, (STerm.stabAt A SFormula.boundNat).eval Surface.code.body fuel rho E = some v) :
    DerivWF (logicalZOffRowLocalCommutes D A hFalse) Surface.code.body fuel rho E := by
  unfold logicalZOffRowLocalCommutes
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  refine derivWF_localCommutesOfRightI _ _ _
    (derivWF_cast_type rfl ?_ _ _ (derivWF_cast_type rfl ?_ _ _
      (derivWF_stabAtClosedIteLamEqElse _ _ _ _ _ wFalse ?lhs ?rhs)))
    ?fd
  · simp only [logicalZOdd, logicalZ, Formula.qVar, SC.closed, SC.p, OddSurfaceDistance.distance,
      oddDistance, STerm.weaken, STerm.lift, Term.lift, Term.weaken, Term.weakenVar]
    first | rfl | simp [Term.instantiateTopNat, Term.instantiateNatAt, Term.weakenVar]
  · simp only [logicalZOdd, logicalZ, Formula.qVar, SC.closed, SC.p, OddSurfaceDistance.distance,
      oddDistance, STerm.weaken, STerm.lift, Term.lift, Term.weaken, Term.weakenVar]
    first | rfl | simp [Term.instantiateTopNat, Term.instantiateNatAt, Term.weakenVar]
  case lhs =>
    exact ⟨(if rho 0 / D.distance = 0 then Pauli.Z else Pauli.I),
      by simp [SC.closed, STerm.eval, Term.eval, Formula.qVar, Env.cons, bind, Option.bind];
         split <;> rfl⟩
  case rhs =>
    exact ⟨Pauli.I, by simp [Term.instantiateTopNat, Term.instantiateNatAt, Term.eval]⟩
  case fd =>
    refine formulaDefined_localCommutesAt hA ?_
    exact ⟨if rho 0 / D.distance = 0 then Pauli.Z else Pauli.I,
      by simp only [logicalZOdd, logicalZ, SC.closed, SC.p, OddSurfaceDistance.distance, oddDistance,
            STerm.weaken, STerm.lift, Term.lift, Term.weaken, Term.weakenVar, SFormula.boundNat];
         simp [STerm.eval, Term.eval, Formula.qVar, Env.cons, bind, Option.bind,
            Term.lift, Term.weakenVar];
         split <;> rfl⟩

/-- Reusable: the lifted-`logicalX` operator evaluates at the symbolic qubit binder
`boundNat` (X on column 0, I off it — either way total).  Supplies the `B`-side of the
`localCommutesAt … (liftedLX2 D) boundNat` `FormulaDefined`. -/
theorem liftedLX2_boundNat_eval (D : OddSurfaceDistance)
    {fuel : Nat} {rho : Env 2} {E : PartialStabilizer} :
    ∃ v, (STerm.stabAt (liftedLX2 D) SFormula.boundNat).eval Surface.code.body fuel rho E = some v :=
  ⟨if rho 0 % D.distance = 0 then Pauli.X else Pauli.I,
    by simp only [liftedLX2, logicalXOdd, logicalX, SC.closed, SC.p, OddSurfaceDistance.distance,
          oddDistance, STerm.weaken, STerm.lift, Term.lift, Term.weaken, Term.weakenVar,
          SFormula.boundNat];
       simp [STerm.eval, Term.eval, Formula.qVar, Env.cons, bind, Option.bind,
          Term.lift, Term.weakenVar];
       split <;> rfl⟩

/-- WF of `colCommFromEntry` — column-0 local commutation from a non-Z row entry. -/
theorem colCommFromEntry_WF (D : OddSurfaceDistance) (p : Pauli) {Δ : List (SFormula 2)}
    {hEntry : SFormula.Deriv Δ (.eqPauli (.stabAt (rowK2 D) SFormula.boundNat) (SC.p p))}
    {hAnti : SFormula.Deriv Δ (.eqBool (.anticommutes (SC.p Pauli.X) (SC.p p)) (SC.b false))}
    {hcol : SFormula.Deriv Δ (.eqBool (logicalXColGuardAt2 D) (SC.b true))}
    {fuel : Nat} {rho : Env 2} {E : PartialStabilizer}
    (wEntry : DerivWF hEntry Surface.code.body fuel rho E)
    (wAnti : DerivWF hAnti Surface.code.body fuel rho E)
    (wcol : DerivWF hcol Surface.code.body fuel rho E)
    (hA : ∃ v, (STerm.stabAt (rowK2 D) SFormula.boundNat).eval Surface.code.body fuel rho E = some v) :
    DerivWF (colCommFromEntry D p hEntry hAnti hcol) Surface.code.body fuel rho E := by
  unfold colCommFromEntry
  refine derivWF_localCommutesOfLeftEqNoAntiRight _ _ _ _ wEntry ?noAnti ?fd
  · exact derivWF_eqBoolFalseNotTrue
      (derivWF_anticommutesTransport _ _ _ _ _ (lxOnColEntryX_WF D wcol)
        (derivWF_pauliEqLit' _) wAnti
        (formulaDefined_eqBool
          (sterm_eval_anticommutes (liftedLX2_boundNat_eval D) (sterm_eval_p _)) (sterm_eval_b _)))
  · exact formulaDefined_localCommutesAt hA (liftedLX2_boundNat_eval D)

/-- WF of `lcFromLeaf` — local commutation from a resolved leaf entry. -/
theorem lcFromLeaf_WF (D : OddSurfaceDistance) (p : Pauli) {Δ : List (SFormula 2)}
    {hEntry : SFormula.Deriv Δ (entryFlat2F D)}
    {hLeaf : SFormula.Deriv Δ
      (.eqPauli (SC.closed (baseLeafTreeTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.p p))}
    {hAnti : SFormula.Deriv Δ (.eqBool (.anticommutes (SC.p Pauli.X) (SC.p p)) (SC.b false))}
    {hcol : SFormula.Deriv Δ (.eqBool (logicalXColGuardAt2 D) (SC.b true))}
    {fuel : Nat} {rho : Env 2} {E : PartialStabilizer}
    (wEntry : DerivWF hEntry Surface.code.body fuel rho E)
    (wLeaf : DerivWF hLeaf Surface.code.body fuel rho E)
    (wAnti : DerivWF hAnti Surface.code.body fuel rho E)
    (wcol : DerivWF hcol Surface.code.body fuel rho E)
    (hA : ∃ v, (STerm.stabAt (rowK2 D) SFormula.boundNat).eval Surface.code.body fuel rho E = some v) :
    DerivWF (lcFromLeaf D p hEntry hLeaf hAnti hcol) Surface.code.body fuel rho E := by
  unfold lcFromLeaf
  exact colCommFromEntry_WF D p (derivWF_eqPauliTrans' wEntry wLeaf) wAnti wcol hA

/-- `disp_wf`: walks the column-0 dispatcher `boolCases` tree, citing the proved
`lcFromLeaf_WF`/`baseLeaf*_WF`/`cwN_WF`/`antiX*_WF` leaf lemmas; `True.intro` closes the
`hyp`/`assumption` leaves and `assumption` supplies the purity/`hA`/guard-WF arguments.
Leaves the two `hZbulk`/`hZleft` higher-order applications as residual goals. -/
macro "disp_wf" : tactic =>
  `(tactic|
    repeat (any_goals (first
      | exact True.intro
      | refine derivWF_boolCases _ _
          (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?_ ?_
      | refine derivWF_botElim ?_
      | refine derivWF_notElim ?_ ?_
      | refine derivWF_eqBoolFalseNotTrue ?_
      | refine lcFromLeaf_WF _ _ ?_ ?_ ?_ ?_ ?_
      | refine baseLeafBulkX_WF _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
      | refine baseLeafBulkI_WF _ _ _ ?_ ?_ ?_ ?_ ?_
      | refine baseLeafTopX_WF _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
      | refine baseLeafTopI_WF _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
      | refine baseLeafRightI_WF _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      | refine baseLeafLeftI_WF _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      | refine baseLeafBottomX_WF _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      | refine baseLeafBottomI_WF _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      | refine lcFromLeafZ_WF _ _ ?_ ?_ ?_ ?_ ?_
      | refine baseLeafZ_WF _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
      | refine baseLeafRightZ_WF _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      | refine baseLeafLeftZ_WF _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      | exact antiXX_WF
      | exact antiXI_WF
      | exact antiZZ_WF
      | exact antiZI_WF
      | refine cw5_WF ?_
      | refine cw4_WF ?_
      | refine cw3_WF ?_
      | refine cw2_WF ?_
      | refine cw1_WF ?_
      | assumption)))

/-- WF of `colDispatchOnTrue` — the column-0 entry dispatcher.  Mirrors the def's
`boolCases` tree via `disp_wf`; the two `Z`-leaf handlers `hZbulk`/`hZleft` carry
higher-order `DerivWF` hypotheses (the lift + its WF-preservation + each input WF). -/
theorem colDispatchOnTrue_WF (D : OddSurfaceDistance) {Δ : List (SFormula 2)}
    {hEntry : SFormula.Deriv Δ (entryFlat2F D)}
    {hcol : SFormula.Deriv Δ (.eqBool (logicalXColGuardAt2 D) (SC.b true))}
    {hRBF : SFormula.Deriv Δ
      (.eqBool (SC.closed (rightBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.b false))}
    {hZbulk : ∀ (Δ' : List (SFormula 2)),
      (∀ {A : SFormula 2}, SFormula.Deriv Δ A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (entryFlat2F D) →
      SFormula.Deriv Δ' (.eqBool (logicalXColGuardAt2 D) (SC.b true)) →
      SFormula.Deriv Δ' (gBulk D true) → SFormula.Deriv Δ' (gBand D true) →
      SFormula.Deriv Δ' (gKind D true) → SFormula.Deriv Δ' (lcGoal D)}
    {hZleft : ∀ (Δ' : List (SFormula 2)),
      (∀ {A : SFormula 2}, SFormula.Deriv Δ A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (entryFlat2F D) →
      SFormula.Deriv Δ' (.eqBool (logicalXColGuardAt2 D) (SC.b true)) →
      SFormula.Deriv Δ' (gBulk D false) → SFormula.Deriv Δ' (gTopC D false) →
      SFormula.Deriv Δ' (gRightC D false) → SFormula.Deriv Δ' (gLeftC D true) →
      SFormula.Deriv Δ' (gLeftB D true) → SFormula.Deriv Δ' (lcGoal D)}
    {fuel : Nat} {rho : Env 2} {E : PartialStabilizer}
    (wEntry : DerivWF hEntry Surface.code.body fuel rho E)
    (wcol : DerivWF hcol Surface.code.body fuel rho E)
    (wRBF : DerivWF hRBF Surface.code.body fuel rho E)
    (wZbulk : ∀ (Δ' : List (SFormula 2))
        (lift : ∀ {A : SFormula 2}, SFormula.Deriv Δ A → SFormula.Deriv Δ' A),
        (∀ {A : SFormula 2} {h : SFormula.Deriv Δ A},
          DerivWF h Surface.code.body fuel rho E → DerivWF (lift h) Surface.code.body fuel rho E) →
        ∀ {he : SFormula.Deriv Δ' (entryFlat2F D)}, DerivWF he Surface.code.body fuel rho E →
        ∀ {hc : SFormula.Deriv Δ' (.eqBool (logicalXColGuardAt2 D) (SC.b true))},
          DerivWF hc Surface.code.body fuel rho E →
        ∀ {hbu : SFormula.Deriv Δ' (gBulk D true)}, DerivWF hbu Surface.code.body fuel rho E →
        ∀ {hba : SFormula.Deriv Δ' (gBand D true)}, DerivWF hba Surface.code.body fuel rho E →
        ∀ {hki : SFormula.Deriv Δ' (gKind D true)}, DerivWF hki Surface.code.body fuel rho E →
        DerivWF (hZbulk Δ' lift he hc hbu hba hki) Surface.code.body fuel rho E)
    (wZleft : ∀ (Δ' : List (SFormula 2))
        (lift : ∀ {A : SFormula 2}, SFormula.Deriv Δ A → SFormula.Deriv Δ' A),
        (∀ {A : SFormula 2} {h : SFormula.Deriv Δ A},
          DerivWF h Surface.code.body fuel rho E → DerivWF (lift h) Surface.code.body fuel rho E) →
        ∀ {he : SFormula.Deriv Δ' (entryFlat2F D)}, DerivWF he Surface.code.body fuel rho E →
        ∀ {hc : SFormula.Deriv Δ' (.eqBool (logicalXColGuardAt2 D) (SC.b true))},
          DerivWF hc Surface.code.body fuel rho E →
        ∀ {hbu : SFormula.Deriv Δ' (gBulk D false)}, DerivWF hbu Surface.code.body fuel rho E →
        ∀ {htc : SFormula.Deriv Δ' (gTopC D false)}, DerivWF htc Surface.code.body fuel rho E →
        ∀ {hrc : SFormula.Deriv Δ' (gRightC D false)}, DerivWF hrc Surface.code.body fuel rho E →
        ∀ {hlc : SFormula.Deriv Δ' (gLeftC D true)}, DerivWF hlc Surface.code.body fuel rho E →
        ∀ {hlb : SFormula.Deriv Δ' (gLeftB D true)}, DerivWF hlb Surface.code.body fuel rho E →
        DerivWF (hZleft Δ' lift he hc hbu htc hrc hlc hlb) Surface.code.body fuel rho E)
    (hA : ∃ v, (STerm.stabAt (rowK2 D) SFormula.boundNat).eval Surface.code.body fuel rho E = some v) :
    DerivWF (colDispatchOnTrue D hEntry hcol hRBF hZbulk hZleft) Surface.code.body fuel rho E := by
  have hd : SFormula.PureNatTerm (dX2 D) := (distAtBoundIdx2 D).pure
  have hk : SFormula.PureNatTerm kX2 := .var _
  have hq : SFormula.PureNatTerm (Term.var (⟨0, by decide⟩ : Fin 2)) := .var _
  unfold colDispatchOnTrue
  disp_wf
  · exact wZbulk _ (fun h => cw3 h) (fun w => cw3_WF w) (cw3_WF wEntry) (cw3_WF wcol)
      (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _)
  · exact wZleft _ (fun h => cw5 h) (fun w => cw5_WF w) (cw5_WF wEntry) (cw5_WF wcol)
      (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _)

/-- WF of `commPointwiseSym` — pointwise per-`k` commutation.  The qubit-binder context
`ΔC = colGuard :: boundNatLt :: Γ.map weaken` is the `Δ` of the inner `colDispatchOnTrue`. -/
theorem commPointwiseSym_WF (D : OddSurfaceDistance) {Γ : List (SFormula 1)}
    {hEntryF : SFormula.Deriv Γ (entryFlatF1 D)}
    {hRBFF : SFormula.Deriv Γ (rightBandFalseF D)}
    {hZbulk : ∀ (Δ' : List (SFormula 2)),
      (∀ {A : SFormula 2}, SFormula.Deriv (.eqBool (logicalXColGuardAt2 D) (SC.b true)
          :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (entryFlat2F D) →
      SFormula.Deriv Δ' (.eqBool (logicalXColGuardAt2 D) (SC.b true)) →
      SFormula.Deriv Δ' (gBulk D true) → SFormula.Deriv Δ' (gBand D true) →
      SFormula.Deriv Δ' (gKind D true) → SFormula.Deriv Δ' (lcGoal D)}
    {hZleft : ∀ (Δ' : List (SFormula 2)),
      (∀ {A : SFormula 2}, SFormula.Deriv (.eqBool (logicalXColGuardAt2 D) (SC.b true)
          :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (entryFlat2F D) →
      SFormula.Deriv Δ' (.eqBool (logicalXColGuardAt2 D) (SC.b true)) →
      SFormula.Deriv Δ' (gBulk D false) → SFormula.Deriv Δ' (gTopC D false) →
      SFormula.Deriv Δ' (gRightC D false) → SFormula.Deriv Δ' (gLeftC D true) →
      SFormula.Deriv Δ' (gLeftB D true) → SFormula.Deriv Δ' (lcGoal D)}
    {rho : Env 1} {E : PartialStabilizer}
    (wEntryF : DerivWF hEntryF Surface.code.body (D.distance + 2) rho E)
    (wRBFF : DerivWF hRBFF Surface.code.body (D.distance + 2) rho E)
    (wZbulk : ∀ (x : Nat) (Δ' : List (SFormula 2))
        (lift : ∀ {A : SFormula 2}, SFormula.Deriv (.eqBool (logicalXColGuardAt2 D) (SC.b true)
            :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A),
        (∀ {A : SFormula 2} {h : SFormula.Deriv (.eqBool (logicalXColGuardAt2 D) (SC.b true)
            :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A},
          DerivWF h Surface.code.body (D.distance + 2) (Env.cons x rho) E →
          DerivWF (lift h) Surface.code.body (D.distance + 2) (Env.cons x rho) E) →
        ∀ {he : SFormula.Deriv Δ' (entryFlat2F D)},
          DerivWF he Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        ∀ {hc : SFormula.Deriv Δ' (.eqBool (logicalXColGuardAt2 D) (SC.b true))},
          DerivWF hc Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        ∀ {hbu : SFormula.Deriv Δ' (gBulk D true)},
          DerivWF hbu Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        ∀ {hba : SFormula.Deriv Δ' (gBand D true)},
          DerivWF hba Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        ∀ {hki : SFormula.Deriv Δ' (gKind D true)},
          DerivWF hki Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        DerivWF (hZbulk Δ' lift he hc hbu hba hki) Surface.code.body (D.distance + 2) (Env.cons x rho) E)
    (wZleft : ∀ (x : Nat) (Δ' : List (SFormula 2))
        (lift : ∀ {A : SFormula 2}, SFormula.Deriv (.eqBool (logicalXColGuardAt2 D) (SC.b true)
            :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A),
        (∀ {A : SFormula 2} {h : SFormula.Deriv (.eqBool (logicalXColGuardAt2 D) (SC.b true)
            :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A},
          DerivWF h Surface.code.body (D.distance + 2) (Env.cons x rho) E →
          DerivWF (lift h) Surface.code.body (D.distance + 2) (Env.cons x rho) E) →
        ∀ {he : SFormula.Deriv Δ' (entryFlat2F D)},
          DerivWF he Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        ∀ {hc : SFormula.Deriv Δ' (.eqBool (logicalXColGuardAt2 D) (SC.b true))},
          DerivWF hc Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        ∀ {hbu : SFormula.Deriv Δ' (gBulk D false)},
          DerivWF hbu Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        ∀ {htc : SFormula.Deriv Δ' (gTopC D false)},
          DerivWF htc Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        ∀ {hrc : SFormula.Deriv Δ' (gRightC D false)},
          DerivWF hrc Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        ∀ {hlc : SFormula.Deriv Δ' (gLeftC D true)},
          DerivWF hlc Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        ∀ {hlb : SFormula.Deriv Δ' (gLeftB D true)},
          DerivWF hlb Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        DerivWF (hZleft Δ' lift he hc hbu htc hrc hlc hlb) Surface.code.body (D.distance + 2) (Env.cons x rho) E)
    (hCtx : SFormula.ContextHolds Surface.code.body (D.distance + 2) rho E Γ) :
    DerivWF (commPointwiseSym D hEntryF hRBFF hZbulk hZleft) Surface.code.body (D.distance + 2) rho E := by
  unfold commPointwiseSym
  refine derivWF_commutesOfPointwise ?child ?fd
  case child =>
    show DerivWF (SFormula.Deriv.allNatLtIntroBounded _ _ _) _ _ _ _
    refine derivWF_allNatLtIntroBounded _ _ ⟨nQubits D.distance, scn_eval _ _ _ _ _, ?_⟩
    intro x hx
    refine ⟨?_, hCtx⟩
    have hA : ∃ v, (STerm.stabAt (rowK2 D) SFormula.boundNat).eval Surface.code.body
        (D.distance + 2) (Env.cons x rho) E = some v := by
      obtain ⟨sa, hsa, htot⟩ := recCall_total_symbolicDK_all D.index (D.distance + 2)
        (by simp only [OddSurfaceDistance.distance, oddDistance]; omega) (Env.cons x rho)
        (dT := dX2 D) (kT := kX2)
        (fun f' => by simp [dX2, distAtBoundIdx2, SC.closed, Term.eval, Term.lift,
          OddSurfaceDistance.distance, oddDistance]) (.var _)
      refine sterm_eval_stabAt (sv := sa) (qv := x) ?_ ?_ (htot x)
      · rw [rowK2_eq]; simpa [SC.closed, STerm.eval] using hsa
      · simp [SFormula.boundNat, SC.closed, STerm.eval, Term.eval, Env.cons]
    refine derivWF_boolCases _ _
      ⟨decide (x % D.distance = 0), by
        simp [logicalXColGuardAt2, Formula.qVar, SC.closed, STerm.eval, Term.instantiateTopNat,
          Term.instantiateNatAt, Term.eval, Env.cons, bind, Option.bind]⟩ ?colT ?colF
    · exact colDispatchOnTrue_WF D
        (entryAtBound_WF D (cw2_WF (derivWF_weakenFresh wEntryF)) (derivWF_hyp _))
        (derivWF_hyp _)
        (rbfAtBound_WF D (cw2_WF (derivWF_weakenFresh wRBFF)) (derivWF_hyp _)
          (by show DerivWF (cast _ SFormula.Deriv.assumption) _ _ _ _
              exact derivWF_cast_type rfl (colGuard2_eq D) _ _ (derivWF_hyp _)))
        (wZbulk x) (wZleft x) hA
    · exact logicalXOffColumnLocalCommutes_WF D (rowK2 D) (derivWF_hyp _) hA
  case fd =>
    obtain ⟨sa, hsa, htot⟩ := recCall_total_symbolicDK_all D.index (D.distance + 2)
      (by simp only [OddSurfaceDistance.distance, oddDistance]; omega) rho
      (dT := Term.lift 0 (Term.natLit D.distance)) (kT := Term.var ⟨0, by decide⟩)
      (fun f' => by simp [SC.closed, Term.eval, Term.lift,
        OddSurfaceDistance.distance, oddDistance]) (.var _)
    obtain ⟨g, hg⟩ := logicalX_eval_total Surface.code.body (D.distance + 1) D.distance Env.empty
    refine formulaDefined_commutesUpTo (nv := nQubits D.distance) (Av := sa)
      (Bv := fun q => some (g q)) ?_ ?_ ?_ (fun q _ => htot q) StabTotalUpTo.ofTotal
    · simp [SC.closed, STerm.eval, Term.eval, Term.lift]
    · simpa [SC.closed, STerm.eval] using hsa
    · simp only [SC.closed, STerm.eval]
      have hrho : rho = Env.cons (rho ⟨0, by decide⟩) Env.empty := by
        funext i
        match i with
        | ⟨0, _⟩ => rfl
      rw [hrho, Term.eval_weaken_top]
      simpa [logicalXOdd, OddSurfaceDistance.distance, oddDistance] using hg

/-- The arity-1 row recCall stabilizer evaluates at any pure qubit `qT` (the entry is
total).  Supplies the `A`-side of the `anticommutes` `FormulaDefined` in the two-anti cases. -/
theorem recCall1_pure_eval (D : OddSurfaceDistance) (qT : Term 1 .nat)
    (hq : SFormula.PureNatTerm qT) {rho : Env 1} {E : PartialStabilizer} :
    ∃ v, (STerm.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed qT)).eval
      Surface.code.body (D.distance + 2) rho E = some v := by
  obtain ⟨sa, hsa, htot⟩ := recCall_total_symbolicDK_all D.index (D.distance + 2)
    (by simp only [OddSurfaceDistance.distance, oddDistance]; omega) rho (dT := dX1 D) (kT := kX1)
    (fun f' => by simp [dX1, SC.closed, Term.eval, Term.lift, OddSurfaceDistance.distance, oddDistance])
    (.var _)
  obtain ⟨qv, hqv⟩ := SFormula.PureNatTerm.eval_total hq Surface.code.body (D.distance + 2) (rho := rho)
  refine sterm_eval_stabAt (sv := sa) (qv := qv) ?_ ?_ (htot qv)
  · simpa [SC.closed, STerm.eval] using hsa
  · simpa [SC.closed, STerm.eval] using hqv

/-- The lifted-logicalX operator evaluates at any pure qubit `qT`.  Supplies the `B`-side. -/
theorem liftedLX1_pure_eval (D : OddSurfaceDistance) (qT : Term 1 .nat)
    (hq : SFormula.PureNatTerm qT) {rho : Env 1} {E : PartialStabilizer} :
    ∃ v, (STerm.stabAt (liftedLX1 D) (SC.closed qT)).eval
      Surface.code.body (D.distance + 2) rho E = some v := by
  obtain ⟨g, hg⟩ := logicalX_eval_total Surface.code.body (D.distance + 1) D.distance Env.empty
  obtain ⟨qv, hqv⟩ := SFormula.PureNatTerm.eval_total hq Surface.code.body (D.distance + 2) (rho := rho)
  refine sterm_eval_stabAt (sv := fun q => some (g q)) (qv := qv) ?_ ?_ ⟨g qv, rfl⟩
  · simp only [liftedLX1, SC.closed, STerm.eval]
    have hrho : rho = Env.cons (rho ⟨0, by decide⟩) Env.empty := by
      funext i; match i with | ⟨0, _⟩ => rfl
    rw [hrho, Term.eval_weaken_top]
    simpa [logicalXOdd, OddSurfaceDistance.distance, oddDistance] using hg
  · simpa [SC.closed, STerm.eval] using hqv

/-- WF of `classABulkZPinAt` (the pin: col ∧ band ∧ c=0 ⟹ q=q0 ∨ q=q1).  Pure
`allNatLtElim`/`applyNatBoundNatBeta`/`mp` tree — `comm_deriv_wf` walks it. -/
theorem classABulkZPinAt_WF (D : OddSurfaceDistance) {Δ : List (SFormula 2)}
    {hW : SFormula.Deriv Δ (classABulkZPinF D).weaken}
    {hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nQ1 D).weaken)}
    {hcol : SFormula.Deriv Δ (colGuardRaw2 D)}
    {hband : SFormula.Deriv Δ
      (.eqBool (SC.closed (baseBulkBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.b true))}
    {hcz : SFormula.Deriv Δ (cZero2 D true)}
    {fuel : Nat} {rho : Env 2} {E : PartialStabilizer}
    (wW : DerivWF hW Surface.code.body fuel rho E) (wq : DerivWF hq Surface.code.body fuel rho E)
    (wcol : DerivWF hcol Surface.code.body fuel rho E) (wband : DerivWF hband Surface.code.body fuel rho E)
    (wcz : DerivWF hcz Surface.code.body fuel rho E) :
    DerivWF (classABulkZPinAt D hW hq hcol hband hcz) Surface.code.body fuel rho E := by
  unfold classABulkZPinAt
  comm_deriv_wf

/-- WF of `commTwoAntiA` — two-anticommutation class (a): the bulk-Z row stabilizer
anticommutes with logicalX at exactly the two column-0 qubits `qa0`/`qa1`, so the two
anticommutations cancel and they commute.  `commutesOfTwoAnti`: anti at qa0/qa1, commute
elsewhere (wrest).  Reuses `antiZAtA_WF`/`lxPureEntryX_WF` + the `commPointwiseSym` wrest recipe. -/
theorem commTwoAntiA_WF (D : OddSurfaceDistance) {Γ : List (SFormula 1)}
    {hBulk : SFormula.Deriv Γ (gBulk1 D true)} {hCZ : SFormula.Deriv Γ (cZero1 D true)}
    {hKind : SFormula.Deriv Γ (gKind1 D true)} {hClassA : SFormula.Deriv Γ (classAPackF D)}
    {hCol : SFormula.Deriv Γ (qaColGuardF D)} {hPin : SFormula.Deriv Γ (classABulkZPinF D)}
    {hEntryF : SFormula.Deriv Γ (entryFlatF1 D)} {hRBFF : SFormula.Deriv Γ (rightBandFalseF D)}
    {hEntry0 : SFormula.Deriv Γ
      (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed (qa0 D)))
        (SC.closed (baseLeafTreeTA (dX1 D) kX1 (qa0 D))))}
    {hEntry1 : SFormula.Deriv Γ
      (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed (qa1 D)))
        (SC.closed (baseLeafTreeTA (dX1 D) kX1 (qa1 D))))}
    {rho : Env 1} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk Surface.code.body (D.distance + 2) rho E)
    (wCZ : DerivWF hCZ Surface.code.body (D.distance + 2) rho E)
    (wKind : DerivWF hKind Surface.code.body (D.distance + 2) rho E)
    (wClassA : DerivWF hClassA Surface.code.body (D.distance + 2) rho E)
    (wCol : DerivWF hCol Surface.code.body (D.distance + 2) rho E)
    (wPin : DerivWF hPin Surface.code.body (D.distance + 2) rho E)
    (wEntryF : DerivWF hEntryF Surface.code.body (D.distance + 2) rho E)
    (wRBFF : DerivWF hRBFF Surface.code.body (D.distance + 2) rho E)
    (wEntry0 : DerivWF hEntry0 Surface.code.body (D.distance + 2) rho E)
    (wEntry1 : DerivWF hEntry1 Surface.code.body (D.distance + 2) rho E)
    (hCtx : SFormula.ContextHolds Surface.code.body (D.distance + 2) rho E Γ) :
    DerivWF (commTwoAntiA D hBulk hCZ hKind hClassA hCol hPin hEntryF hRBFF hEntry0 hEntry1)
      Surface.code.body (D.distance + 2) rho E := by
  unfold commTwoAntiA
  refine derivWF_commutesOfTwoAnti ?h0 ?h1 ?hne ?ha0 ?ha1 ?hr
  case h0 => comm_deriv_wf  -- hLt0 : andElim chain over mp-pack — closes
  case h1 => comm_deriv_wf  -- hLt1 : ditto
  -- hne : notIntro ⟨FormulaDefined (eqNat qa0 qa1), notElim (eqNatBoolTrue .assumption) (eqBoolFalseNotTrue (cw1 hNe))⟩.
  --   fd = formulaDefined_eqNat ⟨_, qa0 eval⟩ ⟨_, qa1 eval⟩ via PureNatTerm.eval_total (qa0_pure/qa1_pure);
  --   child via comm_deriv_wf (cw1_WF + assumption).
  case hne =>
    obtain ⟨v0, hv0⟩ := SFormula.PureNatTerm.eval_total (qa0_pure D) Surface.code.body (D.distance + 2) (rho := rho)
    obtain ⟨v1, hv1⟩ := SFormula.PureNatTerm.eval_total (qa1_pure D) Surface.code.body (D.distance + 2) (rho := rho)
    refine derivWF_notIntro (formulaDefined_eqNat ⟨v0, by simpa [SC.closed, STerm.eval] using hv0⟩
      ⟨v1, by simpa [SC.closed, STerm.eval] using hv1⟩) ?_
    comm_deriv_wf
  -- ha0/ha1 : derivWF_anticommutesTransport _ _ _ _ _ (antiZAtA_WF D (qa0 D) (qa0_pure D) wEntry0 wBulk wBand0 wKind)
  --   (lxPureEntryX_WF D (qa0 D) (qa0_pure D) (derivWF_andElimLeft' wCol)) (derivWF_pauliAnticommutesLit Z X)
  --   (formulaDefined_eqBool (sterm_eval_anticommutes <recCall@qa0 eval> <liftedLX1@qa0 eval>) (sterm_eval_b _)).
  --   recCall@qa0 = recCall_total_symbolicDK_all + sterm_eval_stabAt (qv := qa0 eval); liftedLX1@qa0 = logicalX_eval_total + weaken bridge.
  --   wBand0 = derivWF_andElimLeft' of the mp-pack (same chain as hne's hNe).
  case ha0 =>
    exact derivWF_anticommutesTransport _ _ _ _ _
      (antiZAtA_WF D (qa0 D) (qa0_pure D) wEntry0 wBulk (by comm_deriv_wf) wKind)
      (lxPureEntryX_WF D (qa0 D) (qa0_pure D) (derivWF_andElimLeft' wCol))
      (derivWF_pauliAnticommutesLit _ _)
      (formulaDefined_eqBool (sterm_eval_anticommutes (recCall1_pure_eval D (qa0 D) (qa0_pure D))
        (sterm_eval_p _)) (sterm_eval_b _))
  case ha1 =>
    exact derivWF_anticommutesTransport _ _ _ _ _
      (antiZAtA_WF D (qa1 D) (qa1_pure D) wEntry1 wBulk (by comm_deriv_wf) wKind)
      (lxPureEntryX_WF D (qa1 D) (qa1_pure D) (derivWF_andElimRight' wCol))
      (derivWF_pauliAnticommutesLit _ _)
      (formulaDefined_eqBool (sterm_eval_anticommutes (recCall1_pure_eval D (qa1 D) (qa1_pure D))
        (sterm_eval_p _)) (sterm_eval_b _))
  -- hr (wrest) : derivWF_allNatLtIntroBounded (commPointwiseSym recipe) + derivWF_impIntro×2 (exclusions via
  --   formulaDefined_not (formulaDefined_eqNat ...) per SurfaceCodeLevelDefined:1077) + boolCases +
  --   colDispatchOnTrue_WF with INLINE hZbulk (classABulkZPinAt + derivWF_orElim + botElim/notElim + cw1_WF)
  --   and hZleft (eqBoolContra_WF). Uses cw4_WF (2 extra exclusion hyps). hA = same recCall recipe as commPointwiseSym.
  case hr =>
    refine derivWF_allNatLtIntroBounded _ _
      ⟨nQubits D.distance, scn_eval _ _ _ _ _, fun x hx => ⟨?_, hCtx⟩⟩
    obtain ⟨vq0, hvq0⟩ := SFormula.PureNatTerm.eval_total (qa0_pure D) Surface.code.body
      (D.distance + 2) (rho := rho)
    obtain ⟨vq1, hvq1⟩ := SFormula.PureNatTerm.eval_total (qa1_pure D) Surface.code.body
      (D.distance + 2) (rho := rho)
    refine derivWF_impIntro (formulaDefined_not (formulaDefined_eqNat
      ⟨x, by simp [SFormula.boundNat, SC.closed, STerm.eval, Term.eval, Env.cons]⟩
      (by rw [sterm_eval_weaken_top]; exact ⟨vq0, by simpa [SC.closed, STerm.eval] using hvq0⟩))) ?_
    refine derivWF_impIntro (formulaDefined_not (formulaDefined_eqNat
      ⟨x, by simp [SFormula.boundNat, SC.closed, STerm.eval, Term.eval, Env.cons]⟩
      (by rw [sterm_eval_weaken_top]; exact ⟨vq1, by simpa [SC.closed, STerm.eval] using hvq1⟩))) ?_
    have hA : ∃ v, (STerm.stabAt (rowK2 D) SFormula.boundNat).eval Surface.code.body
        (D.distance + 2) (Env.cons x rho) E = some v := by
      obtain ⟨sa, hsa, htot⟩ := recCall_total_symbolicDK_all D.index (D.distance + 2)
        (by simp only [OddSurfaceDistance.distance, oddDistance]; omega) (Env.cons x rho)
        (dT := dX2 D) (kT := kX2)
        (fun f' => by simp [dX2, distAtBoundIdx2, SC.closed, Term.eval, Term.lift,
          OddSurfaceDistance.distance, oddDistance]) (.var _)
      refine sterm_eval_stabAt (sv := sa) (qv := x) ?_ ?_ (htot x)
      · rw [rowK2_eq]; simpa [SC.closed, STerm.eval] using hsa
      · simp [SFormula.boundNat, SC.closed, STerm.eval, Term.eval, Env.cons]
    refine derivWF_boolCases _ _
      ⟨decide (x % D.distance = 0), by
        simp [logicalXColGuardAt2, Formula.qVar, SC.closed, STerm.eval, Term.instantiateTopNat,
          Term.instantiateNatAt, Term.eval, Env.cons, bind, Option.bind]⟩ ?colT ?colF
    · -- colT branch: the def's `set ΔT`/`rw` leave a `let` + `Eq.mpr` wrapper; `simp only
      -- [eq_mpr_eq_cast, cast_eq]` strips the let and the reflexive `hΔT` casts, after which
      -- `colDispatchOnTrue_WF` unifies.  The remaining `colGuard2_eq` casts use `derivWF_cast_type`.
      simp only [eq_mpr_eq_cast, cast_eq]
      refine colDispatchOnTrue_WF D ?wEntry ?wColT ?wRBF ?wZbulk ?wZleft hA
      · exact entryAtBound_WF D (cw4_WF (derivWF_weakenFresh wEntryF)) (derivWF_hyp _)
      · exact derivWF_hyp _
      · refine rbfAtBound_WF D (cw4_WF (derivWF_weakenFresh wRBFF)) (derivWF_hyp _) ?_
        exact derivWF_cast_type rfl (colGuard2_eq D) _ _ (derivWF_hyp _)
      · -- hZbulk: pin (col ∧ band ∧ c=0) ⟹ q=q0 ∨ q=q1, each disjunct ⊥ the exclusions.
        intro Δ' lift liftWF he whe hc whc hbu whbu hba whba hki whki
        exact derivWF_orElim
          (classABulkZPinAt_WF D (liftWF (cw4_WF (derivWF_weakenFresh wPin)))
            (liftWF (derivWF_hyp _)) (derivWF_cast_type rfl (colGuard2_eq D) _ _ whc) whba
            (liftWF (cw4_WF (derivWF_weakenFresh wCZ))))
          (derivWF_botElim (derivWF_notElim (derivWF_hyp _) (cw1_WF (liftWF (derivWF_hyp _)))))
          (derivWF_botElim (derivWF_notElim (derivWF_hyp _) (cw1_WF (liftWF (derivWF_hyp _)))))
      · -- hZleft: class (a) has bulk TRUE, contradicting the cascade's bulk FALSE.
        intro Δ' lift liftWF he whe hc whc hbu whbu htc whtc hrc whrc hlc whlc hlb whlb
        exact eqBoolContra_WF _ (liftWF (cw4_WF (derivWF_weakenFresh wBulk))) whbu
    · exact logicalXOffColumnLocalCommutes_WF D (rowK2 D) (derivWF_hyp _) hA

/-- WF of `antiZAtB` (class-(b) left-`Z` entry = Z), mirror of `antiZAtA_WF` with the
left-`Z` cascade (`baseLeafLeftZ`) instead of the bulk-`Z` (`baseLeafZ`). -/
theorem antiZAtB_WF (D : OddSurfaceDistance) {Γ : List (SFormula 1)} (qT : Term 1 .nat)
    (hqpure : SFormula.PureNatTerm qT)
    {hEntry : SFormula.Deriv Γ
      (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed qT))
        (SC.closed (baseLeafTreeTA (dX1 D) kX1 qT)))}
    {hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dX1 D) kX1)) (SC.b false))}
    {hTopC : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dX1 D) kX1)) (SC.b false))}
    {hRightC : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dX1 D) kX1)) (SC.b false))}
    {hLeftC : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA (dX1 D) kX1)) (SC.b true))}
    {hLeftB : SFormula.Deriv Γ (.eqBool (SC.closed (leftBandGuardTA (dX1 D) kX1 qT)) (SC.b true))}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env 1} {E : PartialStabilizer}
    (wEntry : DerivWF hEntry cb fuel rho E) (wBulk : DerivWF hBulk cb fuel rho E)
    (wTopC : DerivWF hTopC cb fuel rho E) (wRightC : DerivWF hRightC cb fuel rho E)
    (wLeftC : DerivWF hLeftC cb fuel rho E) (wLeftB : DerivWF hLeftB cb fuel rho E) :
    DerivWF (antiZAtB D qT hEntry hBulk hTopC hRightC hLeftC hLeftB) cb fuel rho E := by
  have hd : SFormula.PureNatTerm (dX1 D) := dX1_pure D
  have hk : SFormula.PureNatTerm kX1 := SFormula.PureNatTerm.var _
  unfold antiZAtB baseLeafLeftZ
  comm_deriv_wf

/-- WF of `classBLeftZPinAt` (left-`Z` pin: col ∧ leftBand ⟹ q=q0 ∨ q=q1), mirror of
`classABulkZPinAt_WF` — pure `allNatLtElim`/`applyNatBoundNatBeta`/`mp` tree. -/
theorem classBLeftZPinAt_WF (D : OddSurfaceDistance) {Δ : List (SFormula 2)}
    {hW : SFormula.Deriv Δ (classBLeftZPinF D).weaken}
    {hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nQ1 D).weaken)}
    {hcol : SFormula.Deriv Δ (colGuardRaw2 D)}
    {hband : SFormula.Deriv Δ
      (.eqBool (SC.closed (leftBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.b true))}
    {fuel : Nat} {rho : Env 2} {E : PartialStabilizer}
    (wW : DerivWF hW Surface.code.body fuel rho E) (wq : DerivWF hq Surface.code.body fuel rho E)
    (wcol : DerivWF hcol Surface.code.body fuel rho E) (wband : DerivWF hband Surface.code.body fuel rho E) :
    DerivWF (classBLeftZPinAt D hW hq hcol hband) Surface.code.body fuel rho E := by
  unfold classBLeftZPinAt
  comm_deriv_wf

/-- WF of `commTwoAntiB` — class-(b) left-`Z` boundary two-anticommutation.  Mirror of
`commTwoAntiA_WF` with `antiZAtB`/`qb0`/`qb1`/`classBLeftZPinAt`; the geometric mirror SWAPS the
colT dispatch handlers — hZbulk uses `eqBoolContra` (class-b is bulk-FALSE vs dispatch bulk-TRUE),
hZleft uses the left-`Z` pin (`classBLeftZPinAt`). -/
theorem commTwoAntiB_WF (D : OddSurfaceDistance) {Γ : List (SFormula 1)}
    {hBulk : SFormula.Deriv Γ (gBulk1 D false)} {hTopC : SFormula.Deriv Γ (gTopC1 D false)}
    {hRightC : SFormula.Deriv Γ (gRightC1 D false)} {hLeftC : SFormula.Deriv Γ (gLeftC1 D true)}
    {hClassB : SFormula.Deriv Γ (classBPackF D)} {hCol : SFormula.Deriv Γ (qbColGuardF D)}
    {hPin : SFormula.Deriv Γ (classBLeftZPinF D)}
    {hEntryF : SFormula.Deriv Γ (entryFlatF1 D)} {hRBFF : SFormula.Deriv Γ (rightBandFalseF D)}
    {hEntry0 : SFormula.Deriv Γ
      (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed (qb0 D)))
        (SC.closed (baseLeafTreeTA (dX1 D) kX1 (qb0 D))))}
    {hEntry1 : SFormula.Deriv Γ
      (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed (qb1 D)))
        (SC.closed (baseLeafTreeTA (dX1 D) kX1 (qb1 D))))}
    {rho : Env 1} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk Surface.code.body (D.distance + 2) rho E)
    (wTopC : DerivWF hTopC Surface.code.body (D.distance + 2) rho E)
    (wRightC : DerivWF hRightC Surface.code.body (D.distance + 2) rho E)
    (wLeftC : DerivWF hLeftC Surface.code.body (D.distance + 2) rho E)
    (wClassB : DerivWF hClassB Surface.code.body (D.distance + 2) rho E)
    (wCol : DerivWF hCol Surface.code.body (D.distance + 2) rho E)
    (wPin : DerivWF hPin Surface.code.body (D.distance + 2) rho E)
    (wEntryF : DerivWF hEntryF Surface.code.body (D.distance + 2) rho E)
    (wRBFF : DerivWF hRBFF Surface.code.body (D.distance + 2) rho E)
    (wEntry0 : DerivWF hEntry0 Surface.code.body (D.distance + 2) rho E)
    (wEntry1 : DerivWF hEntry1 Surface.code.body (D.distance + 2) rho E)
    (hCtx : SFormula.ContextHolds Surface.code.body (D.distance + 2) rho E Γ) :
    DerivWF (commTwoAntiB D hBulk hTopC hRightC hLeftC hClassB hCol hPin hEntryF hRBFF hEntry0 hEntry1)
      Surface.code.body (D.distance + 2) rho E := by
  unfold commTwoAntiB
  refine derivWF_commutesOfTwoAnti ?h0 ?h1 ?hne ?ha0 ?ha1 ?hr
  case h0 => comm_deriv_wf
  case h1 => comm_deriv_wf
  case hne =>
    obtain ⟨v0, hv0⟩ := SFormula.PureNatTerm.eval_total (qb0_pure D) Surface.code.body (D.distance + 2) (rho := rho)
    obtain ⟨v1, hv1⟩ := SFormula.PureNatTerm.eval_total (qb1_pure D) Surface.code.body (D.distance + 2) (rho := rho)
    refine derivWF_notIntro (formulaDefined_eqNat ⟨v0, by simpa [SC.closed, STerm.eval] using hv0⟩
      ⟨v1, by simpa [SC.closed, STerm.eval] using hv1⟩) ?_
    comm_deriv_wf
  case ha0 =>
    exact derivWF_anticommutesTransport _ _ _ _ _
      (antiZAtB_WF D (qb0 D) (qb0_pure D) wEntry0 wBulk wTopC wRightC wLeftC (by comm_deriv_wf))
      (lxPureEntryX_WF D (qb0 D) (qb0_pure D) (derivWF_andElimLeft' wCol))
      (derivWF_pauliAnticommutesLit _ _)
      (formulaDefined_eqBool (sterm_eval_anticommutes (recCall1_pure_eval D (qb0 D) (qb0_pure D))
        (sterm_eval_p _)) (sterm_eval_b _))
  case ha1 =>
    exact derivWF_anticommutesTransport _ _ _ _ _
      (antiZAtB_WF D (qb1 D) (qb1_pure D) wEntry1 wBulk wTopC wRightC wLeftC (by comm_deriv_wf))
      (lxPureEntryX_WF D (qb1 D) (qb1_pure D) (derivWF_andElimRight' wCol))
      (derivWF_pauliAnticommutesLit _ _)
      (formulaDefined_eqBool (sterm_eval_anticommutes (recCall1_pure_eval D (qb1 D) (qb1_pure D))
        (sterm_eval_p _)) (sterm_eval_b _))
  case hr =>
    refine derivWF_allNatLtIntroBounded _ _
      ⟨nQubits D.distance, scn_eval _ _ _ _ _, fun x hx => ⟨?_, hCtx⟩⟩
    obtain ⟨vq0, hvq0⟩ := SFormula.PureNatTerm.eval_total (qb0_pure D) Surface.code.body
      (D.distance + 2) (rho := rho)
    obtain ⟨vq1, hvq1⟩ := SFormula.PureNatTerm.eval_total (qb1_pure D) Surface.code.body
      (D.distance + 2) (rho := rho)
    refine derivWF_impIntro (formulaDefined_not (formulaDefined_eqNat
      ⟨x, by simp [SFormula.boundNat, SC.closed, STerm.eval, Term.eval, Env.cons]⟩
      (by rw [sterm_eval_weaken_top]; exact ⟨vq0, by simpa [SC.closed, STerm.eval] using hvq0⟩))) ?_
    refine derivWF_impIntro (formulaDefined_not (formulaDefined_eqNat
      ⟨x, by simp [SFormula.boundNat, SC.closed, STerm.eval, Term.eval, Env.cons]⟩
      (by rw [sterm_eval_weaken_top]; exact ⟨vq1, by simpa [SC.closed, STerm.eval] using hvq1⟩))) ?_
    have hA : ∃ v, (STerm.stabAt (rowK2 D) SFormula.boundNat).eval Surface.code.body
        (D.distance + 2) (Env.cons x rho) E = some v := by
      obtain ⟨sa, hsa, htot⟩ := recCall_total_symbolicDK_all D.index (D.distance + 2)
        (by simp only [OddSurfaceDistance.distance, oddDistance]; omega) (Env.cons x rho)
        (dT := dX2 D) (kT := kX2)
        (fun f' => by simp [dX2, distAtBoundIdx2, SC.closed, Term.eval, Term.lift,
          OddSurfaceDistance.distance, oddDistance]) (.var _)
      refine sterm_eval_stabAt (sv := sa) (qv := x) ?_ ?_ (htot x)
      · rw [rowK2_eq]; simpa [SC.closed, STerm.eval] using hsa
      · simp [SFormula.boundNat, SC.closed, STerm.eval, Term.eval, Env.cons]
    refine derivWF_boolCases _ _
      ⟨decide (x % D.distance = 0), by
        simp [logicalXColGuardAt2, Formula.qVar, SC.closed, STerm.eval, Term.instantiateTopNat,
          Term.instantiateNatAt, Term.eval, Env.cons, bind, Option.bind]⟩ ?colT ?colF
    · simp only [eq_mpr_eq_cast, cast_eq]
      refine colDispatchOnTrue_WF D ?wEntry ?wColT ?wRBF ?wZbulk ?wZleft hA
      · exact entryAtBound_WF D (cw4_WF (derivWF_weakenFresh wEntryF)) (derivWF_hyp _)
      · exact derivWF_hyp _
      · refine rbfAtBound_WF D (cw4_WF (derivWF_weakenFresh wRBFF)) (derivWF_hyp _) ?_
        exact derivWF_cast_type rfl (colGuard2_eq D) _ _ (derivWF_hyp _)
      · -- hZbulk: class (b) has bulk FALSE, contradicting the dispatch's bulk TRUE.
        intro Δ' lift liftWF he whe hc whc hbu whbu hba whba hki whki
        exact eqBoolContra_WF _ whbu (liftWF (cw4_WF (derivWF_weakenFresh wBulk)))
      · -- hZleft: left-Z pin (col ∧ leftBand) ⟹ q=q0 ∨ q=q1, each disjunct ⊥ the exclusions.
        intro Δ' lift liftWF he whe hc whc hbu whbu htc whtc hrc whrc hlc whlc hlb whlb
        exact derivWF_orElim
          (classBLeftZPinAt_WF D (liftWF (cw4_WF (derivWF_weakenFresh wPin)))
            (liftWF (derivWF_hyp _)) (derivWF_cast_type rfl (colGuard2_eq D) _ _ whc) whlb)
          (derivWF_botElim (derivWF_notElim (derivWF_hyp _) (cw1_WF (liftWF (derivWF_hyp _)))))
          (derivWF_botElim (derivWF_notElim (derivWF_hyp _) (cw1_WF (liftWF (derivWF_hyp _)))))
    · exact logicalXOffColumnLocalCommutes_WF D (rowK2 D) (derivWF_hyp _) hA

/-! ## Z-mirror leaf helper WFs (X/Z dual of the class-(a)/(b) helpers) -/

/-- WF of `antiXAtA` (class-(a) [Z] bulk-`X` entry = X), X/Z dual of `antiZAtA_WF`. -/
theorem antiXAtA_WF (D : OddSurfaceDistance) {Γ : List (SFormula 1)} (qT : Term 1 .nat)
    (hqpure : SFormula.PureNatTerm qT)
    {hEntry : SFormula.Deriv Γ
      (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed qT))
        (SC.closed (baseLeafTreeTA (dX1 D) kX1 qT)))}
    {hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dX1 D) kX1)) (SC.b true))}
    {hBand : SFormula.Deriv Γ (.eqBool (SC.closed (baseBulkBandGuardTA (dX1 D) kX1 qT)) (SC.b true))}
    {hKind : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dX1 D) kX1)) (SC.b false))}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env 1} {E : PartialStabilizer}
    (wEntry : DerivWF hEntry cb fuel rho E) (wBulk : DerivWF hBulk cb fuel rho E)
    (wBand : DerivWF hBand cb fuel rho E) (wKind : DerivWF hKind cb fuel rho E) :
    DerivWF (antiXAtA D qT hEntry hBulk hBand hKind) cb fuel rho E := by
  have hd : SFormula.PureNatTerm (dX1 D) := dX1_pure D
  have hk : SFormula.PureNatTerm kX1 := SFormula.PureNatTerm.var _
  unfold antiXAtA baseLeafBulkX
  comm_deriv_wf

/-- WF of `antiXAtB` (class-(b) [Z] top-`X` entry = X), X/Z dual of `antiZAtB_WF`. -/
theorem antiXAtB_WF (D : OddSurfaceDistance) {Γ : List (SFormula 1)} (qT : Term 1 .nat)
    (hqpure : SFormula.PureNatTerm qT)
    {hEntry : SFormula.Deriv Γ
      (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed qT))
        (SC.closed (baseLeafTreeTA (dX1 D) kX1 qT)))}
    {hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dX1 D) kX1)) (SC.b false))}
    {hTopC : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dX1 D) kX1)) (SC.b true))}
    {hTopB : SFormula.Deriv Γ (.eqBool (SC.closed (topBandGuardTA (dX1 D) kX1 qT)) (SC.b true))}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env 1} {E : PartialStabilizer}
    (wEntry : DerivWF hEntry cb fuel rho E) (wBulk : DerivWF hBulk cb fuel rho E)
    (wTopC : DerivWF hTopC cb fuel rho E) (wTopB : DerivWF hTopB cb fuel rho E) :
    DerivWF (antiXAtB D qT hEntry hBulk hTopC hTopB) cb fuel rho E := by
  have hd : SFormula.PureNatTerm (dX1 D) := dX1_pure D
  have hk : SFormula.PureNatTerm kX1 := SFormula.PureNatTerm.var _
  unfold antiXAtB baseLeafTopX
  comm_deriv_wf

/-- WF of `classZABulkXPinAt`, X/Z dual of `classABulkZPinAt_WF`. -/
theorem classZABulkXPinAt_WF (D : OddSurfaceDistance) {Δ : List (SFormula 2)}
    {hW : SFormula.Deriv Δ (classZABulkXPinF D).weaken}
    {hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nQ1 D).weaken)}
    {hrow : SFormula.Deriv Δ (rowGuardRaw2 D)}
    {hband : SFormula.Deriv Δ
      (.eqBool (SC.closed (baseBulkBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.b true))}
    {hrz : SFormula.Deriv Δ (gRZero2 D true)}
    {fuel : Nat} {rho : Env 2} {E : PartialStabilizer}
    (wW : DerivWF hW Surface.code.body fuel rho E) (wq : DerivWF hq Surface.code.body fuel rho E)
    (wrow : DerivWF hrow Surface.code.body fuel rho E) (wband : DerivWF hband Surface.code.body fuel rho E)
    (wrz : DerivWF hrz Surface.code.body fuel rho E) :
    DerivWF (classZABulkXPinAt D hW hq hrow hband hrz) Surface.code.body fuel rho E := by
  unfold classZABulkXPinAt
  comm_deriv_wf

/-- WF of `classZBTopXPinAt`, X/Z dual of `classBLeftZPinAt_WF`. -/
theorem classZBTopXPinAt_WF (D : OddSurfaceDistance) {Δ : List (SFormula 2)}
    {hW : SFormula.Deriv Δ (classZBTopXPinF D).weaken}
    {hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nQ1 D).weaken)}
    {hrow : SFormula.Deriv Δ (rowGuardRaw2 D)}
    {hband : SFormula.Deriv Δ
      (.eqBool (SC.closed (topBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.b true))}
    {fuel : Nat} {rho : Env 2} {E : PartialStabilizer}
    (wW : DerivWF hW Surface.code.body fuel rho E) (wq : DerivWF hq Surface.code.body fuel rho E)
    (wrow : DerivWF hrow Surface.code.body fuel rho E) (wband : DerivWF hband Surface.code.body fuel rho E) :
    DerivWF (classZBTopXPinAt D hW hq hrow hband) Surface.code.body fuel rho E := by
  unfold classZBTopXPinAt
  comm_deriv_wf

/-- WF of `bbfAtBound` (bottom-band-false at bound), X/Z dual of `rbfAtBound_WF`. -/
theorem bbfAtBound_WF (D : OddSurfaceDistance) {Δ : List (SFormula 2)}
    {hW : SFormula.Deriv Δ (bottomBandFalseF D).weaken}
    {hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nQ1 D).weaken)}
    {hrow : SFormula.Deriv Δ (rowGuardRaw2 D)}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env 2} {E : PartialStabilizer}
    (wW : DerivWF hW cb fuel rho E) (wq : DerivWF hq cb fuel rho E)
    (wrow : DerivWF hrow cb fuel rho E) :
    DerivWF (bbfAtBound D hW hq hrow) cb fuel rho E := by
  unfold bbfAtBound
  exact derivWF_mp (derivWF_applyNatBoundNatBeta _ (derivWF_allNatLtElim _ _ _ wW wq)) wrow

/-- WF of `antiZZ` / `antiZI` (pure `pauliAnticommutesLit` leaves), Z dual of `antiXX_WF`. -/
theorem antiZZ_WF {Δ : List (SFormula 2)} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env 2} {E : PartialStabilizer} :
    DerivWF (antiZZ (Δ := Δ)) cb fuel rho E := by
  unfold antiZZ; exact derivWF_pauliAnticommutesLit _ _

theorem antiZI_WF {Δ : List (SFormula 2)} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env 2} {E : PartialStabilizer} :
    DerivWF (antiZI (Δ := Δ)) cb fuel rho E := by
  unfold antiZI; exact derivWF_pauliAnticommutesLit _ _

/-- WF of `baseLeafRightZ` — pure `eqPauliTrans`/`pauliIteSelect` tree (Z dual of right-I). -/
theorem baseLeafRightZ_WF {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false))}
    {hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false))}
    {hRightClass : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b true))}
    {hRightBand : SFormula.Deriv Γ (.eqBool (SC.closed (rightBandGuardTA dT kT qT)) (SC.b true))}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wRightBand : DerivWF hRightBand cb fuel rho E) :
    DerivWF (baseLeafRightZ dT kT qT hBulk hTopClass hRightClass hRightBand) cb fuel rho E := by
  unfold baseLeafRightZ; flat_deriv_wf

/-- WF of `baseLeafLeftZ` — pure `eqPauliTrans`/`pauliIteSelect` tree (Z dual of left-I). -/
theorem baseLeafLeftZ_WF {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    {hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false))}
    {hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false))}
    {hRightClass : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b false))}
    {hLeftClass : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA dT kT)) (SC.b true))}
    {hLeftBand : SFormula.Deriv Γ (.eqBool (SC.closed (leftBandGuardTA dT kT qT)) (SC.b true))}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wLeftClass : DerivWF hLeftClass cb fuel rho E)
    (wLeftBand : DerivWF hLeftBand cb fuel rho E) :
    DerivWF (baseLeafLeftZ dT kT qT hBulk hTopClass hRightClass hLeftClass hLeftBand) cb fuel rho E := by
  unfold baseLeafLeftZ; flat_deriv_wf

/-- Z dual of `liftedLX2_boundNat_eval`: lifted-`logicalZ` evaluates at `boundNat`
(Z on row 0, I off it — `q / d` not `q % d`). -/
theorem liftedLZ2_boundNat_eval (D : OddSurfaceDistance)
    {fuel : Nat} {rho : Env 2} {E : PartialStabilizer} :
    ∃ v, (STerm.stabAt (liftedLZ2 D) SFormula.boundNat).eval Surface.code.body fuel rho E = some v :=
  ⟨if rho 0 / D.distance = 0 then Pauli.Z else Pauli.I,
    by simp only [liftedLZ2, logicalZOdd, logicalZ, SC.closed, SC.p, OddSurfaceDistance.distance,
          oddDistance, STerm.weaken, STerm.lift, Term.lift, Term.weaken, Term.weakenVar,
          SFormula.boundNat];
       simp [STerm.eval, Term.eval, Formula.qVar, Env.cons, bind, Option.bind,
          Term.lift, Term.weakenVar];
       split <;> rfl⟩

/-- WF of `rowCommFromEntry` — row-0 local commutation from a non-X column entry,
X/Z dual of `colCommFromEntry_WF`. -/
theorem rowCommFromEntry_WF (D : OddSurfaceDistance) (p : Pauli) {Δ : List (SFormula 2)}
    {hEntry : SFormula.Deriv Δ (.eqPauli (.stabAt (rowK2 D) SFormula.boundNat) (SC.p p))}
    {hAnti : SFormula.Deriv Δ (.eqBool (.anticommutes (SC.p Pauli.Z) (SC.p p)) (SC.b false))}
    {hrow : SFormula.Deriv Δ (.eqBool (logicalZRowGuardAt2 D) (SC.b true))}
    {fuel : Nat} {rho : Env 2} {E : PartialStabilizer}
    (wEntry : DerivWF hEntry Surface.code.body fuel rho E)
    (wAnti : DerivWF hAnti Surface.code.body fuel rho E)
    (wrow : DerivWF hrow Surface.code.body fuel rho E)
    (hA : ∃ v, (STerm.stabAt (rowK2 D) SFormula.boundNat).eval Surface.code.body fuel rho E = some v) :
    DerivWF (rowCommFromEntry D p hEntry hAnti hrow) Surface.code.body fuel rho E := by
  unfold rowCommFromEntry
  refine derivWF_localCommutesOfLeftEqNoAntiRight _ _ _ _ wEntry ?noAnti ?fd
  · exact derivWF_eqBoolFalseNotTrue
      (derivWF_anticommutesTransport _ _ _ _ _ (lzOnRowEntryZ_WF D wrow)
        (derivWF_pauliEqLit' _) wAnti
        (formulaDefined_eqBool
          (sterm_eval_anticommutes (liftedLZ2_boundNat_eval D) (sterm_eval_p _)) (sterm_eval_b _)))
  · exact formulaDefined_localCommutesAt hA (liftedLZ2_boundNat_eval D)

/-- WF of `lcFromLeafZ` — Z dual of `lcFromLeaf_WF`. -/
theorem lcFromLeafZ_WF (D : OddSurfaceDistance) (p : Pauli) {Δ : List (SFormula 2)}
    {hEntry : SFormula.Deriv Δ (entryFlat2F D)}
    {hLeaf : SFormula.Deriv Δ
      (.eqPauli (SC.closed (baseLeafTreeTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.p p))}
    {hAnti : SFormula.Deriv Δ (.eqBool (.anticommutes (SC.p Pauli.Z) (SC.p p)) (SC.b false))}
    {hrow : SFormula.Deriv Δ (.eqBool (logicalZRowGuardAt2 D) (SC.b true))}
    {fuel : Nat} {rho : Env 2} {E : PartialStabilizer}
    (wEntry : DerivWF hEntry Surface.code.body fuel rho E)
    (wLeaf : DerivWF hLeaf Surface.code.body fuel rho E)
    (wAnti : DerivWF hAnti Surface.code.body fuel rho E)
    (wrow : DerivWF hrow Surface.code.body fuel rho E)
    (hA : ∃ v, (STerm.stabAt (rowK2 D) SFormula.boundNat).eval Surface.code.body fuel rho E = some v) :
    DerivWF (lcFromLeafZ D p hEntry hLeaf hAnti hrow) Surface.code.body fuel rho E := by
  unfold lcFromLeafZ
  exact rowCommFromEntry_WF D p (derivWF_eqPauliTrans' wEntry wLeaf) wAnti wrow hA

/-- WF of `rowDispatchOnTrue` — the row-0 entry dispatcher, X/Z dual of `colDispatchOnTrue_WF`.
The shared `disp_wf` walks the (same-shape) `boolCases` tree, now resolving the `Z`-leaves; the two
delegated handlers `hXbulk`/`hXtop` are both at depth-3 (`cw3`) — the top boundary is shallow. -/
theorem rowDispatchOnTrue_WF (D : OddSurfaceDistance) {Δ : List (SFormula 2)}
    {hEntry : SFormula.Deriv Δ (entryFlat2F D)}
    {hrow : SFormula.Deriv Δ (.eqBool (logicalZRowGuardAt2 D) (SC.b true))}
    {hBBF : SFormula.Deriv Δ
      (.eqBool (SC.closed (bottomBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.b false))}
    {hXbulk : ∀ (Δ' : List (SFormula 2)),
      (∀ {A : SFormula 2}, SFormula.Deriv Δ A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (entryFlat2F D) →
      SFormula.Deriv Δ' (.eqBool (logicalZRowGuardAt2 D) (SC.b true)) →
      SFormula.Deriv Δ' (gBulk D true) → SFormula.Deriv Δ' (gBand D true) →
      SFormula.Deriv Δ' (gKind D false) → SFormula.Deriv Δ' (lcGoalZ D)}
    {hXtop : ∀ (Δ' : List (SFormula 2)),
      (∀ {A : SFormula 2}, SFormula.Deriv Δ A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (entryFlat2F D) →
      SFormula.Deriv Δ' (.eqBool (logicalZRowGuardAt2 D) (SC.b true)) →
      SFormula.Deriv Δ' (gBulk D false) → SFormula.Deriv Δ' (gTopC D true) →
      SFormula.Deriv Δ' (gTopB D true) → SFormula.Deriv Δ' (lcGoalZ D)}
    {fuel : Nat} {rho : Env 2} {E : PartialStabilizer}
    (wEntry : DerivWF hEntry Surface.code.body fuel rho E)
    (wrow : DerivWF hrow Surface.code.body fuel rho E)
    (wBBF : DerivWF hBBF Surface.code.body fuel rho E)
    (wXbulk : ∀ (Δ' : List (SFormula 2))
        (lift : ∀ {A : SFormula 2}, SFormula.Deriv Δ A → SFormula.Deriv Δ' A),
        (∀ {A : SFormula 2} {h : SFormula.Deriv Δ A},
          DerivWF h Surface.code.body fuel rho E → DerivWF (lift h) Surface.code.body fuel rho E) →
        ∀ {he : SFormula.Deriv Δ' (entryFlat2F D)}, DerivWF he Surface.code.body fuel rho E →
        ∀ {hr : SFormula.Deriv Δ' (.eqBool (logicalZRowGuardAt2 D) (SC.b true))},
          DerivWF hr Surface.code.body fuel rho E →
        ∀ {hbu : SFormula.Deriv Δ' (gBulk D true)}, DerivWF hbu Surface.code.body fuel rho E →
        ∀ {hba : SFormula.Deriv Δ' (gBand D true)}, DerivWF hba Surface.code.body fuel rho E →
        ∀ {hki : SFormula.Deriv Δ' (gKind D false)}, DerivWF hki Surface.code.body fuel rho E →
        DerivWF (hXbulk Δ' lift he hr hbu hba hki) Surface.code.body fuel rho E)
    (wXtop : ∀ (Δ' : List (SFormula 2))
        (lift : ∀ {A : SFormula 2}, SFormula.Deriv Δ A → SFormula.Deriv Δ' A),
        (∀ {A : SFormula 2} {h : SFormula.Deriv Δ A},
          DerivWF h Surface.code.body fuel rho E → DerivWF (lift h) Surface.code.body fuel rho E) →
        ∀ {he : SFormula.Deriv Δ' (entryFlat2F D)}, DerivWF he Surface.code.body fuel rho E →
        ∀ {hr : SFormula.Deriv Δ' (.eqBool (logicalZRowGuardAt2 D) (SC.b true))},
          DerivWF hr Surface.code.body fuel rho E →
        ∀ {hbu : SFormula.Deriv Δ' (gBulk D false)}, DerivWF hbu Surface.code.body fuel rho E →
        ∀ {htc : SFormula.Deriv Δ' (gTopC D true)}, DerivWF htc Surface.code.body fuel rho E →
        ∀ {htb : SFormula.Deriv Δ' (gTopB D true)}, DerivWF htb Surface.code.body fuel rho E →
        DerivWF (hXtop Δ' lift he hr hbu htc htb) Surface.code.body fuel rho E)
    (hA : ∃ v, (STerm.stabAt (rowK2 D) SFormula.boundNat).eval Surface.code.body fuel rho E = some v) :
    DerivWF (rowDispatchOnTrue D hEntry hrow hBBF hXbulk hXtop) Surface.code.body fuel rho E := by
  have hd : SFormula.PureNatTerm (dX2 D) := (distAtBoundIdx2 D).pure
  have hk : SFormula.PureNatTerm kX2 := .var _
  have hq : SFormula.PureNatTerm (Term.var (⟨0, by decide⟩ : Fin 2)) := .var _
  unfold rowDispatchOnTrue
  repeat (any_goals (first
    | exact True.intro
    | refine derivWF_boolCases _ _
        (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?_ ?_
    | refine derivWF_botElim ?_
    | refine derivWF_notElim ?_ ?_
    | refine derivWF_eqBoolFalseNotTrue ?_
    | refine lcFromLeafZ_WF _ _ ?_ ?_ ?_ ?_ ?_
    | refine baseLeafZ_WF _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
    | refine baseLeafBulkI_WF _ _ _ ?_ ?_ ?_ ?_ ?_
    | refine baseLeafTopI_WF _ _ _ ?_ ?_ ?_ ?_ ?_ ?_
    | refine baseLeafRightZ_WF _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    | refine baseLeafRightI_WF _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    | refine baseLeafLeftZ_WF _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    | refine baseLeafLeftI_WF _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    | refine baseLeafBottomI_WF _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    | exact antiZZ_WF
    | exact antiZI_WF
    | refine cw5_WF ?_ | refine cw4_WF ?_ | refine cw3_WF ?_ | refine cw2_WF ?_ | refine cw1_WF ?_
    | assumption))
  · exact wXbulk _ (fun h => cw3 h) (fun w => cw3_WF w) (cw3_WF wEntry) (cw3_WF wrow)
      (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _)
  · exact wXtop _ (fun h => cw3 h) (fun w => cw3_WF w) (cw3_WF wEntry) (cw3_WF wrow)
      (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _)

/-- WF of `commZTwoAntiA` — class-(a) [Z] bulk-`X` two-anticommutation, X/Z dual of
`commTwoAntiA_WF` (`antiXAtA`/`lzPureEntryZ`/`classZABulkXPinAt`/`rowDispatchOnTrue`; row guard,
`q / d` not `q % d`).  Colt handlers: wXbulk = pin, wXtop = eqBoolContra. -/
theorem commZTwoAntiA_WF (D : OddSurfaceDistance) {Γ : List (SFormula 1)}
    {hBulk : SFormula.Deriv Γ (gBulk1 D true)} {hRZ : SFormula.Deriv Γ (gRZero1 D true)}
    {hKind : SFormula.Deriv Γ (gKind1 D false)} {hClassA : SFormula.Deriv Γ (classZAPackF D)}
    {hRow : SFormula.Deriv Γ (qzaRowGuardF D)} {hPin : SFormula.Deriv Γ (classZABulkXPinF D)}
    {hEntryF : SFormula.Deriv Γ (entryFlatF1 D)} {hBBFF : SFormula.Deriv Γ (bottomBandFalseF D)}
    {hEntry0 : SFormula.Deriv Γ
      (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed (qza0 D)))
        (SC.closed (baseLeafTreeTA (dX1 D) kX1 (qza0 D))))}
    {hEntry1 : SFormula.Deriv Γ
      (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed (qza1 D)))
        (SC.closed (baseLeafTreeTA (dX1 D) kX1 (qza1 D))))}
    {rho : Env 1} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk Surface.code.body (D.distance + 2) rho E)
    (wRZ : DerivWF hRZ Surface.code.body (D.distance + 2) rho E)
    (wKind : DerivWF hKind Surface.code.body (D.distance + 2) rho E)
    (wClassA : DerivWF hClassA Surface.code.body (D.distance + 2) rho E)
    (wRow : DerivWF hRow Surface.code.body (D.distance + 2) rho E)
    (wPin : DerivWF hPin Surface.code.body (D.distance + 2) rho E)
    (wEntryF : DerivWF hEntryF Surface.code.body (D.distance + 2) rho E)
    (wBBFF : DerivWF hBBFF Surface.code.body (D.distance + 2) rho E)
    (wEntry0 : DerivWF hEntry0 Surface.code.body (D.distance + 2) rho E)
    (wEntry1 : DerivWF hEntry1 Surface.code.body (D.distance + 2) rho E)
    (hCtx : SFormula.ContextHolds Surface.code.body (D.distance + 2) rho E Γ) :
    DerivWF (commZTwoAntiA D hBulk hRZ hKind hClassA hRow hPin hEntryF hBBFF hEntry0 hEntry1)
      Surface.code.body (D.distance + 2) rho E := by
  unfold commZTwoAntiA
  refine derivWF_commutesOfTwoAnti ?h0 ?h1 ?hne ?ha0 ?ha1 ?hr
  case h0 => comm_deriv_wf
  case h1 => comm_deriv_wf
  case hne =>
    obtain ⟨v0, hv0⟩ := SFormula.PureNatTerm.eval_total (qza0_pure D) Surface.code.body (D.distance + 2) (rho := rho)
    obtain ⟨v1, hv1⟩ := SFormula.PureNatTerm.eval_total (qza1_pure D) Surface.code.body (D.distance + 2) (rho := rho)
    refine derivWF_notIntro (formulaDefined_eqNat ⟨v0, by simpa [SC.closed, STerm.eval] using hv0⟩
      ⟨v1, by simpa [SC.closed, STerm.eval] using hv1⟩) ?_
    comm_deriv_wf
  case ha0 =>
    exact derivWF_anticommutesTransport _ _ _ _ _
      (antiXAtA_WF D (qza0 D) (qza0_pure D) wEntry0 wBulk (by comm_deriv_wf) wKind)
      (lzPureEntryZ_WF D (qza0 D) (qza0_pure D) (derivWF_andElimLeft' wRow))
      (derivWF_pauliAnticommutesLit _ _)
      (formulaDefined_eqBool (sterm_eval_anticommutes (recCall1_pure_eval D (qza0 D) (qza0_pure D))
        (sterm_eval_p _)) (sterm_eval_b _))
  case ha1 =>
    exact derivWF_anticommutesTransport _ _ _ _ _
      (antiXAtA_WF D (qza1 D) (qza1_pure D) wEntry1 wBulk (by comm_deriv_wf) wKind)
      (lzPureEntryZ_WF D (qza1 D) (qza1_pure D) (derivWF_andElimRight' wRow))
      (derivWF_pauliAnticommutesLit _ _)
      (formulaDefined_eqBool (sterm_eval_anticommutes (recCall1_pure_eval D (qza1 D) (qza1_pure D))
        (sterm_eval_p _)) (sterm_eval_b _))
  case hr =>
    refine derivWF_allNatLtIntroBounded _ _
      ⟨nQubits D.distance, scn_eval _ _ _ _ _, fun x hx => ⟨?_, hCtx⟩⟩
    obtain ⟨vq0, hvq0⟩ := SFormula.PureNatTerm.eval_total (qza0_pure D) Surface.code.body
      (D.distance + 2) (rho := rho)
    obtain ⟨vq1, hvq1⟩ := SFormula.PureNatTerm.eval_total (qza1_pure D) Surface.code.body
      (D.distance + 2) (rho := rho)
    refine derivWF_impIntro (formulaDefined_not (formulaDefined_eqNat
      ⟨x, by simp [SFormula.boundNat, SC.closed, STerm.eval, Term.eval, Env.cons]⟩
      (by rw [sterm_eval_weaken_top]; exact ⟨vq0, by simpa [SC.closed, STerm.eval] using hvq0⟩))) ?_
    refine derivWF_impIntro (formulaDefined_not (formulaDefined_eqNat
      ⟨x, by simp [SFormula.boundNat, SC.closed, STerm.eval, Term.eval, Env.cons]⟩
      (by rw [sterm_eval_weaken_top]; exact ⟨vq1, by simpa [SC.closed, STerm.eval] using hvq1⟩))) ?_
    have hA : ∃ v, (STerm.stabAt (rowK2 D) SFormula.boundNat).eval Surface.code.body
        (D.distance + 2) (Env.cons x rho) E = some v := by
      obtain ⟨sa, hsa, htot⟩ := recCall_total_symbolicDK_all D.index (D.distance + 2)
        (by simp only [OddSurfaceDistance.distance, oddDistance]; omega) (Env.cons x rho)
        (dT := dX2 D) (kT := kX2)
        (fun f' => by simp [dX2, distAtBoundIdx2, SC.closed, Term.eval, Term.lift,
          OddSurfaceDistance.distance, oddDistance]) (.var _)
      refine sterm_eval_stabAt (sv := sa) (qv := x) ?_ ?_ (htot x)
      · rw [rowK2_eq]; simpa [SC.closed, STerm.eval] using hsa
      · simp [SFormula.boundNat, SC.closed, STerm.eval, Term.eval, Env.cons]
    refine derivWF_boolCases _ _
      ⟨decide (x / D.distance = 0), by
        simp [logicalZRowGuardAt2, Formula.qVar, SC.closed, STerm.eval, Term.instantiateTopNat,
          Term.instantiateNatAt, Term.eval, Env.cons, bind, Option.bind]⟩ ?rowT ?rowF
    · simp only [eq_mpr_eq_cast, cast_eq]
      refine rowDispatchOnTrue_WF D ?wEntry ?wRowT ?wBBF ?wXbulk ?wXtop hA
      · exact entryAtBound_WF D (cw4_WF (derivWF_weakenFresh wEntryF)) (derivWF_hyp _)
      · exact derivWF_hyp _
      · refine bbfAtBound_WF D (cw4_WF (derivWF_weakenFresh wBBFF)) (derivWF_hyp _) ?_
        exact derivWF_cast_type rfl (rowGuard2_eq D) _ _ (derivWF_hyp _)
      · -- wXbulk: bulk-X pin (row ∧ band ∧ r=0) ⟹ q=q0 ∨ q=q1, each disjunct ⊥ the exclusions.
        intro Δ' lift liftWF he whe hr whr hbu whbu hba whba hki whki
        exact derivWF_orElim
          (classZABulkXPinAt_WF D (liftWF (cw4_WF (derivWF_weakenFresh wPin)))
            (liftWF (derivWF_hyp _)) (derivWF_cast_type rfl (rowGuard2_eq D) _ _ whr) whba
            (liftWF (cw4_WF (derivWF_weakenFresh wRZ))))
          (derivWF_botElim (derivWF_notElim (derivWF_hyp _) (cw1_WF (liftWF (derivWF_hyp _)))))
          (derivWF_botElim (derivWF_notElim (derivWF_hyp _) (cw1_WF (liftWF (derivWF_hyp _)))))
      · -- wXtop: class (a) has bulk TRUE, contradicting the cascade's bulk FALSE.
        intro Δ' lift liftWF he whe hr whr hbu whbu htc whtc htb whtb
        exact eqBoolContra_WF _ (liftWF (cw4_WF (derivWF_weakenFresh wBulk))) whbu
    · exact logicalZOffRowLocalCommutes_WF D (rowK2 D) (derivWF_hyp _) hA

/-- WF of `commZTwoAntiB` — class-(b) [Z] top-`X` boundary two-anticommutation, X/Z dual of
`commTwoAntiB_WF` (`antiXAtB`/`classZBTopXPinAt`).  Colt handlers SWAP: wXbulk = eqBoolContra
(class-b is bulk-FALSE vs dispatch bulk-TRUE), wXtop = top-`X` pin. -/
theorem commZTwoAntiB_WF (D : OddSurfaceDistance) {Γ : List (SFormula 1)}
    {hBulk : SFormula.Deriv Γ (gBulk1 D false)} {hTopC : SFormula.Deriv Γ (gTopC1 D true)}
    {hClassB : SFormula.Deriv Γ (classZBPackF D)} {hRow : SFormula.Deriv Γ (qzbRowGuardF D)}
    {hPin : SFormula.Deriv Γ (classZBTopXPinF D)}
    {hEntryF : SFormula.Deriv Γ (entryFlatF1 D)} {hBBFF : SFormula.Deriv Γ (bottomBandFalseF D)}
    {hEntry0 : SFormula.Deriv Γ
      (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed (qzb0 D)))
        (SC.closed (baseLeafTreeTA (dX1 D) kX1 (qzb0 D))))}
    {hEntry1 : SFormula.Deriv Γ
      (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed (qzb1 D)))
        (SC.closed (baseLeafTreeTA (dX1 D) kX1 (qzb1 D))))}
    {rho : Env 1} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk Surface.code.body (D.distance + 2) rho E)
    (wTopC : DerivWF hTopC Surface.code.body (D.distance + 2) rho E)
    (wClassB : DerivWF hClassB Surface.code.body (D.distance + 2) rho E)
    (wRow : DerivWF hRow Surface.code.body (D.distance + 2) rho E)
    (wPin : DerivWF hPin Surface.code.body (D.distance + 2) rho E)
    (wEntryF : DerivWF hEntryF Surface.code.body (D.distance + 2) rho E)
    (wBBFF : DerivWF hBBFF Surface.code.body (D.distance + 2) rho E)
    (wEntry0 : DerivWF hEntry0 Surface.code.body (D.distance + 2) rho E)
    (wEntry1 : DerivWF hEntry1 Surface.code.body (D.distance + 2) rho E)
    (hCtx : SFormula.ContextHolds Surface.code.body (D.distance + 2) rho E Γ) :
    DerivWF (commZTwoAntiB D hBulk hTopC hClassB hRow hPin hEntryF hBBFF hEntry0 hEntry1)
      Surface.code.body (D.distance + 2) rho E := by
  unfold commZTwoAntiB
  refine derivWF_commutesOfTwoAnti ?h0 ?h1 ?hne ?ha0 ?ha1 ?hr
  case h0 => comm_deriv_wf
  case h1 => comm_deriv_wf
  case hne =>
    obtain ⟨v0, hv0⟩ := SFormula.PureNatTerm.eval_total (qzb0_pure D) Surface.code.body (D.distance + 2) (rho := rho)
    obtain ⟨v1, hv1⟩ := SFormula.PureNatTerm.eval_total (qzb1_pure D) Surface.code.body (D.distance + 2) (rho := rho)
    refine derivWF_notIntro (formulaDefined_eqNat ⟨v0, by simpa [SC.closed, STerm.eval] using hv0⟩
      ⟨v1, by simpa [SC.closed, STerm.eval] using hv1⟩) ?_
    comm_deriv_wf
  case ha0 =>
    exact derivWF_anticommutesTransport _ _ _ _ _
      (antiXAtB_WF D (qzb0 D) (qzb0_pure D) wEntry0 wBulk wTopC (by comm_deriv_wf))
      (lzPureEntryZ_WF D (qzb0 D) (qzb0_pure D) (by comm_deriv_wf))
      (derivWF_pauliAnticommutesLit _ _)
      (formulaDefined_eqBool (sterm_eval_anticommutes (recCall1_pure_eval D (qzb0 D) (qzb0_pure D))
        (sterm_eval_p _)) (sterm_eval_b _))
  case ha1 =>
    exact derivWF_anticommutesTransport _ _ _ _ _
      (antiXAtB_WF D (qzb1 D) (qzb1_pure D) wEntry1 wBulk wTopC (by comm_deriv_wf))
      (lzPureEntryZ_WF D (qzb1 D) (qzb1_pure D) (by comm_deriv_wf))
      (derivWF_pauliAnticommutesLit _ _)
      (formulaDefined_eqBool (sterm_eval_anticommutes (recCall1_pure_eval D (qzb1 D) (qzb1_pure D))
        (sterm_eval_p _)) (sterm_eval_b _))
  case hr =>
    refine derivWF_allNatLtIntroBounded _ _
      ⟨nQubits D.distance, scn_eval _ _ _ _ _, fun x hx => ⟨?_, hCtx⟩⟩
    obtain ⟨vq0, hvq0⟩ := SFormula.PureNatTerm.eval_total (qzb0_pure D) Surface.code.body
      (D.distance + 2) (rho := rho)
    obtain ⟨vq1, hvq1⟩ := SFormula.PureNatTerm.eval_total (qzb1_pure D) Surface.code.body
      (D.distance + 2) (rho := rho)
    refine derivWF_impIntro (formulaDefined_not (formulaDefined_eqNat
      ⟨x, by simp [SFormula.boundNat, SC.closed, STerm.eval, Term.eval, Env.cons]⟩
      (by rw [sterm_eval_weaken_top]; exact ⟨vq0, by simpa [SC.closed, STerm.eval] using hvq0⟩))) ?_
    refine derivWF_impIntro (formulaDefined_not (formulaDefined_eqNat
      ⟨x, by simp [SFormula.boundNat, SC.closed, STerm.eval, Term.eval, Env.cons]⟩
      (by rw [sterm_eval_weaken_top]; exact ⟨vq1, by simpa [SC.closed, STerm.eval] using hvq1⟩))) ?_
    have hA : ∃ v, (STerm.stabAt (rowK2 D) SFormula.boundNat).eval Surface.code.body
        (D.distance + 2) (Env.cons x rho) E = some v := by
      obtain ⟨sa, hsa, htot⟩ := recCall_total_symbolicDK_all D.index (D.distance + 2)
        (by simp only [OddSurfaceDistance.distance, oddDistance]; omega) (Env.cons x rho)
        (dT := dX2 D) (kT := kX2)
        (fun f' => by simp [dX2, distAtBoundIdx2, SC.closed, Term.eval, Term.lift,
          OddSurfaceDistance.distance, oddDistance]) (.var _)
      refine sterm_eval_stabAt (sv := sa) (qv := x) ?_ ?_ (htot x)
      · rw [rowK2_eq]; simpa [SC.closed, STerm.eval] using hsa
      · simp [SFormula.boundNat, SC.closed, STerm.eval, Term.eval, Env.cons]
    refine derivWF_boolCases _ _
      ⟨decide (x / D.distance = 0), by
        simp [logicalZRowGuardAt2, Formula.qVar, SC.closed, STerm.eval, Term.instantiateTopNat,
          Term.instantiateNatAt, Term.eval, Env.cons, bind, Option.bind]⟩ ?rowT ?rowF
    · simp only [eq_mpr_eq_cast, cast_eq]
      refine rowDispatchOnTrue_WF D ?wEntry ?wRowT ?wBBF ?wXbulk ?wXtop hA
      · exact entryAtBound_WF D (cw4_WF (derivWF_weakenFresh wEntryF)) (derivWF_hyp _)
      · exact derivWF_hyp _
      · refine bbfAtBound_WF D (cw4_WF (derivWF_weakenFresh wBBFF)) (derivWF_hyp _) ?_
        exact derivWF_cast_type rfl (rowGuard2_eq D) _ _ (derivWF_hyp _)
      · -- wXbulk: class (b) has bulk FALSE, contradicting the dispatch's bulk TRUE.
        intro Δ' lift liftWF he whe hr whr hbu whbu hba whba hki whki
        exact eqBoolContra_WF _ whbu (liftWF (cw4_WF (derivWF_weakenFresh wBulk)))
      · -- wXtop: top-X pin (row ∧ topBand) ⟹ q=q0 ∨ q=q1, each disjunct ⊥ the exclusions.
        intro Δ' lift liftWF he whe hr whr hbu whbu htc whtc htb whtb
        exact derivWF_orElim
          (classZBTopXPinAt_WF D (liftWF (cw4_WF (derivWF_weakenFresh wPin)))
            (liftWF (derivWF_hyp _)) (derivWF_cast_type rfl (rowGuard2_eq D) _ _ whr) whtb)
          (derivWF_botElim (derivWF_notElim (derivWF_hyp _) (cw1_WF (liftWF (derivWF_hyp _)))))
          (derivWF_botElim (derivWF_notElim (derivWF_hyp _) (cw1_WF (liftWF (derivWF_hyp _)))))
    · exact logicalZOffRowLocalCommutes_WF D (rowK2 D) (derivWF_hyp _) hA

/-- WF of `commPointwiseZSym` — pointwise per-`k` commutation against `logicalZ`, X/Z dual
of `commPointwiseSym_WF` (row guard, `rowDispatchOnTrue`, `bbfAtBound`, `logicalZ`). -/
theorem commPointwiseZSym_WF (D : OddSurfaceDistance) {Γ : List (SFormula 1)}
    {hEntryF : SFormula.Deriv Γ (entryFlatF1 D)}
    {hBBFF : SFormula.Deriv Γ (bottomBandFalseF D)}
    {hXbulk : ∀ (Δ' : List (SFormula 2)),
      (∀ {A : SFormula 2}, SFormula.Deriv (.eqBool (logicalZRowGuardAt2 D) (SC.b true)
          :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (entryFlat2F D) →
      SFormula.Deriv Δ' (.eqBool (logicalZRowGuardAt2 D) (SC.b true)) →
      SFormula.Deriv Δ' (gBulk D true) → SFormula.Deriv Δ' (gBand D true) →
      SFormula.Deriv Δ' (gKind D false) → SFormula.Deriv Δ' (lcGoalZ D)}
    {hXtop : ∀ (Δ' : List (SFormula 2)),
      (∀ {A : SFormula 2}, SFormula.Deriv (.eqBool (logicalZRowGuardAt2 D) (SC.b true)
          :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (entryFlat2F D) →
      SFormula.Deriv Δ' (.eqBool (logicalZRowGuardAt2 D) (SC.b true)) →
      SFormula.Deriv Δ' (gBulk D false) → SFormula.Deriv Δ' (gTopC D true) →
      SFormula.Deriv Δ' (gTopB D true) → SFormula.Deriv Δ' (lcGoalZ D)}
    {rho : Env 1} {E : PartialStabilizer}
    (wEntryF : DerivWF hEntryF Surface.code.body (D.distance + 2) rho E)
    (wBBFF : DerivWF hBBFF Surface.code.body (D.distance + 2) rho E)
    (wXbulk : ∀ (x : Nat) (Δ' : List (SFormula 2))
        (lift : ∀ {A : SFormula 2}, SFormula.Deriv (.eqBool (logicalZRowGuardAt2 D) (SC.b true)
            :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A),
        (∀ {A : SFormula 2} {h : SFormula.Deriv (.eqBool (logicalZRowGuardAt2 D) (SC.b true)
            :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A},
          DerivWF h Surface.code.body (D.distance + 2) (Env.cons x rho) E →
          DerivWF (lift h) Surface.code.body (D.distance + 2) (Env.cons x rho) E) →
        ∀ {he : SFormula.Deriv Δ' (entryFlat2F D)},
          DerivWF he Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        ∀ {hr : SFormula.Deriv Δ' (.eqBool (logicalZRowGuardAt2 D) (SC.b true))},
          DerivWF hr Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        ∀ {hbu : SFormula.Deriv Δ' (gBulk D true)},
          DerivWF hbu Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        ∀ {hba : SFormula.Deriv Δ' (gBand D true)},
          DerivWF hba Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        ∀ {hki : SFormula.Deriv Δ' (gKind D false)},
          DerivWF hki Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        DerivWF (hXbulk Δ' lift he hr hbu hba hki) Surface.code.body (D.distance + 2) (Env.cons x rho) E)
    (wXtop : ∀ (x : Nat) (Δ' : List (SFormula 2))
        (lift : ∀ {A : SFormula 2}, SFormula.Deriv (.eqBool (logicalZRowGuardAt2 D) (SC.b true)
            :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A),
        (∀ {A : SFormula 2} {h : SFormula.Deriv (.eqBool (logicalZRowGuardAt2 D) (SC.b true)
            :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A},
          DerivWF h Surface.code.body (D.distance + 2) (Env.cons x rho) E →
          DerivWF (lift h) Surface.code.body (D.distance + 2) (Env.cons x rho) E) →
        ∀ {he : SFormula.Deriv Δ' (entryFlat2F D)},
          DerivWF he Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        ∀ {hr : SFormula.Deriv Δ' (.eqBool (logicalZRowGuardAt2 D) (SC.b true))},
          DerivWF hr Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        ∀ {hbu : SFormula.Deriv Δ' (gBulk D false)},
          DerivWF hbu Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        ∀ {htc : SFormula.Deriv Δ' (gTopC D true)},
          DerivWF htc Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        ∀ {htb : SFormula.Deriv Δ' (gTopB D true)},
          DerivWF htb Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        DerivWF (hXtop Δ' lift he hr hbu htc htb) Surface.code.body (D.distance + 2) (Env.cons x rho) E)
    (hCtx : SFormula.ContextHolds Surface.code.body (D.distance + 2) rho E Γ) :
    DerivWF (commPointwiseZSym D hEntryF hBBFF hXbulk hXtop) Surface.code.body (D.distance + 2) rho E := by
  unfold commPointwiseZSym
  refine derivWF_commutesOfPointwise ?child ?fd
  case child =>
    show DerivWF (SFormula.Deriv.allNatLtIntroBounded _ _ _) _ _ _ _
    refine derivWF_allNatLtIntroBounded _ _ ⟨nQubits D.distance, scn_eval _ _ _ _ _, ?_⟩
    intro x hx
    refine ⟨?_, hCtx⟩
    have hA : ∃ v, (STerm.stabAt (rowK2 D) SFormula.boundNat).eval Surface.code.body
        (D.distance + 2) (Env.cons x rho) E = some v := by
      obtain ⟨sa, hsa, htot⟩ := recCall_total_symbolicDK_all D.index (D.distance + 2)
        (by simp only [OddSurfaceDistance.distance, oddDistance]; omega) (Env.cons x rho)
        (dT := dX2 D) (kT := kX2)
        (fun f' => by simp [dX2, distAtBoundIdx2, SC.closed, Term.eval, Term.lift,
          OddSurfaceDistance.distance, oddDistance]) (.var _)
      refine sterm_eval_stabAt (sv := sa) (qv := x) ?_ ?_ (htot x)
      · rw [rowK2_eq]; simpa [SC.closed, STerm.eval] using hsa
      · simp [SFormula.boundNat, SC.closed, STerm.eval, Term.eval, Env.cons]
    refine derivWF_boolCases _ _
      ⟨decide (x / D.distance = 0), by
        simp [logicalZRowGuardAt2, Formula.qVar, SC.closed, STerm.eval, Term.instantiateTopNat,
          Term.instantiateNatAt, Term.eval, Env.cons, bind, Option.bind]⟩ ?rowT ?rowF
    · exact rowDispatchOnTrue_WF D
        (entryAtBound_WF D (cw2_WF (derivWF_weakenFresh wEntryF)) (derivWF_hyp _))
        (derivWF_hyp _)
        (bbfAtBound_WF D (cw2_WF (derivWF_weakenFresh wBBFF)) (derivWF_hyp _)
          (by show DerivWF (cast _ SFormula.Deriv.assumption) _ _ _ _
              exact derivWF_cast_type rfl (rowGuard2_eq D) _ _ (derivWF_hyp _)))
        (wXbulk x) (wXtop x) hA
    · exact logicalZOffRowLocalCommutes_WF D (rowK2 D) (derivWF_hyp _) hA
  case fd =>
    obtain ⟨sa, hsa, htot⟩ := recCall_total_symbolicDK_all D.index (D.distance + 2)
      (by simp only [OddSurfaceDistance.distance, oddDistance]; omega) rho
      (dT := Term.lift 0 (Term.natLit D.distance)) (kT := Term.var ⟨0, by decide⟩)
      (fun f' => by simp [SC.closed, Term.eval, Term.lift,
        OddSurfaceDistance.distance, oddDistance]) (.var _)
    obtain ⟨g, hg⟩ := logicalZ_eval_total Surface.code.body (D.distance + 1) D.distance Env.empty
    refine formulaDefined_commutesUpTo (nv := nQubits D.distance) (Av := sa)
      (Bv := fun q => some (g q)) ?_ ?_ ?_ (fun q _ => htot q) StabTotalUpTo.ofTotal
    · simp [SC.closed, STerm.eval, Term.eval, Term.lift]
    · simpa [SC.closed, STerm.eval] using hsa
    · simp only [SC.closed, STerm.eval]
      have hrho : rho = Env.cons (rho ⟨0, by decide⟩) Env.empty := by
        funext i
        match i with
        | ⟨0, _⟩ => rfl
      rw [hrho, Term.eval_weaken_top]
      simpa [logicalZOdd, OddSurfaceDistance.distance, oddDistance] using hg


/-! ## The per-`k` `boolCases` classification tree (`Dcore`)

The `cut1` head of `xNormCommuteSym` is a 5-deep `boolCases` over the cell guards
(`bulkGuard` / `cZero` / `kind` / `leftClass` / `rightClass`), bottoming out at the
six commutator leaves `commTwoAntiA` / `commPointwiseSym` (×4) / `commTwoAntiB`.
The `boolCases` structure + the five guard bool-evals are discharged here; the six
commutator-leaf `DerivWF`s are residual #2. -/

/-- The X-normalizer bundle evals `true` at every stabilizer index `x`: soundness of
the `xBundle` family derivation.  Supplies the `xBundleF` conjunct of the
`ContextHolds` each commutator leaf needs. -/
theorem xBundleHolds (D : OddSurfaceDistance) (x : Nat) (E : PartialStabilizer) :
    (xBundleF D).eval Surface.code.body (D.distance + 2) (Env.cons x Env.empty) E = some true :=
  PureFamilyDerivA.sound (xBundle D) (Env.cons x Env.empty) E
    (pfda_defined (xBundle D) (Env.cons x Env.empty) E (xBundle_WF D))

/-- Discharge a commutator leaf's `ContextHolds Γ` obligation: split `Γ` into its
conjuncts, reduce each guard conjunct from the boolCases truth already in context
(`hbulk` / `hcz` / `hkind` / …), and close the bundle conjunct with `bundleHolds`. -/
local macro "leaf_ctx " bundleHolds:term : tactic =>
  `(tactic|
    (intro A hA
     simp only [List.mem_cons, List.mem_singleton] at hA
     casesm* _ ∨ _ <;> subst_vars <;>
       first
         | exact $bundleHolds
         | simp_all [SFormula.eval, SC.closed, SC.b, STerm.eval, Term.eval]))

/-- Band-pin WF for the `cnz` pointwise leaf's bulk handler (`zhBulkByCNZ`).  Mirrors the
handler body at the `DerivWF` level: the `band ∧ col → c=0` pin (`allNatLtElim` +
`applyNatBoundNatBeta` + `mp`×2) builds `cZero2 true`, contradicting the context `c≠0`. -/
theorem zhBulkByCNZ_WF (D : OddSurfaceDistance) {Γ : List (SFormula 1)}
    {hCNZ : SFormula.Deriv Γ (cZero1 D false)}
    {hImp : SFormula.Deriv Γ (bandImpCZeroF D)}
    {rho : Env 1} {E : PartialStabilizer}
    (wCNZ : DerivWF hCNZ Surface.code.body (D.distance + 2) rho E)
    (wImp : DerivWF hImp Surface.code.body (D.distance + 2) rho E) :
    ∀ (x : Nat) (Δ' : List (SFormula 2))
        (lift : ∀ {A : SFormula 2}, SFormula.Deriv (.eqBool (logicalXColGuardAt2 D) (SC.b true)
            :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A),
        (∀ {A : SFormula 2} {h : SFormula.Deriv (.eqBool (logicalXColGuardAt2 D) (SC.b true)
            :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A},
          DerivWF h Surface.code.body (D.distance + 2) (Env.cons x rho) E →
          DerivWF (lift h) Surface.code.body (D.distance + 2) (Env.cons x rho) E) →
        ∀ {he : SFormula.Deriv Δ' (entryFlat2F D)},
          DerivWF he Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        ∀ {hc : SFormula.Deriv Δ' (.eqBool (logicalXColGuardAt2 D) (SC.b true))},
          DerivWF hc Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        ∀ {hbu : SFormula.Deriv Δ' (gBulk D true)},
          DerivWF hbu Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        ∀ {hba : SFormula.Deriv Δ' (gBand D true)},
          DerivWF hba Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        ∀ {hki : SFormula.Deriv Δ' (gKind D true)},
          DerivWF hki Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        DerivWF (zhBulkByCNZ D hCNZ hImp Δ' lift he hc hbu hba hki)
          Surface.code.body (D.distance + 2) (Env.cons x rho) E := by
  intro _ _ _ liftWF _ _whe _ whc _ _whbu _ whba _ _whki
  refine eqBoolContra_WF _ ?_ (liftWF (cw2_WF (derivWF_weakenFresh wCNZ)))
  refine derivWF_mp (derivWF_mp (derivWF_applyNatBoundNatBeta _
    (derivWF_allNatLtElim _ _ _
      (liftWF (cw2_WF (derivWF_weakenFresh wImp)))
      (liftWF (derivWF_hyp _)))) ?hcol) whba
  case hcol => exact derivWF_cast_type rfl (colGuard2_eq D) _ _ whc

/-- Band-pin WF for the `rzF` pointwise leaf's bulk handler (`zhXbulkByRNZ`); Z mirror
of `zhBulkByCNZ_WF` under col↔row (`band ∧ row → r=0`). -/
theorem zhXbulkByRNZ_WF (D : OddSurfaceDistance) {Γ : List (SFormula 1)}
    {hRNZ : SFormula.Deriv Γ (gRZero1 D false)}
    {hImp : SFormula.Deriv Γ (bandImpRZeroF D)}
    {rho : Env 1} {E : PartialStabilizer}
    (wRNZ : DerivWF hRNZ Surface.code.body (D.distance + 2) rho E)
    (wImp : DerivWF hImp Surface.code.body (D.distance + 2) rho E) :
    ∀ (x : Nat) (Δ' : List (SFormula 2))
        (lift : ∀ {A : SFormula 2}, SFormula.Deriv (.eqBool (logicalZRowGuardAt2 D) (SC.b true)
            :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A),
        (∀ {A : SFormula 2} {h : SFormula.Deriv (.eqBool (logicalZRowGuardAt2 D) (SC.b true)
            :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A},
          DerivWF h Surface.code.body (D.distance + 2) (Env.cons x rho) E →
          DerivWF (lift h) Surface.code.body (D.distance + 2) (Env.cons x rho) E) →
        ∀ {he : SFormula.Deriv Δ' (entryFlat2F D)},
          DerivWF he Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        ∀ {hr : SFormula.Deriv Δ' (.eqBool (logicalZRowGuardAt2 D) (SC.b true))},
          DerivWF hr Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        ∀ {hbu : SFormula.Deriv Δ' (gBulk D true)},
          DerivWF hbu Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        ∀ {hba : SFormula.Deriv Δ' (gBand D true)},
          DerivWF hba Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        ∀ {hki : SFormula.Deriv Δ' (gKind D false)},
          DerivWF hki Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        DerivWF (zhXbulkByRNZ D hRNZ hImp Δ' lift he hr hbu hba hki)
          Surface.code.body (D.distance + 2) (Env.cons x rho) E := by
  intro _ _ _ liftWF _ _whe _ whr _ _whbu _ whba _ _whki
  refine eqBoolContra_WF _ ?_ (liftWF (cw2_WF (derivWF_weakenFresh wRNZ)))
  refine derivWF_mp (derivWF_mp (derivWF_applyNatBoundNatBeta _
    (derivWF_allNatLtElim _ _ _
      (liftWF (cw2_WF (derivWF_weakenFresh wImp)))
      (liftWF (derivWF_hyp _)))) ?hrow) whba
  case hrow => exact derivWF_cast_type rfl (rowGuard2_eq D) _ _ whr

set_option maxHeartbeats 1000000 in
theorem xNormScaffold_WF (D : OddSurfaceDistance) (E : PartialStabilizer) :
    DerivWFA (xNormScaffold D) Env.empty E := by
  unfold xNormScaffold xNormCommuteSym
  simp only [eq_mpr_eq_cast, id]
  refine derivWFA_cast_type rfl _ _ ?_
  refine derivWFA_allNatLtIntro _ ⟨numStab D.distance, ?_, fun x hx => ?_⟩
  · simp [SC.closed, STerm.eval, Term.eval]
  · refine derivWFA_cut1 ?_ (xBundle_WF D)
    -- the 5-deep boolCases classification tree, now via `derivWF_boolCases_cond` so each
    -- branch carries its guard's truth (`intro h…`) — exactly the `ContextHolds` the leaf needs.
    refine derivWF_boolCases_cond _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?bulkT ?bulkF
    case bulkT =>
      intro hbulk
      refine derivWF_boolCases_cond _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?czT ?czF
      case czT =>
        intro hcz
        refine derivWF_boolCases_cond _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?kindT ?kindF
        case kindT =>
          intro hkind
          exact commTwoAntiA_WF D (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _)
            (by comm_deriv_wf) (by comm_deriv_wf) (by comm_deriv_wf) (by comm_deriv_wf)
            (by comm_deriv_wf) (by comm_deriv_wf) (by comm_deriv_wf)
            (by leaf_ctx (xBundleHolds D x E))
        case kindF =>
          intro hkindF
          exact commPointwiseSym_WF D (by comm_deriv_wf) (by comm_deriv_wf)
            (by intro _ _ _ liftWF _ _whe _ _whc _ _whbu _ _whba _ whki
                exact eqBoolContra_WF _ whki (liftWF (cw2_WF (derivWF_weakenFresh (derivWF_hyp _)))))
            (by intro _ _ _ liftWF _ _whe _ _whc _ whbu _ _whtc _ _whrc _ _whlc _ _whlb
                exact eqBoolContra_WF _ (liftWF (cw2_WF (derivWF_weakenFresh (derivWF_hyp _)))) whbu)
            (by leaf_ctx (xBundleHolds D x E))
      case czF =>
        intro hcnz
        exact commPointwiseSym_WF D (by comm_deriv_wf) (by comm_deriv_wf)
          (zhBulkByCNZ_WF D (derivWF_hyp _) (by comm_deriv_wf))
          (by intro _ _ _ liftWF _ _whe _ _whc _ whbu _ _whtc _ _whrc _ _whlc _ _whlb
              exact eqBoolContra_WF _ (liftWF (cw2_WF (derivWF_weakenFresh (derivWF_hyp _)))) whbu)
          (by leaf_ctx (xBundleHolds D x E))
    case bulkF =>
      intro hbulkF
      refine derivWF_boolCases_cond _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?lcT ?lcF
      case lcT =>
        intro hlc
        refine derivWF_boolCases_cond _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?rcT ?rcF
        case rcT =>
          intro hrc
          exact commPointwiseSym_WF D (by comm_deriv_wf) (by comm_deriv_wf)
            (by intro _ _ _ liftWF _ _whe _ _whc _ whbu _ _whba _ _whki
                exact eqBoolContra_WF _ whbu (liftWF (cw2_WF (derivWF_weakenFresh (derivWF_hyp _)))))
            (by intro _ _ _ liftWF _ _whe _ _whc _ _whbu _ _whtc _ whrc _ _whlc _ _whlb
                exact eqBoolContra_WF _ (liftWF (cw2_WF (derivWF_weakenFresh (derivWF_hyp _)))) whrc)
            (by leaf_ctx (xBundleHolds D x E))
        case rcF =>
          intro hrcF
          exact commTwoAntiB_WF D (derivWF_hyp _) (by comm_deriv_wf) (derivWF_hyp _) (derivWF_hyp _)
            (by comm_deriv_wf) (by comm_deriv_wf) (by comm_deriv_wf) (by comm_deriv_wf)
            (by comm_deriv_wf) (by comm_deriv_wf) (by comm_deriv_wf)
            (by leaf_ctx (xBundleHolds D x E))
      case lcF =>
        intro hlcF
        exact commPointwiseSym_WF D (by comm_deriv_wf) (by comm_deriv_wf)
          (by intro _ _ _ liftWF _ _whe _ _whc _ whbu _ _whba _ _whki
              exact eqBoolContra_WF _ whbu (liftWF (cw2_WF (derivWF_weakenFresh (derivWF_hyp _)))))
          (by intro _ _ _ liftWF _ _whe _ _whc _ _whbu _ _whtc _ _whrc _ whlc _ _whlb
              exact eqBoolContra_WF _ whlc (liftWF (cw2_WF (derivWF_weakenFresh (derivWF_hyp _)))))
          (by leaf_ctx (xBundleHolds D x E))

/-! ## Z/col transpose

`zNormScaffold D = zNormCommuteSym D` mirrors the X version under the div↔mod /
row↔col / X↔Z swap.  The bundle and boolCases scaffolding transpose cleanly; the
residuals are the same two (`rowEntryFlatSym_WF` and the commutator leaves
`commZTwoAntiA`/`commZTwoAntiB`/`commPointwiseZSym`). -/

theorem bottomBandFalsePack_WF (D : OddSurfaceDistance) {x : Nat} {E : PartialStabilizer} :
    DerivWFA (bottomBandFalsePack D) (Env.cons x Env.empty) E := by
  unfold bottomBandFalsePack; exact nQ1ArithBoolPack_WF

theorem classZABulkXPinPack_WF (D : OddSurfaceDistance) {x : Nat} {E : PartialStabilizer} :
    DerivWFA (classZABulkXPinPack D) (Env.cons x Env.empty) E := by
  unfold classZABulkXPinPack; exact nQ1ArithBoolPack_WF

theorem classZBTopXPinPack_WF (D : OddSurfaceDistance) {x : Nat} {E : PartialStabilizer} :
    DerivWFA (classZBTopXPinPack D) (Env.cons x Env.empty) E := by
  unfold classZBTopXPinPack; exact nQ1ArithBoolPack_WF

theorem bandImpRZeroPack_WF (D : OddSurfaceDistance) {x : Nat} {E : PartialStabilizer} :
    DerivWFA (bandImpRZeroPack D) (Env.cons x Env.empty) E := by
  unfold bandImpRZeroPack; exact nQ1ArithBoolPack_WF

/-- `DerivWFA (zBundle D)`: the 13-pack conjunction (transpose of `xBundle_WF`). -/
theorem zBundle_WF (D : OddSurfaceDistance) {x : Nat} {E : PartialStabilizer} :
    DerivWFA (zBundle D) (Env.cons x Env.empty) E := by
  unfold zBundle
  exact pfdaAnd_WF (entryFlatPack_WF D)
    (pfdaAnd_WF (bottomBandFalsePack_WF D)
      (pfdaAnd_WF True.intro
        (pfdaAnd_WF True.intro
          (pfdaAnd_WF (classZABulkXPinPack_WF D)
            (pfdaAnd_WF True.intro
              (pfdaAnd_WF True.intro
                (pfdaAnd_WF (classZBTopXPinPack_WF D)
                  (pfdaAnd_WF (xEntryFlat1_WF D (qza0 D) (qza0_pure D))
                    (pfdaAnd_WF (xEntryFlat1_WF D (qza1 D) (qza1_pure D))
                      (pfdaAnd_WF (xEntryFlat1_WF D (qzb0 D) (qzb0_pure D))
                        (pfdaAnd_WF (xEntryFlat1_WF D (qzb1 D) (qzb1_pure D))
                          (bandImpRZeroPack_WF D))))))))))))

/-- The Z-normalizer bundle evals `true` at every stabilizer index `x` (transpose of
`xBundleHolds`). -/
theorem zBundleHolds (D : OddSurfaceDistance) (x : Nat) (E : PartialStabilizer) :
    (zBundleF D).eval Surface.code.body (D.distance + 2) (Env.cons x Env.empty) E = some true :=
  PureFamilyDerivA.sound (zBundle D) (Env.cons x Env.empty) E
    (pfda_defined (zBundle D) (Env.cons x Env.empty) E (zBundle_WF D))

set_option maxHeartbeats 1000000 in
theorem zNormScaffold_WF (D : OddSurfaceDistance) (E : PartialStabilizer) :
    DerivWFA (zNormScaffold D) Env.empty E := by
  unfold zNormScaffold zNormCommuteSym
  simp only [eq_mpr_eq_cast, id]
  refine derivWFA_cast_type rfl _ _ ?_
  refine derivWFA_allNatLtIntro _ ⟨numStab D.distance, ?_, fun x hx => ?_⟩
  · simp [SC.closed, STerm.eval, Term.eval]
  · refine derivWFA_cut1 ?_ (zBundle_WF D)
    -- the boolCases classification tree (transpose) via `derivWF_boolCases_cond`.
    refine derivWF_boolCases_cond _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?bulkT ?bulkF
    case bulkT =>
      intro hbulk
      refine derivWF_boolCases_cond _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?rzT ?rzF
      case rzT =>
        intro hrz
        refine derivWF_boolCases_cond _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?kindT ?kindF
        case kindT =>
          intro hkind
          exact commPointwiseZSym_WF D (by comm_deriv_wf) (by comm_deriv_wf)
            (by intro _ _ _ liftWF _ _whe _ _whr _ _whbu _ _whba _ whki
                exact eqBoolContra_WF _ (liftWF (cw2_WF (derivWF_weakenFresh (derivWF_hyp _)))) whki)
            (by intro _ _ _ liftWF _ _whe _ _whr _ whbu _ _whtc _ _whtb
                exact eqBoolContra_WF _ (liftWF (cw2_WF (derivWF_weakenFresh (derivWF_hyp _)))) whbu)
            (by leaf_ctx (zBundleHolds D x E))
        case kindF =>
          intro hkindF
          exact commZTwoAntiA_WF D (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _)
            (by comm_deriv_wf) (by comm_deriv_wf) (by comm_deriv_wf) (by comm_deriv_wf)
            (by comm_deriv_wf) (by comm_deriv_wf) (by comm_deriv_wf)
            (by leaf_ctx (zBundleHolds D x E))
      case rzF =>
        intro hrnz
        exact commPointwiseZSym_WF D (by comm_deriv_wf) (by comm_deriv_wf)
          (zhXbulkByRNZ_WF D (derivWF_hyp _) (by comm_deriv_wf))
          (by intro _ _ _ liftWF _ _whe _ _whr _ whbu _ _whtc _ _whtb
              exact eqBoolContra_WF _ (liftWF (cw2_WF (derivWF_weakenFresh (derivWF_hyp _)))) whbu)
          (by leaf_ctx (zBundleHolds D x E))
    case bulkF =>
      intro hbulkF
      refine derivWF_boolCases_cond _ _ (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?tcT ?tcF
      case tcT =>
        intro htc
        exact commZTwoAntiB_WF D (derivWF_hyp _) (derivWF_hyp _)
          (by comm_deriv_wf) (by comm_deriv_wf) (by comm_deriv_wf) (by comm_deriv_wf)
          (by comm_deriv_wf) (by comm_deriv_wf) (by comm_deriv_wf)
          (by leaf_ctx (zBundleHolds D x E))
      case tcF =>
        intro htcF
        exact commPointwiseZSym_WF D (by comm_deriv_wf) (by comm_deriv_wf)
          (by intro _ _ _ liftWF _ _whe _ _whr _ whbu _ _whba _ _whki
              exact eqBoolContra_WF _ whbu (liftWF (cw2_WF (derivWF_weakenFresh (derivWF_hyp _)))))
          (by intro _ _ _ liftWF _ _whe _ _whr _ _whbu _ whtc _ _whtb
              exact eqBoolContra_WF _ whtc (liftWF (cw2_WF (derivWF_weakenFresh (derivWF_hyp _)))))
          (by leaf_ctx (zBundleHolds D x E))

/-! ## Axiom audit of the sorry-free scaffolding

The reusable combinators and the bundle glue carry no new axioms (no `sorryAx`).
Both headline `*_WF` lemmas (`xNormScaffold_WF` / `zNormScaffold_WF`) are now
fully discharged — the commutator leaves close through `commTwoAntiA_WF` /
`commTwoAntiB_WF` / `commPointwiseSym_WF` (+ Z mirrors), the per-leaf
`ContextHolds` through `xBundleHolds` / `zBundleHolds`, and the two band-pin
handlers through `zhBulkByCNZ_WF` / `zhXbulkByRNZ_WF`.  They carry the standard
axioms only (`propext`, `Classical.choice`, `Quot.sound`); no `sorryAx`. -/

#print axioms xNormScaffold_WF
#print axioms zNormScaffold_WF
#print axioms derivWFA_cast_type
#print axioms derivWFA_allNatLtIntro
#print axioms pfdaAnd_WF
#print axioms nQ1ArithBoolPack_WF
#print axioms xEntryFlat1_WF
#print axioms entryFlatPack_WF
#print axioms xBundle_WF
#print axioms zBundle_WF

/-! ## Axiom audit of the new combinators + the keystone `m`-induction collapse

The extra `DerivWF` node combinators (`derivWF_eqPauliTrans'` etc.) are
`rfl`-transparent and carry no new axioms.  `surfaceRowEntryCharSymbolicA_WF` — the
keystone `m`-induction — has a **sorry-free body**: it reduces to `baseRowConvergeA_WF`
(BASE master) + `recRowConvergeA_WF` (REC master), the two FLAT (non-`m`-recursing)
leaf-grind residuals.  Its transitive `#print axioms` therefore shows `sorryAx` *only*
through those two masters; closing them closes the keystone with no per-level multiply. -/
#print axioms derivWF_eqPauliTrans'
#print axioms derivWF_eqPauliSymm'
#print axioms derivWF_pauliIteSelectThen'
#print axioms surfaceRowEntryCharSymbolicA_WF

/-! ## Axiom audit of the STEP 0-2 rec-side foundation (sorry-free) -/
#print axioms pureNatTerm_eval_total_allFuel
#print axioms RecEvalData.lamBody_total
#print axioms recEvalData_of_DistAtA
#print axioms RecEvalData.recOkSubst_total
#print axioms RecEvalData.instRecOkSubst_total
#print axioms recPeel_lamFD

end QHL.CodeLang.Surface.Verify
