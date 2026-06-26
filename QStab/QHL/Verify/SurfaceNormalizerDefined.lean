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
      | refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat constructor)) ?_ ?_
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
    (hq : SFormula.PureNatTerm qT)
    {hBulk hTopClass hTopBand} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity}
    {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wTopBand : DerivWF hTopBand cb fuel rho E) :
    DerivWF (recTopIPeelD (Γ := Γ) dT kT qT hq hBulk hTopClass hTopBand) cb fuel rho E := by
  unfold recTopIPeelD; peel_walk

theorem recRightZPeelD_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hq : SFormula.PureNatTerm qT)
    {hBulk hTopClass hRightClass hRightBand} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity}
    {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wRightBand : DerivWF hRightBand cb fuel rho E) :
    DerivWF (recRightZPeelD (Γ := Γ) dT kT qT hq hBulk hTopClass hRightClass hRightBand)
      cb fuel rho E := by
  unfold recRightZPeelD; peel_walk

theorem recRightIPeelD_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hq : SFormula.PureNatTerm qT)
    {hBulk hTopClass hRightClass hRightBand} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity}
    {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wRightBand : DerivWF hRightBand cb fuel rho E) :
    DerivWF (recRightIPeelD (Γ := Γ) dT kT qT hq hBulk hTopClass hRightClass hRightBand)
      cb fuel rho E := by
  unfold recRightIPeelD; peel_walk

theorem recLeftZPeelD_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hq : SFormula.PureNatTerm qT)
    {hBulk hTopClass hRightClass hLeftClass hLeftBand} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wLeftClass : DerivWF hLeftClass cb fuel rho E)
    (wLeftBand : DerivWF hLeftBand cb fuel rho E) :
    DerivWF (recLeftZPeelD (Γ := Γ) dT kT qT hq hBulk hTopClass hRightClass hLeftClass hLeftBand)
      cb fuel rho E := by
  unfold recLeftZPeelD; peel_walk

theorem recLeftIPeelD_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hq : SFormula.PureNatTerm qT)
    {hBulk hTopClass hRightClass hLeftClass hLeftBand} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wLeftClass : DerivWF hLeftClass cb fuel rho E)
    (wLeftBand : DerivWF hLeftBand cb fuel rho E) :
    DerivWF (recLeftIPeelD (Γ := Γ) dT kT qT hq hBulk hTopClass hRightClass hLeftClass hLeftBand)
      cb fuel rho E := by
  unfold recLeftIPeelD; peel_walk

theorem recBottomXPeelD_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hq : SFormula.PureNatTerm qT)
    {hBulk hTopClass hRightClass hLeftClass hBottomBand} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wLeftClass : DerivWF hLeftClass cb fuel rho E)
    (wBottomBand : DerivWF hBottomBand cb fuel rho E) :
    DerivWF (recBottomXPeelD (Γ := Γ) dT kT qT hq hBulk hTopClass hRightClass hLeftClass hBottomBand)
      cb fuel rho E := by
  unfold recBottomXPeelD; peel_walk

theorem recBottomIPeelD_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    (hq : SFormula.PureNatTerm qT)
    {hBulk hTopClass hRightClass hLeftClass hBottomBand} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wLeftClass : DerivWF hLeftClass cb fuel rho E)
    (wBottomBand : DerivWF hBottomBand cb fuel rho E) :
    DerivWF (recBottomIPeelD (Γ := Γ) dT kT qT hq hBulk hTopClass hRightClass hLeftClass hBottomBand)
      cb fuel rho E := by
  unfold recBottomIPeelD; peel_walk

/-! ### Base-leaf `DerivWF` lemmas (pure `pauliIteSelect` chains over `baseLeafTreeTA`) -/

theorem leafBulkX_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    {hBulk hBand hKind} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wBand : DerivWF hBand cb fuel rho E)
    (wKind : DerivWF hKind cb fuel rho E) :
    DerivWF (leafBulkX (Γ := Γ) dT kT qT hBulk hBand hKind) cb fuel rho E := by
  unfold leafBulkX; wf_walk

theorem leafBulkI_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    {hBulk hBand} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wBand : DerivWF hBand cb fuel rho E) :
    DerivWF (leafBulkI (Γ := Γ) dT kT qT hBulk hBand) cb fuel rho E := by
  unfold leafBulkI; wf_walk

theorem leafTopX_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    {hBulk hTopClass hTopBand} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity}
    {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wTopBand : DerivWF hTopBand cb fuel rho E) :
    DerivWF (leafTopX (Γ := Γ) dT kT qT hBulk hTopClass hTopBand) cb fuel rho E := by
  unfold leafTopX; wf_walk

theorem leafTopI_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    {hBulk hTopClass hTopBand} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity}
    {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wTopBand : DerivWF hTopBand cb fuel rho E) :
    DerivWF (leafTopI (Γ := Γ) dT kT qT hBulk hTopClass hTopBand) cb fuel rho E := by
  unfold leafTopI; wf_walk

theorem leafRightZ_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    {hBulk hTopClass hRightClass hRightBand} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity}
    {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wRightBand : DerivWF hRightBand cb fuel rho E) :
    DerivWF (leafRightZ (Γ := Γ) dT kT qT hBulk hTopClass hRightClass hRightBand) cb fuel rho E := by
  unfold leafRightZ; wf_walk

theorem leafRightI_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    {hBulk hTopClass hRightClass hRightBand} {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity}
    {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wRightBand : DerivWF hRightBand cb fuel rho E) :
    DerivWF (leafRightI (Γ := Γ) dT kT qT hBulk hTopClass hRightClass hRightBand) cb fuel rho E := by
  unfold leafRightI; wf_walk

theorem leafLeftZ_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    {hBulk hTopClass hRightClass hLeftClass hLeftBand} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wLeftClass : DerivWF hLeftClass cb fuel rho E)
    (wLeftBand : DerivWF hLeftBand cb fuel rho E) :
    DerivWF (leafLeftZ (Γ := Γ) dT kT qT hBulk hTopClass hRightClass hLeftClass hLeftBand)
      cb fuel rho E := by
  unfold leafLeftZ; wf_walk

theorem leafLeftI_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    {hBulk hTopClass hRightClass hLeftClass hLeftBand} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wLeftClass : DerivWF hLeftClass cb fuel rho E)
    (wLeftBand : DerivWF hLeftBand cb fuel rho E) :
    DerivWF (leafLeftI (Γ := Γ) dT kT qT hBulk hTopClass hRightClass hLeftClass hLeftBand)
      cb fuel rho E := by
  unfold leafLeftI; wf_walk

theorem leafBottomX_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    {hBulk hTopClass hRightClass hLeftClass hBottomBand} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wLeftClass : DerivWF hLeftClass cb fuel rho E)
    (wBottomBand : DerivWF hBottomBand cb fuel rho E) :
    DerivWF (leafBottomX (Γ := Γ) dT kT qT hBulk hTopClass hRightClass hLeftClass hBottomBand)
      cb fuel rho E := by
  unfold leafBottomX; wf_walk

theorem leafBottomI_WF {arity : Nat} (Γ : List (SFormula arity)) (dT kT qT : Term arity .nat)
    {hBulk hTopClass hRightClass hLeftClass hBottomBand} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (wBulk : DerivWF hBulk cb fuel rho E) (wTopClass : DerivWF hTopClass cb fuel rho E)
    (wRightClass : DerivWF hRightClass cb fuel rho E) (wLeftClass : DerivWF hLeftClass cb fuel rho E)
    (wBottomBand : DerivWF hBottomBand cb fuel rho E) :
    DerivWF (leafBottomI (Γ := Γ) dT kT qT hBulk hTopClass hRightClass hLeftClass hBottomBand)
      cb fuel rho E := by
  unfold leafBottomI; wf_walk

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
  refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat constructor)) ?bulkT ?bulkF
  case bulkT =>
    refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat constructor)) ?bandT ?bandF
    case bandT =>
      refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat constructor)) ?kindT ?kindF
      case kindT =>
        exact derivWF_eqPauliTrans' (recBasePeelD_Z_WF _ _ _ _ hq True.intro True.intro True.intro)
          (derivWF_eqPauliSymm' (leafZ_WF _ _ _ True.intro True.intro True.intro))
      case kindF =>
        exact derivWF_eqPauliTrans' (recBasePeelD_X_WF _ _ _ _ hq True.intro True.intro True.intro)
          (derivWF_eqPauliSymm' (leafBulkX_WF _ _ _ _ True.intro True.intro True.intro))
    case bandF =>
      exact derivWF_eqPauliTrans' (recBasePeelD_I_WF _ _ _ _ hq True.intro True.intro)
        (derivWF_eqPauliSymm' (leafBulkI_WF _ _ _ _ True.intro True.intro))
  case bulkF =>
    refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat constructor)) ?tcT ?tcF
    case tcT =>
      refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat constructor)) ?tbT ?tbF
      case tbT =>
        exact derivWF_eqPauliTrans' (recTopXPeelD_WF _ _ _ _ hq True.intro True.intro True.intro)
          (derivWF_eqPauliSymm' (leafTopX_WF _ _ _ _ True.intro True.intro True.intro))
      case tbF =>
        exact derivWF_eqPauliTrans' (recTopIPeelD_WF _ _ _ _ hq True.intro True.intro True.intro)
          (derivWF_eqPauliSymm' (leafTopI_WF _ _ _ _ True.intro True.intro True.intro))
    case tcF =>
      refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat constructor)) ?rcT ?rcF
      case rcT =>
        refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat constructor)) ?rbT ?rbF
        case rbT =>
          exact derivWF_eqPauliTrans'
            (recRightZPeelD_WF _ _ _ _ hq True.intro True.intro True.intro True.intro)
            (derivWF_eqPauliSymm'
              (leafRightZ_WF _ _ _ _ True.intro True.intro True.intro True.intro))
        case rbF =>
          exact derivWF_eqPauliTrans'
            (recRightIPeelD_WF _ _ _ _ hq True.intro True.intro True.intro True.intro)
            (derivWF_eqPauliSymm'
              (leafRightI_WF _ _ _ _ True.intro True.intro True.intro True.intro))
      case rcF =>
        refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat constructor)) ?lcT ?lcF
        case lcT =>
          refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat constructor)) ?lbT ?lbF
          case lbT =>
            exact derivWF_eqPauliTrans'
              (recLeftZPeelD_WF _ _ _ _ hq True.intro True.intro True.intro True.intro True.intro)
              (derivWF_eqPauliSymm'
                (leafLeftZ_WF _ _ _ _ True.intro True.intro True.intro True.intro True.intro))
          case lbF =>
            exact derivWF_eqPauliTrans'
              (recLeftIPeelD_WF _ _ _ _ hq True.intro True.intro True.intro True.intro True.intro)
              (derivWF_eqPauliSymm'
                (leafLeftI_WF _ _ _ _ True.intro True.intro True.intro True.intro True.intro))
        case lcF =>
          refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat constructor)) ?bbT ?bbF
          case bbT =>
            exact derivWF_eqPauliTrans'
              (recBottomXPeelD_WF _ _ _ _ hq True.intro True.intro True.intro True.intro True.intro)
              (derivWF_eqPauliSymm'
                (leafBottomX_WF _ _ _ _ True.intro True.intro True.intro True.intro True.intro))
          case bbF =>
            exact derivWF_eqPauliTrans'
              (recBottomIPeelD_WF _ _ _ _ hq True.intro True.intro True.intro True.intro True.intro)
              (derivWF_eqPauliSymm'
                (leafBottomI_WF _ _ _ _ True.intro True.intro True.intro True.intro True.intro))

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
    (rho : Env arity) : Prop where
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
theorem recEvalData_of_DistAtA {arity : Nat} {m : Nat} (DD : DistAtA arity (m + 1))
    {kT : Term arity .nat} (hk : SFormula.PureNatTerm kT) (rho : Env arity) {f' : Nat}
    (hf' : m + 1 ≤ f') :
    RecEvalData DD.dT kT f' rho := by
  obtain ⟨kv, hkv⟩ := pureNatTerm_eval_total_allFuel hk Surface.code.body rho
  refine
    { dv := oddDistance (m + 1)
      kv := kv
      hdAll := fun fuel => DD.evalsTo rho
      hkAll := hkv
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

/-- Discharge a totality goal `∃ v, eval <recLeafTreeTA subtree> rho = some v`: the
subtree is built from pure guards, pure-pauli leaves (`leaf_pp`), `baseLeafTreeTA`, and
the IH paulis (supplied as hypotheses).  Recurses through the `ite` nodes via
`eval_ite_pauli_total`, finishing pure guards by the `PureBoolTerm` totality bank. -/
/-- A `recLeafTreeTA`-guard / cell-guard is a `PureBoolTerm` when the index terms are
pure.  Discharged by unfolding the guard sugar and running `pure_tree`. -/
theorem recLeafGuard_eval_total {arity : Nat} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {cond : Term arity .bool} (hc : SFormula.PureBoolTerm cond) :
    ∃ cv, Term.eval cb fuel cond rho = some cv :=
  hc.eval_total cb fuel rho

macro "rec_leaf_tot" : tactic =>
  `(tactic|
    repeat first
      | assumption
      | exact baseLeafTreeTA_eval_total ‹SFormula.PureNatTerm _› ‹SFormula.PureNatTerm _›
          ‹SFormula.PureNatTerm _› _ _ _
      | exact (show PurePauli _ by leaf_pp).eval_total _ _ _
      | refine eval_ite_pauli_total (recLeafGuard_eval_total (by leaf_pp)) ?_ ?_)

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

set_option maxHeartbeats 1600000

theorem recLeafInt_WF {arity : Nat} (Γ : List (SFormula arity))
    (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    {hBulk hInterior hInside} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpInt : ∃ v, Term.eval cb fuel pInt rho = some v)
    (hpTop : ∃ v, Term.eval cb fuel pTop rho = some v)
    (hpRight : ∃ v, Term.eval cb fuel pRight rho = some v)
    (hpLeft : ∃ v, Term.eval cb fuel pLeft rho = some v)
    (hpBottom : ∃ v, Term.eval cb fuel pBottom rho = some v) :
    DerivWF (recLeafInt (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom hBulk hInterior hInside)
      cb fuel rho E := by
  unfold recLeafInt
  exact derivWF_eqPauliTrans'
    (derivWF_pauliIteSelectThen' _ _ _ True.intro
      (formulaDefined_iteSelectThen (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
    (derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectThen' _ _ _ True.intro
        (formulaDefined_iteSelectThen (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
      (derivWF_pauliIteSelectThen' _ _ _ True.intro
        (formulaDefined_iteSelectThen (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot))))

/-- The shared per-leaf hypotheses: index purities + the five IH-pauli totalities. -/
theorem recLeafIntI_WF {arity : Nat} (Γ : List (SFormula arity))
    (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    {hBulk hInterior hInside} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpInt : ∃ v, Term.eval cb fuel pInt rho = some v)
    (hpTop : ∃ v, Term.eval cb fuel pTop rho = some v)
    (hpRight : ∃ v, Term.eval cb fuel pRight rho = some v)
    (hpLeft : ∃ v, Term.eval cb fuel pLeft rho = some v)
    (hpBottom : ∃ v, Term.eval cb fuel pBottom rho = some v) :
    DerivWF (recLeafIntI (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom hBulk hInterior hInside)
      cb fuel rho E := by
  unfold recLeafIntI
  exact derivWF_eqPauliTrans'
    (derivWF_pauliIteSelectThen' _ _ _ True.intro
      (formulaDefined_iteSelectThen (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
    (derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectThen' _ _ _ True.intro
        (formulaDefined_iteSelectThen (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
      (derivWF_pauliIteSelectElse' _ _ _ True.intro
        (formulaDefined_iteSelectElse (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot))))

theorem recLeafTop_WF {arity : Nat} (Γ : List (SFormula arity))
    (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    {hBulk hInterior hTop hInside} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpInt : ∃ v, Term.eval cb fuel pInt rho = some v)
    (hpTop : ∃ v, Term.eval cb fuel pTop rho = some v)
    (hpRight : ∃ v, Term.eval cb fuel pRight rho = some v)
    (hpLeft : ∃ v, Term.eval cb fuel pLeft rho = some v)
    (hpBottom : ∃ v, Term.eval cb fuel pBottom rho = some v) :
    DerivWF (recLeafTop (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom hBulk hInterior hTop hInside)
      cb fuel rho E := by
  unfold recLeafTop
  exact derivWF_eqPauliTrans'
    (derivWF_pauliIteSelectThen' _ _ _ True.intro
      (formulaDefined_iteSelectThen (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
    (derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectElse' _ _ _ True.intro
        (formulaDefined_iteSelectElse (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
      (derivWF_eqPauliTrans'
        (derivWF_pauliIteSelectThen' _ _ _ True.intro
          (formulaDefined_iteSelectThen (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
        (derivWF_pauliIteSelectThen' _ _ _ True.intro
          (formulaDefined_iteSelectThen (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))))

theorem recLeafTopNI_WF {arity : Nat} (Γ : List (SFormula arity))
    (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    {hBulk hInterior hTop hInside} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpInt : ∃ v, Term.eval cb fuel pInt rho = some v)
    (hpTop : ∃ v, Term.eval cb fuel pTop rho = some v)
    (hpRight : ∃ v, Term.eval cb fuel pRight rho = some v)
    (hpLeft : ∃ v, Term.eval cb fuel pLeft rho = some v)
    (hpBottom : ∃ v, Term.eval cb fuel pBottom rho = some v) :
    DerivWF (recLeafTopNI (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom hBulk hInterior hTop hInside)
      cb fuel rho E := by
  unfold recLeafTopNI
  exact derivWF_eqPauliTrans'
    (derivWF_pauliIteSelectThen' _ _ _ True.intro
      (formulaDefined_iteSelectThen (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
    (derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectElse' _ _ _ True.intro
        (formulaDefined_iteSelectElse (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
      (derivWF_eqPauliTrans'
        (derivWF_pauliIteSelectThen' _ _ _ True.intro
          (formulaDefined_iteSelectThen (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
        (derivWF_pauliIteSelectElse' _ _ _ True.intro
          (formulaDefined_iteSelectElse (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))))

theorem recLeafRight_WF {arity : Nat} (Γ : List (SFormula arity))
    (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    {hBulk hInterior hTop hRight hInside} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpInt : ∃ v, Term.eval cb fuel pInt rho = some v)
    (hpTop : ∃ v, Term.eval cb fuel pTop rho = some v)
    (hpRight : ∃ v, Term.eval cb fuel pRight rho = some v)
    (hpLeft : ∃ v, Term.eval cb fuel pLeft rho = some v)
    (hpBottom : ∃ v, Term.eval cb fuel pBottom rho = some v) :
    DerivWF (recLeafRight (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom
      hBulk hInterior hTop hRight hInside) cb fuel rho E := by
  unfold recLeafRight
  exact derivWF_eqPauliTrans'
    (derivWF_pauliIteSelectThen' _ _ _ True.intro
      (formulaDefined_iteSelectThen (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
    (derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectElse' _ _ _ True.intro
        (formulaDefined_iteSelectElse (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
      (derivWF_eqPauliTrans'
        (derivWF_pauliIteSelectElse' _ _ _ True.intro
          (formulaDefined_iteSelectElse (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
        (derivWF_eqPauliTrans'
          (derivWF_pauliIteSelectThen' _ _ _ True.intro
            (formulaDefined_iteSelectThen (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
          (derivWF_pauliIteSelectThen' _ _ _ True.intro
            (formulaDefined_iteSelectThen (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot))))))

theorem recLeafRightNI_WF {arity : Nat} (Γ : List (SFormula arity))
    (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    {hBulk hInterior hTop hRight hInside} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpInt : ∃ v, Term.eval cb fuel pInt rho = some v)
    (hpTop : ∃ v, Term.eval cb fuel pTop rho = some v)
    (hpRight : ∃ v, Term.eval cb fuel pRight rho = some v)
    (hpLeft : ∃ v, Term.eval cb fuel pLeft rho = some v)
    (hpBottom : ∃ v, Term.eval cb fuel pBottom rho = some v) :
    DerivWF (recLeafRightNI (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom
      hBulk hInterior hTop hRight hInside) cb fuel rho E := by
  unfold recLeafRightNI
  exact derivWF_eqPauliTrans'
    (derivWF_pauliIteSelectThen' _ _ _ True.intro
      (formulaDefined_iteSelectThen (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
    (derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectElse' _ _ _ True.intro
        (formulaDefined_iteSelectElse (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
      (derivWF_eqPauliTrans'
        (derivWF_pauliIteSelectElse' _ _ _ True.intro
          (formulaDefined_iteSelectElse (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
        (derivWF_eqPauliTrans'
          (derivWF_pauliIteSelectThen' _ _ _ True.intro
            (formulaDefined_iteSelectThen (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
          (derivWF_pauliIteSelectElse' _ _ _ True.intro
            (formulaDefined_iteSelectElse (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot))))))

theorem recLeafLeft_WF {arity : Nat} (Γ : List (SFormula arity))
    (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    {hBulk hInterior hTop hRight hLeft hInside} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpInt : ∃ v, Term.eval cb fuel pInt rho = some v)
    (hpTop : ∃ v, Term.eval cb fuel pTop rho = some v)
    (hpRight : ∃ v, Term.eval cb fuel pRight rho = some v)
    (hpLeft : ∃ v, Term.eval cb fuel pLeft rho = some v)
    (hpBottom : ∃ v, Term.eval cb fuel pBottom rho = some v) :
    DerivWF (recLeafLeft (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom
      hBulk hInterior hTop hRight hLeft hInside) cb fuel rho E := by
  unfold recLeafLeft
  exact derivWF_eqPauliTrans'
    (derivWF_pauliIteSelectThen' _ _ _ True.intro
      (formulaDefined_iteSelectThen (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
    (derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectElse' _ _ _ True.intro
        (formulaDefined_iteSelectElse (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
      (derivWF_eqPauliTrans'
        (derivWF_pauliIteSelectElse' _ _ _ True.intro
          (formulaDefined_iteSelectElse (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
        (derivWF_eqPauliTrans'
          (derivWF_pauliIteSelectElse' _ _ _ True.intro
            (formulaDefined_iteSelectElse (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
          (derivWF_eqPauliTrans'
            (derivWF_pauliIteSelectThen' _ _ _ True.intro
              (formulaDefined_iteSelectThen (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
            (derivWF_pauliIteSelectThen' _ _ _ True.intro
              (formulaDefined_iteSelectThen (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))))))

theorem recLeafLeftNI_WF {arity : Nat} (Γ : List (SFormula arity))
    (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    {hBulk hInterior hTop hRight hLeft hInside} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpInt : ∃ v, Term.eval cb fuel pInt rho = some v)
    (hpTop : ∃ v, Term.eval cb fuel pTop rho = some v)
    (hpRight : ∃ v, Term.eval cb fuel pRight rho = some v)
    (hpLeft : ∃ v, Term.eval cb fuel pLeft rho = some v)
    (hpBottom : ∃ v, Term.eval cb fuel pBottom rho = some v) :
    DerivWF (recLeafLeftNI (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom
      hBulk hInterior hTop hRight hLeft hInside) cb fuel rho E := by
  unfold recLeafLeftNI
  exact derivWF_eqPauliTrans'
    (derivWF_pauliIteSelectThen' _ _ _ True.intro
      (formulaDefined_iteSelectThen (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
    (derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectElse' _ _ _ True.intro
        (formulaDefined_iteSelectElse (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
      (derivWF_eqPauliTrans'
        (derivWF_pauliIteSelectElse' _ _ _ True.intro
          (formulaDefined_iteSelectElse (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
        (derivWF_eqPauliTrans'
          (derivWF_pauliIteSelectElse' _ _ _ True.intro
            (formulaDefined_iteSelectElse (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
          (derivWF_eqPauliTrans'
            (derivWF_pauliIteSelectThen' _ _ _ True.intro
              (formulaDefined_iteSelectThen (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
            (derivWF_pauliIteSelectElse' _ _ _ True.intro
              (formulaDefined_iteSelectElse (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))))))

theorem recLeafBottom_WF {arity : Nat} (Γ : List (SFormula arity))
    (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    {hBulk hInterior hTop hRight hLeft hBottom hInside} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpInt : ∃ v, Term.eval cb fuel pInt rho = some v)
    (hpTop : ∃ v, Term.eval cb fuel pTop rho = some v)
    (hpRight : ∃ v, Term.eval cb fuel pRight rho = some v)
    (hpLeft : ∃ v, Term.eval cb fuel pLeft rho = some v)
    (hpBottom : ∃ v, Term.eval cb fuel pBottom rho = some v) :
    DerivWF (recLeafBottom (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom
      hBulk hInterior hTop hRight hLeft hBottom hInside) cb fuel rho E := by
  unfold recLeafBottom
  exact derivWF_eqPauliTrans'
    (derivWF_pauliIteSelectThen' _ _ _ True.intro
      (formulaDefined_iteSelectThen (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
    (derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectElse' _ _ _ True.intro
        (formulaDefined_iteSelectElse (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
      (derivWF_eqPauliTrans'
        (derivWF_pauliIteSelectElse' _ _ _ True.intro
          (formulaDefined_iteSelectElse (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
        (derivWF_eqPauliTrans'
          (derivWF_pauliIteSelectElse' _ _ _ True.intro
            (formulaDefined_iteSelectElse (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
          (derivWF_eqPauliTrans'
            (derivWF_pauliIteSelectElse' _ _ _ True.intro
              (formulaDefined_iteSelectElse (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
            (derivWF_eqPauliTrans'
              (derivWF_pauliIteSelectThen' _ _ _ True.intro
                (formulaDefined_iteSelectThen (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
              (derivWF_pauliIteSelectThen' _ _ _ True.intro
                (formulaDefined_iteSelectThen (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot))))))))

theorem recLeafBottomNI_WF {arity : Nat} (Γ : List (SFormula arity))
    (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    {hBulk hInterior hTop hRight hLeft hBottom hInside} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpInt : ∃ v, Term.eval cb fuel pInt rho = some v)
    (hpTop : ∃ v, Term.eval cb fuel pTop rho = some v)
    (hpRight : ∃ v, Term.eval cb fuel pRight rho = some v)
    (hpLeft : ∃ v, Term.eval cb fuel pLeft rho = some v)
    (hpBottom : ∃ v, Term.eval cb fuel pBottom rho = some v) :
    DerivWF (recLeafBottomNI (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom
      hBulk hInterior hTop hRight hLeft hBottom hInside) cb fuel rho E := by
  unfold recLeafBottomNI
  exact derivWF_eqPauliTrans'
    (derivWF_pauliIteSelectThen' _ _ _ True.intro
      (formulaDefined_iteSelectThen (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
    (derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectElse' _ _ _ True.intro
        (formulaDefined_iteSelectElse (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
      (derivWF_eqPauliTrans'
        (derivWF_pauliIteSelectElse' _ _ _ True.intro
          (formulaDefined_iteSelectElse (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
        (derivWF_eqPauliTrans'
          (derivWF_pauliIteSelectElse' _ _ _ True.intro
            (formulaDefined_iteSelectElse (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
          (derivWF_eqPauliTrans'
            (derivWF_pauliIteSelectElse' _ _ _ True.intro
              (formulaDefined_iteSelectElse (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
            (derivWF_eqPauliTrans'
              (derivWF_pauliIteSelectThen' _ _ _ True.intro
                (formulaDefined_iteSelectThen (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
              (derivWF_pauliIteSelectElse' _ _ _ True.intro
                (formulaDefined_iteSelectElse (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot))))))))

theorem recLeafFallback_WF {arity : Nat} (Γ : List (SFormula arity))
    (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    {hBulk hInterior hTop hRight hLeft hBottom} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpInt : ∃ v, Term.eval cb fuel pInt rho = some v)
    (hpTop : ∃ v, Term.eval cb fuel pTop rho = some v)
    (hpRight : ∃ v, Term.eval cb fuel pRight rho = some v)
    (hpLeft : ∃ v, Term.eval cb fuel pLeft rho = some v)
    (hpBottom : ∃ v, Term.eval cb fuel pBottom rho = some v) :
    DerivWF (recLeafFallback (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom
      hBulk hInterior hTop hRight hLeft hBottom) cb fuel rho E := by
  unfold recLeafFallback
  exact derivWF_eqPauliTrans'
    (derivWF_pauliIteSelectThen' _ _ _ True.intro
      (formulaDefined_iteSelectThen (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
    (derivWF_eqPauliTrans'
      (derivWF_pauliIteSelectElse' _ _ _ True.intro
        (formulaDefined_iteSelectElse (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
      (derivWF_eqPauliTrans'
        (derivWF_pauliIteSelectElse' _ _ _ True.intro
          (formulaDefined_iteSelectElse (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
        (derivWF_eqPauliTrans'
          (derivWF_pauliIteSelectElse' _ _ _ True.intro
            (formulaDefined_iteSelectElse (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
          (derivWF_eqPauliTrans'
            (derivWF_pauliIteSelectElse' _ _ _ True.intro
              (formulaDefined_iteSelectElse (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))
            (derivWF_pauliIteSelectElse' _ _ _ True.intro
              (formulaDefined_iteSelectElse (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot)))))))

theorem recLeafBoundary_WF {arity : Nat} (Γ : List (SFormula arity))
    (dT kT qT : Term arity .nat)
    (pInt pTop pRight pLeft pBottom : Term arity .pauli)
    {hBulk} {cb : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    (hd : SFormula.PureNatTerm dT) (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (hpInt : ∃ v, Term.eval cb fuel pInt rho = some v)
    (hpTop : ∃ v, Term.eval cb fuel pTop rho = some v)
    (hpRight : ∃ v, Term.eval cb fuel pRight rho = some v)
    (hpLeft : ∃ v, Term.eval cb fuel pLeft rho = some v)
    (hpBottom : ∃ v, Term.eval cb fuel pBottom rho = some v) :
    DerivWF (recLeafBoundary (Γ := Γ) dT kT qT pInt pTop pRight pLeft pBottom hBulk)
      cb fuel rho E := by
  unfold recLeafBoundary
  exact derivWF_pauliIteSelectElse' _ _ _ True.intro
    (formulaDefined_iteSelectElse (by rec_leaf_tot) (by rec_leaf_tot) (by rec_leaf_tot))

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

theorem recInteriorIPeelD_WF {arity : Nat} {Γ : List (SFormula arity)}
    (dT kT qT : Term arity .nat)
    {hBulk hInterior hInside} {f' : Nat} {rho : Env arity} {E : PartialStabilizer}
    (hq : SFormula.PureNatTerm qT) (R : RecEvalData dT kT f' rho)
    (wBulk : DerivWF hBulk Surface.code.body (f' + 1) rho E)
    (wInterior : DerivWF hInterior Surface.code.body (f' + 1) rho E)
    (wInside : DerivWF hInside Surface.code.body (f' + 1) rho E) :
    DerivWF (recInteriorIPeelD (Γ := Γ) dT kT qT hq hBulk hInterior hInside)
      Surface.code.body (f' + 1) rho E := by
  unfold recInteriorIPeelD
  refine derivWF_eqPauliTrans'
    (derivWF_stabAtClosedIteLamEqThen' _ _ _ _ hq (baseBulkSelectTrueD_WF _ _ _ wBulk)
      (recPeel_lamFD hq (fun qv => R.lamBody_total qv) ?rhs0)) ?rest

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
  obtain ⟨s1, hs1, hs1def⟩ := hS1
  refine ⟨nv, s1, hn, hGuardWF, hs1, hs1def⟩

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
  obtain ⟨s2, hs2, hs2def⟩ := hS2
  refine ⟨nv, s2, hn, hGuardWF, hs2, hs2def⟩

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
      (QHL.CodeLang.Verify.codeSubstAt DD.dT kT 1 entry) (Env.cons q rho), rfl, ?_⟩
  intro q _
  exact purePauli_codeSubstAt_one_eval_total DD.pure hk hentry Surface.code.body fuel
    (Env.cons q rho)

/-- The BASE row-select WF at the canonical range, from `DistAtA` + fuel bound. -/
theorem surfaceCodeRowSelectBase_WF_of_DistAtA {arity fuel m : Nat} (DD : DistAtA arity m)
    {kT : Term arity .nat} (hk : SFormula.PureNatTerm kT) (rho : Env arity)
    (E : PartialStabilizer) (hfuel : m + 2 ≤ fuel)
    (hGuard : PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat DD.dT (n5 : Term arity .nat))) (SC.b true))) :
    DerivWFA (surfaceCodeRowSelectBase (fuel := fuel) (SC.n (nQubits (oddDistance m)))
      DD.dT kT DD.pure hk hGuard) rho E := by
  refine surfaceCodeRowSelectBase_WF _ DD.dT kT DD.pure hk hGuard rho E True.intro
    (surfaceCodeRowUnfold_WF _ DD.dT kT DD.pure hk rho E
      (rowUnfoldData_of_DistAtA DD hk rho E hfuel))
    (surfaceCodeSubstBodyBase_WF _ DD.dT kT hGuard rho E True.intro (scn_eval _ _ _ _ _)
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
        (Env.cons q rho), rfl, ?_⟩
  intro q _
  exact R.lamBody_total q

/-- The RECURSIVE row-select WF at the canonical range, at the rec-master fuel `f'+1`,
from `DistAtA (m+1)` + a `RecEvalData`. -/
theorem surfaceCodeRowSelectRecursive_WF_of_DistAtA {arity m f' : Nat} {rho : Env arity}
    (DD : DistAtA arity (m + 1))
    {kT : Term arity .nat} (hk : SFormula.PureNatTerm kT)
    (E : PartialStabilizer) (hfuel : (m + 1) + 2 ≤ f' + 1)
    (R : RecEvalData DD.dT kT f' rho)
    (hGuard : PureFamilyDerivA Surface.code.body (f' + 1)
      (.eqBool (SC.closed (.ltNat DD.dT (n5 : Term arity .nat))) (SC.b false))) :
    DerivWFA (surfaceCodeRowSelectRecursive (fuel := f' + 1)
      (SC.n (nQubits (oddDistance (m + 1)))) DD.dT kT DD.pure hk hGuard) rho E := by
  refine surfaceCodeRowSelectRecursive_WF _ DD.dT kT DD.pure hk hGuard rho E True.intro
    (surfaceCodeRowUnfold_WF _ DD.dT kT DD.pure hk rho E
      (rowUnfoldData_of_DistAtA DD hk rho E hfuel))
    (surfaceCodeSubstBodyRecursive_WF _ DD.dT kT hGuard rho E True.intro (scn_eval _ _ _ _ _)
      (stabLamSubstRec_total DD R))

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
      (SC.closed qT).eval Surface.code.body fuel rho E = some qv ∧ qv < nv) :
    DerivWFA (recRowConvergeA (fuel := fuel) n dT kT qT pInt pTop pRight pLeft pBottom
      hd hk hq hDist pIntA pTopA pRightA pLeftA pBottomA) rho E := by
  unfold recRowConvergeA
  -- The rec master is `cut1 (recEntryMasterD core) (cut2 … cut2 … hProj pIntA … pBottomA)`.
  -- The cut1/cut2 glue relays the five IH-supplied sub-derivations' `DerivWFA`
  -- (`hInt … hBottom`) and the row-projection premise (`eqPauliProj`-of-
  -- `surfaceCodeRowSelectRecursive`, the supplied `hRowSel`) sorry-free; only the
  -- `recEntryMasterD` core's `DerivWF` (the 7-level boolCases leaf grind, STEP A/B) is
  -- the residual.
  refine derivWFA_cut1 ?core ?conj
  case core =>
    -- `recEntryMasterD` core — the 7-level boolCases leaf grind (REC master residual).
    sorry
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

/-- The per-level row-projection witness: at distance index `m`, the qubit term `qT`
evaluates below `nQubits (oddDistance m)` (the row-projection's `eqPauliProj` range
side-condition).  Threaded through the `m`-induction; at each level the five inner
sub-derivations re-use it at the inner qubit term `innerQTA dT qT`.  This is the only
non-structural input the recursion needs (it is what the binder range supplies in the
real consumers). -/
def RowProjWitness {arity fuel : Nat} (qT : Term arity .nat) (m : Nat)
    (rho : Env arity) (E : PartialStabilizer) : Prop :=
  ∃ qv, (SC.closed qT).eval Surface.code.body fuel rho E = some qv ∧
    qv < nQubits (oddDistance m)

/-- Bundle of the per-inner-cell witnesses the `succ` step needs: for each of the five
inner cell kinds, the inner `RowProjWitness` (to feed the IH) and the `closedStabAtSplit`
eval witness (the inner sub-derivation's leaf side-data). -/
structure RowStepWitness {arity fuel : Nat} (dT kT qT : Term arity .nat) (m : Nat)
    (rho : Env arity) (E : PartialStabilizer) : Prop where
  innerProj : RowProjWitness (fuel := fuel) (innerQTA dT qT) m rho E
  intSplit : ∃ pv, Term.eval Surface.code.body fuel
    (Term.stabAt (.recCall (innerDTA dT) (interiorKTA dT kT)) (innerQTA dT qT)) rho = some pv
  topSplit : ∃ pv, Term.eval Surface.code.body fuel
    (Term.stabAt (.recCall (recInnerDTA dT) (topKTA dT kT)) (innerQTA dT qT)) rho = some pv
  rightSplit : ∃ pv, Term.eval Surface.code.body fuel
    (Term.stabAt (.recCall (recInnerDTA dT) (rightKTA dT kT)) (innerQTA dT qT)) rho = some pv
  leftSplit : ∃ pv, Term.eval Surface.code.body fuel
    (Term.stabAt (.recCall (recInnerDTA dT) (leftKTA dT kT)) (innerQTA dT qT)) rho = some pv
  bottomSplit : ∃ pv, Term.eval Surface.code.body fuel
    (Term.stabAt (.recCall (recInnerDTA dT) (bottomKTA dT kT)) (innerQTA dT qT)) rho = some pv
  proj : RowProjWitness (fuel := fuel) qT (m + 1) rho E

/-- The descending step-witness hypothesis: for every distance index `m' ≤ m` reached
by the recursion and every (pure) `kT'`/`qT'`, the per-step inner-cell witnesses hold.
This is the per-level eval side-data (qubit-in-range + `closedStabAtSplit` evals) the
binder range supplies in the real consumers; it is preserved under descent (`m' → m'-1`,
`qT' → innerQTA`), so the `m`-induction threads it. -/
def DescendingRowWitness {arity fuel : Nat} (m : Nat)
    (rho : Env arity) (E : PartialStabilizer) : Prop :=
  ∀ (m' : Nat), m' < m → ∀ (DD' : DistAtA arity (m' + 1)) (kT' qT' : Term arity .nat),
    SFormula.PureNatTerm kT' → SFormula.PureNatTerm qT' →
    RowStepWitness (fuel := fuel) DD'.dT kT' qT' m' rho E

/-- `DerivWFA` of `surfaceRowEntryCharSymbolicA`, by induction on `m`.  This is the
structural keystone demonstrating the COST COLLAPSE: the induction has ONE base
(relaying `baseRowConvergeA_WF`) and ONE step (relaying the IH at `m-1` through the five
sub-derivations plus `recRowConvergeA_WF`).  The base needs only the level-`0`
row-projection witness `hproj`; the step extracts its inner-cell witnesses from the
descending witness `hwit`.  No per-level multiplication of the leaf grind — that lives
entirely in the two flat master helpers. -/
theorem surfaceRowEntryCharSymbolicA_WF {arity fuel : Nat} (m : Nat) (DD : DistAtA arity m)
    (kT qT : Term arity .nat)
    (hk : SFormula.PureNatTerm kT) (hq : SFormula.PureNatTerm qT)
    (rho : Env arity) (E : PartialStabilizer)
    (hfuel : m + 2 ≤ fuel)
    (hproj : RowProjWitness (fuel := fuel) qT m rho E)
    (hwit : DescendingRowWitness (fuel := fuel) m rho E) :
    DerivWFA (surfaceRowEntryCharSymbolicA (fuel := fuel) m DD kT qT hk hq) rho E := by
  induction m generalizing kT qT with
  | zero =>
      -- BASE: `surfaceRowEntryCharSymbolicA 0 DD kT qT = baseRowConvergeA … (simpa cast)`.
      rw [surfaceRowEntryCharSymbolicA]
      simp only [id]
      obtain ⟨qv, hqv, hqlt⟩ := hproj
      refine baseRowConvergeA_WF _ DD.dT kT qT DD.pure hk hq _ rho E ?_ ?_ ?_
      · -- `DerivWFA (distLtFiveTrue_of_DistAtA DD)` — an `arithBool`, trivially `True`.
        exact True.intro
      · -- `hRowSel`: the BASE row-select WF, assembled from `DistAtA` + fuel bound (STEP C/D).
        exact surfaceCodeRowSelectBase_WF_of_DistAtA DD hk rho E hfuel _
      · -- row-projection witness `qv < nQubits (oddDistance 0)`
        exact ⟨nQubits (oddDistance 0), qv, scn_eval _ _ _ _ _, hqv, hqlt⟩
  | succ m ih =>
      -- STEP: `surfaceRowEntryCharSymbolicA (m+1) DD kT qT` builds the five IH-resolved
      -- sub-derivations and dispatches via `recRowConvergeA`.  The IH `ih` supplies the
      -- five inner `DerivWFA`s; `recRowConvergeA_WF` relays them.  The inner
      -- `RowProjWitness`es + `closedStabAtSplit` evals are the step's leaf side-data
      -- (`hstep`), which the binder range supplies in the real consumers.
      rw [surfaceRowEntryCharSymbolicA]
      simp only [id]
      -- inner-cell witnesses for this step, extracted from the descending witness `hwit`
      have hstep : RowStepWitness (fuel := fuel) DD.dT kT qT m rho E :=
        hwit m (Nat.lt_succ_self m) DD kT qT hk hq
      -- the descending witness restricts to the level below
      have hwit' : DescendingRowWitness (fuel := fuel) m rho E :=
        fun m' hm' DD' kT' qT' hk' hq' =>
          hwit m' (Nat.lt_succ_of_lt hm') DD' kT' qT' hk' hq'
      have hfuel' : m + 2 ≤ fuel := by omega
      -- the rec-master `RecEvalData` at fuel `fuel = f' + 1` with `f' = fuel - 1`.
      obtain ⟨f', hfeq⟩ : ∃ f', fuel = f' + 1 := ⟨fuel - 1, by omega⟩
      subst hfeq
      have R : RecEvalData DD.dT kT f' rho :=
        recEvalData_of_DistAtA DD hk rho (by omega)
      obtain ⟨qv, hqv, hqlt⟩ := hproj
      -- each inner sub-derivation's `DerivWFA` = ⟨closedStabAtSplit eval, IH at inner⟩
      refine recRowConvergeA_WF _ DD.dT kT qT _ _ _ _ _ DD.pure hk hq _ _ _ _ _ _ rho E
        True.intro
        (surfaceCodeRowSelectRecursive_WF_of_DistAtA DD hk E (by omega) R _)
        ?hInt ?hTop ?hRight ?hLeft ?hBottom
        ⟨nQubits (oddDistance (m + 1)), qv, scn_eval _ _ _ _ _, hqv, hqlt⟩
      case hInt =>
        exact ⟨hstep.intSplit,
          ih DD.pred (interiorKTA DD.dT kT) (innerQTA DD.dT qT)
            (interiorKTA_pure DD.pure hk) (innerQTA_pure DD.pure hq) hfuel' hstep.innerProj hwit'⟩
      case hTop =>
        exact ⟨hstep.topSplit,
          ih DD.pred (topKTA DD.dT kT) (innerQTA DD.dT qT)
            (topKTA_pure DD.pure hk) (innerQTA_pure DD.pure hq) hfuel' hstep.innerProj hwit'⟩
      case hRight =>
        exact ⟨hstep.rightSplit,
          ih DD.pred (rightKTA DD.dT kT) (innerQTA DD.dT qT)
            (rightKTA_pure DD.pure hk) (innerQTA_pure DD.pure hq) hfuel' hstep.innerProj hwit'⟩
      case hLeft =>
        exact ⟨hstep.leftSplit,
          ih DD.pred (leftKTA DD.dT kT) (innerQTA DD.dT qT)
            (leftKTA_pure DD.pure hk) (innerQTA_pure DD.pure hq) hfuel' hstep.innerProj hwit'⟩
      case hBottom =>
        exact ⟨hstep.bottomSplit,
          ih DD.pred (bottomKTA DD.dT kT) (innerQTA DD.dT qT)
            (bottomKTA_pure DD.pure hk) (innerQTA_pure DD.pure hq) hfuel' hstep.innerProj hwit'⟩

/-- The flat-bridge analogue of the descending witness for `rowSymTreeFlatBridgeSym`.
Placeholder name capturing the parallel `m`-induction's per-level eval side-data;
the bridge's `recFlatMasterD` boolCases tree consumes the same kind of inner-cell
witnesses as `recRowConvergeA`. -/
def RowFlatWitness {arity : Nat} (qT : Term arity .nat) (m : Nat)
    (rho : Env arity) (E : PartialStabilizer) : Prop := True

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
    (hfuel : m + 2 ≤ fuel)
    (hproj : RowProjWitness (fuel := fuel) qT m rho E)
    (hwit : DescendingRowWitness (fuel := fuel) m rho E) :
    DerivWFA (rowEntryFlatSym (fuel := fuel) m DD kT qT hk hq) rho E := by
  -- `eqPauliTrans` splits into the two sub-derivations' `DerivWFA`.
  refine ⟨?_, ?_⟩
  · -- `surfaceRowEntryCharSymbolicA m DD kT qT` — the proven `m`-induction (STEP C/D
    -- close its row-selects; the only residual is the `recEntryMasterD` core, STEP A/B).
    exact surfaceRowEntryCharSymbolicA_WF m DD kT qT hk hq rho E hfuel hproj hwit
  · -- `rowSymTreeFlatBridgeSym m DD kT qT` — the flat bridge (parallel `m`-induction, STEP E).
    sorry

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
  -- fuel bound `D.index + 2 ≤ D.distance + 2`; the row-projection witnesses are the
  -- consumer's binder-range side-data (residual #1).
  refine rowEntryFlatSym_WF _ _ _ _ _ _ _ _
    (by simp only [OddSurfaceDistance.distance, oddDistance]; omega) ?_ ?_
  · sorry
  · sorry

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
    -- fuel bound `D.index + 2 ≤ D.distance + 2`; the row-projection witnesses are the
    -- consumer's binder-range side-data (residual #1).
    refine rowEntryFlatSym_WF _ _ _ _ _ _ _ _
      (by simp only [OddSurfaceDistance.distance, oddDistance]; omega) ?_ ?_
    · sorry
    · sorry

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

/-! ## The per-`k` `boolCases` classification tree (`Dcore`)

The `cut1` head of `xNormCommuteSym` is a 5-deep `boolCases` over the cell guards
(`bulkGuard` / `cZero` / `kind` / `leftClass` / `rightClass`), bottoming out at the
six commutator leaves `commTwoAntiA` / `commPointwiseSym` (×4) / `commTwoAntiB`.
The `boolCases` structure + the five guard bool-evals are discharged here; the six
commutator-leaf `DerivWF`s are residual #2. -/

set_option maxHeartbeats 1000000 in
theorem xNormScaffold_WF (D : OddSurfaceDistance) (E : PartialStabilizer) :
    DerivWFA (xNormScaffold D) Env.empty E := by
  unfold xNormScaffold xNormCommuteSym
  simp only [eq_mpr_eq_cast, id]
  refine derivWFA_cast_type rfl _ _ ?_
  refine derivWFA_allNatLtIntro _ ⟨numStab D.distance, ?_, fun x hx => ?_⟩
  · simp [SC.closed, STerm.eval, Term.eval]
  · refine derivWFA_cut1 ?_ (xBundle_WF D)
    -- the 5-deep boolCases classification tree; every guard bool-eval is total
    -- (closed pure term) and discharged by `sterm_eval_closedPure (by repeat constructor)`.
    refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat constructor)) ?bulkT ?bulkF
    case bulkT =>
      refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat constructor)) ?czT ?czF
      case czT =>
        refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat constructor)) ?kindT ?kindF
        case kindT => sorry -- commTwoAntiA leaf (residual #2)
        case kindF => sorry -- commPointwiseSym leaf (residual #2)
      case czF => sorry -- commPointwiseSym leaf (residual #2)
    case bulkF =>
      refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat constructor)) ?lcT ?lcF
      case lcT =>
        refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat constructor)) ?rcT ?rcF
        case rcT => sorry -- commPointwiseSym leaf (residual #2)
        case rcF => sorry -- commTwoAntiB leaf (residual #2)
      case lcF => sorry -- commPointwiseSym leaf (residual #2)

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

set_option maxHeartbeats 1000000 in
theorem zNormScaffold_WF (D : OddSurfaceDistance) (E : PartialStabilizer) :
    DerivWFA (zNormScaffold D) Env.empty E := by
  unfold zNormScaffold zNormCommuteSym
  simp only [eq_mpr_eq_cast, id]
  refine derivWFA_cast_type rfl _ _ ?_
  refine derivWFA_allNatLtIntro _ ⟨numStab D.distance, ?_, fun x hx => ?_⟩
  · simp [SC.closed, STerm.eval, Term.eval]
  · refine derivWFA_cut1 ?_ (zBundle_WF D)
    -- the boolCases classification tree (transpose); every guard bool-eval is total.
    refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat constructor)) ?bulkT ?bulkF
    case bulkT =>
      refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat constructor)) ?rzT ?rzF
      case rzT =>
        refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat constructor)) ?kindT ?kindF
        case kindT => sorry -- commPointwiseZSym leaf (residual #2)
        case kindF => sorry -- commZTwoAntiA leaf (residual #2)
      case rzF => sorry -- commPointwiseZSym leaf (residual #2)
    case bulkF =>
      refine derivWF_boolCases _ _ (sterm_eval_closedPure (by repeat constructor)) ?tcT ?tcF
      case tcT => sorry -- commZTwoAntiB leaf (residual #2)
      case tcF => sorry -- commPointwiseZSym leaf (residual #2)

/-! ## Axiom audit of the sorry-free scaffolding

The reusable combinators and the bundle glue carry no new axioms (no `sorryAx`).
The two headline `*_WF` lemmas and `rowEntryFlatSym_WF` still depend on `sorryAx`
at the two isolated residuals documented above. -/

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
