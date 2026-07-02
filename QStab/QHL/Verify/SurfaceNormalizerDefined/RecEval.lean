import QStab.QHL.Verify.SurfaceNormalizerDefined.BaseMaster

/-!
# Normalizer sub-tree definedness — RecEval

STEP 0 (`RecEvalData` per-level rec-eval side-data), STEP 2 (rec-peel lam-node FormulaDefined
discharger), and STEP 3 (rec-leaf `pauliIteSelect` dischargers over `recLeafTreeTA`).
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

set_option maxHeartbeats 1600000

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

end QHL.CodeLang.Surface.Verify
