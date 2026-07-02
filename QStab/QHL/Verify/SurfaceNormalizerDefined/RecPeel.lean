import QStab.QHL.Verify.SurfaceNormalizerDefined.RecLeaf

/-!
# Normalizer sub-tree definedness — RecPeel

STEP A — the recursive-peel `DerivWF` lemmas and their head-form infrastructure (RecOk leaf
totality + lam-body FormulaDefined).
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

set_option maxHeartbeats 1600000

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

end QHL.CodeLang.Surface.Verify
