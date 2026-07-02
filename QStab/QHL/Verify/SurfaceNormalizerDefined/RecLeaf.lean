import QStab.QHL.Verify.SurfaceNormalizerDefined.RecEval

/-!
# Normalizer sub-tree definedness — RecLeaf

The rec-leaf `DerivWF` lemmas (explicit-combinator chains over `recLeafTreeTA`), the named
guard-purity lemmas, and the per-cell totality lemmas (each proved once, bottom-up).
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

set_option maxHeartbeats 1600000

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

end QHL.CodeLang.Surface.Verify
