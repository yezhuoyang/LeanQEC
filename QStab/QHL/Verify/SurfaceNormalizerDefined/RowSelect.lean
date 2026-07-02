import QStab.QHL.Verify.SurfaceNormalizerDefined.RecPeel

/-!
# Normalizer sub-tree definedness — RowSelect

Residual leaf #1 (flat row-entry totality): the `m`-induction skeleton and STEP C/D/D'
row-select `DerivWFA` / WF providers (per-width and all-width).
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

set_option maxHeartbeats 1600000

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

end QHL.CodeLang.Surface.Verify
