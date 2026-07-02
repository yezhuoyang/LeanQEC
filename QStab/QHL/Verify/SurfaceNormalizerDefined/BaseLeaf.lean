import QStab.QHL.Verify.SurfaceNormalizerDefined.PurePauliCerts

/-!
# Normalizer sub-tree definedness — BaseLeaf

Per-peel / per-leaf `DerivWF` lemmas for the BASE master leaves: the `baseEntry` head-`ite`
definedness bridge and the base-leaf `pauliIteSelect` chains over `baseLeafTreeTA`.
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

set_option maxHeartbeats 1600000

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

end QHL.CodeLang.Surface.Verify
