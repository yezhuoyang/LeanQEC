import QStab.QHL.Verify.SurfaceRowsCommuteDefined.Dispatch

/-!
# Rows-commute definedness — TypeClosers

The same-type closers and ∀∀ same-type families (via the conditional `impIntro` fix),
and the different-type generic two-anti closer WF.
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

set_option maxHeartbeats 1600000

/-! ## Same-type closers (pairCommutePointwise_WF + withLeafG_WF contradiction handlers) -/

/-- WF of `pairCommuteSameTypeX` — both rows X-type ⟹ commute.  The two anti-handlers
re-resolve the offending row's leaf and contradict (an X-type row never yields a `Z`
leaf), via `leafNotPandZ_WF` (leaf-value clash) and `eqBoolContra_WF` (class-guard clash). -/
theorem pairCommuteSameTypeX_WF (D : OddSurfaceDistance) {Γ : List (SFormula 2)}
    {hEntryAF : SFormula.Deriv Γ (entryAQuant D)} {hEntryBF : SFormula.Deriv Γ (entryBQuant D)}
    {hk1X : SFormula.Deriv Γ (k1IsX D true)} {hk2X : SFormula.Deriv Γ (k2IsX D true)}
    {hExcl1 : SFormula.Deriv Γ (typeExclF D k1P)} {hExcl2 : SFormula.Deriv Γ (typeExclF D k2P)}
    {rho : Env 2} {E : PartialStabilizer}
    (wEntryAF : DerivWF hEntryAF Surface.code.body (D.distance + 2) rho E)
    (wEntryBF : DerivWF hEntryBF Surface.code.body (D.distance + 2) rho E)
    (wk1X : DerivWF hk1X Surface.code.body (D.distance + 2) rho E)
    (wk2X : DerivWF hk2X Surface.code.body (D.distance + 2) rho E)
    (wExcl1 : DerivWF hExcl1 Surface.code.body (D.distance + 2) rho E)
    (wExcl2 : DerivWF hExcl2 Surface.code.body (D.distance + 2) rho E)
    (hCtx : SFormula.ContextHolds Surface.code.body (D.distance + 2) rho E Γ) :
    DerivWF (pairCommuteSameTypeX D hEntryAF hEntryBF hk1X hk2X hExcl1 hExcl2)
      Surface.code.body (D.distance + 2) rho E := by
  unfold pairCommuteSameTypeX
  refine pairCommutePointwise_WF D wEntryAF wEntryBF ?wAntiXZ ?wAntiZX hCtx
  case wAntiXZ =>
    intro x Δ' lift liftWF hA wA hB wB
    have wk2Xd := liftWF (cw1_WF (derivWF_weakenFresh wk2X))
    have wExcl2d := liftWF (cw1_WF (derivWF_weakenFresh wExcl2))
    have wxnbz := derivWF_andElimLeft' wExcl2d
    have wxnrz := derivWF_andElimLeft' (derivWF_andElimRight' wExcl2d)
    have wxnlz := derivWF_andElimLeft' (derivWF_andElimRight' (derivWF_andElimRight' wExcl2d))
    refine withLeafG_WF D (.var _) _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro Δ'' lift2 liftWF2 hI wI
      exact leafNotPandZ_WF D (.var _) Pauli.I rfl wI (liftWF2 wB)
    · intro Δ'' lift2 liftWF2 hL wL hb wb hk wk
      exact eqBoolContra_WF _ wk (derivWF_mp (derivWF_mp (liftWF2 wxnbz) (liftWF2 wk2Xd)) wb)
    · intro Δ'' lift2 liftWF2 hX wX hb wb hk wk
      exact leafNotPandZ_WF D (.var _) Pauli.X rfl wX (liftWF2 wB)
    · intro Δ'' lift2 liftWF2 hX wX hb wb ht wt
      exact leafNotPandZ_WF D (.var _) Pauli.X rfl wX (liftWF2 wB)
    · intro Δ'' lift2 liftWF2 hL wL hb wb ht wt hr wr
      exact eqBoolContra_WF _ wr
        (derivWF_mp (derivWF_mp (derivWF_mp (liftWF2 wxnrz) (liftWF2 wk2Xd)) wb) wt)
    · intro Δ'' lift2 liftWF2 hL wL hb wb ht wt hr wr hlc wlc
      exact eqBoolContra_WF _ wlc
        (derivWF_mp (derivWF_mp (derivWF_mp (derivWF_mp (liftWF2 wxnlz) (liftWF2 wk2Xd)) wb) wt) wr)
    · intro Δ'' lift2 liftWF2 hX wX hb wb ht wt hr wr hlc wlc
      exact leafNotPandZ_WF D (.var _) Pauli.X rfl wX (liftWF2 wB)
  case wAntiZX =>
    intro x Δ' lift liftWF hA wA hB wB
    have wk1Xd := liftWF (cw1_WF (derivWF_weakenFresh wk1X))
    have wExcl1d := liftWF (cw1_WF (derivWF_weakenFresh wExcl1))
    have wxnbz := derivWF_andElimLeft' wExcl1d
    have wxnrz := derivWF_andElimLeft' (derivWF_andElimRight' wExcl1d)
    have wxnlz := derivWF_andElimLeft' (derivWF_andElimRight' (derivWF_andElimRight' wExcl1d))
    refine withLeafG_WF D (.var _) _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro Δ'' lift2 liftWF2 hI wI
      exact leafNotPandZ_WF D (.var _) Pauli.I rfl wI (liftWF2 wA)
    · intro Δ'' lift2 liftWF2 hL wL hb wb hk wk
      exact eqBoolContra_WF _ wk (derivWF_mp (derivWF_mp (liftWF2 wxnbz) (liftWF2 wk1Xd)) wb)
    · intro Δ'' lift2 liftWF2 hX wX hb wb hk wk
      exact leafNotPandZ_WF D (.var _) Pauli.X rfl wX (liftWF2 wA)
    · intro Δ'' lift2 liftWF2 hX wX hb wb ht wt
      exact leafNotPandZ_WF D (.var _) Pauli.X rfl wX (liftWF2 wA)
    · intro Δ'' lift2 liftWF2 hL wL hb wb ht wt hr wr
      exact eqBoolContra_WF _ wr
        (derivWF_mp (derivWF_mp (derivWF_mp (liftWF2 wxnrz) (liftWF2 wk1Xd)) wb) wt)
    · intro Δ'' lift2 liftWF2 hL wL hb wb ht wt hr wr hlc wlc
      exact eqBoolContra_WF _ wlc
        (derivWF_mp (derivWF_mp (derivWF_mp (derivWF_mp (liftWF2 wxnlz) (liftWF2 wk1Xd)) wb) wt) wr)
    · intro Δ'' lift2 liftWF2 hX wX hb wb ht wt hr wr hlc wlc
      exact leafNotPandZ_WF D (.var _) Pauli.X rfl wX (liftWF2 wA)

/-- WF of `pairCommuteSameTypeZ` — both rows Z-type ⟹ commute (dual of the X case;
`leafNotPandX_WF` for the leaf clashes, `eqBoolContra_WF` for the X-class guard clashes). -/
theorem pairCommuteSameTypeZ_WF (D : OddSurfaceDistance) {Γ : List (SFormula 2)}
    {hEntryAF : SFormula.Deriv Γ (entryAQuant D)} {hEntryBF : SFormula.Deriv Γ (entryBQuant D)}
    {hk1X : SFormula.Deriv Γ (k1IsX D false)} {hk2X : SFormula.Deriv Γ (k2IsX D false)}
    {hExcl1 : SFormula.Deriv Γ (typeExclF D k1P)} {hExcl2 : SFormula.Deriv Γ (typeExclF D k2P)}
    {rho : Env 2} {E : PartialStabilizer}
    (wEntryAF : DerivWF hEntryAF Surface.code.body (D.distance + 2) rho E)
    (wEntryBF : DerivWF hEntryBF Surface.code.body (D.distance + 2) rho E)
    (wk1X : DerivWF hk1X Surface.code.body (D.distance + 2) rho E)
    (wk2X : DerivWF hk2X Surface.code.body (D.distance + 2) rho E)
    (wExcl1 : DerivWF hExcl1 Surface.code.body (D.distance + 2) rho E)
    (wExcl2 : DerivWF hExcl2 Surface.code.body (D.distance + 2) rho E)
    (hCtx : SFormula.ContextHolds Surface.code.body (D.distance + 2) rho E Γ) :
    DerivWF (pairCommuteSameTypeZ D hEntryAF hEntryBF hk1X hk2X hExcl1 hExcl2)
      Surface.code.body (D.distance + 2) rho E := by
  unfold pairCommuteSameTypeZ
  refine pairCommutePointwise_WF D wEntryAF wEntryBF ?wAntiXZ ?wAntiZX hCtx
  case wAntiXZ =>
    intro x Δ' lift liftWF hA wA hB wB
    have wk1Xd := liftWF (cw1_WF (derivWF_weakenFresh wk1X))
    have wExcl1d := liftWF (cw1_WF (derivWF_weakenFresh wExcl1))
    have wznbx := derivWF_andElimLeft'
      (derivWF_andElimRight' (derivWF_andElimRight' (derivWF_andElimRight' wExcl1d)))
    have wzntx := derivWF_andElimLeft' (derivWF_andElimRight'
      (derivWF_andElimRight' (derivWF_andElimRight' (derivWF_andElimRight' wExcl1d))))
    have wznbtx := derivWF_andElimRight' (derivWF_andElimRight'
      (derivWF_andElimRight' (derivWF_andElimRight' (derivWF_andElimRight' wExcl1d))))
    refine withLeafG_WF D (.var _) _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro Δ'' lift2 liftWF2 hI wI
      exact leafNotPandX_WF D (.var _) Pauli.I rfl wI (liftWF2 wA)
    · intro Δ'' lift2 liftWF2 hZ wZ hb wb hk wk
      exact leafNotPandX_WF D (.var _) Pauli.Z rfl wZ (liftWF2 wA)
    · intro Δ'' lift2 liftWF2 hL wL hb wb hk wk
      exact eqBoolContra_WF _ (derivWF_mp (derivWF_mp (liftWF2 wznbx) (liftWF2 wk1Xd)) wb) wk
    · intro Δ'' lift2 liftWF2 hL wL hb wb ht wt
      exact eqBoolContra_WF _ wt (derivWF_mp (derivWF_mp (liftWF2 wzntx) (liftWF2 wk1Xd)) wb)
    · intro Δ'' lift2 liftWF2 hZ wZ hb wb ht wt hr wr
      exact leafNotPandX_WF D (.var _) Pauli.Z rfl wZ (liftWF2 wA)
    · intro Δ'' lift2 liftWF2 hZ wZ hb wb ht wt hr wr hlc wlc
      exact leafNotPandX_WF D (.var _) Pauli.Z rfl wZ (liftWF2 wA)
    · intro Δ'' lift2 liftWF2 hL wL hb wb ht wt hr wr hlc wlc
      exact eqBoolContra_WF _
        (derivWF_mp (derivWF_mp (derivWF_mp (liftWF2 wznbtx) (liftWF2 wk1Xd)) wb) wt) wlc
  case wAntiZX =>
    intro x Δ' lift liftWF hA wA hB wB
    have wk2Xd := liftWF (cw1_WF (derivWF_weakenFresh wk2X))
    have wExcl2d := liftWF (cw1_WF (derivWF_weakenFresh wExcl2))
    have wznbx := derivWF_andElimLeft'
      (derivWF_andElimRight' (derivWF_andElimRight' (derivWF_andElimRight' wExcl2d)))
    have wzntx := derivWF_andElimLeft' (derivWF_andElimRight'
      (derivWF_andElimRight' (derivWF_andElimRight' (derivWF_andElimRight' wExcl2d))))
    have wznbtx := derivWF_andElimRight' (derivWF_andElimRight'
      (derivWF_andElimRight' (derivWF_andElimRight' (derivWF_andElimRight' wExcl2d))))
    refine withLeafG_WF D (.var _) _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro Δ'' lift2 liftWF2 hI wI
      exact leafNotPandX_WF D (.var _) Pauli.I rfl wI (liftWF2 wB)
    · intro Δ'' lift2 liftWF2 hZ wZ hb wb hk wk
      exact leafNotPandX_WF D (.var _) Pauli.Z rfl wZ (liftWF2 wB)
    · intro Δ'' lift2 liftWF2 hL wL hb wb hk wk
      exact eqBoolContra_WF _ (derivWF_mp (derivWF_mp (liftWF2 wznbx) (liftWF2 wk2Xd)) wb) wk
    · intro Δ'' lift2 liftWF2 hL wL hb wb ht wt
      exact eqBoolContra_WF _ wt (derivWF_mp (derivWF_mp (liftWF2 wzntx) (liftWF2 wk2Xd)) wb)
    · intro Δ'' lift2 liftWF2 hZ wZ hb wb ht wt hr wr
      exact leafNotPandX_WF D (.var _) Pauli.Z rfl wZ (liftWF2 wB)
    · intro Δ'' lift2 liftWF2 hZ wZ hb wb ht wt hr wr hlc wlc
      exact leafNotPandX_WF D (.var _) Pauli.Z rfl wZ (liftWF2 wB)
    · intro Δ'' lift2 liftWF2 hL wL hb wb ht wt hr wr hlc wlc
      exact eqBoolContra_WF _
        (derivWF_mp (derivWF_mp (derivWF_mp (liftWF2 wznbtx) (liftWF2 wk2Xd)) wb) wt) wlc

/-! ## The ∀∀ same-type families (via derivWF_impIntro_cond — the conditional-impIntro fix) -/

theorem sameTypeXFamily_WF (D : OddSurfaceDistance) {E : PartialStabilizer} :
    DerivWFA (sameTypeXFamily D) Env.empty E := by
  unfold sameTypeXFamily
  refine derivWFA_allNatLtIntro _ ⟨numStab D.distance,
    by simp [SC.closed, STerm.eval, Term.eval], fun k1 _ => ?_⟩
  refine derivWFA_allNatLtIntro _ ⟨numStab D.distance,
    by simp [SC.closed, STerm.eval, Term.eval, Term.lift], fun k2 _ => ?_⟩
  refine derivWFA_cut1 ?core (pairBundle_WF D)
  refine derivWF_impIntro_cond ?fdA (fun hk1 => derivWF_impIntro_cond ?fdB (fun hk2 => ?inner))
  case fdA =>
    exact formulaDefined_eqBool (sterm_eval_closedPure (by repeat (first | assumption | constructor)))
      (sterm_eval_b _)
  case fdB =>
    exact formulaDefined_eqBool (sterm_eval_closedPure (by repeat (first | assumption | constructor)))
      (sterm_eval_b _)
  case inner =>
    refine pairCommuteSameTypeX_WF D (by comm_deriv_wf) (by comm_deriv_wf) (by comm_deriv_wf)
      (by comm_deriv_wf) (by comm_deriv_wf) (by comm_deriv_wf) ?hCtx
    intro F hF
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with h | h | h <;> subst h
    · exact hk2
    · exact hk1
    · exact pairBundleHolds D _ E

theorem sameTypeZFamily_WF (D : OddSurfaceDistance) {E : PartialStabilizer} :
    DerivWFA (sameTypeZFamily D) Env.empty E := by
  unfold sameTypeZFamily
  refine derivWFA_allNatLtIntro _ ⟨numStab D.distance,
    by simp [SC.closed, STerm.eval, Term.eval], fun k1 _ => ?_⟩
  refine derivWFA_allNatLtIntro _ ⟨numStab D.distance,
    by simp [SC.closed, STerm.eval, Term.eval, Term.lift], fun k2 _ => ?_⟩
  refine derivWFA_cut1 ?core (pairBundle_WF D)
  refine derivWF_impIntro_cond ?fdA (fun hk1 => derivWF_impIntro_cond ?fdB (fun hk2 => ?inner))
  case fdA =>
    exact formulaDefined_eqBool (sterm_eval_closedPure (by repeat (first | assumption | constructor)))
      (sterm_eval_b _)
  case fdB =>
    exact formulaDefined_eqBool (sterm_eval_closedPure (by repeat (first | assumption | constructor)))
      (sterm_eval_b _)
  case inner =>
    refine pairCommuteSameTypeZ_WF D (by comm_deriv_wf) (by comm_deriv_wf) (by comm_deriv_wf)
      (by comm_deriv_wf) (by comm_deriv_wf) (by comm_deriv_wf) ?hCtx
    intro F hF
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with h | h | h <;> subst h
    · exact hk2
    · exact hk1
    · exact pairBundleHolds D _ E

/-! ## Different-type path: the generic two-anti closer WF -/

/-- Eval-totality of `stabAt (recCall (dP2 D) kP) q` at a pure qubit `q` (recCall recipe). -/
theorem rowStabEval (D : OddSurfaceDistance) (kP : Term 2 .nat) (hkPp : SFormula.PureNatTerm kP)
    {q : Term 2 .nat} (hqp : SFormula.PureNatTerm q) (rho : Env 2) (E : PartialStabilizer) :
    ∃ v, (STerm.stabAt (SC.closed (.recCall (dP2 D) kP)) (SC.closed q)).eval
        Surface.code.body (D.distance + 2) rho E = some v := by
  obtain ⟨sa, hsa, htot⟩ := recCall_total_symbolicDK_all D.index (D.distance + 2)
    (by simp only [OddSurfaceDistance.distance, oddDistance]; omega) rho
    (dT := dP2 D) (kT := kP)
    (fun f' => by simp [dP2, Term.eval, Term.lift, OddSurfaceDistance.distance, oddDistance]) hkPp
  obtain ⟨qv, hqv⟩ := hqp.eval_total Surface.code.body (D.distance + 2) rho
  exact sterm_eval_stabAt (sv := sa) (qv := qv)
    (by simpa [SC.closed, STerm.eval] using hsa) (by simpa [SC.closed, STerm.eval] using hqv) (htot qv)

/-- WF of `commTwoAntiXZ` — the generic overlapping (X-vs-Z) two-anti closer.  Mirrors
the normalizer's `commTwoAntiA_WF`: `commutesOfTwoAnti`'s six children, with the two
`anticommutesTransport` definedness leaves discharged from the rowA/rowB stab evals at
`q0`/`q1` (recCall recipe).  `q0`/`q1` are pure closed arithmetic coords. -/
theorem commTwoAntiXZ_WF (D : OddSurfaceDistance) {Γ : List (SFormula 2)}
    (q0 q1 : Term 2 .nat) (hq0p : SFormula.PureNatTerm q0) (hq1p : SFormula.PureNatTerm q1)
    {hLt0 : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed q0) (nP2 D))}
    {hLt1 : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed q1) (nP2 D))}
    {hNe : SFormula.Deriv Γ (.eqBool (SC.closed (.eqNat q0 q1)) (SC.b false))}
    {hAX0 : SFormula.Deriv Γ (.eqPauli (.stabAt (rowA D) (SC.closed q0)) (SC.p Pauli.X))}
    {hAX1 : SFormula.Deriv Γ (.eqPauli (.stabAt (rowA D) (SC.closed q1)) (SC.p Pauli.X))}
    {hBZ0 : SFormula.Deriv Γ (.eqPauli (.stabAt (rowB D) (SC.closed q0)) (SC.p Pauli.Z))}
    {hBZ1 : SFormula.Deriv Γ (.eqPauli (.stabAt (rowB D) (SC.closed q1)) (SC.p Pauli.Z))}
    {hRest : SFormula.Deriv Γ (twoAntiRest D q0 q1)}
    {rho : Env 2} {E : PartialStabilizer}
    (wHLt0 : DerivWF hLt0 Surface.code.body (D.distance + 2) rho E)
    (wHLt1 : DerivWF hLt1 Surface.code.body (D.distance + 2) rho E)
    (wHNe : DerivWF hNe Surface.code.body (D.distance + 2) rho E)
    (wHAX0 : DerivWF hAX0 Surface.code.body (D.distance + 2) rho E)
    (wHAX1 : DerivWF hAX1 Surface.code.body (D.distance + 2) rho E)
    (wHBZ0 : DerivWF hBZ0 Surface.code.body (D.distance + 2) rho E)
    (wHBZ1 : DerivWF hBZ1 Surface.code.body (D.distance + 2) rho E)
    (wHRest : DerivWF hRest Surface.code.body (D.distance + 2) rho E) :
    DerivWF (commTwoAntiXZ D q0 q1 hLt0 hLt1 hNe hAX0 hAX1 hBZ0 hBZ1 hRest)
      Surface.code.body (D.distance + 2) rho E := by
  unfold commTwoAntiXZ
  refine derivWF_commutesOfTwoAnti wHLt0 wHLt1 ?hne ?ha0 ?ha1 wHRest
  case hne =>
    refine derivWF_notIntro ?_ (derivWF_notElim
      (derivWF_eqNatBoolTrue _ _ (derivWF_hyp _)) (derivWF_eqBoolFalseNotTrue (cw1_WF wHNe)))
    exact formulaDefined_eqNat (sterm_eval_closed (hq0p.eval_total _ _ _))
      (sterm_eval_closed (hq1p.eval_total _ _ _))
  case ha0 =>
    exact derivWF_anticommutesTransport _ _ _ _ _ wHAX0 wHBZ0 (derivWF_pauliAnticommutesLit _ _)
      (formulaDefined_eqBool (sterm_eval_anticommutes
        (rowStabEval D k1P (.var _) hq0p rho E) (sterm_eval_p _)) (sterm_eval_b _))
  case ha1 =>
    exact derivWF_anticommutesTransport _ _ _ _ _ wHAX1 wHBZ1 (derivWF_pauliAnticommutesLit _ _)
      (formulaDefined_eqBool (sterm_eval_anticommutes
        (rowStabEval D k1P (.var _) hq1p rho E) (sterm_eval_p _)) (sterm_eval_b _))

/-- WF of `twoAntiRestXZ` — the all-others discharger for the overlapping (X-vs-Z) case.
Reuses `pairCommutePointwise_WF`'s shell (qubit binder + recCall `hAe`/`hBe` + `localDispatch_WF`)
and `pairCommuteSameTypeX_WF`'s (Z,X) type-exclusion block; the `(X,Z)` overlap delegates to the
per-class pin handler `hXZpin`.  The two `≠q0/≠q1` `impIntro`s are unconditional (the body is
defined regardless). -/
theorem twoAntiRestXZ_WF (D : OddSurfaceDistance) {Γ : List (SFormula 2)}
    (q0 q1 : Term 2 .nat) (hq0p : SFormula.PureNatTerm q0) (hq1p : SFormula.PureNatTerm q1)
    {hEntryAF : SFormula.Deriv Γ (entryAQuant D)} {hEntryBF : SFormula.Deriv Γ (entryBQuant D)}
    {hk1X : SFormula.Deriv Γ (k1IsX D true)} {hExcl1 : SFormula.Deriv Γ (typeExclF D k1P)}
    {hXZpin : ∀ (Δ' : List (SFormula 3)),
      (∀ {A : SFormula 3}, SFormula.Deriv (.not (.eqNat SFormula.boundNat (SC.closed q1).weaken)
          :: .not (.eqNat SFormula.boundNat (SC.closed q0).weaken)
          :: SFormula.boundNatLt (nP2 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3)) (SC.p Pauli.X)) →
      SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p Pauli.Z)) →
        SFormula.Deriv Δ' (lcGoalP D)}
    {rho : Env 2} {E : PartialStabilizer}
    (wEntryAF : DerivWF hEntryAF Surface.code.body (D.distance + 2) rho E)
    (wEntryBF : DerivWF hEntryBF Surface.code.body (D.distance + 2) rho E)
    (wHk1X : DerivWF hk1X Surface.code.body (D.distance + 2) rho E)
    (wHExcl1 : DerivWF hExcl1 Surface.code.body (D.distance + 2) rho E)
    (wHXZpin : ∀ (x : Nat) (Δ' : List (SFormula 3))
        (lift : ∀ {A : SFormula 3}, SFormula.Deriv (.not (.eqNat SFormula.boundNat (SC.closed q1).weaken)
            :: .not (.eqNat SFormula.boundNat (SC.closed q0).weaken)
            :: SFormula.boundNatLt (nP2 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A),
        (∀ {A : SFormula 3} {h : SFormula.Deriv (.not (.eqNat SFormula.boundNat (SC.closed q1).weaken)
            :: .not (.eqNat SFormula.boundNat (SC.closed q0).weaken)
            :: SFormula.boundNatLt (nP2 D) :: List.map (fun G => G.weaken) Γ) A},
          DerivWF h Surface.code.body (D.distance + 2) (Env.cons x rho) E →
            DerivWF (lift h) Surface.code.body (D.distance + 2) (Env.cons x rho) E) →
        ∀ {hX : SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3)) (SC.p Pauli.X))},
          DerivWF hX Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        ∀ {hZ : SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p Pauli.Z))},
          DerivWF hZ Surface.code.body (D.distance + 2) (Env.cons x rho) E →
          DerivWF (hXZpin Δ' lift hX hZ) Surface.code.body (D.distance + 2) (Env.cons x rho) E)
    (hCtx : SFormula.ContextHolds Surface.code.body (D.distance + 2) rho E Γ) :
    DerivWF (twoAntiRestXZ D q0 q1 hEntryAF hEntryBF hk1X hExcl1 hXZpin)
      Surface.code.body (D.distance + 2) rho E := by
  unfold twoAntiRestXZ
  refine derivWF_allNatLtIntroBounded _ _ ⟨nQubits D.distance, ?_, fun x hx => ⟨?_, hCtx⟩⟩
  · simp [nP2, SC.closed, STerm.eval, Term.eval, Term.lift]
  simp only [eq_mpr_eq_cast, cast_eq]
  refine derivWF_impIntro ?fd1 (derivWF_impIntro ?fd2 ?inner)
  case fd1 =>
    refine formulaDefined_not (formulaDefined_eqNat
      ⟨x, by simp [SFormula.boundNat, SC.closed, STerm.eval, Term.eval, Env.cons]⟩
      (sterm_eval_closed ?_))
    obtain ⟨v, hv⟩ := hq0p.eval_total Surface.code.body (D.distance + 2) rho
    exact ⟨v, by rw [Term.eval_weaken_top]; exact hv⟩
  case fd2 =>
    refine formulaDefined_not (formulaDefined_eqNat
      ⟨x, by simp [SFormula.boundNat, SC.closed, STerm.eval, Term.eval, Env.cons]⟩
      (sterm_eval_closed ?_))
    obtain ⟨v, hv⟩ := hq1p.eval_total Surface.code.body (D.distance + 2) rho
    exact ⟨v, by rw [Term.eval_weaken_top]; exact hv⟩
  case inner =>
    have hAe : ∃ v, (STerm.stabAt (rowA D).weaken SFormula.boundNat).eval Surface.code.body
        (D.distance + 2) (Env.cons x rho) E = some v := by
      obtain ⟨sa, hsa, htot⟩ := recCall_total_symbolicDK_all D.index (D.distance + 2)
        (by simp only [OddSurfaceDistance.distance, oddDistance]; omega) (Env.cons x rho)
        (dT := dP3 D) (kT := k1P3)
        (fun f' => by simp [dP3, dP2, Term.eval, Term.lift, OddSurfaceDistance.distance, oddDistance]) (.var _)
      refine sterm_eval_stabAt (sv := sa) (qv := x) ?_ ?_ (htot x)
      · rw [rowA_weaken]; simpa [SC.closed, STerm.eval] using hsa
      · simp [SFormula.boundNat, SC.closed, STerm.eval, Term.eval, Env.cons]
    have hBe : ∃ v, (STerm.stabAt (rowB D).weaken SFormula.boundNat).eval Surface.code.body
        (D.distance + 2) (Env.cons x rho) E = some v := by
      obtain ⟨sa, hsa, htot⟩ := recCall_total_symbolicDK_all D.index (D.distance + 2)
        (by simp only [OddSurfaceDistance.distance, oddDistance]; omega) (Env.cons x rho)
        (dT := dP3 D) (kT := k2P3)
        (fun f' => by simp [dP3, dP2, Term.eval, Term.lift, OddSurfaceDistance.distance, oddDistance]) (.var _)
      refine sterm_eval_stabAt (sv := sa) (qv := x) ?_ ?_ (htot x)
      · rw [rowB_weaken]; simpa [SC.closed, STerm.eval] using hsa
      · simp [SFormula.boundNat, SC.closed, STerm.eval, Term.eval, Env.cons]
    refine localDispatch_WF D
      (entryAAtBound_WF D (cw3_WF (derivWF_weakenFresh wEntryAF)) (derivWF_hyp _))
      (entryBAtBound_WF D (cw3_WF (derivWF_weakenFresh wEntryBF)) (derivWF_hyp _))
      ?wAntiXZ ?wAntiZX hAe hBe
    case wAntiXZ =>
      intro Δ' lift liftWF hLA wLA hLB wLB
      exact wHXZpin x Δ' (fun h => lift h) (fun w => liftWF w) wLA wLB
    case wAntiZX =>
      intro Δ' lift liftWF hLA wLA hLB wLB
      have wk1Xd := liftWF (cw3_WF (derivWF_weakenFresh wHk1X))
      have wExcl1d := liftWF (cw3_WF (derivWF_weakenFresh wHExcl1))
      have wxnbz := derivWF_andElimLeft' wExcl1d
      have wxnrz := derivWF_andElimLeft' (derivWF_andElimRight' wExcl1d)
      have wxnlz := derivWF_andElimLeft' (derivWF_andElimRight' (derivWF_andElimRight' wExcl1d))
      refine withLeafG_WF D (.var _) _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · intro Δ'' lift2 liftWF2 hI wI
        exact leafNotPandZ_WF D (.var _) Pauli.I rfl wI (liftWF2 wLA)
      · intro Δ'' lift2 liftWF2 hL wL hb wb hk wk
        exact eqBoolContra_WF _ wk (derivWF_mp (derivWF_mp (liftWF2 wxnbz) (liftWF2 wk1Xd)) wb)
      · intro Δ'' lift2 liftWF2 hX wX hb wb hk wk
        exact leafNotPandZ_WF D (.var _) Pauli.X rfl wX (liftWF2 wLA)
      · intro Δ'' lift2 liftWF2 hX wX hb wb ht wt
        exact leafNotPandZ_WF D (.var _) Pauli.X rfl wX (liftWF2 wLA)
      · intro Δ'' lift2 liftWF2 hL wL hb wb ht wt hr wr
        exact eqBoolContra_WF _ wr
          (derivWF_mp (derivWF_mp (derivWF_mp (liftWF2 wxnrz) (liftWF2 wk1Xd)) wb) wt)
      · intro Δ'' lift2 liftWF2 hL wL hb wb ht wt hr wr hlc wlc
        exact eqBoolContra_WF _ wlc
          (derivWF_mp (derivWF_mp (derivWF_mp (derivWF_mp (liftWF2 wxnlz) (liftWF2 wk1Xd)) wb) wt) wr)
      · intro Δ'' lift2 liftWF2 hX wX hb wb ht wt hr wr hlc wlc
        exact leafNotPandZ_WF D (.var _) Pauli.X rfl wX (liftWF2 wLA)

/-- WF of `commBulkTopXZ` — direct composition of the two keystones
`commTwoAntiXZ_WF` (overlap) and `twoAntiRestXZ_WF` (all-others).  This is what all four
`commBulkBulk*`/bulk-boundary combo closers route through. -/
theorem commBulkTopXZ_WF (D : OddSurfaceDistance) {Γ : List (SFormula 2)}
    (q0 q1 : Term 2 .nat) (hq0p : SFormula.PureNatTerm q0) (hq1p : SFormula.PureNatTerm q1)
    {hEntryAF : SFormula.Deriv Γ (entryAQuant D)} {hEntryBF : SFormula.Deriv Γ (entryBQuant D)}
    {hk1X : SFormula.Deriv Γ (k1IsX D true)} {hExcl1 : SFormula.Deriv Γ (typeExclF D k1P)}
    {hLt0 : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed q0) (nP2 D))}
    {hLt1 : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed q1) (nP2 D))}
    {hNe : SFormula.Deriv Γ (.eqBool (SC.closed (.eqNat q0 q1)) (SC.b false))}
    {hAX0 : SFormula.Deriv Γ (.eqPauli (.stabAt (rowA D) (SC.closed q0)) (SC.p Pauli.X))}
    {hAX1 : SFormula.Deriv Γ (.eqPauli (.stabAt (rowA D) (SC.closed q1)) (SC.p Pauli.X))}
    {hBZ0 : SFormula.Deriv Γ (.eqPauli (.stabAt (rowB D) (SC.closed q0)) (SC.p Pauli.Z))}
    {hBZ1 : SFormula.Deriv Γ (.eqPauli (.stabAt (rowB D) (SC.closed q1)) (SC.p Pauli.Z))}
    {hXZpin : ∀ (Δ' : List (SFormula 3)),
      (∀ {A : SFormula 3}, SFormula.Deriv (.not (.eqNat SFormula.boundNat (SC.closed q1).weaken)
          :: .not (.eqNat SFormula.boundNat (SC.closed q0).weaken)
          :: SFormula.boundNatLt (nP2 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3)) (SC.p Pauli.X)) →
      SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p Pauli.Z)) →
        SFormula.Deriv Δ' (lcGoalP D)}
    {rho : Env 2} {E : PartialStabilizer}
    (wEntryAF : DerivWF hEntryAF Surface.code.body (D.distance + 2) rho E)
    (wEntryBF : DerivWF hEntryBF Surface.code.body (D.distance + 2) rho E)
    (wHk1X : DerivWF hk1X Surface.code.body (D.distance + 2) rho E)
    (wHExcl1 : DerivWF hExcl1 Surface.code.body (D.distance + 2) rho E)
    (wHLt0 : DerivWF hLt0 Surface.code.body (D.distance + 2) rho E)
    (wHLt1 : DerivWF hLt1 Surface.code.body (D.distance + 2) rho E)
    (wHNe : DerivWF hNe Surface.code.body (D.distance + 2) rho E)
    (wHAX0 : DerivWF hAX0 Surface.code.body (D.distance + 2) rho E)
    (wHAX1 : DerivWF hAX1 Surface.code.body (D.distance + 2) rho E)
    (wHBZ0 : DerivWF hBZ0 Surface.code.body (D.distance + 2) rho E)
    (wHBZ1 : DerivWF hBZ1 Surface.code.body (D.distance + 2) rho E)
    (wHXZpin : ∀ (x : Nat) (Δ' : List (SFormula 3))
        (lift : ∀ {A : SFormula 3}, SFormula.Deriv (.not (.eqNat SFormula.boundNat (SC.closed q1).weaken)
            :: .not (.eqNat SFormula.boundNat (SC.closed q0).weaken)
            :: SFormula.boundNatLt (nP2 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A),
        (∀ {A : SFormula 3} {h : SFormula.Deriv (.not (.eqNat SFormula.boundNat (SC.closed q1).weaken)
            :: .not (.eqNat SFormula.boundNat (SC.closed q0).weaken)
            :: SFormula.boundNatLt (nP2 D) :: List.map (fun G => G.weaken) Γ) A},
          DerivWF h Surface.code.body (D.distance + 2) (Env.cons x rho) E →
            DerivWF (lift h) Surface.code.body (D.distance + 2) (Env.cons x rho) E) →
        ∀ {hX : SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3)) (SC.p Pauli.X))},
          DerivWF hX Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        ∀ {hZ : SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p Pauli.Z))},
          DerivWF hZ Surface.code.body (D.distance + 2) (Env.cons x rho) E →
          DerivWF (hXZpin Δ' lift hX hZ) Surface.code.body (D.distance + 2) (Env.cons x rho) E)
    (hCtx : SFormula.ContextHolds Surface.code.body (D.distance + 2) rho E Γ) :
    DerivWF (commBulkTopXZ D q0 q1 hEntryAF hEntryBF hk1X hExcl1 hLt0 hLt1 hNe
        hAX0 hAX1 hBZ0 hBZ1 hXZpin) Surface.code.body (D.distance + 2) rho E := by
  unfold commBulkTopXZ
  exact commTwoAntiXZ_WF D q0 q1 hq0p hq1p wHLt0 wHLt1 wHNe wHAX0 wHAX1 wHBZ0 wHBZ1
    (twoAntiRestXZ_WF D q0 q1 hq0p hq1p wEntryAF wEntryBF wHk1X wHExcl1 wHXZpin hCtx)

end QHL.CodeLang.Surface.Verify
