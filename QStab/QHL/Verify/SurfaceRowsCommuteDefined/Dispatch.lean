import QStab.QHL.Verify.SurfaceRowsCommuteDefined.Leaves

/-!
# Rows-commute definedness — Dispatch

The dispatch-tree WFs (auto-walk + handler-WF hypotheses), `localDispatch_WF`, and
`pairCommutePointwise_WF` (commutes-of-pointwise over the qubit binder).
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

set_option maxHeartbeats 1600000

/-! ## Dispatch-tree WFs (auto-walk + handler-WF hypotheses, mirror colDispatchOnTrue_WF) -/

/-- WF of `withLeafA` — the 11-leaf cell-classification cascade for row A (`k1P3`).
The `boolCases` tree + `baseLeaf*` leaves auto-discharge; the three handler outcomes
(`I`/`X`/`Z` leaf) are supplied as higher-order `DerivWF` hypotheses. -/
theorem withLeafA_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)} (C : SFormula 3)
    (H : LeafHandlers Δ D k1P3 C) {fuel : Nat} {rho : Env 3} {E : PartialStabilizer}
    (wHI : ∀ (Δ' : List (SFormula 3))
        (lift : ∀ {A : SFormula 3}, SFormula.Deriv Δ A → SFormula.Deriv Δ' A),
        (∀ {A : SFormula 3} {h : SFormula.Deriv Δ A},
          DerivWF h Surface.code.body fuel rho E → DerivWF (lift h) Surface.code.body fuel rho E) →
        ∀ {hL : SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3)) (SC.p Pauli.I))},
          DerivWF hL Surface.code.body fuel rho E →
          DerivWF (H.hI Δ' lift hL) Surface.code.body fuel rho E)
    (wHX : ∀ (Δ' : List (SFormula 3))
        (lift : ∀ {A : SFormula 3}, SFormula.Deriv Δ A → SFormula.Deriv Δ' A),
        (∀ {A : SFormula 3} {h : SFormula.Deriv Δ A},
          DerivWF h Surface.code.body fuel rho E → DerivWF (lift h) Surface.code.body fuel rho E) →
        ∀ {hL : SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3)) (SC.p Pauli.X))},
          DerivWF hL Surface.code.body fuel rho E →
          DerivWF (H.hX Δ' lift hL) Surface.code.body fuel rho E)
    (wHZ : ∀ (Δ' : List (SFormula 3))
        (lift : ∀ {A : SFormula 3}, SFormula.Deriv Δ A → SFormula.Deriv Δ' A),
        (∀ {A : SFormula 3} {h : SFormula.Deriv Δ A},
          DerivWF h Surface.code.body fuel rho E → DerivWF (lift h) Surface.code.body fuel rho E) →
        ∀ {hL : SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3)) (SC.p Pauli.Z))},
          DerivWF hL Surface.code.body fuel rho E →
          DerivWF (H.hZ Δ' lift hL) Surface.code.body fuel rho E) :
    DerivWF (withLeafA D C H) Surface.code.body fuel rho E := by
  have hd := dP3_pure D
  unfold withLeafA
  repeat (any_goals
    refine derivWF_boolCases _ _
      (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?_ ?_)
  · exact wHZ _ _ (fun w => cw3_WF w)
      (baseLeafZ_WF (dP3 D) k1P3 qP3 hd (.var _) (.var _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _))
  · exact wHX _ _ (fun w => cw3_WF w)
      (baseLeafBulkX_WF (dP3 D) k1P3 qP3 hd (.var _) (.var _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _))
  · exact wHI _ _ (fun w => cw2_WF w)
      (baseLeafBulkI_WF (dP3 D) k1P3 qP3 hd (.var _) (.var _) (derivWF_hyp _) (derivWF_hyp _))
  · exact wHX _ _ (fun w => cw3_WF w)
      (baseLeafTopX_WF (dP3 D) k1P3 qP3 hd (.var _) (.var _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _))
  · exact wHI _ _ (fun w => cw3_WF w)
      (baseLeafTopI_WF (dP3 D) k1P3 qP3 hd (.var _) (.var _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _))
  · exact wHZ _ _ (fun w => cw4_WF w)
      (baseLeafRightZ_WF (dP3 D) k1P3 qP3 hd (.var _) (.var _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _))
  · exact wHI _ _ (fun w => cw4_WF w)
      (baseLeafRightI_WF (dP3 D) k1P3 qP3 hd (.var _) (.var _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _))
  · exact wHZ _ _ (fun w => cw5_WF w)
      (baseLeafLeftZ_WF (dP3 D) k1P3 qP3 hd (.var _) (.var _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _))
  · exact wHI _ _ (fun w => cw5_WF w)
      (baseLeafLeftI_WF (dP3 D) k1P3 qP3 hd (.var _) (.var _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _))
  · exact wHX _ _ (fun w => cw5_WF w)
      (baseLeafBottomX_WF (dP3 D) k1P3 qP3 hd (.var _) (.var _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _))
  · exact wHI _ _ (fun w => cw5_WF w)
      (baseLeafBottomI_WF (dP3 D) k1P3 qP3 hd (.var _) (.var _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _))

/-- WF of `withLeafB` — row B (`k2P3`); identical cascade to `withLeafA_WF`. -/
theorem withLeafB_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)} (C : SFormula 3)
    (H : LeafHandlers Δ D k2P3 C) {fuel : Nat} {rho : Env 3} {E : PartialStabilizer}
    (wHI : ∀ (Δ' : List (SFormula 3))
        (lift : ∀ {A : SFormula 3}, SFormula.Deriv Δ A → SFormula.Deriv Δ' A),
        (∀ {A : SFormula 3} {h : SFormula.Deriv Δ A},
          DerivWF h Surface.code.body fuel rho E → DerivWF (lift h) Surface.code.body fuel rho E) →
        ∀ {hL : SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p Pauli.I))},
          DerivWF hL Surface.code.body fuel rho E →
          DerivWF (H.hI Δ' lift hL) Surface.code.body fuel rho E)
    (wHX : ∀ (Δ' : List (SFormula 3))
        (lift : ∀ {A : SFormula 3}, SFormula.Deriv Δ A → SFormula.Deriv Δ' A),
        (∀ {A : SFormula 3} {h : SFormula.Deriv Δ A},
          DerivWF h Surface.code.body fuel rho E → DerivWF (lift h) Surface.code.body fuel rho E) →
        ∀ {hL : SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p Pauli.X))},
          DerivWF hL Surface.code.body fuel rho E →
          DerivWF (H.hX Δ' lift hL) Surface.code.body fuel rho E)
    (wHZ : ∀ (Δ' : List (SFormula 3))
        (lift : ∀ {A : SFormula 3}, SFormula.Deriv Δ A → SFormula.Deriv Δ' A),
        (∀ {A : SFormula 3} {h : SFormula.Deriv Δ A},
          DerivWF h Surface.code.body fuel rho E → DerivWF (lift h) Surface.code.body fuel rho E) →
        ∀ {hL : SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p Pauli.Z))},
          DerivWF hL Surface.code.body fuel rho E →
          DerivWF (H.hZ Δ' lift hL) Surface.code.body fuel rho E) :
    DerivWF (withLeafB D C H) Surface.code.body fuel rho E := by
  have hd := dP3_pure D
  unfold withLeafB
  repeat (any_goals
    refine derivWF_boolCases _ _
      (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?_ ?_)
  · exact wHZ _ _ (fun w => cw3_WF w)
      (baseLeafZ_WF (dP3 D) k2P3 qP3 hd (.var _) (.var _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _))
  · exact wHX _ _ (fun w => cw3_WF w)
      (baseLeafBulkX_WF (dP3 D) k2P3 qP3 hd (.var _) (.var _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _))
  · exact wHI _ _ (fun w => cw2_WF w)
      (baseLeafBulkI_WF (dP3 D) k2P3 qP3 hd (.var _) (.var _) (derivWF_hyp _) (derivWF_hyp _))
  · exact wHX _ _ (fun w => cw3_WF w)
      (baseLeafTopX_WF (dP3 D) k2P3 qP3 hd (.var _) (.var _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _))
  · exact wHI _ _ (fun w => cw3_WF w)
      (baseLeafTopI_WF (dP3 D) k2P3 qP3 hd (.var _) (.var _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _))
  · exact wHZ _ _ (fun w => cw4_WF w)
      (baseLeafRightZ_WF (dP3 D) k2P3 qP3 hd (.var _) (.var _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _))
  · exact wHI _ _ (fun w => cw4_WF w)
      (baseLeafRightI_WF (dP3 D) k2P3 qP3 hd (.var _) (.var _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _))
  · exact wHZ _ _ (fun w => cw5_WF w)
      (baseLeafLeftZ_WF (dP3 D) k2P3 qP3 hd (.var _) (.var _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _))
  · exact wHI _ _ (fun w => cw5_WF w)
      (baseLeafLeftI_WF (dP3 D) k2P3 qP3 hd (.var _) (.var _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _))
  · exact wHX _ _ (fun w => cw5_WF w)
      (baseLeafBottomX_WF (dP3 D) k2P3 qP3 hd (.var _) (.var _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _))
  · exact wHI _ _ (fun w => cw5_WF w)
      (baseLeafBottomI_WF (dP3 D) k2P3 qP3 hd (.var _) (.var _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _))

/-- WF of `withLeafG` — the guard-exposing 7-handler cascade (generic index `kT`).
Same auto-walk as `withLeafA_WF`; each non-`I` handler additionally receives the
branch's class-guard `DerivWF`s (all `derivWF_hyp`). -/
theorem withLeafG_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)} {kT : Term 3 .nat}
    (hkP : SFormula.PureNatTerm kT) (C : SFormula 3)
    (H : LeafHandlersG Δ D kT C) {fuel : Nat} {rho : Env 3} {E : PartialStabilizer}
    (wHI : ∀ (Δ' : List (SFormula 3))
        (lift : ∀ {A : SFormula 3}, SFormula.Deriv Δ A → SFormula.Deriv Δ' A),
        (∀ {A : SFormula 3} {h : SFormula.Deriv Δ A},
          DerivWF h Surface.code.body fuel rho E → DerivWF (lift h) Surface.code.body fuel rho E) →
        ∀ {hL : SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) kT qP3)) (SC.p Pauli.I))},
          DerivWF hL Surface.code.body fuel rho E →
          DerivWF (H.hI Δ' lift hL) Surface.code.body fuel rho E)
    (wHBulkZ : ∀ (Δ' : List (SFormula 3))
        (lift : ∀ {A : SFormula 3}, SFormula.Deriv Δ A → SFormula.Deriv Δ' A),
        (∀ {A : SFormula 3} {h : SFormula.Deriv Δ A},
          DerivWF h Surface.code.body fuel rho E → DerivWF (lift h) Surface.code.body fuel rho E) →
        ∀ {hL : SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) kT qP3)) (SC.p Pauli.Z))},
          DerivWF hL Surface.code.body fuel rho E →
        ∀ {hb : SFormula.Deriv Δ' (.eqBool (SC.closed (bulkGuardTA (dP3 D) kT)) (SC.b true))},
          DerivWF hb Surface.code.body fuel rho E →
        ∀ {hk : SFormula.Deriv Δ' (.eqBool (SC.closed (baseKindGuardTA (dP3 D) kT)) (SC.b true))},
          DerivWF hk Surface.code.body fuel rho E →
          DerivWF (H.hBulkZ Δ' lift hL hb hk) Surface.code.body fuel rho E)
    (wHBulkX : ∀ (Δ' : List (SFormula 3))
        (lift : ∀ {A : SFormula 3}, SFormula.Deriv Δ A → SFormula.Deriv Δ' A),
        (∀ {A : SFormula 3} {h : SFormula.Deriv Δ A},
          DerivWF h Surface.code.body fuel rho E → DerivWF (lift h) Surface.code.body fuel rho E) →
        ∀ {hL : SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) kT qP3)) (SC.p Pauli.X))},
          DerivWF hL Surface.code.body fuel rho E →
        ∀ {hb : SFormula.Deriv Δ' (.eqBool (SC.closed (bulkGuardTA (dP3 D) kT)) (SC.b true))},
          DerivWF hb Surface.code.body fuel rho E →
        ∀ {hk : SFormula.Deriv Δ' (.eqBool (SC.closed (baseKindGuardTA (dP3 D) kT)) (SC.b false))},
          DerivWF hk Surface.code.body fuel rho E →
          DerivWF (H.hBulkX Δ' lift hL hb hk) Surface.code.body fuel rho E)
    (wHTopX : ∀ (Δ' : List (SFormula 3))
        (lift : ∀ {A : SFormula 3}, SFormula.Deriv Δ A → SFormula.Deriv Δ' A),
        (∀ {A : SFormula 3} {h : SFormula.Deriv Δ A},
          DerivWF h Surface.code.body fuel rho E → DerivWF (lift h) Surface.code.body fuel rho E) →
        ∀ {hL : SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) kT qP3)) (SC.p Pauli.X))},
          DerivWF hL Surface.code.body fuel rho E →
        ∀ {hb : SFormula.Deriv Δ' (.eqBool (SC.closed (bulkGuardTA (dP3 D) kT)) (SC.b false))},
          DerivWF hb Surface.code.body fuel rho E →
        ∀ {ht : SFormula.Deriv Δ' (.eqBool (SC.closed (topClassGuardTA (dP3 D) kT)) (SC.b true))},
          DerivWF ht Surface.code.body fuel rho E →
          DerivWF (H.hTopX Δ' lift hL hb ht) Surface.code.body fuel rho E)
    (wHRightZ : ∀ (Δ' : List (SFormula 3))
        (lift : ∀ {A : SFormula 3}, SFormula.Deriv Δ A → SFormula.Deriv Δ' A),
        (∀ {A : SFormula 3} {h : SFormula.Deriv Δ A},
          DerivWF h Surface.code.body fuel rho E → DerivWF (lift h) Surface.code.body fuel rho E) →
        ∀ {hL : SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) kT qP3)) (SC.p Pauli.Z))},
          DerivWF hL Surface.code.body fuel rho E →
        ∀ {hb : SFormula.Deriv Δ' (.eqBool (SC.closed (bulkGuardTA (dP3 D) kT)) (SC.b false))},
          DerivWF hb Surface.code.body fuel rho E →
        ∀ {ht : SFormula.Deriv Δ' (.eqBool (SC.closed (topClassGuardTA (dP3 D) kT)) (SC.b false))},
          DerivWF ht Surface.code.body fuel rho E →
        ∀ {hr : SFormula.Deriv Δ' (.eqBool (SC.closed (rightClassGuardTA (dP3 D) kT)) (SC.b true))},
          DerivWF hr Surface.code.body fuel rho E →
          DerivWF (H.hRightZ Δ' lift hL hb ht hr) Surface.code.body fuel rho E)
    (wHLeftZ : ∀ (Δ' : List (SFormula 3))
        (lift : ∀ {A : SFormula 3}, SFormula.Deriv Δ A → SFormula.Deriv Δ' A),
        (∀ {A : SFormula 3} {h : SFormula.Deriv Δ A},
          DerivWF h Surface.code.body fuel rho E → DerivWF (lift h) Surface.code.body fuel rho E) →
        ∀ {hL : SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) kT qP3)) (SC.p Pauli.Z))},
          DerivWF hL Surface.code.body fuel rho E →
        ∀ {hb : SFormula.Deriv Δ' (.eqBool (SC.closed (bulkGuardTA (dP3 D) kT)) (SC.b false))},
          DerivWF hb Surface.code.body fuel rho E →
        ∀ {ht : SFormula.Deriv Δ' (.eqBool (SC.closed (topClassGuardTA (dP3 D) kT)) (SC.b false))},
          DerivWF ht Surface.code.body fuel rho E →
        ∀ {hr : SFormula.Deriv Δ' (.eqBool (SC.closed (rightClassGuardTA (dP3 D) kT)) (SC.b false))},
          DerivWF hr Surface.code.body fuel rho E →
        ∀ {hlc : SFormula.Deriv Δ' (.eqBool (SC.closed (leftClassGuardTA (dP3 D) kT)) (SC.b true))},
          DerivWF hlc Surface.code.body fuel rho E →
          DerivWF (H.hLeftZ Δ' lift hL hb ht hr hlc) Surface.code.body fuel rho E)
    (wHBottomX : ∀ (Δ' : List (SFormula 3))
        (lift : ∀ {A : SFormula 3}, SFormula.Deriv Δ A → SFormula.Deriv Δ' A),
        (∀ {A : SFormula 3} {h : SFormula.Deriv Δ A},
          DerivWF h Surface.code.body fuel rho E → DerivWF (lift h) Surface.code.body fuel rho E) →
        ∀ {hL : SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) kT qP3)) (SC.p Pauli.X))},
          DerivWF hL Surface.code.body fuel rho E →
        ∀ {hb : SFormula.Deriv Δ' (.eqBool (SC.closed (bulkGuardTA (dP3 D) kT)) (SC.b false))},
          DerivWF hb Surface.code.body fuel rho E →
        ∀ {ht : SFormula.Deriv Δ' (.eqBool (SC.closed (topClassGuardTA (dP3 D) kT)) (SC.b false))},
          DerivWF ht Surface.code.body fuel rho E →
        ∀ {hr : SFormula.Deriv Δ' (.eqBool (SC.closed (rightClassGuardTA (dP3 D) kT)) (SC.b false))},
          DerivWF hr Surface.code.body fuel rho E →
        ∀ {hlc : SFormula.Deriv Δ' (.eqBool (SC.closed (leftClassGuardTA (dP3 D) kT)) (SC.b false))},
          DerivWF hlc Surface.code.body fuel rho E →
          DerivWF (H.hBottomX Δ' lift hL hb ht hr hlc) Surface.code.body fuel rho E) :
    DerivWF (withLeafG D kT C H) Surface.code.body fuel rho E := by
  unfold withLeafG
  repeat (any_goals
    refine derivWF_boolCases _ _
      (sterm_eval_closedPure (by repeat (first | assumption | constructor))) ?_ ?_)
  · exact wHBulkZ _ _ (fun w => cw3_WF w)
      (baseLeafZ_WF (dP3 D) kT qP3 (dP3_pure D) hkP (.var _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _))
      (derivWF_hyp _) (derivWF_hyp _)
  · exact wHBulkX _ _ (fun w => cw3_WF w)
      (baseLeafBulkX_WF (dP3 D) kT qP3 (dP3_pure D) hkP (.var _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _))
      (derivWF_hyp _) (derivWF_hyp _)
  · exact wHI _ _ (fun w => cw2_WF w)
      (baseLeafBulkI_WF (dP3 D) kT qP3 (dP3_pure D) hkP (.var _) (derivWF_hyp _) (derivWF_hyp _))
  · exact wHTopX _ _ (fun w => cw3_WF w)
      (baseLeafTopX_WF (dP3 D) kT qP3 (dP3_pure D) hkP (.var _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _))
      (derivWF_hyp _) (derivWF_hyp _)
  · exact wHI _ _ (fun w => cw3_WF w)
      (baseLeafTopI_WF (dP3 D) kT qP3 (dP3_pure D) hkP (.var _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _))
  · exact wHRightZ _ _ (fun w => cw4_WF w)
      (baseLeafRightZ_WF (dP3 D) kT qP3 (dP3_pure D) hkP (.var _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _))
      (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _)
  · exact wHI _ _ (fun w => cw4_WF w)
      (baseLeafRightI_WF (dP3 D) kT qP3 (dP3_pure D) hkP (.var _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _))
  · exact wHLeftZ _ _ (fun w => cw5_WF w)
      (baseLeafLeftZ_WF (dP3 D) kT qP3 (dP3_pure D) hkP (.var _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _))
      (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _)
  · exact wHI _ _ (fun w => cw5_WF w)
      (baseLeafLeftI_WF (dP3 D) kT qP3 (dP3_pure D) hkP (.var _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _))
  · exact wHBottomX _ _ (fun w => cw5_WF w)
      (baseLeafBottomX_WF (dP3 D) kT qP3 (dP3_pure D) hkP (.var _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _))
      (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _)
  · exact wHI _ _ (fun w => cw5_WF w)
      (baseLeafBottomI_WF (dP3 D) kT qP3 (dP3_pure D) hkP (.var _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _) (derivWF_hyp _))

/-! ## localDispatch WF (composes withLeafA/B_WF + lcFrom*_WF + the two anti-handlers) -/

/-- WF of `localDispatch` — resolves both row leaves and dispatches on the Pauli pair.
The commuting pairs close via `lcFrom*_WF`; the `(X,Z)`/`(Z,X)` pairs delegate to the
two anti-handler WF hypotheses.  `hAe`/`hBe` are the rowA/rowB stab evals (passed up). -/
theorem localDispatch_WF (D : OddSurfaceDistance) {Δ : List (SFormula 3)}
    {hEntryA : SFormula.Deriv Δ (entryAF D)} {hEntryB : SFormula.Deriv Δ (entryBF D)}
    {hAntiXZ : ∀ (Δ' : List (SFormula 3)),
      (∀ {A : SFormula 3}, SFormula.Deriv Δ A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3)) (SC.p Pauli.X)) →
      SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p Pauli.Z)) →
        SFormula.Deriv Δ' (lcGoalP D)}
    {hAntiZX : ∀ (Δ' : List (SFormula 3)),
      (∀ {A : SFormula 3}, SFormula.Deriv Δ A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3)) (SC.p Pauli.Z)) →
      SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p Pauli.X)) →
        SFormula.Deriv Δ' (lcGoalP D)}
    {fuel : Nat} {rho : Env 3} {E : PartialStabilizer}
    (wEntryA : DerivWF hEntryA Surface.code.body fuel rho E)
    (wEntryB : DerivWF hEntryB Surface.code.body fuel rho E)
    (wAntiXZ : ∀ (Δ' : List (SFormula 3))
        (lift : ∀ {A : SFormula 3}, SFormula.Deriv Δ A → SFormula.Deriv Δ' A),
        (∀ {A : SFormula 3} {h : SFormula.Deriv Δ A},
          DerivWF h Surface.code.body fuel rho E → DerivWF (lift h) Surface.code.body fuel rho E) →
        ∀ {hA : SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3)) (SC.p Pauli.X))},
          DerivWF hA Surface.code.body fuel rho E →
        ∀ {hB : SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p Pauli.Z))},
          DerivWF hB Surface.code.body fuel rho E →
          DerivWF (hAntiXZ Δ' lift hA hB) Surface.code.body fuel rho E)
    (wAntiZX : ∀ (Δ' : List (SFormula 3))
        (lift : ∀ {A : SFormula 3}, SFormula.Deriv Δ A → SFormula.Deriv Δ' A),
        (∀ {A : SFormula 3} {h : SFormula.Deriv Δ A},
          DerivWF h Surface.code.body fuel rho E → DerivWF (lift h) Surface.code.body fuel rho E) →
        ∀ {hA : SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3)) (SC.p Pauli.Z))},
          DerivWF hA Surface.code.body fuel rho E →
        ∀ {hB : SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p Pauli.X))},
          DerivWF hB Surface.code.body fuel rho E →
          DerivWF (hAntiZX Δ' lift hA hB) Surface.code.body fuel rho E)
    (hAe : ∃ v, (STerm.stabAt (rowA D).weaken SFormula.boundNat).eval Surface.code.body fuel rho E = some v)
    (hBe : ∃ v, (STerm.stabAt (rowB D).weaken SFormula.boundNat).eval Surface.code.body fuel rho E = some v) :
    DerivWF (localDispatch D hEntryA hEntryB hAntiXZ hAntiZX) Surface.code.body fuel rho E := by
  unfold localDispatch
  refine withLeafA_WF D _ _ ?wAI ?wAX ?wAZ
  · -- A leaf I → lcFromLeftI
    intro Δ1 lift1 liftWF1 hL wL
    exact lcFromLeftI_WF D (liftWF1 wEntryA) wL hAe hBe
  · -- A leaf X
    intro Δ1 lift1 liftWF1 hL wL
    refine withLeafB_WF D _ _ ?wXBI ?wXX ?wXZ
    · intro Δ2 lift2 liftWF2 hLB wLB
      exact lcFromRightI_WF D (liftWF2 (liftWF1 wEntryB)) wLB hAe hBe
    · intro Δ2 lift2 liftWF2 hLB wLB
      exact lcFromTwoLeaves_WF D Pauli.X Pauli.X (liftWF2 (liftWF1 wEntryA)) (liftWF2 wL)
        (liftWF2 (liftWF1 wEntryB)) wLB (antiP_WF _ _ _) hAe hBe
    · intro Δ2 lift2 liftWF2 hLB wLB
      exact wAntiXZ Δ2 (fun h => lift2 (lift1 h)) (fun w => liftWF2 (liftWF1 w)) (liftWF2 wL) wLB
  · -- A leaf Z
    intro Δ1 lift1 liftWF1 hL wL
    refine withLeafB_WF D _ _ ?wZBI ?wZX ?wZZ
    · intro Δ2 lift2 liftWF2 hLB wLB
      exact lcFromRightI_WF D (liftWF2 (liftWF1 wEntryB)) wLB hAe hBe
    · intro Δ2 lift2 liftWF2 hLB wLB
      exact wAntiZX Δ2 (fun h => lift2 (lift1 h)) (fun w => liftWF2 (liftWF1 w)) (liftWF2 wL) wLB
    · intro Δ2 lift2 liftWF2 hLB wLB
      exact lcFromTwoLeaves_WF D Pauli.Z Pauli.Z (liftWF2 (liftWF1 wEntryA)) (liftWF2 wL)
        (liftWF2 (liftWF1 wEntryB)) wLB (antiP_WF _ _ _) hAe hBe

/-! ## pairCommutePointwise WF (commutesOfPointwise + qubit binder + localDispatch_WF;
the rowA/rowB recCall totality enters here, mirroring commPointwiseSym_WF). -/

theorem pairCommutePointwise_WF (D : OddSurfaceDistance) {Γ : List (SFormula 2)}
    {hEntryAF : SFormula.Deriv Γ (entryAQuant D)} {hEntryBF : SFormula.Deriv Γ (entryBQuant D)}
    {hAntiXZ : ∀ (Δ' : List (SFormula 3)),
      (∀ {A : SFormula 3}, SFormula.Deriv (pwCtx D Γ) A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3)) (SC.p Pauli.X)) →
      SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p Pauli.Z)) →
        SFormula.Deriv Δ' (lcGoalP D)}
    {hAntiZX : ∀ (Δ' : List (SFormula 3)),
      (∀ {A : SFormula 3}, SFormula.Deriv (pwCtx D Γ) A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3)) (SC.p Pauli.Z)) →
      SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p Pauli.X)) →
        SFormula.Deriv Δ' (lcGoalP D)}
    {rho : Env 2} {E : PartialStabilizer}
    (wEntryAF : DerivWF hEntryAF Surface.code.body (D.distance + 2) rho E)
    (wEntryBF : DerivWF hEntryBF Surface.code.body (D.distance + 2) rho E)
    (wAntiXZ : ∀ (x : Nat) (Δ' : List (SFormula 3))
        (lift : ∀ {A : SFormula 3}, SFormula.Deriv (pwCtx D Γ) A → SFormula.Deriv Δ' A),
        (∀ {A : SFormula 3} {h : SFormula.Deriv (pwCtx D Γ) A},
          DerivWF h Surface.code.body (D.distance + 2) (Env.cons x rho) E →
            DerivWF (lift h) Surface.code.body (D.distance + 2) (Env.cons x rho) E) →
        ∀ {hA : SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3)) (SC.p Pauli.X))},
          DerivWF hA Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        ∀ {hB : SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p Pauli.Z))},
          DerivWF hB Surface.code.body (D.distance + 2) (Env.cons x rho) E →
          DerivWF (hAntiXZ Δ' lift hA hB) Surface.code.body (D.distance + 2) (Env.cons x rho) E)
    (wAntiZX : ∀ (x : Nat) (Δ' : List (SFormula 3))
        (lift : ∀ {A : SFormula 3}, SFormula.Deriv (pwCtx D Γ) A → SFormula.Deriv Δ' A),
        (∀ {A : SFormula 3} {h : SFormula.Deriv (pwCtx D Γ) A},
          DerivWF h Surface.code.body (D.distance + 2) (Env.cons x rho) E →
            DerivWF (lift h) Surface.code.body (D.distance + 2) (Env.cons x rho) E) →
        ∀ {hA : SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3)) (SC.p Pauli.Z))},
          DerivWF hA Surface.code.body (D.distance + 2) (Env.cons x rho) E →
        ∀ {hB : SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p Pauli.X))},
          DerivWF hB Surface.code.body (D.distance + 2) (Env.cons x rho) E →
          DerivWF (hAntiZX Δ' lift hA hB) Surface.code.body (D.distance + 2) (Env.cons x rho) E)
    (hCtx : SFormula.ContextHolds Surface.code.body (D.distance + 2) rho E Γ) :
    DerivWF (pairCommutePointwise D hEntryAF hEntryBF hAntiXZ hAntiZX)
      Surface.code.body (D.distance + 2) rho E := by
  unfold pairCommutePointwise
  refine derivWF_commutesOfPointwise ?child ?fd
  case child =>
    show DerivWF (SFormula.Deriv.allNatLtIntroBounded _ _ _) _ _ _ _
    refine derivWF_allNatLtIntroBounded _ _ ⟨nQubits D.distance, ?_, ?_⟩
    · simp [nP2, SC.closed, STerm.eval, Term.eval, Term.lift]
    intro x hx
    refine ⟨?_, hCtx⟩
    have hAe : ∃ v, (STerm.stabAt (rowA D).weaken SFormula.boundNat).eval Surface.code.body
        (D.distance + 2) (Env.cons x rho) E = some v := by
      obtain ⟨sa, hsa, htot⟩ := recCall_total_symbolicDK_all D.index (D.distance + 2)
        (by simp only [OddSurfaceDistance.distance, oddDistance]; omega) (Env.cons x rho)
        (dT := dP3 D) (kT := k1P3)
        (fun f' => by simp [dP3, dP2, Term.eval, Term.lift,
          OddSurfaceDistance.distance, oddDistance]) (.var _)
      refine sterm_eval_stabAt (sv := sa) (qv := x) ?_ ?_ (htot x)
      · rw [rowA_weaken]; simpa [SC.closed, STerm.eval] using hsa
      · simp [SFormula.boundNat, SC.closed, STerm.eval, Term.eval, Env.cons]
    have hBe : ∃ v, (STerm.stabAt (rowB D).weaken SFormula.boundNat).eval Surface.code.body
        (D.distance + 2) (Env.cons x rho) E = some v := by
      obtain ⟨sa, hsa, htot⟩ := recCall_total_symbolicDK_all D.index (D.distance + 2)
        (by simp only [OddSurfaceDistance.distance, oddDistance]; omega) (Env.cons x rho)
        (dT := dP3 D) (kT := k2P3)
        (fun f' => by simp [dP3, dP2, Term.eval, Term.lift,
          OddSurfaceDistance.distance, oddDistance]) (.var _)
      refine sterm_eval_stabAt (sv := sa) (qv := x) ?_ ?_ (htot x)
      · rw [rowB_weaken]; simpa [SC.closed, STerm.eval] using hsa
      · simp [SFormula.boundNat, SC.closed, STerm.eval, Term.eval, Env.cons]
    exact localDispatch_WF D
      (entryAAtBound_WF D (cw1_WF (derivWF_weakenFresh wEntryAF)) (derivWF_hyp _))
      (entryBAtBound_WF D (cw1_WF (derivWF_weakenFresh wEntryBF)) (derivWF_hyp _))
      (wAntiXZ x) (wAntiZX x) hAe hBe
  case fd =>
    obtain ⟨saA, hsaA, htotA⟩ := recCall_total_symbolicDK_all D.index (D.distance + 2)
      (by simp only [OddSurfaceDistance.distance, oddDistance]; omega) rho
      (dT := dP2 D) (kT := k1P)
      (fun f' => by simp [dP2, Term.eval, Term.lift,
        OddSurfaceDistance.distance, oddDistance]) (.var _)
    obtain ⟨saB, hsaB, htotB⟩ := recCall_total_symbolicDK_all D.index (D.distance + 2)
      (by simp only [OddSurfaceDistance.distance, oddDistance]; omega) rho
      (dT := dP2 D) (kT := k2P)
      (fun f' => by simp [dP2, Term.eval, Term.lift,
        OddSurfaceDistance.distance, oddDistance]) (.var _)
    refine formulaDefined_commutesUpTo (nv := nQubits D.distance) (Av := saA) (Bv := saB)
      ?_ ?_ ?_ (fun q _ => htotA q) (fun q _ => htotB q)
    · simp [nP2, SC.closed, STerm.eval, Term.eval, Term.lift]
    · simpa [rowA, SC.closed, STerm.eval] using hsaA
    · simpa [rowB, SC.closed, STerm.eval] using hsaB

end QHL.CodeLang.Surface.Verify
