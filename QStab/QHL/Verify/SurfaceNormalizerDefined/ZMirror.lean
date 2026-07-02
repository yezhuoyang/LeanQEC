import QStab.QHL.Verify.SurfaceNormalizerDefined.LeafHelpers

/-!
# Normalizer sub-tree definedness — ZMirror

The Z-mirror leaf helper WFs (X/Z dual of the class-(a)/(b) helpers).
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

set_option maxHeartbeats 1600000

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

end QHL.CodeLang.Surface.Verify
