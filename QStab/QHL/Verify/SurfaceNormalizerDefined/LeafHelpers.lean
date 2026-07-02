import QStab.QHL.Verify.SurfaceNormalizerDefined.Commutators

/-!
# Normalizer sub-tree definedness — LeafHelpers

Leaf helper WFs shared across all commutators (X and Z).
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

set_option maxHeartbeats 1600000

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

end QHL.CodeLang.Surface.Verify
