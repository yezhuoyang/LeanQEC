import QStab.QHL.Verify.SurfaceNormalizerDefined
import QStab.QHL.Verify.SurfaceRecLeafFlat

namespace QHL.CodeLang.Surface.Verify

open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface
open QHL.CodeLang.Surface.OpenStab

set_option maxHeartbeats 1600000

/-- General `eqPauli` extraction: from `eqPauli a b` evaluating `true` and `b.eval = some bv`,
recover `a.eval = some bv`. -/
theorem eqPauli_extract {arity : Nat} (a b : STerm arity .pauli) {bv : Pauli}
    {cb : Term 2 .stab} {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    (hb : STerm.eval cb fuel b rho E = some bv)
    (h : (SFormula.eqPauli a b).eval cb fuel rho E = some true) :
    STerm.eval cb fuel a rho E = some bv := by
  simp only [SFormula.eval, hb] at h
  cases ha : STerm.eval cb fuel a rho E with
  | none => rw [ha] at h; simp at h
  | some av => rw [ha] at h; simp at h; exact congrArg some h

/-- Direct eval of the (clean, recCall-free) base tree = the flat classifier.
Avoids the whnf-timeout of the tactic-built `baseLeafTreeTA_resolveA` derivation. -/
theorem baseLeafTreeTA_eval {arity d kv qv : Nat} {dT kT qT : Term arity .nat} {fuel : Nat}
    {rho : Env arity} (hd1 : 1 ≤ d) (hdodd : d % 2 = 1)
    (hdv : Term.eval Surface.code.body fuel dT rho = some d)
    (hkv : Term.eval Surface.code.body fuel kT rho = some kv)
    (hqv : Term.eval Surface.code.body fuel qT rho = some qv) :
    Term.eval Surface.code.body fuel (baseLeafTreeTA dT kT qT) rho
      = some (surfaceCellPauli d kv qv) := by
  have hdd : d * d = (d - 1) * (d - 1) + 2 * (d - 1) + 1 := by
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    simp only [Nat.add_sub_cancel, Nat.succ_mul, Nat.mul_succ]; omega
  rw [baseLeafTreeTA]
  simp only [Term.eval, bulkGuardTA_eval rho hdv hkv,
    baseBulkBandGuardTA_eval rho hdv hkv hqv, baseKindGuardTA_eval rho hdv hkv,
    topClassGuardTA_eval rho hdv hkv, topBandGuardTA_eval rho hdv hkv hqv,
    rightClassGuardTA_eval rho hdv hkv, rightBandGuardTA_eval rho hdv hkv hqv,
    leftClassGuardTA_eval rho hdv hkv, leftBandGuardTA_eval rho hdv hkv hqv,
    bottomBandGuardTA_eval rho hdv hkv hqv, Option.bind]
  unfold surfaceCellPauli baseBulkBandVal baseKindVal topClassVal topBandVal
    rightClassVal rightBandVal leftClassVal leftBandVal bottomBandVal inBulkBand bulkKind
  simp only [cellRow, cellCol, cellR, cellC, Bool.and_assoc, decide_eq_true_eq,
    Bool.and_eq_true, beq_iff_eq, decide_eq_decide]
  have hd0 : 0 < d := by omega
  split_ifs <;>
    first
      | rfl
      | omega
      | simp_all (config := {decide := true}) [Nat.div_eq_zero_iff, hd0]
      | (exfalso; omega)
  all_goals (split_ifs <;> first | rfl | assumption | omega | (exfalso; omega) | simp_all (config := {decide := true}) [Nat.div_eq_zero_iff, hd0])

/-- **The recCall-free bridge** `rowSymTreeA eval = recLeaf`, by induction on `m`,
evaluating the clean (recCall-free) symbolic tree. -/
theorem rowSymTreeA_eval {fuel : Nat} :
    (m : Nat) → (D : DistAtA 0 m) → (kT qT : Term 0 .nat) → (kv qv : Nat) →
    SFormula.PureNatTerm kT → SFormula.PureNatTerm qT →
    (∀ rho, Term.eval Surface.code.body fuel kT rho = some kv) →
    (∀ rho, Term.eval Surface.code.body fuel qT rho = some qv) →
    ∀ (rho : Env 0),
      Term.eval Surface.code.body fuel (rowSymTreeA m D.dT kT qT) rho = some (recLeaf m kv qv)
  | 0, D, kT, qT, kv, qv, _hk, _hq, hkv, hqv, rho => by
      rw [rowSymTreeA, recLeaf]
      exact baseLeafTreeTA_eval (by decide) (by decide) (D.evalsTo rho) (hkv rho) (hqv rho)
  | m + 1, D, kT, qT, kv, qv, hk, hq, hkv, hqv, rho => by
      have hdv := D.evalsTo (fuel := fuel) rho
      set d := oddDistance (m + 1) with hd_def
      have hd1 : 1 ≤ d := by rw [hd_def]; simp only [oddDistance]; omega
      have hdodd : d % 2 = 1 := by rw [hd_def]; simp only [oddDistance]; omega
      have hInt := rowSymTreeA_eval m (DistAtA.pred D) (interiorKTA D.dT kT) (innerQTA D.dT qT)
        (innerInteriorK d kv) (innerQval d qv) (interiorKTA_pure D.pure hk) (innerQTA_pure D.pure hq)
        (fun r => interiorKTA_evalsTo r (D.evalsTo r) (hkv r))
        (fun r => innerQTA_evalsTo r (D.evalsTo r) (hqv r)) rho
      have hTop := rowSymTreeA_eval m (DistAtA.pred D) (topKTA D.dT kT) (innerQTA D.dT qT)
        (innerTopK d kv) (innerQval d qv) (topKTA_pure D.pure hk) (innerQTA_pure D.pure hq)
        (fun r => topKTA_evalsTo r (D.evalsTo r) (hkv r))
        (fun r => innerQTA_evalsTo r (D.evalsTo r) (hqv r)) rho
      have hRight := rowSymTreeA_eval m (DistAtA.pred D) (rightKTA D.dT kT) (innerQTA D.dT qT)
        (innerRightK d kv) (innerQval d qv) (rightKTA_pure D.pure hk) (innerQTA_pure D.pure hq)
        (fun r => rightKTA_evalsTo r (D.evalsTo r) (hkv r))
        (fun r => innerQTA_evalsTo r (D.evalsTo r) (hqv r)) rho
      have hLeft := rowSymTreeA_eval m (DistAtA.pred D) (leftKTA D.dT kT) (innerQTA D.dT qT)
        (innerLeftK d kv) (innerQval d qv) (leftKTA_pure D.pure hk) (innerQTA_pure D.pure hq)
        (fun r => leftKTA_evalsTo r (D.evalsTo r) (hkv r))
        (fun r => innerQTA_evalsTo r (D.evalsTo r) (hqv r)) rho
      have hBottom := rowSymTreeA_eval m (DistAtA.pred D) (bottomKTA D.dT kT) (innerQTA D.dT qT)
        (innerBottomK d kv) (innerQval d qv) (bottomKTA_pure D.pure hk) (innerQTA_pure D.pure hq)
        (fun r => bottomKTA_evalsTo r (D.evalsTo r) (hkv r))
        (fun r => innerQTA_evalsTo r (D.evalsTo r) (hqv r)) rho
      have hBase := baseLeafTreeTA_eval hd1 hdodd hdv (hkv rho) (hqv rho)
      have hd0 : 0 < d := by omega
      have hdd : d * d = (d - 1) * (d - 1) + 2 * (d - 1) + 1 := by
        obtain ⟨e, he⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
        rw [he]; simp only [Nat.add_sub_cancel, Nat.succ_mul, Nat.mul_succ]; omega
      rw [rowSymTreeA]
      simp only [recLeafTreeTA, recInteriorChainTA, recTopChainTA, recRightChainTA,
        recLeftChainTA, recBottomChainTA, Term.eval,
        bulkGuardTA_eval rho hdv (hkv rho), interiorCellGuardTA_eval rho hdv (hkv rho),
        insideGuardTA_eval rho hdv (hqv rho), topCellGuardTA_eval rho hdv (hkv rho),
        rightCellGuardTA_eval rho hdv (hkv rho), leftCellGuardTA_eval rho hdv (hkv rho),
        bottomCellGuardTA_eval rho hdv (hkv rho),
        topOuterGuardTA_eval rho hdv (hkv rho) (hqv rho),
        rightOuterGuardTA_eval rho hdv (hkv rho) (hqv rho),
        leftOuterGuardTA_eval rho hdv (hkv rho) (hqv rho),
        bottomOuterGuardTA_eval rho hdv (hkv rho) (hqv rho),
        hInt, hTop, hRight, hLeft, hBottom, hBase, Option.bind]
      rw [recLeaf, ← hd_def]
      split_ifs <;> first | rfl | assumption | omega | (exfalso; omega) | simp_all (config := {decide := true, maxSteps := 1000000}) [surfaceCellPauli_topCell_notInside, surfaceCellPauli_rightCell_notInside, surfaceCellPauli_leftCell_notInside, surfaceCellPauli_bottomCell_notInside, Nat.div_eq_zero_iff, hd0]
      all_goals ((try split_ifs) <;> first | rfl | assumption | omega | (exfalso; omega) | simp_all (config := {decide := true, maxSteps := 2000000}) [surfaceCellPauli_topCell_notInside, surfaceCellPauli_rightCell_notInside, surfaceCellPauli_leftCell_notInside, surfaceCellPauli_bottomCell_notInside, surfaceCellPauli, inBulkBand, bulkKind, baseBulkBandVal, baseKindVal, topClassVal, topBandVal, rightClassVal, rightBandVal, leftClassVal, leftBandVal, bottomBandVal, cellRow, cellCol, cellR, cellC, Bool.and_assoc, Nat.div_eq_zero_iff, hd0])

/-- **The char eval via the proven Symbolic WF** + the recCall-free bridge.
NOTE: `hbridge` (`rowSymTreeA eval = recLeaf`) is proved *directly* (not via the
`resolveA` derivation soundness, whose WF whnf-times-out) — see `rowSymTreeA_eval` below. -/
theorem recCall_eval_recLeaf (D : OddSurfaceDistance) (kv qv : Nat) (E : PartialStabilizer) :
    (STerm.stabAt (SC.closed (Term.recCall (Term.natLit D.distance) (Term.natLit kv)))
        (SC.closed (Term.natLit qv))).eval Surface.code.body (D.distance + 2) Env.empty E
      = some (recLeaf D.index kv qv) := by
  have hbridge : STerm.eval Surface.code.body (D.distance + 2)
        (SC.closed (rowSymTreeA D.index (Term.natLit D.distance) (Term.natLit kv)
          (Term.natLit qv))) Env.empty E
      = some (recLeaf D.index kv qv) := by
    have h := rowSymTreeA_eval (fuel := D.distance + 2) D.index (DistAtA.lit 0 D.index)
      (Term.natLit kv) (Term.natLit qv) kv qv (SFormula.PureNatTerm.nat kv)
      (SFormula.PureNatTerm.nat qv) (fun r => by simp [Term.eval])
      (fun r => by simp [Term.eval]) Env.empty
    simpa [SC.closed, STerm.eval, DistAtA.lit, OddSurfaceDistance.distance] using h
  have hfuel : D.index + 2 ≤ D.distance + 2 := by
    simp only [OddSurfaceDistance.distance, oddDistance]; omega
  have hwf := surfaceRowEntryCharSymbolicA_WF (fuel := D.distance + 2) D.index
    (DistAtA.lit 0 D.index) (Term.natLit kv) (Term.natLit qv)
    (SFormula.PureNatTerm.nat kv) (SFormula.PureNatTerm.nat qv) Env.empty E hfuel
  have hdef := pfda_defined _ Env.empty E hwf
  have hsound := PureFamilyDerivA.sound
    (surfaceRowEntryCharSymbolicA (fuel := D.distance + 2) D.index (DistAtA.lit 0 D.index)
      (Term.natLit kv) (Term.natLit qv) (SFormula.PureNatTerm.nat kv) (SFormula.PureNatTerm.nat qv))
    Env.empty E hdef
  exact eqPauli_extract _ _ hbridge hsound


/-- **The full gateway**: `stabAt(recCall d k) q` evaluates to the flat classifier
`surfaceCellPauli d k q`, for every odd distance. -/
theorem recCall_eval_surfaceCellPauli (D : OddSurfaceDistance) (kv qv : Nat)
    (E : PartialStabilizer) :
    (STerm.stabAt (SC.closed (Term.recCall (Term.natLit D.distance) (Term.natLit kv)))
        (SC.closed (Term.natLit qv))).eval Surface.code.body (D.distance + 2) Env.empty E
      = some (surfaceCellPauli D.distance kv qv) := by
  rw [recCall_eval_recLeaf, recLeaf_eq_surfaceCellPauli]
  rfl

