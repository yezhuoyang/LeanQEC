import QStab.QHL.Verify.SurfaceNormalizers.XClassB

/-!
# Logical-normalizer consumers — XTop

X top-level: bundle the supporting packs and classify `k`; the pointwise Z-handler helpers
and the `BundleExtract` pack projectors.
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface

set_option maxRecDepth 65536

/-! ## Top-level: bundle the supporting packs and classify `k` -/

/-- `rightClass = false → topClass = false` (since `topClass ⊆ rightClass`).
A closed-in-`k` arithmetic implication, discharged by `arithBool`. -/
abbrev topCFromRightCF (D : OddSurfaceDistance) : SFormula 1 :=
  .imp (gRightC1 D false) (gTopC1 D false)

def topCFromRightCPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (topCFromRightCF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [topCFromRightCF, gRightC1, gTopC1, topClassGuardTA, rightClassGuardTA, baseBTA,
    baseHalfTA, bulkCountTA, dX1, distAtBoundIdx, dm1TA, SFormula.eval, SC.closed, SC.b, STerm.eval,
    Term.eval, Term.lift, bind, Option.bind]
  set k := rho ⟨0, by decide⟩
  set d := D.distance
  by_cases hrc : k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)
  · have : decide (decide (k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = false := by
      rw [decide_eq_false_iff_not]; simp [hrc]
    simp only [this, Bool.false_eq_true, if_false, reduceIte]
  · have hrcd : decide (decide (k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = true := by
      rw [decide_eq_true_eq]; simp [hrc]
    have htc : decide (k - (d - 1) * (d - 1) < (d - 1) / 2) = false := by
      rw [decide_eq_false_iff_not]
      have : (d - 1) / 2 ≤ 2 * ((d - 1) / 2) := by omega
      omega
    simp only [hrcd, htc, decide_false, decide_true, Bool.false_eq_true, if_false, if_true, reduceIte]

/-- Entry-at-`q` facts at the four anti qubits, as formulas (cut into context). -/
abbrev entryAtF (D : OddSurfaceDistance) (qT : Term 1 .nat) : SFormula 1 :=
  .eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed qT))
    (SC.closed (baseLeafTreeTA (dX1 D) kX1 qT))

/-- The big conjunction of every supporting pack used by the per-`k` classification. -/
abbrev xBundleF (D : OddSurfaceDistance) : SFormula 1 :=
  .and (entryFlatF1 D)
  (.and (rightBandFalseF D)
  (.and (classAPackF D)
  (.and (qaColGuardF D)
  (.and (classABulkZPinF D)
  (.and (classBPackF D)
  (.and (qbColGuardF D)
  (.and (classBLeftZPinF D)
  (.and (entryAtF D (qa0 D))
  (.and (entryAtF D (qa1 D))
  (.and (entryAtF D (qb0 D))
  (.and (entryAtF D (qb1 D))
  (.and (topCFromRightCF D) (bandImpCZeroF D)))))))))))))

/-- Combine two PFDA facts into their conjunction. -/
def pfdaAnd {D : OddSurfaceDistance} {A B : SFormula 1}
    (hA : PureFamilyDerivA Surface.code.body (D.distance + 2) A)
    (hB : PureFamilyDerivA Surface.code.body (D.distance + 2) B) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (.and A B) :=
  PureFamilyDerivA.cut2 (SFormula.Deriv.andIntro .assumption (.hyp (by right; exact List.mem_cons_self))) hA hB

def xBundle (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (xBundleF D) :=
  pfdaAnd (entryFlatPack D) (pfdaAnd (rightBandFalsePack D)
    (pfdaAnd (classAPack D) (pfdaAnd (qaColGuardPack D)
      (pfdaAnd (classABulkZPinPack D) (pfdaAnd (classBPack D)
        (pfdaAnd (qbColGuardPack D) (pfdaAnd (classBLeftZPinPack D)
          (pfdaAnd (xEntryFlat1 D (qa0 D) (qa0_pure D))
            (pfdaAnd (xEntryFlat1 D (qa1 D) (qa1_pure D))
              (pfdaAnd (xEntryFlat1 D (qb0 D) (qb0_pure D))
                (pfdaAnd (xEntryFlat1 D (qb1 D) (qb1_pure D))
                  (pfdaAnd (topCFromRightCPack D) (bandImpCZeroPack D)))))))))))))

/-! ### Pointwise Z-handler helpers (close `Z` leaves by `k`-fact contradiction) -/

/-- A bulk-`Z` handler that kills the leaf because the cascade's `gKind D true`
contradicts a context `gKind1 D false` fact (carried via `lift`). -/
def zhBulkByKindFalse {Γ : List (SFormula 1)} (D : OddSurfaceDistance)
    (hKindF : SFormula.Deriv Γ (gKind1 D false)) :
    ∀ (Δ' : List (SFormula 2)),
      (∀ {A : SFormula 2}, SFormula.Deriv (.eqBool (logicalXColGuardAt2 D) (SC.b true)
          :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (entryFlat2F D) →
      SFormula.Deriv Δ' (.eqBool (logicalXColGuardAt2 D) (SC.b true)) →
      SFormula.Deriv Δ' (gBulk D true) → SFormula.Deriv Δ' (gBand D true) →
      SFormula.Deriv Δ' (gKind D true) → SFormula.Deriv Δ' (lcGoal D) := by
  intro Δ' lift _ _ _ _ hKindT
  have hKF : SFormula.Deriv _ (gKind D false) :=
    lift (cw2 (SFormula.Deriv.weakenFresh (A := gKind1 D false) hKindF))
  exact eqBoolContra _ hKindT hKF

/-- A bulk-`Z` handler that kills the leaf because the band-pin (`band ∧ col → c=0`)
contradicts a context `cZero1 D false` (`c ≠ 0`) fact. -/
def zhBulkByCNZ {Γ : List (SFormula 1)} (D : OddSurfaceDistance)
    (hCNZ : SFormula.Deriv Γ (cZero1 D false))
    (hImp : SFormula.Deriv Γ (bandImpCZeroF D)) :
    ∀ (Δ' : List (SFormula 2)),
      (∀ {A : SFormula 2}, SFormula.Deriv (.eqBool (logicalXColGuardAt2 D) (SC.b true)
          :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (entryFlat2F D) →
      SFormula.Deriv Δ' (.eqBool (logicalXColGuardAt2 D) (SC.b true)) →
      SFormula.Deriv Δ' (gBulk D true) → SFormula.Deriv Δ' (gBand D true) →
      SFormula.Deriv Δ' (gKind D true) → SFormula.Deriv Δ' (lcGoal D) := by
  intro Δ' lift _ hcolΔ _ hBandΔ _
  have hcolRaw : SFormula.Deriv Δ' (colGuardRaw2 D) := by rw [← colGuard2_eq]; exact hcolΔ
  -- pin: from col ∧ band → c = 0
  have hImpW : SFormula.Deriv _ (bandImpCZeroF D).weaken :=
    lift (cw2 (SFormula.Deriv.weakenFresh (A := bandImpCZeroF D) hImp))
  have hq : SFormula.Deriv _ (SFormula.witnessLt SFormula.boundNat (nQ1 D).weaken) :=
    lift (.hyp (by right; exact List.mem_cons_self))
  have hElim := SFormula.Deriv.allNatLtElim (nQ1 D).weaken ((bandImpCZeroBody D).lift 1)
    SFormula.boundNat hImpW hq
  have hBody := SFormula.Deriv.applyNatBoundNatBeta (bandImpCZeroBody D) hElim
  have hCZtrue := SFormula.Deriv.mp (SFormula.Deriv.mp hBody hcolRaw) hBandΔ
  have hCZfalse : SFormula.Deriv _ (cZero2 D false) :=
    lift (cw2 (SFormula.Deriv.weakenFresh (A := cZero1 D false) hCNZ))
  exact eqBoolContra _ hCZtrue hCZfalse

/-- A bulk-`Z` handler that kills the leaf because the cascade's `gBulk D true`
contradicts a context `gBulk1 D false` fact. -/
def zhBulkByBulkFalse {Γ : List (SFormula 1)} (D : OddSurfaceDistance)
    (hBulkF : SFormula.Deriv Γ (gBulk1 D false)) :
    ∀ (Δ' : List (SFormula 2)),
      (∀ {A : SFormula 2}, SFormula.Deriv (.eqBool (logicalXColGuardAt2 D) (SC.b true)
          :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (entryFlat2F D) →
      SFormula.Deriv Δ' (.eqBool (logicalXColGuardAt2 D) (SC.b true)) →
      SFormula.Deriv Δ' (gBulk D true) → SFormula.Deriv Δ' (gBand D true) →
      SFormula.Deriv Δ' (gKind D true) → SFormula.Deriv Δ' (lcGoal D) := by
  intro Δ' lift _ _ hBulkT _ _
  have hBF : SFormula.Deriv _ (gBulk D false) :=
    lift (cw2 (SFormula.Deriv.weakenFresh (A := gBulk1 D false) hBulkF))
  exact eqBoolContra _ hBulkT hBF

/-- A left-`Z` handler that kills the leaf because the cascade's `gBulk D false`
contradicts a context `gBulk1 D true` fact. -/
def zhLeftByBulkTrue {Γ : List (SFormula 1)} (D : OddSurfaceDistance)
    (hBulkT : SFormula.Deriv Γ (gBulk1 D true)) :
    ∀ (Δ' : List (SFormula 2)),
      (∀ {A : SFormula 2}, SFormula.Deriv (.eqBool (logicalXColGuardAt2 D) (SC.b true)
          :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (entryFlat2F D) →
      SFormula.Deriv Δ' (.eqBool (logicalXColGuardAt2 D) (SC.b true)) →
      SFormula.Deriv Δ' (gBulk D false) → SFormula.Deriv Δ' (gTopC D false) →
      SFormula.Deriv Δ' (gRightC D false) → SFormula.Deriv Δ' (gLeftC D true) →
      SFormula.Deriv Δ' (gLeftB D true) → SFormula.Deriv Δ' (lcGoal D) := by
  intro Δ' lift _ _ hBulkFΔ _ _ _ _
  have hBT : SFormula.Deriv _ (gBulk D true) :=
    lift (cw2 (SFormula.Deriv.weakenFresh (A := gBulk1 D true) hBulkT))
  exact eqBoolContra _ hBT hBulkFΔ

/-- A left-`Z` handler that kills the leaf because the cascade's `gLeftC D true`
contradicts a context `gLeftC1 D false` fact. -/
def zhLeftByLeftCFalse {Γ : List (SFormula 1)} (D : OddSurfaceDistance)
    (hLeftCF : SFormula.Deriv Γ (gLeftC1 D false)) :
    ∀ (Δ' : List (SFormula 2)),
      (∀ {A : SFormula 2}, SFormula.Deriv (.eqBool (logicalXColGuardAt2 D) (SC.b true)
          :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (entryFlat2F D) →
      SFormula.Deriv Δ' (.eqBool (logicalXColGuardAt2 D) (SC.b true)) →
      SFormula.Deriv Δ' (gBulk D false) → SFormula.Deriv Δ' (gTopC D false) →
      SFormula.Deriv Δ' (gRightC D false) → SFormula.Deriv Δ' (gLeftC D true) →
      SFormula.Deriv Δ' (gLeftB D true) → SFormula.Deriv Δ' (lcGoal D) := by
  intro Δ' lift _ _ _ _ _ hLeftCTΔ _
  have hLF : SFormula.Deriv _ (gLeftC D false) :=
    lift (cw2 (SFormula.Deriv.weakenFresh (A := gLeftC1 D false) hLeftCF))
  exact eqBoolContra _ hLeftCTΔ hLF

/-- A left-`Z` handler that kills the leaf because the cascade's `gRightC D false`
contradicts a context `gRightC1 D true` fact. -/
def zhLeftByRightCTrue {Γ : List (SFormula 1)} (D : OddSurfaceDistance)
    (hRightCT : SFormula.Deriv Γ (gRightC1 D true)) :
    ∀ (Δ' : List (SFormula 2)),
      (∀ {A : SFormula 2}, SFormula.Deriv (.eqBool (logicalXColGuardAt2 D) (SC.b true)
          :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (entryFlat2F D) →
      SFormula.Deriv Δ' (.eqBool (logicalXColGuardAt2 D) (SC.b true)) →
      SFormula.Deriv Δ' (gBulk D false) → SFormula.Deriv Δ' (gTopC D false) →
      SFormula.Deriv Δ' (gRightC D false) → SFormula.Deriv Δ' (gLeftC D true) →
      SFormula.Deriv Δ' (gLeftB D true) → SFormula.Deriv Δ' (lcGoal D) := by
  intro Δ' lift _ _ _ _ hRightCFΔ _ _
  have hRT : SFormula.Deriv _ (gRightC D true) :=
    lift (cw2 (SFormula.Deriv.weakenFresh (A := gRightC1 D true) hRightCT))
  exact eqBoolContra _ hRT hRightCFΔ

/-! ### Bundle extractors (project the 12 packs from a context `xBundleF` hyp) -/

namespace BundleExtract
variable {Γ : List (SFormula 1)} {D : OddSurfaceDistance}
def entryF (h : SFormula.Deriv Γ (xBundleF D)) : SFormula.Deriv Γ (entryFlatF1 D) :=
  SFormula.Deriv.andElimLeft h
def rbf (h : SFormula.Deriv Γ (xBundleF D)) : SFormula.Deriv Γ (rightBandFalseF D) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight h)
def classA (h : SFormula.Deriv Γ (xBundleF D)) : SFormula.Deriv Γ (classAPackF D) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight h))
def qaCol (h : SFormula.Deriv Γ (xBundleF D)) : SFormula.Deriv Γ (qaColGuardF D) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight h)))
def aPin (h : SFormula.Deriv Γ (xBundleF D)) : SFormula.Deriv Γ (classABulkZPinF D) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight h))))
def classB (h : SFormula.Deriv Γ (xBundleF D)) : SFormula.Deriv Γ (classBPackF D) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight h)))))
def qbCol (h : SFormula.Deriv Γ (xBundleF D)) : SFormula.Deriv Γ (qbColGuardF D) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight h))))))
def bPin (h : SFormula.Deriv Γ (xBundleF D)) : SFormula.Deriv Γ (classBLeftZPinF D) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight h)))))))
def eqa0 (h : SFormula.Deriv Γ (xBundleF D)) : SFormula.Deriv Γ (entryAtF D (qa0 D)) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight h))))))))
def eqa1 (h : SFormula.Deriv Γ (xBundleF D)) : SFormula.Deriv Γ (entryAtF D (qa1 D)) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
        (SFormula.Deriv.andElimRight h)))))))))
def eqb0 (h : SFormula.Deriv Γ (xBundleF D)) : SFormula.Deriv Γ (entryAtF D (qb0 D)) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
        (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight h))))))))))
def eqb1 (h : SFormula.Deriv Γ (xBundleF D)) : SFormula.Deriv Γ (entryAtF D (qb1 D)) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
        (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
          (SFormula.Deriv.andElimRight h)))))))))))
def topC (h : SFormula.Deriv Γ (xBundleF D)) : SFormula.Deriv Γ (topCFromRightCF D) :=
  h.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimLeft
def bandImpC (h : SFormula.Deriv Γ (xBundleF D)) : SFormula.Deriv Γ (bandImpCZeroF D) :=
  h.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight
end BundleExtract

/-- **The symbolic (∀ D) `logicalX` normalizer.**  For every `OddSurfaceDistance`,
`logicalX` commutes with every generated stabilizer row of the recursive Surface
code.  Proof: `allNatLtIntro` the stabilizer index `k`, `cut1` the supporting pack
bundle, then classify `k` by its (purely arithmetic) cell guards via nested
`boolCases`, dispatching each class to `commPointwiseSym` / `commTwoAntiA` /
`commTwoAntiB`. -/
def xNormCommuteSym (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2)
      (closedSF (logicalXNormalizesOddF D)) := by
  unfold closedSF logicalXNormalizesOddF Formula.normalizesCodeUpTo
  simp only [closedSF, Formula.codeRow, Term.weaken]
  refine PureFamilyDerivA.allNatLtIntro _ ?_
  -- Per-`k` goal `commGoal1 D`; cut in the bundle.
  refine PureFamilyDerivA.cut1 ?_ (xBundle D)
  -- Context: [xBundleF D].  Classify `k` by its k-only cell guards.
  open BundleExtract in
  refine SFormula.Deriv.boolCases (SC.closed (bulkGuardTA (dX1 D) kX1)) _ ?bulkT ?bulkF
  case bulkT =>
    -- bulk TRUE.  Context: [gBulk1 true, xBundle].
    refine SFormula.Deriv.boolCases (SC.closed (.eqNat (.mod kX1 (dm1TA (dX1 D))) (.natLit 0))) _ ?cz ?cnz
    case cz =>
      -- c = 0.  Context: [cZero1 true, gBulk1 true, xBundle].
      refine SFormula.Deriv.boolCases (SC.closed (baseKindGuardTA (dX1 D) kX1)) _ ?kt ?kf
      case kt =>
        -- kind TRUE → class (a).
        exact commTwoAntiA D
          (.hyp (by right; right; exact List.mem_cons_self))   -- gBulk1 true
          (.hyp (by right; exact List.mem_cons_self))          -- cZero1 true
          (.assumption)                                        -- gKind1 true
          (BundleExtract.classA (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtract.qaCol (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtract.aPin (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtract.entryF (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtract.rbf (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtract.eqa0 (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtract.eqa1 (.hyp (by right; right; right; exact List.mem_cons_self)))
      case kf =>
        -- kind FALSE → pointwise.
        refine commPointwiseSym D
          (BundleExtract.entryF (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtract.rbf (.hyp (by right; right; right; exact List.mem_cons_self)))
          (zhBulkByKindFalse D (.assumption))
          (zhLeftByBulkTrue D (.hyp (by right; right; exact List.mem_cons_self)))
    case cnz =>
      -- c ≠ 0 → pointwise.  Context: [cZero1 false, gBulk1 true, xBundle].
      refine commPointwiseSym D
        (BundleExtract.entryF (.hyp (by right; right; exact List.mem_cons_self)))
        (BundleExtract.rbf (.hyp (by right; right; exact List.mem_cons_self)))
        (zhBulkByCNZ D (.assumption)
          (BundleExtract.bandImpC (.hyp (by right; right; exact List.mem_cons_self))))
        (zhLeftByBulkTrue D (.hyp (by right; exact List.mem_cons_self)))
  case bulkF =>
    -- bulk FALSE.  Context: [gBulk1 false, xBundle].
    refine SFormula.Deriv.boolCases (SC.closed (leftClassGuardTA (dX1 D) kX1)) _ ?lt ?lf
    case lt =>
      -- leftClass TRUE.  Context: [gLeftC1 true, gBulk1 false, xBundle].
      refine SFormula.Deriv.boolCases (SC.closed (rightClassGuardTA (dX1 D) kX1)) _ ?rt ?rf
      case rt =>
        -- rightClass TRUE → pointwise.
        refine commPointwiseSym D
          (BundleExtract.entryF (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtract.rbf (.hyp (by right; right; right; exact List.mem_cons_self)))
          (zhBulkByBulkFalse D (.hyp (by right; right; exact List.mem_cons_self)))
          (zhLeftByRightCTrue D (.assumption))
      case rf =>
        -- rightClass FALSE → class (b).  Context: [gRightC1 false, gLeftC1 true, gBulk1 false, xBundle].
        exact commTwoAntiB D
          (.hyp (by right; right; exact List.mem_cons_self))          -- gBulk1 false
          (SFormula.Deriv.mp
            (BundleExtract.topC (.hyp (by right; right; right; exact List.mem_cons_self)))
            (.assumption))                                            -- gTopC1 false (from rightC false)
          (.assumption)                                              -- gRightC1 false
          (.hyp (by right; exact List.mem_cons_self))                -- gLeftC1 true
          (BundleExtract.classB (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtract.qbCol (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtract.bPin (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtract.entryF (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtract.rbf (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtract.eqb0 (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtract.eqb1 (.hyp (by right; right; right; exact List.mem_cons_self)))
    case lf =>
      -- leftClass FALSE → pointwise.  Context: [gLeftC1 false, gBulk1 false, xBundle].
      refine commPointwiseSym D
        (BundleExtract.entryF (.hyp (by right; right; exact List.mem_cons_self)))
        (BundleExtract.rbf (.hyp (by right; right; exact List.mem_cons_self)))
        (zhBulkByBulkFalse D (.hyp (by right; exact List.mem_cons_self)))
        (zhLeftByLeftCFalse D (.assumption))

end QHL.CodeLang.Surface.Verify
