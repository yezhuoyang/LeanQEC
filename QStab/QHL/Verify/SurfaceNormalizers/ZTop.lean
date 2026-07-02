import QStab.QHL.Verify.SurfaceNormalizers.ZClassB

/-!
# Logical-normalizer consumers — ZTop

Z top-level: bundle the supporting packs and classify `k`; the pointwise X-handler helpers,
the Z supporting-pack bundle (`BundleExtractZ`), and the classification driver.
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface

set_option maxRecDepth 65536

/-! ## Top-level [Z]: bundle the supporting packs and classify `k`

The transpose of the `logicalX` top-level assembly: bundle every supporting pack,
then classify `k` by its (purely arithmetic) cell guards via nested `boolCases`,
dispatching each class to `commPointwiseZSym` / `commZTwoAntiA` / `commZTwoAntiB`. -/

/-- On row 0, if the bulk band fires then `r = k/(d-1) = 0`.  Quantified over
`q < nQubits`.  Transpose of `bandImpCZeroPack`. -/
abbrev bandImpRZeroBody (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (rowGuardRaw2 D)
    (.imp (.eqBool (SC.closed (baseBulkBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.b true))
      (gRZero2 D true))

abbrev bandImpRZeroF (D : OddSurfaceDistance) : SFormula 1 :=
  .allNatLt (nQ1 D) (bandImpRZeroBody D)

def bandImpRZeroPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (bandImpRZeroF D) := by
  refine PureFamilyDerivA.allNatLtIntro _ ?_
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [bandImpRZeroBody, rowGuardRaw2, baseBulkBandGuardTA, gRZero2, dX2,
    distAtBoundIdx2, kX2, dm1TA, orEqSucc, band3, bulkCountTA, SFormula.eval, SC.closed, SC.b,
    STerm.eval, Term.eval, Term.lift, bind, Option.bind]
  set q := rho ⟨0, by decide⟩ with hq'
  set k := rho ⟨1, by decide⟩ with hk'
  set d := D.distance with hdd
  have hdpos : 0 < d := by omega
  by_cases hq : q / d = 0
  · rw [hq]
    by_cases hrz : k / (d - 1) = 0
    · -- r = 0 → conclusion `decide (k/(d-1)=0) = true` holds; whatever the band
      -- evaluates to, the implication result is `some true`.
      rw [hrz]
      by_cases hc0 : q % d = k % (d - 1)
      · simp only [hc0, if_true]
        cases (decide (k < (d - 1) * (d - 1))) <;> simp
      · by_cases hc1 : q % d = k % (d - 1) + 1 <;> simp_all
    · -- r ≠ 0 → on row 0 the band disjuncts `0 = r`, `0 = r+1` are false, band false.
      have hb0 : decide (0 = k / (d - 1)) = false := by
        rw [decide_eq_false_iff_not]; exact fun h => hrz h.symm
      have hb1 : decide (0 = k / (d - 1) + 1) = false := by
        rw [decide_eq_false_iff_not]; exact fun h => Nat.succ_ne_zero _ h.symm
      simp only [hb0, hb1, decide_false, Bool.false_eq_true, if_false]
      cases (decide (k / (d - 1) = 0)) <;> simp
  · simp only [hq, decide_false, Bool.false_eq_true, if_false]

/-! ### Pointwise X-handler helpers (close `X` leaves by `k`-fact contradiction) -/

/-- A bulk-`X` handler that kills the leaf because the cascade's `gKind D false`
contradicts a context `gKind1 D true` fact. -/
def zhXbulkByKindTrue {Γ : List (SFormula 1)} (D : OddSurfaceDistance)
    (hKindT : SFormula.Deriv Γ (gKind1 D true)) :
    ∀ (Δ' : List (SFormula 2)),
      (∀ {A : SFormula 2}, SFormula.Deriv (.eqBool (logicalZRowGuardAt2 D) (SC.b true)
          :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (entryFlat2F D) →
      SFormula.Deriv Δ' (.eqBool (logicalZRowGuardAt2 D) (SC.b true)) →
      SFormula.Deriv Δ' (gBulk D true) → SFormula.Deriv Δ' (gBand D true) →
      SFormula.Deriv Δ' (gKind D false) → SFormula.Deriv Δ' (lcGoalZ D) := by
  intro Δ' lift _ _ _ _ hKindF
  have hKT : SFormula.Deriv _ (gKind D true) :=
    lift (cw2 (SFormula.Deriv.weakenFresh (A := gKind1 D true) hKindT))
  exact eqBoolContra _ hKT hKindF

/-- A bulk-`X` handler that kills the leaf because the band-pin (`band ∧ row → r=0`)
contradicts a context `gRZero1 D false` (`r ≠ 0`) fact. -/
def zhXbulkByRNZ {Γ : List (SFormula 1)} (D : OddSurfaceDistance)
    (hRNZ : SFormula.Deriv Γ (gRZero1 D false))
    (hImp : SFormula.Deriv Γ (bandImpRZeroF D)) :
    ∀ (Δ' : List (SFormula 2)),
      (∀ {A : SFormula 2}, SFormula.Deriv (.eqBool (logicalZRowGuardAt2 D) (SC.b true)
          :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (entryFlat2F D) →
      SFormula.Deriv Δ' (.eqBool (logicalZRowGuardAt2 D) (SC.b true)) →
      SFormula.Deriv Δ' (gBulk D true) → SFormula.Deriv Δ' (gBand D true) →
      SFormula.Deriv Δ' (gKind D false) → SFormula.Deriv Δ' (lcGoalZ D) := by
  intro Δ' lift _ hrowΔ _ hBandΔ _
  have hrowRaw : SFormula.Deriv Δ' (rowGuardRaw2 D) := by rw [← rowGuard2_eq]; exact hrowΔ
  have hImpW : SFormula.Deriv _ (bandImpRZeroF D).weaken :=
    lift (cw2 (SFormula.Deriv.weakenFresh (A := bandImpRZeroF D) hImp))
  have hq : SFormula.Deriv _ (SFormula.witnessLt SFormula.boundNat (nQ1 D).weaken) :=
    lift (.hyp (by right; exact List.mem_cons_self))
  have hElim := SFormula.Deriv.allNatLtElim (nQ1 D).weaken ((bandImpRZeroBody D).lift 1)
    SFormula.boundNat hImpW hq
  have hBody := SFormula.Deriv.applyNatBoundNatBeta (bandImpRZeroBody D) hElim
  have hRZtrue := SFormula.Deriv.mp (SFormula.Deriv.mp hBody hrowRaw) hBandΔ
  have hRZfalse : SFormula.Deriv _ (gRZero2 D false) :=
    lift (cw2 (SFormula.Deriv.weakenFresh (A := gRZero1 D false) hRNZ))
  exact eqBoolContra _ hRZtrue hRZfalse

/-- A bulk-`X` handler that kills the leaf because the cascade's `gBulk D true`
contradicts a context `gBulk1 D false` fact. -/
def zhXbulkByBulkFalse {Γ : List (SFormula 1)} (D : OddSurfaceDistance)
    (hBulkF : SFormula.Deriv Γ (gBulk1 D false)) :
    ∀ (Δ' : List (SFormula 2)),
      (∀ {A : SFormula 2}, SFormula.Deriv (.eqBool (logicalZRowGuardAt2 D) (SC.b true)
          :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (entryFlat2F D) →
      SFormula.Deriv Δ' (.eqBool (logicalZRowGuardAt2 D) (SC.b true)) →
      SFormula.Deriv Δ' (gBulk D true) → SFormula.Deriv Δ' (gBand D true) →
      SFormula.Deriv Δ' (gKind D false) → SFormula.Deriv Δ' (lcGoalZ D) := by
  intro Δ' lift _ _ hBulkT _ _
  have hBF : SFormula.Deriv _ (gBulk D false) :=
    lift (cw2 (SFormula.Deriv.weakenFresh (A := gBulk1 D false) hBulkF))
  exact eqBoolContra _ hBulkT hBF

/-- A top-`X` handler that kills the leaf because the cascade's `gBulk D false`
contradicts a context `gBulk1 D true` fact. -/
def zhXtopByBulkTrue {Γ : List (SFormula 1)} (D : OddSurfaceDistance)
    (hBulkT : SFormula.Deriv Γ (gBulk1 D true)) :
    ∀ (Δ' : List (SFormula 2)),
      (∀ {A : SFormula 2}, SFormula.Deriv (.eqBool (logicalZRowGuardAt2 D) (SC.b true)
          :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (entryFlat2F D) →
      SFormula.Deriv Δ' (.eqBool (logicalZRowGuardAt2 D) (SC.b true)) →
      SFormula.Deriv Δ' (gBulk D false) → SFormula.Deriv Δ' (gTopC D true) →
      SFormula.Deriv Δ' (gTopB D true) → SFormula.Deriv Δ' (lcGoalZ D) := by
  intro Δ' lift _ _ hBulkFΔ _ _
  have hBT : SFormula.Deriv _ (gBulk D true) :=
    lift (cw2 (SFormula.Deriv.weakenFresh (A := gBulk1 D true) hBulkT))
  exact eqBoolContra _ hBT hBulkFΔ

/-- A top-`X` handler that kills the leaf because the cascade's `gTopC D true`
contradicts a context `gTopC1 D false` fact. -/
def zhXtopByTopCFalse {Γ : List (SFormula 1)} (D : OddSurfaceDistance)
    (hTopCF : SFormula.Deriv Γ (gTopC1 D false)) :
    ∀ (Δ' : List (SFormula 2)),
      (∀ {A : SFormula 2}, SFormula.Deriv (.eqBool (logicalZRowGuardAt2 D) (SC.b true)
          :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (entryFlat2F D) →
      SFormula.Deriv Δ' (.eqBool (logicalZRowGuardAt2 D) (SC.b true)) →
      SFormula.Deriv Δ' (gBulk D false) → SFormula.Deriv Δ' (gTopC D true) →
      SFormula.Deriv Δ' (gTopB D true) → SFormula.Deriv Δ' (lcGoalZ D) := by
  intro Δ' lift _ _ _ hTopCTΔ _
  have hTF : SFormula.Deriv _ (gTopC D false) :=
    lift (cw2 (SFormula.Deriv.weakenFresh (A := gTopC1 D false) hTopCF))
  exact eqBoolContra _ hTopCTΔ hTF

/-! ### The Z supporting-pack bundle and the classification driver -/

/-- The big conjunction of every supporting pack used by the per-`k` [Z]
classification.  Transpose of `xBundleF`. -/
abbrev zBundleF (D : OddSurfaceDistance) : SFormula 1 :=
  .and (entryFlatF1 D)
  (.and (bottomBandFalseF D)
  (.and (classZAPackF D)
  (.and (qzaRowGuardF D)
  (.and (classZABulkXPinF D)
  (.and (classZBPackF D)
  (.and (qzbRowGuardF D)
  (.and (classZBTopXPinF D)
  (.and (entryAtF D (qza0 D))
  (.and (entryAtF D (qza1 D))
  (.and (entryAtF D (qzb0 D))
  (.and (entryAtF D (qzb1 D))
  (bandImpRZeroF D))))))))))))

def zBundle (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (zBundleF D) :=
  pfdaAnd (entryFlatPack D) (pfdaAnd (bottomBandFalsePack D)
    (pfdaAnd (classZAPack D) (pfdaAnd (qzaRowGuardPack D)
      (pfdaAnd (classZABulkXPinPack D) (pfdaAnd (classZBPack D)
        (pfdaAnd (qzbRowGuardPack D) (pfdaAnd (classZBTopXPinPack D)
          (pfdaAnd (xEntryFlat1 D (qza0 D) (qza0_pure D))
            (pfdaAnd (xEntryFlat1 D (qza1 D) (qza1_pure D))
              (pfdaAnd (xEntryFlat1 D (qzb0 D) (qzb0_pure D))
                (pfdaAnd (xEntryFlat1 D (qzb1 D) (qzb1_pure D))
                  (bandImpRZeroPack D))))))))))))

namespace BundleExtractZ
variable {Γ : List (SFormula 1)} {D : OddSurfaceDistance}
def entryF (h : SFormula.Deriv Γ (zBundleF D)) : SFormula.Deriv Γ (entryFlatF1 D) :=
  SFormula.Deriv.andElimLeft h
def bbf (h : SFormula.Deriv Γ (zBundleF D)) : SFormula.Deriv Γ (bottomBandFalseF D) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight h)
def classA (h : SFormula.Deriv Γ (zBundleF D)) : SFormula.Deriv Γ (classZAPackF D) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight h))
def qzaRow (h : SFormula.Deriv Γ (zBundleF D)) : SFormula.Deriv Γ (qzaRowGuardF D) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight h)))
def aPin (h : SFormula.Deriv Γ (zBundleF D)) : SFormula.Deriv Γ (classZABulkXPinF D) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight h))))
def classB (h : SFormula.Deriv Γ (zBundleF D)) : SFormula.Deriv Γ (classZBPackF D) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight h)))))
def qzbRow (h : SFormula.Deriv Γ (zBundleF D)) : SFormula.Deriv Γ (qzbRowGuardF D) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight h))))))
def bPin (h : SFormula.Deriv Γ (zBundleF D)) : SFormula.Deriv Γ (classZBTopXPinF D) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight h)))))))
def eqa0 (h : SFormula.Deriv Γ (zBundleF D)) : SFormula.Deriv Γ (entryAtF D (qza0 D)) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight h))))))))
def eqa1 (h : SFormula.Deriv Γ (zBundleF D)) : SFormula.Deriv Γ (entryAtF D (qza1 D)) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
        (SFormula.Deriv.andElimRight h)))))))))
def eqb0 (h : SFormula.Deriv Γ (zBundleF D)) : SFormula.Deriv Γ (entryAtF D (qzb0 D)) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
        (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight h))))))))))
def eqb1 (h : SFormula.Deriv Γ (zBundleF D)) : SFormula.Deriv Γ (entryAtF D (qzb1 D)) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
        (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
          (SFormula.Deriv.andElimRight h)))))))))))
def bandImpR (h : SFormula.Deriv Γ (zBundleF D)) : SFormula.Deriv Γ (bandImpRZeroF D) :=
  h.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight
end BundleExtractZ

/-- **The symbolic (∀ D) `logicalZ` normalizer.**  For every `OddSurfaceDistance`,
`logicalZ` commutes with every generated stabilizer row of the recursive Surface
code.  Transpose of `xNormCommuteSym`: `allNatLtIntro` the stabilizer index `k`,
`cut1` the Z pack bundle, then classify `k` by its (purely arithmetic) cell guards
via nested `boolCases`, dispatching each class to `commPointwiseZSym` /
`commZTwoAntiA` / `commZTwoAntiB`. -/
def zNormCommuteSym (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2)
      (closedSF (logicalZNormalizesOddF D)) := by
  unfold closedSF logicalZNormalizesOddF Formula.normalizesCodeUpTo
  simp only [closedSF, Formula.codeRow, Term.weaken]
  refine PureFamilyDerivA.allNatLtIntro _ ?_
  refine PureFamilyDerivA.cut1 ?_ (zBundle D)
  -- Context: [zBundleF D].  Classify `k` by its k-only cell guards.
  open BundleExtractZ in
  refine SFormula.Deriv.boolCases (SC.closed (bulkGuardTA (dX1 D) kX1)) _ ?bulkT ?bulkF
  case bulkT =>
    -- bulk TRUE.  Context: [gBulk1 true, zBundle].
    refine SFormula.Deriv.boolCases (SC.closed (.eqNat (.div kX1 (dm1TA (dX1 D))) (.natLit 0))) _ ?rz ?rnz
    case rz =>
      -- r = 0.  Context: [gRZero1 true, gBulk1 true, zBundle].
      refine SFormula.Deriv.boolCases (SC.closed (baseKindGuardTA (dX1 D) kX1)) _ ?kt ?kf
      case kt =>
        -- kind TRUE → pointwise.
        refine commPointwiseZSym D
          (BundleExtractZ.entryF (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtractZ.bbf (.hyp (by right; right; right; exact List.mem_cons_self)))
          (zhXbulkByKindTrue D (.assumption))
          (zhXtopByBulkTrue D (.hyp (by right; right; exact List.mem_cons_self)))
      case kf =>
        -- kind FALSE → class (a).
        exact commZTwoAntiA D
          (.hyp (by right; right; exact List.mem_cons_self))   -- gBulk1 true
          (.hyp (by right; exact List.mem_cons_self))          -- gRZero1 true
          (.assumption)                                        -- gKind1 false
          (BundleExtractZ.classA (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtractZ.qzaRow (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtractZ.aPin (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtractZ.entryF (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtractZ.bbf (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtractZ.eqa0 (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtractZ.eqa1 (.hyp (by right; right; right; exact List.mem_cons_self)))
    case rnz =>
      -- r ≠ 0 → pointwise.  Context: [gRZero1 false, gBulk1 true, zBundle].
      refine commPointwiseZSym D
        (BundleExtractZ.entryF (.hyp (by right; right; exact List.mem_cons_self)))
        (BundleExtractZ.bbf (.hyp (by right; right; exact List.mem_cons_self)))
        (zhXbulkByRNZ D (.assumption)
          (BundleExtractZ.bandImpR (.hyp (by right; right; exact List.mem_cons_self))))
        (zhXtopByBulkTrue D (.hyp (by right; exact List.mem_cons_self)))
  case bulkF =>
    -- bulk FALSE.  Context: [gBulk1 false, zBundle].
    refine SFormula.Deriv.boolCases (SC.closed (topClassGuardTA (dX1 D) kX1)) _ ?tt ?tf
    case tt =>
      -- topClass TRUE → class (b).
      exact commZTwoAntiB D
        (.hyp (by right; exact List.mem_cons_self))          -- gBulk1 false
        (.assumption)                                        -- gTopC1 true
        (BundleExtractZ.classB (.hyp (by right; right; exact List.mem_cons_self)))
        (BundleExtractZ.qzbRow (.hyp (by right; right; exact List.mem_cons_self)))
        (BundleExtractZ.bPin (.hyp (by right; right; exact List.mem_cons_self)))
        (BundleExtractZ.entryF (.hyp (by right; right; exact List.mem_cons_self)))
        (BundleExtractZ.bbf (.hyp (by right; right; exact List.mem_cons_self)))
        (BundleExtractZ.eqb0 (.hyp (by right; right; exact List.mem_cons_self)))
        (BundleExtractZ.eqb1 (.hyp (by right; right; exact List.mem_cons_self)))
    case tf =>
      -- topClass FALSE → pointwise.  Context: [gTopC1 false, gBulk1 false, zBundle].
      refine commPointwiseZSym D
        (BundleExtractZ.entryF (.hyp (by right; right; exact List.mem_cons_self)))
        (BundleExtractZ.bbf (.hyp (by right; right; exact List.mem_cons_self)))
        (zhXbulkByBulkFalse D (.hyp (by right; exact List.mem_cons_self)))
        (zhXtopByTopCFalse D (.assumption))


/-- Scaffold: reduce `logicalXNormalizesOddF` to the per-row commutation of the
resolved tree against `logicalX`.

* `allNatLtIntro` introduces the stabilizer index `k = var 0` (arity 1).
* `cut1 _ boundRowsResolved` makes the resolved-row equality
  `∀ q < n, stabAt (recCall (lift d) k) q = rowSymTreeA D.index (lift d) k q`
  available as an `SFormula.Deriv` hypothesis, eliminating `recCall`.

The remaining `SFormula.Deriv` goal is
  `commutesUpTo n (recCall (lift d) (var 0)) (lift logicalX)`.
The OFF-column-0 half of this is fully discharged by the sorry-free reusable
lemma `logicalXOffColumnLocalCommutes` (the `logicalX` entry is `I` wherever the
column guard is `false`).  What genuinely remains is the COLUMN-0 even-parity
argument: classify `k` by geometry and supply, via `commutesOfTwoAnti`, the two
column-0 qubits `q0 k, q1 k` where the Z-type row anticommutes with `logicalX`
(and `commutesOfPointwise` for X-type rows).  Identifying `q0/q1` as functions of
the symbolic recursion depth `D.index` mirrors the whole `rowSymTreeA` recursion
and is the genuinely deep residual — OPEN. -/
def xNormScaffold (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2)
      (closedSF (logicalXNormalizesOddF D)) :=
  -- Closed by the symbolic geometric classification developed above: classify the
  -- bound stabilizer index `k` by its (purely arithmetic) cell guards, and supply
  -- the two anticommuting column-0 qubits for the Z-type rows (`commutesOfTwoAnti`,
  -- classes (a) and (b)) and pointwise commutation for the X/I-type rows.
  xNormCommuteSym D

/-- Scaffold for `zNorm` — the transpose of `xNormScaffold`.  Identical reduction:
`allNatLtIntro` + `cut1 _ boundRowsResolved` discharge `recCall`, leaving the
`SFormula.Deriv` goal `commutesUpTo n (recCall (lift d) (var 0)) (lift logicalZ)`.
The OFF-row half is fully discharged by the sorry-free reusable lemma
`logicalZOffRowLocalCommutes` (the `logicalZ` entry is `I` wherever the row guard
`q / d = 0` is `false`).  The residual is the TOP-ROW even-parity argument —
the row/column transpose of `xNorm`'s frontier — supplying the two anti qubits
for Z-vs-Z overlaps via `commutesOfTwoAnti`, by recursion on `D.index`.
Genuinely deep; OPEN at the same isolated frontier. -/
def zNormScaffold (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2)
      (closedSF (logicalZNormalizesOddF D)) :=
  -- Closed by the symbolic geometric classification developed above (the transpose
  -- of `xNormCommuteSym`): classify the bound stabilizer index `k` by its (purely
  -- arithmetic) cell guards, and supply the two anticommuting ROW-0 qubits for the
  -- X-type rows (`commZTwoAntiA`/`commZTwoAntiB`, classes (a)/(b)) and pointwise
  -- commutation for the Z/I-type rows (`commPointwiseZSym`).
  zNormCommuteSym D

#print axioms logicalXOffColumnLocalCommutes
#print axioms logicalZOffRowLocalCommutes
#print axioms xNormScaffold
#print axioms xNormCommuteSym
#print axioms zNormScaffold
#print axioms zNormCommuteSym

end QHL.CodeLang.Surface.Verify
