import QStab.QHL.Verify.SurfaceNormalizers.ZSetup

/-!
# Logical-normalizer consumers — ZClassA

Two-anti class (a) [Z]: top-row odd-`c` bulk `X`-plaquettes, and their per-`k` commutation.
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface

set_option maxRecDepth 65536

/-! ## Two-anti class (a) [Z]: top-row odd-`c` bulk `X`-plaquettes

`k < (d-1)²`, `r = k/(d-1) = 0`, `c = k%(d-1)` odd (so kind FALSE).  The row
anticommutes with `logicalZ` at the two ROW-0 qubits `q0 = c`, `q1 = c+1`. -/

/-- `c = k % (d-1)` at arity 1 = first class-(a) anti qubit. -/
abbrev qza0 (D : OddSurfaceDistance) : Term 1 .nat := .mod kX1 (dm1TA (dX1 D))
/-- `c + 1` = second class-(a) anti qubit. -/
abbrev qza1 (D : OddSurfaceDistance) : Term 1 .nat := .add (.mod kX1 (dm1TA (dX1 D))) (.natLit 1)

def qza0_pure (D : OddSurfaceDistance) : SFormula.PureNatTerm (qza0 D) :=
  SFormula.PureNatTerm.mod (SFormula.PureNatTerm.var _) (dm1_pure D)
def qza1_pure (D : OddSurfaceDistance) : SFormula.PureNatTerm (qza1 D) :=
  SFormula.PureNatTerm.add (SFormula.PureNatTerm.mod (SFormula.PureNatTerm.var _) (dm1_pure D))
    (SFormula.PureNatTerm.natLit _)

/-- The class-(a) k-condition guard pack: given bulk true, `r = 0`, kind false (`c`
odd), the bulk band fires at `q0 = c` and `q1 = c+1`, `q0 ≠ q1`, both `< nQubits`. -/
abbrev classZAPackF (D : OddSurfaceDistance) : SFormula 1 :=
  .imp (gBulk1 D true) (.imp (gRZero1 D true) (.imp (gKind1 D false)
    (.and (.eqBool (SC.closed (baseBulkBandGuardTA (dX1 D) kX1 (qza0 D))) (SC.b true))
      (.and (.eqBool (SC.closed (baseBulkBandGuardTA (dX1 D) kX1 (qza1 D))) (SC.b true))
        (.and (.eqBool (SC.closed (.eqNat (qza0 D) (qza1 D))) (SC.b false))
          (.and (SFormula.witnessLt (SC.closed (qza0 D)) (SC.n (arity := 1) (nQubits D.distance)))
            (SFormula.witnessLt (SC.closed (qza1 D)) (SC.n (arity := 1) (nQubits D.distance)))))))))

def classZAPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (classZAPackF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [classZAPackF, baseBulkBandGuardTA, gBulk1, gRZero1, gKind1, qza0, qza1, dX1,
    distAtBoundIdx, dm1TA, bulkCountTA, bulkGuardTA, baseKindGuardTA, orEqSucc, band3,
    SFormula.eval, SC.closed, SC.b, SC.n, STerm.eval, SFormula.witnessLt, Term.eval, Term.lift,
    bind, Option.bind]
  set k := rho ⟨0, by decide⟩ with hk
  set d := D.distance with hdd
  have hdpos : 0 < d := by omega
  have hdge : 3 ≤ d := by omega
  by_cases hbulk : k < (d - 1) * (d - 1)
  · simp only [hbulk, decide_true, if_true]
    by_cases hr : k / (d - 1) = 0
    · simp only [hr, decide_true, if_true]
      by_cases hkind : (0 + k % (d - 1)) % 2 = 0
      · -- kind TRUE → `gKind1 D false` antecedent false → vacuous.
        have hkv : decide (decide ((0 + k % (d - 1)) % 2 = 0) = false) = false := by
          rw [decide_eq_false_iff_not]; simp only [decide_eq_false_iff_not]; omega
        simp only [hkv, Bool.false_eq_true, if_false, reduceIte]
      · -- kind FALSE (c odd): the genuine class-(a) case.
        have hkd : decide (decide ((0 + k % (d - 1)) % 2 = 0) = false) = true := by
          rw [decide_eq_true_eq, decide_eq_false_iff_not]; omega
        simp only [hkd, if_true]
        -- c = k % (d-1) < d-1, so c+1 ≤ d-1 < d; q0 = c, q1 = c+1 are row-0 qubits.
        set c := k % (d - 1) with hc
        have hclt : c < d - 1 := Nat.mod_lt _ (by omega)
        have hc0div : c / d = 0 := Nat.div_eq_of_lt (by omega)
        have hc0mod : c % d = c := Nat.mod_eq_of_lt (by omega)
        have hc1div : (c + 1) / d = 0 := Nat.div_eq_of_lt (by omega)
        have hc1mod : (c + 1) % d = c + 1 := Nat.mod_eq_of_lt (by omega)
        have hb0 : c < nQubits d := by
          have hh : c < d := by omega
          simp only [nQubits]; calc c < d := hh
            _ ≤ d * d := Nat.le_mul_of_pos_left d hdpos
        have hb1 : c + 1 < nQubits d := by
          have hh : c + 1 < d := by omega
          simp only [nQubits]; calc c + 1 < d := hh
            _ ≤ d * d := Nat.le_mul_of_pos_left d hdpos
        -- decide the band conjuncts at q0 = c (q/d=0) and q1 = c+1 (q/d=0), r = 0.
        have hd00 : decide (c / d = 0) = true := by rw [hc0div]; simp
        have hd01 : decide (c % d = c) = true := by rw [hc0mod]; simp
        have hd10a : decide ((c + 1) / d = 0) = true := by rw [hc1div]; simp
        have hd11a : decide ((c + 1) % d = c) = false := by
          rw [hc1mod]; rw [decide_eq_false_iff_not]; omega
        have hd11b : decide ((c + 1) % d = c + 1) = true := by rw [hc1mod]; simp
        have hbne : decide (c = c + 1) = false := by rw [decide_eq_false_iff_not]; omega
        have hbb0 : decide (c < nQubits d) = true := by rw [decide_eq_true_eq]; exact hb0
        have hbb1 : decide (c + 1 < nQubits d) = true := by rw [decide_eq_true_eq]; exact hb1
        simp only [hd00, hd01, hd10a, hd11a, hd11b, hbne, hbb0, hbb1, hbulk,
          decide_true, decide_false, Bool.false_eq_true, if_true, if_false, reduceIte]
    · -- r ≠ 0 → `gRZero1 D true` antecedent false → vacuous.
      have hrv : decide (k / (d - 1) = 0) = false := by rw [decide_eq_false_iff_not]; exact hr
      simp only [hrv, decide_false, Bool.false_eq_true, if_false, reduceIte]
  · -- bulk false → `gBulk1 D true` antecedent false → vacuous.
    simp only [hbulk, decide_false, Bool.false_eq_true, if_false, reduceIte]

/-- Arity-2 forms of the class-(a) [Z] anti qubits (`k = var 1`). -/
abbrev qza0_2 (D : OddSurfaceDistance) : Term 2 .nat := .mod kX2 (dm1TA (dX2 D))
abbrev qza1_2 (D : OddSurfaceDistance) : Term 2 .nat := .add (.mod kX2 (dm1TA (dX2 D))) (.natLit 1)
theorem qza0_weaken (D : OddSurfaceDistance) : (qza0 D).weaken = qza0_2 D := rfl
theorem qza1_weaken (D : OddSurfaceDistance) : (qza1 D).weaken = qza1_2 D := rfl

/-- Row guards at the two class-(a) anti qubits: `q0 / d = 0` and `q1 / d = 0`
(both are `< d` since `c = k%(d-1) < d-1`).  Closed in `k`, discharged by
`arithBool`. -/
abbrev qzaRowGuardF (D : OddSurfaceDistance) : SFormula 1 :=
  .and (rowGuardPure1 D (qza0 D)) (rowGuardPure1 D (qza1 D))

def qzaRowGuardPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (qzaRowGuardF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [rowGuardPure1, qza0, qza1, dX1, distAtBoundIdx, dm1TA, SFormula.eval, SC.closed,
    SC.b, STerm.eval, Term.eval, Term.lift, bind, Option.bind]
  set k := rho ⟨0, by decide⟩ with hk
  set d := D.distance with hdd
  have hdpos : 0 < d := by omega
  have hclt : k % (d - 1) < d - 1 := Nat.mod_lt _ (by omega)
  have h0 : k % (d - 1) / d = 0 := Nat.div_eq_of_lt (by omega)
  have h1 : (k % (d - 1) + 1) / d = 0 := Nat.div_eq_of_lt (by omega)
  rw [h0, h1]
  simp

/-- The bulk-`X` all-others pin for class (a) [Z]: on row 0, if the bulk band fires
(with `r = 0`), then `boundNat ∈ {q0, q1}`.  Quantified over `q < nQubits`. -/
abbrev classZABulkXPinBody (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (rowGuardRaw2 D)
    (.imp (.eqBool (SC.closed (baseBulkBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.b true))
      (.imp (gRZero2 D true)
        (.or (.eqNat SFormula.boundNat (SC.closed (qza0_2 D)))
          (.eqNat SFormula.boundNat (SC.closed (qza1_2 D))))))

abbrev classZABulkXPinF (D : OddSurfaceDistance) : SFormula 1 :=
  .allNatLt (nQ1 D) (classZABulkXPinBody D)

def classZABulkXPinPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (classZABulkXPinF D) := by
  refine PureFamilyDerivA.allNatLtIntro _ ?_
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [classZABulkXPinBody, rowGuardRaw2, baseBulkBandGuardTA, gRZero2, qza0_2, qza1_2, dX2,
    distAtBoundIdx2, kX2, dm1TA, orEqSucc, band3, bulkCountTA, SFormula.eval, SC.closed, SC.b,
    STerm.eval, SFormula.boundNat, Term.eval, Term.lift, bind, Option.bind]
  set q := rho ⟨0, by decide⟩ with hq'
  set k := rho ⟨1, by decide⟩ with hk'
  set d := D.distance with hdd
  have hdpos : 0 < d := by omega
  by_cases hq : q / d = 0
  · simp only [hq, decide_true, if_true]
    by_cases hrz : k / (d - 1) = 0
    · -- r = 0; whenever the band fires (col matches), q is `c` or `c+1`.
      simp only [hrz, decide_true, if_true]
      -- on row 0 (q/d=0=r), band fires iff q%d ∈ {c, c+1}; and q = q%d since q < d.
      have hqd : q % d = q := Nat.mod_eq_of_lt (Nat.lt_of_div_eq_zero hdpos hq)
      by_cases hcol0 : q % d = k % (d - 1)
      · -- q%d = c → q = c = q0
        have hqe : decide (q = k % (d - 1)) = true := by rw [decide_eq_true_eq, ← hqd]; exact hcol0
        have hc0 : decide (q % d = k % (d - 1)) = true := by rw [decide_eq_true_eq]; exact hcol0
        simp only [hc0, hqe, decide_true, if_true]
        by_cases hbk : decide (k < (d-1)*(d-1)) = true <;> simp [hbk]
      · by_cases hcol1 : q % d = k % (d - 1) + 1
        · -- q%d = c+1 → q = c+1 = q1
          have hqe : decide (q = k % (d - 1) + 1) = true := by rw [decide_eq_true_eq, ← hqd]; exact hcol1
          have hc0 : decide (q % d = k % (d - 1)) = false := by rw [decide_eq_false_iff_not]; exact hcol0
          have hc1 : decide (q % d = k % (d - 1) + 1) = true := by rw [decide_eq_true_eq]; exact hcol1
          have hq0 : decide (q = k % (d - 1)) = false := by
            rw [decide_eq_false_iff_not, ← hqd]; exact hcol0
          simp only [hc0, hc1, hq0, hqe, decide_true, decide_false, Bool.false_eq_true,
            if_true, if_false, reduceIte]
          by_cases hbk : decide (k < (d-1)*(d-1)) = true <;> simp [hbk]
        · -- neither: band false, antecedent vacuous
          have hc0 : decide (q % d = k % (d - 1)) = false := by rw [decide_eq_false_iff_not]; exact hcol0
          have hc1 : decide (q % d = k % (d - 1) + 1) = false := by rw [decide_eq_false_iff_not]; exact hcol1
          simp only [hc0, hc1, decide_false, Bool.false_eq_true, if_false, reduceIte]
    · -- r ≠ 0: on row 0 (q/d=0) the band disjuncts `0 = r`, `0 = r+1` are both
      -- false, so the band is false and the conclusion is vacuous.
      have hrz' : decide (decide (k / (d - 1) = 0) = true) = false := by
        rw [decide_eq_false_iff_not]; simp [hrz]
      have hb0 : decide (0 = k / (d - 1)) = false := by
        rw [decide_eq_false_iff_not]; exact fun h => hrz h.symm
      have hb1 : decide (0 = k / (d - 1) + 1) = false := by
        rw [decide_eq_false_iff_not]; exact fun h => Nat.succ_ne_zero _ h.symm
      simp only [hrz, hrz', hb0, hb1, decide_false, Bool.false_eq_true, if_false, reduceIte]
  · simp only [hq, decide_false, Bool.false_eq_true, if_false, reduceIte]

/-! ### Class-(a) [Z] two-anti per-`k` commutation -/

/-- Entry-at-`q` resolves to `X` (bulk, band-at-q, kind FALSE), given the class-(a)
[Z] guard pack extracted at `q`.  Mirror of `antiZAtA` (bulk-`X` leaf). -/
def antiXAtA (D : OddSurfaceDistance) {Γ : List (SFormula 1)} (qT : Term 1 .nat)
    (hEntry : SFormula.Deriv Γ
      (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed qT))
        (SC.closed (baseLeafTreeTA (dX1 D) kX1 qT))))
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dX1 D) kX1)) (SC.b true)))
    (hBand : SFormula.Deriv Γ (.eqBool (SC.closed (baseBulkBandGuardTA (dX1 D) kX1 qT)) (SC.b true)))
    (hKind : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dX1 D) kX1)) (SC.b false))) :
    SFormula.Deriv Γ (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed qT)) (SC.p Pauli.X)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ hEntry (baseLeafBulkX _ _ _ hBulk hBand hKind)

/-- Extract the class-(a) [Z] bulk-`X` pin disjunction at `boundNat`. -/
def classZABulkXPinAt {Δ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hW : SFormula.Deriv Δ (classZABulkXPinF D).weaken)
    (hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nQ1 D).weaken))
    (hrow : SFormula.Deriv Δ (rowGuardRaw2 D))
    (hband : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.b true)))
    (hrz : SFormula.Deriv Δ (gRZero2 D true)) :
    SFormula.Deriv Δ
      (.or (.eqNat SFormula.boundNat (SC.closed (qza0_2 D)))
        (.eqNat SFormula.boundNat (SC.closed (qza1_2 D)))) := by
  have hElim := SFormula.Deriv.allNatLtElim (nQ1 D).weaken
    ((classZABulkXPinBody D).lift 1) SFormula.boundNat hW hq
  have hBody := SFormula.Deriv.applyNatBoundNatBeta (classZABulkXPinBody D) hElim
  exact SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp hBody hrow) hband) hrz

/-- **Class-(a) [Z] two-anti per-`k` commutation.**  Given bulk true, `r = 0`, kind
false, and the supporting packs in `Γ`, the row commutes with `logicalZ` by the
even-parity rule: it anticommutes at exactly `q0 = c` and `q1 = c+1`, and commutes
elsewhere.  Transpose of `commTwoAntiA`. -/
def commZTwoAntiA {Γ : List (SFormula 1)} (D : OddSurfaceDistance)
    (hBulk : SFormula.Deriv Γ (gBulk1 D true))
    (hRZ : SFormula.Deriv Γ (gRZero1 D true))
    (hKind : SFormula.Deriv Γ (gKind1 D false))
    (hClassA : SFormula.Deriv Γ (classZAPackF D))
    (hRow : SFormula.Deriv Γ (qzaRowGuardF D))
    (hPin : SFormula.Deriv Γ (classZABulkXPinF D))
    (hEntryF : SFormula.Deriv Γ (entryFlatF1 D))
    (hBBFF : SFormula.Deriv Γ (bottomBandFalseF D))
    (hEntry0 : SFormula.Deriv Γ
      (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed (qza0 D)))
        (SC.closed (baseLeafTreeTA (dX1 D) kX1 (qza0 D)))))
    (hEntry1 : SFormula.Deriv Γ
      (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed (qza1 D)))
        (SC.closed (baseLeafTreeTA (dX1 D) kX1 (qza1 D))))) :
    SFormula.Deriv Γ (commGoalZ1 D) := by
  have hPack := SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp hClassA hBulk) hRZ) hKind
  have hBand0 := SFormula.Deriv.andElimLeft hPack
  have hBand1 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hPack)
  have hNe := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hPack))
  have hLt0 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hPack)))
  have hLt1 := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hPack)))
  -- Entry = X at q0, q1.
  have hX0 := antiXAtA D (qza0 D) hEntry0 hBulk hBand0 hKind
  have hX1 := antiXAtA D (qza1 D) hEntry1 hBulk hBand1 hKind
  -- logicalZ = Z at q0, q1.
  have hZ0 := lzPureEntryZ D (qza0 D) (qza0_pure D) (SFormula.Deriv.andElimLeft hRow)
  have hZ1 := lzPureEntryZ D (qza1 D) (qza1_pure D) (SFormula.Deriv.andElimRight hRow)
  refine SFormula.Deriv.commutesOfTwoAnti _ _ _ (SC.closed (qza0 D)) (SC.closed (qza1 D))
    ?wlt0 ?wlt1 ?wne ?wanti0 ?wanti1 ?wrest
  case wlt0 => exact hLt0
  case wlt1 => exact hLt1
  case wne =>
    refine SFormula.Deriv.notIntro ?_
    refine SFormula.Deriv.notElim
      (SFormula.Deriv.eqNatBoolTrue (Γ := _) (qza0 D) (qza1 D) .assumption) ?_
    exact SFormula.Deriv.eqBoolFalseNotTrue _ (cw1 hNe)
  case wanti0 =>
    exact SFormula.Deriv.anticommutesTransport _ (SC.p Pauli.X) _ (SC.p Pauli.Z) (SC.b true)
      hX0 hZ0 (SFormula.Deriv.pauliAnticommutesLit Pauli.X Pauli.Z)
  case wanti1 =>
    exact SFormula.Deriv.anticommutesTransport _ (SC.p Pauli.X) _ (SC.p Pauli.Z) (SC.b true)
      hX1 hZ1 (SFormula.Deriv.pauliAnticommutesLit Pauli.X Pauli.Z)
  case wrest =>
    refine SFormula.Deriv.allNatLtIntroBounded _ _ ?_
    refine SFormula.Deriv.impIntro (SFormula.Deriv.impIntro ?_)
    refine SFormula.Deriv.boolCases (logicalZRowGuardAt2 D) _ ?_ ?_
    · set ΔT : List (SFormula 2) := .eqBool (logicalZRowGuardAt2 D) (SC.b true)
        :: .not (.eqNat SFormula.boundNat (SC.closed (qza1 D)).weaken)
        :: .not (.eqNat SFormula.boundNat (SC.closed (qza0 D)).weaken)
        :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ with hΔT
      have hEntryW : SFormula.Deriv ΔT (entryFlatF1 D).weaken :=
        cw4 (SFormula.Deriv.weakenFresh (A := entryFlatF1 D) hEntryF)
      have hBBFW : SFormula.Deriv ΔT (bottomBandFalseF D).weaken :=
        cw4 (SFormula.Deriv.weakenFresh (A := bottomBandFalseF D) hBBFF)
      have hq : SFormula.Deriv ΔT (SFormula.witnessLt SFormula.boundNat (nQ1 D).weaken) :=
        SFormula.Deriv.hyp (by rw [hΔT]; right; right; right; exact List.mem_cons_self)
      have hrowT : SFormula.Deriv ΔT (.eqBool (logicalZRowGuardAt2 D) (SC.b true)) := by
        rw [hΔT]; exact .assumption
      have hrowRaw : SFormula.Deriv ΔT (rowGuardRaw2 D) := by rw [← rowGuard2_eq]; exact hrowT
      have hEntry := entryAtBound D hEntryW hq
      have hBBF := bbfAtBound D hBBFW hq hrowRaw
      refine rowDispatchOnTrue D hEntry hrowT hBBF ?hXbulk ?hXtop
      case hXbulk =>
        intro Δ' lift _ hrowΔ hBulkΔ hBandΔ _
        -- bulk-X: use the pin (row ∧ band ∧ r=0) → q=q0 ∨ q=q1, contradicting exclusions.
        have hrowRaw' : SFormula.Deriv Δ' (rowGuardRaw2 D) := by rw [← rowGuard2_eq]; exact hrowΔ
        have hrzΔ0 : SFormula.Deriv ΔT (gRZero2 D true) :=
          cw4 (SFormula.Deriv.weakenFresh (A := gRZero1 D true) hRZ)
        have hPinW0 : SFormula.Deriv ΔT (classZABulkXPinF D).weaken :=
          cw4 (SFormula.Deriv.weakenFresh (A := classZABulkXPinF D) hPin)
        have hdisj := classZABulkXPinAt D (lift hPinW0) (lift hq) hrowRaw' hBandΔ (lift hrzΔ0)
        have hne0 : SFormula.Deriv ΔT (.not (.eqNat SFormula.boundNat (SC.closed (qza0 D)).weaken)) := by
          rw [hΔT]; exact .hyp (by right; right; exact List.mem_cons_self)
        have hne1 : SFormula.Deriv ΔT (.not (.eqNat SFormula.boundNat (SC.closed (qza1 D)).weaken)) := by
          rw [hΔT]; exact .hyp (by right; exact List.mem_cons_self)
        refine SFormula.Deriv.orElim hdisj ?_ ?_
        · exact SFormula.Deriv.botElim (SFormula.Deriv.notElim (.assumption) (cw1 (lift hne0)))
        · exact SFormula.Deriv.botElim (SFormula.Deriv.notElim (.assumption) (cw1 (lift hne1)))
      case hXtop =>
        intro Δ' lift _ _ hBulkFalseΔ _ _
        -- top-X: class (a) has bulk TRUE, contradicting cascade bulk FALSE.
        have hBulkTrue0 : SFormula.Deriv ΔT (gBulk D true) :=
          cw4 (SFormula.Deriv.weakenFresh (A := gBulk1 D true) hBulk)
        exact eqBoolContra _ (lift hBulkTrue0) hBulkFalseΔ
    · exact logicalZOffRowLocalCommutes D (rowK2 D) .assumption

end QHL.CodeLang.Surface.Verify
