import QStab.QHL.Verify.SurfaceNormalizers.ZClassA

/-!
# Logical-normalizer consumers — ZClassB

Two-anti class (b) [Z]: top-`X` boundary stabilisers, and their per-`k` commutation.
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface

set_option maxRecDepth 65536

/-! ## Two-anti class (b) [Z]: top-`X` boundary stabilizers

`¬(k < (d-1)²)`, top-`X` band `b < half` (`b = k - (d-1)²`, `half = (d-1)/2`).
Anti qubits `q0 = 2b`, `q1 = 2b+1` on ROW 0. -/

/-- `q0 = 2·b` at arity 1 (first class-(b) anti qubit), `b = baseBTA`. -/
abbrev qzb0 (D : OddSurfaceDistance) : Term 1 .nat := .mul (.natLit 2) (baseBTA (dX1 D) kX1)
/-- `q1 = 2·b + 1` at arity 1. -/
abbrev qzb1 (D : OddSurfaceDistance) : Term 1 .nat :=
  .add (.mul (.natLit 2) (baseBTA (dX1 D) kX1)) (.natLit 1)

def baseB1_pure (D : OddSurfaceDistance) : SFormula.PureNatTerm (baseBTA (dX1 D) kX1) :=
  SFormula.PureNatTerm.sub (SFormula.PureNatTerm.var _)
    (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.sub (dX1_pure D) (SFormula.PureNatTerm.natLit _))
      (SFormula.PureNatTerm.sub (dX1_pure D) (SFormula.PureNatTerm.natLit _)))
def qzb0_pure (D : OddSurfaceDistance) : SFormula.PureNatTerm (qzb0 D) :=
  SFormula.PureNatTerm.mul (SFormula.PureNatTerm.natLit _) (baseB1_pure D)
def qzb1_pure (D : OddSurfaceDistance) : SFormula.PureNatTerm (qzb1 D) :=
  SFormula.PureNatTerm.add (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.natLit _) (baseB1_pure D))
    (SFormula.PureNatTerm.natLit _)

/-- Arity-2 forms of the class-(b) [Z] anti qubits (`k = var 1`). -/
abbrev qzb0_2 (D : OddSurfaceDistance) : Term 2 .nat := .mul (.natLit 2) (baseBTA (dX2 D) kX2)
abbrev qzb1_2 (D : OddSurfaceDistance) : Term 2 .nat :=
  .add (.mul (.natLit 2) (baseBTA (dX2 D) kX2)) (.natLit 1)
theorem qzb0_weaken (D : OddSurfaceDistance) : (qzb0 D).weaken = qzb0_2 D := rfl
theorem qzb1_weaken (D : OddSurfaceDistance) : (qzb1 D).weaken = qzb1_2 D := rfl

/-- Class-(b) [Z] guard pack: given `¬bulk`, `topClass` (so `b < half`), the top-`X`
band fires at `q0 = 2b`/`q1 = 2b+1`, `q0 ≠ q1`, and both `< nQubits`. -/
abbrev classZBPackF (D : OddSurfaceDistance) : SFormula 1 :=
  .imp (gBulk1 D false) (.imp (gTopC1 D true)
    (.and (.eqBool (SC.closed (topBandGuardTA (dX1 D) kX1 (qzb0 D))) (SC.b true))
      (.and (.eqBool (SC.closed (topBandGuardTA (dX1 D) kX1 (qzb1 D))) (SC.b true))
        (.and (.eqBool (SC.closed (.eqNat (qzb0 D) (qzb1 D))) (SC.b false))
          (.and (SFormula.witnessLt (SC.closed (qzb0 D)) (SC.n (arity := 1) (nQubits D.distance)))
            (SFormula.witnessLt (SC.closed (qzb1 D)) (SC.n (arity := 1) (nQubits D.distance))))))))

def classZBPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (classZBPackF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [classZBPackF, topBandGuardTA, gBulk1, gTopC1, bulkGuardTA, topClassGuardTA, baseBTA,
    baseHalfTA, bulkCountTA, qzb0, qzb1, dX1, distAtBoundIdx, dm1TA, orEqSucc, band3,
    SFormula.eval, SC.closed, SC.b, SC.n, STerm.eval, SFormula.witnessLt, Term.eval, Term.lift,
    bind, Option.bind]
  set k := rho ⟨0, by decide⟩ with hk
  set d := D.distance with hdd
  have hdpos : 0 < d := by omega
  have hdge : 3 ≤ d := by omega
  by_cases hbulk : k < (d - 1) * (d - 1)
  · -- bulk true → `gBulk1 D false` antecedent false → vacuous.
    have hbv : decide (decide (k < (d - 1) * (d - 1)) = false) = false := by
      rw [decide_eq_false_iff_not]; simp [hbulk]
    simp only [hbv, Bool.false_eq_true, if_false, reduceIte]
  · by_cases htc : k - (d - 1) * (d - 1) < (d - 1) / 2
    · -- the genuine class-(b) case.
      have hbv : decide (decide (k < (d - 1) * (d - 1)) = false) = true := by
        rw [decide_eq_true_eq]; simp [hbulk]
      have htcd : decide (decide (k - (d - 1) * (d - 1) < (d - 1) / 2) = true) = true := by
        rw [decide_eq_true_eq]; simp [htc]
      simp only [hbv, htcd, if_true]
      set b := k - (d - 1) * (d - 1) with hb
      -- 2b < d-1, 2b+1 ≤ d-1 < d; q0 = 2b, q1 = 2b+1 row-0 qubits.
      have hhalf : (d - 1) / 2 ≤ (d - 1) := Nat.div_le_self _ _
      have hblt : b < (d - 1) / 2 := htc
      have h2blt : 2 * b < d - 1 := by omega
      have hq0div : 2 * b / d = 0 := Nat.div_eq_of_lt (by omega)
      have hq0mod : 2 * b % d = 2 * b := Nat.mod_eq_of_lt (by omega)
      have hq1div : (2 * b + 1) / d = 0 := Nat.div_eq_of_lt (by omega)
      have hq1mod : (2 * b + 1) % d = 2 * b + 1 := Nat.mod_eq_of_lt (by omega)
      have hk2 : (d - 1) * (d - 1) ≤ k := by omega
      have hkd2 : k < d * d - 1 := by
        have hbnd : k < (d-1)*(d-1) + (d-1)/2 := by omega
        -- (d-1)*(d-1) ≤ d*d - d  since (d-1)*(d-1) ≤ (d-1)*d = d*d - d.
        have hle : (d - 1) * (d - 1) ≤ (d - 1) * d := Nat.mul_le_mul_left (d-1) (by omega)
        have hdd2 : (d - 1) * d = d * d - d := by rw [Nat.sub_mul]; omega
        have hab : (d - 1) * (d - 1) ≤ d * d - d := by rw [← hdd2]; exact hle
        have hdf : d ≤ d * d := Nat.le_mul_of_pos_left d hdpos
        omega
      have hb0 : 2 * b < nQubits d := by
        simp only [nQubits]; have hlt : 2 * b < d := by omega
        calc 2 * b < d := hlt
          _ ≤ d * d := Nat.le_mul_of_pos_left d hdpos
      have hb1 : 2 * b + 1 < nQubits d := by
        simp only [nQubits]; have hlt : 2 * b + 1 < d := by omega
        calc 2 * b + 1 < d := hlt
          _ ≤ d * d := Nat.le_mul_of_pos_left d hdpos
      -- decide the band conjuncts: k < d²-1, q/d=0, q%d ∈ {2b, 2b+1}.
      have hkd : decide (k < d * d - 1) = true := by rw [decide_eq_true_eq]; exact hkd2
      have hq0d0 : decide (2 * b / d = 0) = true := by rw [hq0div]; simp
      have hq0m : decide (2 * b % d = 2 * b) = true := by rw [hq0mod]; simp
      have hq1d0 : decide ((2 * b + 1) / d = 0) = true := by rw [hq1div]; simp
      have hq1ma : decide ((2 * b + 1) % d = 2 * b) = false := by
        rw [hq1mod]; rw [decide_eq_false_iff_not]; omega
      have hq1mb : decide ((2 * b + 1) % d = 2 * b + 1) = true := by rw [hq1mod]; simp
      have hbne : decide (2 * b = 2 * b + 1) = false := by rw [decide_eq_false_iff_not]; omega
      have hbb0 : decide (2 * b < nQubits d) = true := by rw [decide_eq_true_eq]; exact hb0
      have hbb1 : decide (2 * b + 1 < nQubits d) = true := by rw [decide_eq_true_eq]; exact hb1
      simp only [hkd, hq0d0, hq0m, hq1d0, hq1ma, hq1mb, hbne, hbb0, hbb1,
        decide_true, decide_false, Bool.false_eq_true, if_true, if_false, reduceIte]
    · -- topClass false → `gTopC1 D true` antecedent false → vacuous.
      have hbv : decide (decide (k < (d - 1) * (d - 1)) = false) = true := by
        rw [decide_eq_true_eq]; simp [hbulk]
      have htcd : decide (decide (k - (d - 1) * (d - 1) < (d - 1) / 2) = true) = false := by
        rw [decide_eq_false_iff_not]; simp [htc]
      simp only [hbv, htcd, Bool.false_eq_true, if_false, if_true, reduceIte]

/-- Row guards at the class-(b) [Z] anti qubits (`q0, q1 < d` since `2b+1 ≤ d-1`).
Conditional on the class condition.  Discharged by `arithBool`. -/
abbrev qzbRowGuardF (D : OddSurfaceDistance) : SFormula 1 :=
  .imp (gBulk1 D false) (.imp (gTopC1 D true)
    (.and (rowGuardPure1 D (qzb0 D)) (rowGuardPure1 D (qzb1 D))))

def qzbRowGuardPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (qzbRowGuardF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [qzbRowGuardF, rowGuardPure1, gBulk1, gTopC1, bulkGuardTA, topClassGuardTA, baseBTA,
    baseHalfTA, bulkCountTA, qzb0, qzb1, dX1, distAtBoundIdx, dm1TA, SFormula.eval, SC.closed,
    SC.b, STerm.eval, Term.eval, Term.lift, bind, Option.bind]
  set k := rho ⟨0, by decide⟩ with hk
  set d := D.distance with hdd
  have hdpos : 0 < d := by omega
  have hdge : 3 ≤ d := by omega
  by_cases hbulk : k < (d - 1) * (d - 1)
  · have hbv : decide (decide (k < (d - 1) * (d - 1)) = false) = false := by
      rw [decide_eq_false_iff_not]; simp [hbulk]
    simp only [hbv, Bool.false_eq_true, if_false, reduceIte]
  · by_cases htc : k - (d - 1) * (d - 1) < (d - 1) / 2
    · have hbv : decide (decide (k < (d - 1) * (d - 1)) = false) = true := by
        rw [decide_eq_true_eq]; simp [hbulk]
      have htcd : decide (decide (k - (d - 1) * (d - 1) < (d - 1) / 2) = true) = true := by
        rw [decide_eq_true_eq]; simp [htc]
      simp only [hbv, htcd, if_true]
      set b := k - (d - 1) * (d - 1) with hb
      have hhalf : (d - 1) / 2 ≤ (d - 1) := Nat.div_le_self _ _
      have hblt : b < (d - 1) / 2 := htc
      have h2blt : 2 * b < d - 1 := by omega
      have hq0div : 2 * b / d = 0 := Nat.div_eq_of_lt (by omega)
      have hq1div : (2 * b + 1) / d = 0 := Nat.div_eq_of_lt (by omega)
      rw [hq0div, hq1div]; simp
    · have hbv : decide (decide (k < (d - 1) * (d - 1)) = false) = true := by
        rw [decide_eq_true_eq]; simp [hbulk]
      have htcd : decide (decide (k - (d - 1) * (d - 1) < (d - 1) / 2) = true) = false := by
        rw [decide_eq_false_iff_not]; simp [htc]
      simp only [hbv, htcd, Bool.false_eq_true, if_false, if_true, reduceIte]

/-- The top-`X` all-others pin for class (b) [Z]: on row 0, if the top band fires,
then `boundNat ∈ {q0, q1}`.  Mirror of `classBLeftZPinPack`. -/
abbrev classZBTopXPinBody (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (rowGuardRaw2 D)
    (.imp (.eqBool (SC.closed (topBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.b true))
      (.or (.eqNat SFormula.boundNat (SC.closed (qzb0_2 D)))
        (.eqNat SFormula.boundNat (SC.closed (qzb1_2 D)))))

abbrev classZBTopXPinF (D : OddSurfaceDistance) : SFormula 1 :=
  .allNatLt (nQ1 D) (classZBTopXPinBody D)

def classZBTopXPinPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (classZBTopXPinF D) := by
  refine PureFamilyDerivA.allNatLtIntro _ ?_
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [classZBTopXPinBody, rowGuardRaw2, topBandGuardTA, qzb0_2, qzb1_2, baseBTA,
    bulkCountTA, dX2, distAtBoundIdx2, kX2, dm1TA, orEqSucc, band3, SFormula.eval, SC.closed,
    SC.b, STerm.eval, SFormula.boundNat, Term.eval, Term.lift, bind, Option.bind]
  set q := rho ⟨0, by decide⟩ with hq'
  set k := rho ⟨1, by decide⟩ with hk'
  set d := D.distance with hdd
  have hdpos : 0 < d := by omega
  set b := k - (d - 1) * (d - 1) with hb
  by_cases hq : q / d = 0
  · simp only [hq, decide_true, if_true]
    have hqd : q % d = q := Nat.mod_eq_of_lt (Nat.lt_of_div_eq_zero hdpos hq)
    by_cases hkd : k < d * d - 1
    · -- top band's k-bound holds; fires iff q%d ∈ {2b, 2b+1}.
      have hkdd : decide (k < d * d - 1) = true := by rw [decide_eq_true_eq]; exact hkd
      simp only [hkdd, decide_true, if_true]
      by_cases hcol0 : q % d = 2 * b
      · have hqe : decide (q = 2 * b) = true := by rw [decide_eq_true_eq, ← hqd]; exact hcol0
        have hc0 : decide (q % d = 2 * b) = true := by rw [decide_eq_true_eq]; exact hcol0
        simp only [hc0, hqe, decide_true, if_true]
      · by_cases hcol1 : q % d = 2 * b + 1
        · have hqe : decide (q = 2 * b + 1) = true := by rw [decide_eq_true_eq, ← hqd]; exact hcol1
          have hc0 : decide (q % d = 2 * b) = false := by rw [decide_eq_false_iff_not]; exact hcol0
          have hc1 : decide (q % d = 2 * b + 1) = true := by rw [decide_eq_true_eq]; exact hcol1
          have hq0 : decide (q = 2 * b) = false := by rw [decide_eq_false_iff_not, ← hqd]; exact hcol0
          simp only [hc0, hc1, hq0, hqe, decide_true, decide_false, Bool.false_eq_true,
            if_true, if_false, reduceIte]
        · have hc0 : decide (q % d = 2 * b) = false := by rw [decide_eq_false_iff_not]; exact hcol0
          have hc1 : decide (q % d = 2 * b + 1) = false := by rw [decide_eq_false_iff_not]; exact hcol1
          simp only [hc0, hc1, decide_false, Bool.false_eq_true, if_false, reduceIte]
    · -- k ≥ d²-1: top band's first conjunct false → band false → vacuous.
      have hkdd : decide (k < d * d - 1) = false := by rw [decide_eq_false_iff_not]; exact hkd
      simp only [hkdd, decide_false, Bool.false_eq_true, if_false, reduceIte]
  · simp only [hq, decide_false, Bool.false_eq_true, if_false, reduceIte]

/-! ### Class-(b) [Z] two-anti per-`k` commutation -/

/-- Entry-at-`q` resolves to `X` via the top-`X` boundary leaf.  Mirror of
`antiZAtB` (top-`X` leaf). -/
def antiXAtB (D : OddSurfaceDistance) {Γ : List (SFormula 1)} (qT : Term 1 .nat)
    (hEntry : SFormula.Deriv Γ
      (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed qT))
        (SC.closed (baseLeafTreeTA (dX1 D) kX1 qT))))
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dX1 D) kX1)) (SC.b false)))
    (hTopC : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dX1 D) kX1)) (SC.b true)))
    (hTopB : SFormula.Deriv Γ (.eqBool (SC.closed (topBandGuardTA (dX1 D) kX1 qT)) (SC.b true))) :
    SFormula.Deriv Γ (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed qT)) (SC.p Pauli.X)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ hEntry (baseLeafTopX _ _ _ hBulk hTopC hTopB)

/-- Extract the class-(b) [Z] top-`X` pin disjunction at `boundNat`. -/
def classZBTopXPinAt {Δ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hW : SFormula.Deriv Δ (classZBTopXPinF D).weaken)
    (hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nQ1 D).weaken))
    (hrow : SFormula.Deriv Δ (rowGuardRaw2 D))
    (hband : SFormula.Deriv Δ (.eqBool (SC.closed (topBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.b true))) :
    SFormula.Deriv Δ
      (.or (.eqNat SFormula.boundNat (SC.closed (qzb0_2 D)))
        (.eqNat SFormula.boundNat (SC.closed (qzb1_2 D)))) := by
  have hElim := SFormula.Deriv.allNatLtElim (nQ1 D).weaken
    ((classZBTopXPinBody D).lift 1) SFormula.boundNat hW hq
  have hBody := SFormula.Deriv.applyNatBoundNatBeta (classZBTopXPinBody D) hElim
  exact SFormula.Deriv.mp (SFormula.Deriv.mp hBody hrow) hband

/-- **Class-(b) [Z] two-anti per-`k` commutation.**  Transpose of `commTwoAntiB`. -/
def commZTwoAntiB {Γ : List (SFormula 1)} (D : OddSurfaceDistance)
    (hBulk : SFormula.Deriv Γ (gBulk1 D false))
    (hTopC : SFormula.Deriv Γ (gTopC1 D true))
    (hClassB : SFormula.Deriv Γ (classZBPackF D))
    (hRow : SFormula.Deriv Γ (qzbRowGuardF D))
    (hPin : SFormula.Deriv Γ (classZBTopXPinF D))
    (hEntryF : SFormula.Deriv Γ (entryFlatF1 D))
    (hBBFF : SFormula.Deriv Γ (bottomBandFalseF D))
    (hEntry0 : SFormula.Deriv Γ
      (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed (qzb0 D)))
        (SC.closed (baseLeafTreeTA (dX1 D) kX1 (qzb0 D)))))
    (hEntry1 : SFormula.Deriv Γ
      (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed (qzb1 D)))
        (SC.closed (baseLeafTreeTA (dX1 D) kX1 (qzb1 D))))) :
    SFormula.Deriv Γ (commGoalZ1 D) := by
  have hPack := SFormula.Deriv.mp (SFormula.Deriv.mp hClassB hBulk) hTopC
  have hBand0 := SFormula.Deriv.andElimLeft hPack
  have hBand1 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hPack)
  have hNe := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hPack))
  have hLt0 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hPack)))
  have hLt1 := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hPack)))
  have hRowPack := SFormula.Deriv.mp (SFormula.Deriv.mp hRow hBulk) hTopC
  have hX0 := antiXAtB D (qzb0 D) hEntry0 hBulk hTopC hBand0
  have hX1 := antiXAtB D (qzb1 D) hEntry1 hBulk hTopC hBand1
  have hZ0 := lzPureEntryZ D (qzb0 D) (qzb0_pure D) (SFormula.Deriv.andElimLeft hRowPack)
  have hZ1 := lzPureEntryZ D (qzb1 D) (qzb1_pure D) (SFormula.Deriv.andElimRight hRowPack)
  refine SFormula.Deriv.commutesOfTwoAnti _ _ _ (SC.closed (qzb0 D)) (SC.closed (qzb1 D))
    ?wlt0 ?wlt1 ?wne ?wanti0 ?wanti1 ?wrest
  case wlt0 => exact hLt0
  case wlt1 => exact hLt1
  case wne =>
    refine SFormula.Deriv.notIntro ?_
    refine SFormula.Deriv.notElim
      (SFormula.Deriv.eqNatBoolTrue (Γ := _) (qzb0 D) (qzb1 D) .assumption) ?_
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
        :: .not (.eqNat SFormula.boundNat (SC.closed (qzb1 D)).weaken)
        :: .not (.eqNat SFormula.boundNat (SC.closed (qzb0 D)).weaken)
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
        intro Δ' lift _ _ hBulkTrueΔ _ _
        -- bulk-X: class (b) has bulk FALSE, contradicting cascade bulk TRUE.
        have hBulkFalse0 : SFormula.Deriv ΔT (gBulk D false) :=
          cw4 (SFormula.Deriv.weakenFresh (A := gBulk1 D false) hBulk)
        exact eqBoolContra _ hBulkTrueΔ (lift hBulkFalse0)
      case hXtop =>
        intro Δ' lift _ hrowΔ _ _ hTopBΔ
        -- top-X: use the top-X pin → q ∈ {q0, q1}, contradicting exclusions.
        have hrowRaw' : SFormula.Deriv Δ' (rowGuardRaw2 D) := by rw [← rowGuard2_eq]; exact hrowΔ
        have hPinW0 : SFormula.Deriv ΔT (classZBTopXPinF D).weaken :=
          cw4 (SFormula.Deriv.weakenFresh (A := classZBTopXPinF D) hPin)
        have hdisj := classZBTopXPinAt D (lift hPinW0) (lift hq) hrowRaw' hTopBΔ
        have hne0 : SFormula.Deriv ΔT (.not (.eqNat SFormula.boundNat (SC.closed (qzb0 D)).weaken)) := by
          rw [hΔT]; exact .hyp (by right; right; exact List.mem_cons_self)
        have hne1 : SFormula.Deriv ΔT (.not (.eqNat SFormula.boundNat (SC.closed (qzb1 D)).weaken)) := by
          rw [hΔT]; exact .hyp (by right; exact List.mem_cons_self)
        refine SFormula.Deriv.orElim hdisj ?_ ?_
        · exact SFormula.Deriv.botElim (SFormula.Deriv.notElim (.assumption) (cw1 (lift hne0)))
        · exact SFormula.Deriv.botElim (SFormula.Deriv.notElim (.assumption) (cw1 (lift hne1)))
    · exact logicalZOffRowLocalCommutes D (rowK2 D) .assumption

end QHL.CodeLang.Surface.Verify
