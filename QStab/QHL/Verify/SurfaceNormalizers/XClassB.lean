import QStab.QHL.Verify.SurfaceNormalizers.XClassA

/-!
# Logical-normalizer consumers — XClassB

Two-anti class (b): left-`Z` boundary stabilisers.
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface

set_option maxRecDepth 65536

/-! ## Two-anti class (b): left-`Z` boundary stabilizers

`¬(k < (d-1)²)`, left-`Z` band `2·half ≤ b < 3·half` (`b = k - (d-1)²`,
`half = (d-1)/2`).  Anti qubits `q0 = (2·bbL+1)·d`, `q1 = (2·bbL+2)·d`,
`bbL = b - 2·half`. -/

/-- `bbL = (k - (d-1)²) - 2·((d-1)/2)` at arity 1. -/
abbrev bbL1 (D : OddSurfaceDistance) : Term 1 .nat :=
  .sub (baseBTA (dX1 D) kX1) (.mul (.natLit 2) (baseHalfTA (dX1 D)))
abbrev qb0 (D : OddSurfaceDistance) : Term 1 .nat :=
  .mul (.add (.mul (.natLit 2) (bbL1 D)) (.natLit 1)) (dX1 D)
abbrev qb1 (D : OddSurfaceDistance) : Term 1 .nat :=
  .mul (.add (.mul (.natLit 2) (bbL1 D)) (.natLit 2)) (dX1 D)

def bbL1_pure (D : OddSurfaceDistance) : SFormula.PureNatTerm (bbL1 D) :=
  SFormula.PureNatTerm.sub
    (SFormula.PureNatTerm.sub (SFormula.PureNatTerm.var _)
      (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.sub (dX1_pure D) (SFormula.PureNatTerm.natLit _))
        (SFormula.PureNatTerm.sub (dX1_pure D) (SFormula.PureNatTerm.natLit _))))
    (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.natLit _)
      (SFormula.PureNatTerm.div (SFormula.PureNatTerm.sub (dX1_pure D) (SFormula.PureNatTerm.natLit _))
        (SFormula.PureNatTerm.natLit _)))
def qb0_pure (D : OddSurfaceDistance) : SFormula.PureNatTerm (qb0 D) :=
  SFormula.PureNatTerm.mul (SFormula.PureNatTerm.add
    (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.natLit _) (bbL1_pure D))
    (SFormula.PureNatTerm.natLit _)) (dX1_pure D)
def qb1_pure (D : OddSurfaceDistance) : SFormula.PureNatTerm (qb1 D) :=
  SFormula.PureNatTerm.mul (SFormula.PureNatTerm.add
    (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.natLit _) (bbL1_pure D))
    (SFormula.PureNatTerm.natLit _)) (dX1_pure D)

/-- Arity-2 forms of the class-(b) anti qubits. -/
abbrev bbL2 (D : OddSurfaceDistance) : Term 2 .nat :=
  .sub (baseBTA (dX2 D) kX2) (.mul (.natLit 2) (baseHalfTA (dX2 D)))
abbrev qb0_2 (D : OddSurfaceDistance) : Term 2 .nat :=
  .mul (.add (.mul (.natLit 2) (bbL2 D)) (.natLit 1)) (dX2 D)
abbrev qb1_2 (D : OddSurfaceDistance) : Term 2 .nat :=
  .mul (.add (.mul (.natLit 2) (bbL2 D)) (.natLit 2)) (dX2 D)
theorem qb0_weaken (D : OddSurfaceDistance) : (qb0 D).weaken = qb0_2 D := rfl
theorem qb1_weaken (D : OddSurfaceDistance) : (qb1 D).weaken = qb1_2 D := rfl

/-- Class-(b) guard pack: given `¬bulk`, `¬rightClass`, `leftClass` (so `2half ≤ b
< 3half`), the left-`Z` band fires at `q0`/`q1`, `q0 ≠ q1`, and both `< nQubits`. -/
abbrev classBPackF (D : OddSurfaceDistance) : SFormula 1 :=
  .imp (gBulk1 D false) (.imp (gRightC1 D false) (.imp (gLeftC1 D true)
    (.and (.eqBool (SC.closed (leftBandGuardTA (dX1 D) kX1 (qb0 D))) (SC.b true))
      (.and (.eqBool (SC.closed (leftBandGuardTA (dX1 D) kX1 (qb1 D))) (SC.b true))
        (.and (.eqBool (SC.closed (.eqNat (qb0 D) (qb1 D))) (SC.b false))
          (.and (SFormula.witnessLt (SC.closed (qb0 D)) (SC.n (arity := 1) (nQubits D.distance)))
            (SFormula.witnessLt (SC.closed (qb1 D)) (SC.n (arity := 1) (nQubits D.distance)))))))))

def classBPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (classBPackF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [classBPackF, leftBandGuardTA, gBulk1, gRightC1, gLeftC1, bulkGuardTA, rightClassGuardTA,
    leftClassGuardTA, baseBTA, baseHalfTA, bulkCountTA, qb0, qb1, bbL1, dX1, distAtBoundIdx, dm1TA,
    orEqPair, SFormula.eval, SC.closed, SC.b, SC.n, STerm.eval, SFormula.witnessLt, Term.eval,
    Term.lift, bind, Option.bind]
  set k := rho ⟨0, by decide⟩ with hk
  set d := D.distance with hdd
  have hdpos : 0 < d := by omega
  have hdge : 3 ≤ d := by omega
  by_cases hbulk : k < (d - 1) * (d - 1)
  · -- bulk true → `gBulk1 D false` antecedent false → vacuous.
    have : decide (decide (k < (d - 1) * (d - 1)) = false) = false := by
      rw [decide_eq_false_iff_not]; simp [hbulk]
    simp only [this, Bool.false_eq_true, if_false, reduceIte]
  · by_cases hrc : k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)
    · -- rightClass true → `gRightC1 D false` antecedent false → vacuous.
      have hb : decide (decide (k < (d - 1) * (d - 1)) = false) = true := by
        rw [decide_eq_true_eq]; simp [hbulk]
      have hr : decide (decide (k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = false := by
        rw [decide_eq_false_iff_not]; simp [hrc]
      simp only [hb, hr, Bool.false_eq_true, if_false, if_true, reduceIte]
    · by_cases hlc : k - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)
      · -- the genuine class-(b) case.
        set L := k - (d - 1) * (d - 1) - 2 * ((d - 1) / 2) with hL
        have hb : decide (decide (k < (d - 1) * (d - 1)) = false) = true := by
          rw [decide_eq_true_eq]; simp [hbulk]
        have hr : decide (decide (k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = true := by
          rw [decide_eq_true_eq]; simp [hrc]
        have hlcd : decide (decide (k - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)) = true) = true := by
          rw [decide_eq_true_eq]; simp [hlc]
        simp only [hb, hr, hlcd, if_true]
        have hdiv0 : (2 * L + 1) * d / d = 2 * L + 1 := Nat.mul_div_cancel _ hdpos
        have hmod0 : (2 * L + 1) * d % d = 0 := Nat.mul_mod_left _ _
        have hdiv1 : (2 * L + 2) * d / d = 2 * L + 2 := Nat.mul_div_cancel _ hdpos
        have hmod1 : (2 * L + 2) * d % d = 0 := Nat.mul_mod_left _ _
        have hLlt : 2 * L + 2 ≤ d - 1 := by
          have hhf2 : 2 * ((d - 1) / 2) = d - 1 := by omega
          omega
        have hb0 : (2 * L + 1) * d < nQubits d := by
          simp only [nQubits]
          have h1 : (2 * L + 1) * d ≤ (d - 1) * d := Nat.mul_le_mul_right d (by omega)
          have h2 : (d-1) * d < d * d := (Nat.mul_lt_mul_right hdpos).mpr (by omega)
          omega
        have hb1 : (2 * L + 2) * d < nQubits d := by
          simp only [nQubits]
          have h1 : (2 * L + 2) * d ≤ (d - 1) * d := Nat.mul_le_mul_right d (by omega)
          have h2 : (d-1) * d < d * d := (Nat.mul_lt_mul_right hdpos).mpr (by omega)
          omega
        have hne : ¬ ((2 * L + 1) * d = (2 * L + 2) * d) := by
          intro h
          have : (2*L+1) * d < (2*L+2) * d := (Nat.mul_lt_mul_right hdpos).mpr (by omega)
          omega
        have hbd0 : decide ((2 * L + 1) * d % d = 0) = true := by rw [hmod0]; simp
        have hbd1 : decide ((2 * L + 2) * d % d = 0) = true := by rw [hmod1]; simp
        have hbdiv0 : decide ((2 * L + 1) * d / d = 2 * L + 1) = true := by rw [hdiv0]; simp
        have hbdiv1a : decide ((2 * L + 2) * d / d = 2 * L + 1) = false := by
          rw [hdiv1]; rw [decide_eq_false_iff_not]; omega
        have hbdiv1b : decide ((2 * L + 2) * d / d = 2 * L + 2) = true := by rw [hdiv1]; simp
        have hbne : decide (decide ((2 * L + 1) * d = (2 * L + 2) * d) = false) = true := by
          rw [decide_eq_true_eq, decide_eq_false_iff_not]; exact hne
        have hbb0 : decide (decide ((2 * L + 1) * d < nQubits d) = true) = true := by
          rw [decide_eq_true_eq, decide_eq_true_eq]; exact hb0
        have hbb1 : decide (decide ((2 * L + 2) * d < nQubits d) = true) = true := by
          rw [decide_eq_true_eq, decide_eq_true_eq]; exact hb1
        simp only [hbd0, hbd1, hbdiv0, hbdiv1a, hbdiv1b, hbne, hbb0, hbb1,
          decide_true, decide_false, Bool.false_eq_true, if_true, if_false, reduceIte]
      · -- leftClass false → `gLeftC1 D true` antecedent false → vacuous.
        have hb : decide (decide (k < (d - 1) * (d - 1)) = false) = true := by
          rw [decide_eq_true_eq]; simp [hbulk]
        have hr : decide (decide (k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = true := by
          rw [decide_eq_true_eq]; simp [hrc]
        have hlcd : decide (decide (k - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)) = true) = false := by
          rw [decide_eq_false_iff_not]; simp [hlc]
        simp only [hb, hr, hlcd, Bool.false_eq_true, if_false, if_true, reduceIte]

/-- Column guards at the class-(b) anti qubits (`q0, q1` are multiples of `d`). -/
abbrev qbColGuardF (D : OddSurfaceDistance) : SFormula 1 :=
  .and (colGuardPure1 D (qb0 D)) (colGuardPure1 D (qb1 D))

def qbColGuardPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (qbColGuardF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [colGuardPure1, qb0, qb1, bbL1, baseBTA, baseHalfTA, bulkCountTA, dX1, distAtBoundIdx,
    dm1TA, SFormula.eval, SC.closed, SC.b, STerm.eval, Term.eval, Term.lift, bind, Option.bind]
  rw [Nat.mul_mod_left, Nat.mul_mod_left]
  simp

/-- The left-`Z` all-others pin for class (b): on column 0, if the left band fires,
then `boundNat ∈ {q0, q1}`. -/
abbrev classBLeftZPinBody (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (colGuardRaw2 D)
    (.imp (.eqBool (SC.closed (leftBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.b true))
      (.or (.eqNat SFormula.boundNat (SC.closed (qb0_2 D)))
        (.eqNat SFormula.boundNat (SC.closed (qb1_2 D)))))

abbrev classBLeftZPinF (D : OddSurfaceDistance) : SFormula 1 :=
  .allNatLt (nQ1 D) (classBLeftZPinBody D)

def classBLeftZPinPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (classBLeftZPinF D) := by
  refine PureFamilyDerivA.allNatLtIntro _ ?_
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [classBLeftZPinBody, colGuardRaw2, leftBandGuardTA, qb0_2, qb1_2, bbL2, baseBTA,
    baseHalfTA, bulkCountTA, dX2, distAtBoundIdx2, kX2, dm1TA, orEqPair, SFormula.eval, SC.closed,
    SC.b, STerm.eval, SFormula.boundNat, Term.eval, Term.lift, bind, Option.bind]
  set q := rho ⟨0, by decide⟩ with hq'
  set k := rho ⟨1, by decide⟩ with hk'
  set d := D.distance with hdd
  have hdpos : 0 < d := by omega
  set L := k - (d - 1) * (d - 1) - 2 * ((d - 1) / 2) with hL
  by_cases hq : q % d = 0
  · simp only [hq, decide_true, if_true]
    have hqdiv : q = q / d * d := (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hq)).symm
    by_cases hr0 : q / d = 2 * L + 1
    · have hqe : decide (q = (2 * L + 1) * d) = true := by rw [decide_eq_true_eq, hqdiv, hr0]
      have hr0d : decide (q / d = 2 * L + 1) = true := by rw [decide_eq_true_eq]; exact hr0
      simp only [hr0d, hqe, decide_true, if_true]
    · by_cases hr1 : q / d = 2 * L + 2
      · have hqe : decide (q = (2 * L + 2) * d) = true := by rw [decide_eq_true_eq, hqdiv, hr1]
        have hr0d : decide (q / d = 2 * L + 1) = false := by rw [decide_eq_false_iff_not]; exact hr0
        have hr1d : decide (q / d = 2 * L + 2) = true := by rw [decide_eq_true_eq]; exact hr1
        have hq0 : decide (q = (2 * L + 1) * d) = false := by
          rw [decide_eq_false_iff_not]; intro h; apply hr0; rw [hqdiv] at h
          exact Nat.eq_of_mul_eq_mul_right hdpos h
        simp only [hr0d, hr1d, hqe, hq0, decide_true, decide_false, Bool.false_eq_true,
          if_true, if_false, reduceIte]
      · have hr0d : decide (q / d = 2 * L + 1) = false := by rw [decide_eq_false_iff_not]; exact hr0
        have hr1d : decide (q / d = 2 * L + 2) = false := by rw [decide_eq_false_iff_not]; exact hr1
        simp only [hr0d, hr1d, decide_false, Bool.false_eq_true, if_false, reduceIte]
  · simp only [hq, decide_false, Bool.false_eq_true, if_false, reduceIte]

/-- Entry-at-`q` resolves to `Z` via the left-`Z` boundary leaf. -/
def antiZAtB (D : OddSurfaceDistance) {Γ : List (SFormula 1)} (qT : Term 1 .nat)
    (hEntry : SFormula.Deriv Γ
      (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed qT))
        (SC.closed (baseLeafTreeTA (dX1 D) kX1 qT))))
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dX1 D) kX1)) (SC.b false)))
    (hTopC : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dX1 D) kX1)) (SC.b false)))
    (hRightC : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dX1 D) kX1)) (SC.b false)))
    (hLeftC : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA (dX1 D) kX1)) (SC.b true)))
    (hLeftB : SFormula.Deriv Γ (.eqBool (SC.closed (leftBandGuardTA (dX1 D) kX1 qT)) (SC.b true))) :
    SFormula.Deriv Γ (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed qT)) (SC.p Pauli.Z)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ hEntry (baseLeafLeftZ _ _ _ hBulk hTopC hRightC hLeftC hLeftB)

/-- Extract the class-(b) left-`Z` pin disjunction at `boundNat`. -/
def classBLeftZPinAt {Δ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hW : SFormula.Deriv Δ (classBLeftZPinF D).weaken)
    (hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nQ1 D).weaken))
    (hcol : SFormula.Deriv Δ (colGuardRaw2 D))
    (hband : SFormula.Deriv Δ (.eqBool (SC.closed (leftBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.b true))) :
    SFormula.Deriv Δ
      (.or (.eqNat SFormula.boundNat (SC.closed (qb0_2 D)))
        (.eqNat SFormula.boundNat (SC.closed (qb1_2 D)))) := by
  have hElim := SFormula.Deriv.allNatLtElim (nQ1 D).weaken
    ((classBLeftZPinBody D).lift 1) SFormula.boundNat hW hq
  have hBody := SFormula.Deriv.applyNatBoundNatBeta (classBLeftZPinBody D) hElim
  exact SFormula.Deriv.mp (SFormula.Deriv.mp hBody hcol) hband

/-- **Class-(b) two-anti per-`k` commutation.** -/
def commTwoAntiB {Γ : List (SFormula 1)} (D : OddSurfaceDistance)
    (hBulk : SFormula.Deriv Γ (gBulk1 D false))
    (hTopC : SFormula.Deriv Γ (gTopC1 D false))
    (hRightC : SFormula.Deriv Γ (gRightC1 D false))
    (hLeftC : SFormula.Deriv Γ (gLeftC1 D true))
    (hClassB : SFormula.Deriv Γ (classBPackF D))
    (hCol : SFormula.Deriv Γ (qbColGuardF D))
    (hPin : SFormula.Deriv Γ (classBLeftZPinF D))
    (hEntryF : SFormula.Deriv Γ (entryFlatF1 D))
    (hRBFF : SFormula.Deriv Γ (rightBandFalseF D))
    (hEntry0 : SFormula.Deriv Γ
      (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed (qb0 D)))
        (SC.closed (baseLeafTreeTA (dX1 D) kX1 (qb0 D)))))
    (hEntry1 : SFormula.Deriv Γ
      (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed (qb1 D)))
        (SC.closed (baseLeafTreeTA (dX1 D) kX1 (qb1 D))))) :
    SFormula.Deriv Γ (commGoal1 D) := by
  have hPack := SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp hClassB hBulk) hRightC) hLeftC
  have hBand0 := SFormula.Deriv.andElimLeft hPack
  have hBand1 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hPack)
  have hNe := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hPack))
  have hLt0 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hPack)))
  have hLt1 := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hPack)))
  have hZ0 := antiZAtB D (qb0 D) hEntry0 hBulk hTopC hRightC hLeftC hBand0
  have hZ1 := antiZAtB D (qb1 D) hEntry1 hBulk hTopC hRightC hLeftC hBand1
  have hX0 := lxPureEntryX D (qb0 D) (qb0_pure D) (SFormula.Deriv.andElimLeft hCol)
  have hX1 := lxPureEntryX D (qb1 D) (qb1_pure D) (SFormula.Deriv.andElimRight hCol)
  refine SFormula.Deriv.commutesOfTwoAnti _ _ _ (SC.closed (qb0 D)) (SC.closed (qb1 D))
    ?wlt0 ?wlt1 ?wne ?wanti0 ?wanti1 ?wrest
  case wlt0 => exact hLt0
  case wlt1 => exact hLt1
  case wne =>
    refine SFormula.Deriv.notIntro ?_
    refine SFormula.Deriv.notElim
      (SFormula.Deriv.eqNatBoolTrue (Γ := _) (qb0 D) (qb1 D) .assumption) ?_
    exact SFormula.Deriv.eqBoolFalseNotTrue _ (cw1 hNe)
  case wanti0 =>
    exact SFormula.Deriv.anticommutesTransport _ (SC.p Pauli.Z) _ (SC.p Pauli.X) (SC.b true)
      hZ0 hX0 (SFormula.Deriv.pauliAnticommutesLit Pauli.Z Pauli.X)
  case wanti1 =>
    exact SFormula.Deriv.anticommutesTransport _ (SC.p Pauli.Z) _ (SC.p Pauli.X) (SC.b true)
      hZ1 hX1 (SFormula.Deriv.pauliAnticommutesLit Pauli.Z Pauli.X)
  case wrest =>
    refine SFormula.Deriv.allNatLtIntroBounded _ _ ?_
    refine SFormula.Deriv.impIntro (SFormula.Deriv.impIntro ?_)
    refine SFormula.Deriv.boolCases (logicalXColGuardAt2 D) _ ?_ ?_
    · set ΔT : List (SFormula 2) := .eqBool (logicalXColGuardAt2 D) (SC.b true)
        :: .not (.eqNat SFormula.boundNat (SC.closed (qb1 D)).weaken)
        :: .not (.eqNat SFormula.boundNat (SC.closed (qb0 D)).weaken)
        :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ with hΔT
      have hEntryW : SFormula.Deriv ΔT (entryFlatF1 D).weaken :=
        cw4 (SFormula.Deriv.weakenFresh (A := entryFlatF1 D) hEntryF)
      have hRBFW : SFormula.Deriv ΔT (rightBandFalseF D).weaken :=
        cw4 (SFormula.Deriv.weakenFresh (A := rightBandFalseF D) hRBFF)
      have hq : SFormula.Deriv ΔT (SFormula.witnessLt SFormula.boundNat (nQ1 D).weaken) :=
        SFormula.Deriv.hyp (by rw [hΔT]; right; right; right; exact List.mem_cons_self)
      have hcolT : SFormula.Deriv ΔT (.eqBool (logicalXColGuardAt2 D) (SC.b true)) := by
        rw [hΔT]; exact .assumption
      have hcolRaw : SFormula.Deriv ΔT (colGuardRaw2 D) := by rw [← colGuard2_eq]; exact hcolT
      have hEntry := entryAtBound D hEntryW hq
      have hRBF := rbfAtBound D hRBFW hq hcolRaw
      refine colDispatchOnTrue D hEntry hcolT hRBF ?hZbulk ?hZleft
      case hZbulk =>
        intro Δ' lift _ _ hBulkTrueΔ _ _
        -- bulk-Z: class (b) has bulk FALSE, contradicting cascade bulk TRUE.
        have hBulkFalse0 : SFormula.Deriv ΔT (gBulk D false) :=
          cw4 (SFormula.Deriv.weakenFresh (A := gBulk1 D false) hBulk)
        exact eqBoolContra _ hBulkTrueΔ (lift hBulkFalse0)
      case hZleft =>
        intro Δ' lift _ hcolΔ _ _ _ _ hLeftBΔ
        -- left-Z: use the left-Z pin → q ∈ {q0, q1}, contradicting exclusions.
        have hcolRaw' : SFormula.Deriv Δ' (colGuardRaw2 D) := by rw [← colGuard2_eq]; exact hcolΔ
        have hPinW0 : SFormula.Deriv ΔT (classBLeftZPinF D).weaken :=
          cw4 (SFormula.Deriv.weakenFresh (A := classBLeftZPinF D) hPin)
        have hdisj := classBLeftZPinAt D (lift hPinW0) (lift hq) hcolRaw' hLeftBΔ
        have hne0 : SFormula.Deriv ΔT (.not (.eqNat SFormula.boundNat (SC.closed (qb0 D)).weaken)) := by
          rw [hΔT]; exact .hyp (by right; right; exact List.mem_cons_self)
        have hne1 : SFormula.Deriv ΔT (.not (.eqNat SFormula.boundNat (SC.closed (qb1 D)).weaken)) := by
          rw [hΔT]; exact .hyp (by right; exact List.mem_cons_self)
        refine SFormula.Deriv.orElim hdisj ?_ ?_
        · exact SFormula.Deriv.botElim (SFormula.Deriv.notElim (.assumption) (cw1 (lift hne0)))
        · exact SFormula.Deriv.botElim (SFormula.Deriv.notElim (.assumption) (cw1 (lift hne1)))
    · exact logicalXOffColumnLocalCommutes D (rowK2 D) .assumption

end QHL.CodeLang.Surface.Verify
