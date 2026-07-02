import QStab.QHL.Verify.SurfaceNormalizers.XGuards

/-!
# Logical-normalizer consumers — XClassA

Two-anti class (a): left-column even-`r` bulk `Z`-plaquettes, and their per-`k` commutation.
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface

set_option maxRecDepth 65536

/-! ## Two-anti class (a): left-column even-`r` bulk `Z`-plaquettes

`k < (d-1)²`, `k % (d-1) = 0`, `(k/(d-1))` even.  The row anticommutes with
`logicalX` at the two column-0 qubits `q0 = r·d`, `q1 = (r+1)·d` where `r = k/(d-1)`. -/

/-- `r = k / (d-1)` at arity 1. -/
abbrev rA1 (D : OddSurfaceDistance) : Term 1 .nat := .div kX1 (dm1TA (dX1 D))
/-- `q0 = r·d` at arity 1 (first anti qubit). -/
abbrev qa0 (D : OddSurfaceDistance) : Term 1 .nat := .mul (rA1 D) (dX1 D)
/-- `q1 = (r+1)·d` at arity 1 (second anti qubit). -/
abbrev qa1 (D : OddSurfaceDistance) : Term 1 .nat := .mul (.add (rA1 D) (.natLit 1)) (dX1 D)

/-- Purity of the distance term `dX1` (a lifted literal). -/
def dX1_pure (D : OddSurfaceDistance) : SFormula.PureNatTerm (dX1 D) := (distAtBoundIdx D).pure
/-- Purity of `d - 1`. -/
def dm1_pure (D : OddSurfaceDistance) : SFormula.PureNatTerm (dm1TA (dX1 D)) :=
  SFormula.PureNatTerm.sub (dX1_pure D) (SFormula.PureNatTerm.natLit _)
/-- Purity of `r = k/(d-1)`. -/
def rA1_pure (D : OddSurfaceDistance) : SFormula.PureNatTerm (rA1 D) :=
  SFormula.PureNatTerm.div (SFormula.PureNatTerm.var _) (dm1_pure D)

def qa0_pure (D : OddSurfaceDistance) : SFormula.PureNatTerm (qa0 D) :=
  SFormula.PureNatTerm.mul (rA1_pure D) (dX1_pure D)
def qa1_pure (D : OddSurfaceDistance) : SFormula.PureNatTerm (qa1 D) :=
  SFormula.PureNatTerm.mul (SFormula.PureNatTerm.add (rA1_pure D) (SFormula.PureNatTerm.natLit _))
    (dX1_pure D)

/-- The class-(a) k-condition guard pack (arity 1, k = var 0): bulk true, `c = 0`,
kind true (r even), plus the band guards at `q0`/`q1` being true, the `q0 ≠ q1`
fact, and the in-range bounds `q0, q1 < nQubits`.  All are functions of `k` only, so
this is a single closed-in-`k` arithmetic fact discharged by `arithBool`. -/
abbrev classAPackF (D : OddSurfaceDistance) : SFormula 1 :=
  .imp (gBulk1 D true) (.imp (cZero1 D true) (.imp (gKind1 D true)
    (.and (.eqBool (SC.closed (baseBulkBandGuardTA (dX1 D) kX1 (qa0 D))) (SC.b true))
      (.and (.eqBool (SC.closed (baseBulkBandGuardTA (dX1 D) kX1 (qa1 D))) (SC.b true))
        (.and (.eqBool (SC.closed (.eqNat (qa0 D) (qa1 D))) (SC.b false))
          (.and (SFormula.witnessLt (SC.closed (qa0 D)) (SC.n (arity := 1) (nQubits D.distance)))
            (SFormula.witnessLt (SC.closed (qa1 D)) (SC.n (arity := 1) (nQubits D.distance)))))))))

def classAPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (classAPackF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [baseBulkBandGuardTA, cZero1, gBulk1, gKind1, qa0, qa1, rA1, dX1, distAtBoundIdx,
    dm1TA, bulkCountTA, bulkGuardTA, baseKindGuardTA, orEqSucc, band3, SFormula.eval, SC.closed,
    SC.b, SC.n, STerm.eval, SFormula.witnessLt, Term.eval, Term.lift, bind, Option.bind]
  set k := rho ⟨0, by decide⟩ with hk
  set d := D.distance with hdd
  have hdpos : 0 < d := by omega
  by_cases hbulk : k < (d - 1) * (d - 1)
  · -- bulk true
    simp only [hbulk, decide_true, if_true]
    by_cases hc : k % (d - 1) = 0
    · -- c = 0
      simp only [hc, decide_true, if_true]
      by_cases hkind : (k / (d - 1) + 0) % 2 = 0
      · -- kind true (r even).  Prove all band/bound/neq conjuncts.
        simp only [hkind, decide_true, if_true]
        -- Key div/mod facts for `r*d` and `(r+1)*d`.
        have hdiv0 : k / (d - 1) * d / d = k / (d - 1) := Nat.mul_div_cancel _ hdpos
        have hmod0 : k / (d - 1) * d % d = 0 := Nat.mul_mod_left _ _
        have hdiv1 : (k / (d - 1) + 1) * d / d = k / (d - 1) + 1 := Nat.mul_div_cancel _ hdpos
        have hmod1 : (k / (d - 1) + 1) * d % d = 0 := Nat.mul_mod_left _ _
        -- r < d-1, so r+1 ≤ d-1 and both qubits are < d².
        have hr : k / (d - 1) < d - 1 := by
          rcases Nat.lt_or_ge (k / (d-1)) (d-1) with h | h
          · exact h
          · exfalso
            have : (d - 1) * (d - 1) ≤ k / (d - 1) * (d - 1) := Nat.mul_le_mul_right _ h
            have hk2 : k / (d-1) * (d-1) ≤ k := Nat.div_mul_le_self k (d-1)
            omega
        have hb0 : k / (d - 1) * d < nQubits d := by
          simp only [nQubits]
          have h1 : k / (d-1) * d < (d-1) * d := (Nat.mul_lt_mul_right hdpos).mpr hr
          have h2 : (d-1) * d ≤ d * d := (Nat.mul_le_mul_right d (by omega))
          omega
        have hb1 : (k / (d - 1) + 1) * d < nQubits d := by
          simp only [nQubits]
          have h1 : (k / (d-1) + 1) * d ≤ (d-1) * d := (Nat.mul_le_mul_right d (by omega))
          have h2 : (d-1) * d < d * d := (Nat.mul_lt_mul_right hdpos).mpr (by omega)
          omega
        have hne : ¬ (k / (d - 1) * d = (k / (d - 1) + 1) * d) := by
          intro h
          have hlt : k / (d-1) * d < (k / (d-1) + 1) * d :=
            (Nat.mul_lt_mul_right hdpos).mpr (by omega)
          omega
        have hne0 : ¬ (k / (d - 1) = k / (d - 1) + 1) := by omega
        rw [hdiv0, hmod0, hdiv1, hmod1]
        simp only [hc, hbulk, hb0, hb1, hne, hne0, decide_true, decide_false, Nat.lt_irrefl,
          Bool.false_eq_true, if_true, if_false, reduceIte]
        generalize (decide (k / (d - 1) + 1 = k / (d - 1))) = z
        cases z <;> simp
      · simp only [hkind, decide_false, Bool.false_eq_true, if_false, reduceIte]
    · simp only [hc, decide_false, Bool.false_eq_true, if_false, reduceIte]
  · simp only [hbulk, decide_false, Bool.false_eq_true, if_false, reduceIte]

/-- Arity-2 forms of the class-(a) anti qubits (`k = var 1`). -/
abbrev qa0_2 (D : OddSurfaceDistance) : Term 2 .nat := .mul (.div kX2 (dm1TA (dX2 D))) (dX2 D)
abbrev qa1_2 (D : OddSurfaceDistance) : Term 2 .nat :=
  .mul (.add (.div kX2 (dm1TA (dX2 D))) (.natLit 1)) (dX2 D)

/-- `(qa0 D).weaken = qa0_2 D` and similarly for `qa1`. -/
theorem qa0_weaken (D : OddSurfaceDistance) : (qa0 D).weaken = qa0_2 D := rfl
theorem qa1_weaken (D : OddSurfaceDistance) : (qa1 D).weaken = qa1_2 D := rfl

/-- Column guards at the two class-(a) anti qubits: `q0 % d = 0` and `q1 % d = 0`
(both are multiples of `d`).  Closed in `k`, discharged by `arithBool`. -/
abbrev qaColGuardF (D : OddSurfaceDistance) : SFormula 1 :=
  .and (colGuardPure1 D (qa0 D)) (colGuardPure1 D (qa1 D))

def qaColGuardPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (qaColGuardF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [colGuardPure1, qa0, qa1, rA1, dX1, distAtBoundIdx, dm1TA, SFormula.eval, SC.closed,
    SC.b, STerm.eval, Term.eval, Term.lift, bind, Option.bind]
  rw [Nat.mul_mod_left, Nat.mul_mod_left]
  simp

/-- The `bulk-Z` all-others pin for class (a): on column 0, if the bulk band fires
(with `c = 0`), then `boundNat ∈ {q0, q1}`.  Quantified over `q < nQubits`. -/
abbrev classABulkZPinBody (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (colGuardRaw2 D)
    (.imp (.eqBool (SC.closed (baseBulkBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.b true))
      (.imp (cZero2 D true)
        (.or (.eqNat SFormula.boundNat (SC.closed (qa0_2 D)))
          (.eqNat SFormula.boundNat (SC.closed (qa1_2 D))))))

abbrev classABulkZPinF (D : OddSurfaceDistance) : SFormula 1 :=
  .allNatLt (nQ1 D) (classABulkZPinBody D)

def classABulkZPinPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (classABulkZPinF D) := by
  refine PureFamilyDerivA.allNatLtIntro _ ?_
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [classABulkZPinBody, colGuardRaw2, baseBulkBandGuardTA, cZero2, qa0_2, qa1_2, dX2,
    distAtBoundIdx2, kX2, dm1TA, orEqSucc, band3, bulkCountTA, SFormula.eval, SC.closed, SC.b,
    STerm.eval, SFormula.boundNat, Term.eval, Term.lift, bind, Option.bind]
  set q := rho ⟨0, by decide⟩ with hq'
  set k := rho ⟨1, by decide⟩ with hk'
  set d := D.distance with hdd
  have hdpos : 0 < d := by omega
  by_cases hq : q % d = 0
  · simp only [hq, decide_true, if_true]
    by_cases hc : k % (d - 1) = 0
    · -- c = 0; whenever the band fires (row matches), q is `r·d` or `(r+1)·d`.
      simp only [hc, decide_true, if_true]
      have hqdiv : q = q / d * d := (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hq)).symm
      -- Case on the two row-match decides.
      by_cases hrow0 : q / d = k / (d - 1)
      · -- q/d = r → q = r·d = q0
        have hqe : decide (q = k / (d - 1) * d) = true := by
          rw [decide_eq_true_eq, hqdiv, hrow0]
        have hr0 : decide (q / d = k / (d - 1)) = true := by rw [decide_eq_true_eq]; exact hrow0
        simp only [hr0, hqe, decide_true, if_true]
        by_cases hbk : decide (k < (d-1)*(d-1)) = true <;> simp [hbk]
      · by_cases hrow1 : q / d = k / (d - 1) + 1
        · -- q/d = r+1 → q = (r+1)·d = q1
          have hq1 : decide (q = (k / (d - 1) + 1) * d) = true := by
            rw [decide_eq_true_eq, hqdiv, hrow1]
          have hr0 : decide (q / d = k / (d - 1)) = false := by rw [decide_eq_false_iff_not]; exact hrow0
          have hr1 : decide (q / d = k / (d - 1) + 1) = true := by rw [decide_eq_true_eq]; exact hrow1
          have hq0 : decide (q = k / (d - 1) * d) = false := by
            rw [decide_eq_false_iff_not]; intro h; apply hrow0; rw [hqdiv] at h
            exact Nat.eq_of_mul_eq_mul_right hdpos h
          simp only [hr0, hr1, hq0, hq1, decide_true, decide_false, Bool.false_eq_true,
            if_true, if_false, reduceIte]
          by_cases hbk : decide (k < (d-1)*(d-1)) = true <;> simp [hbk]
        · -- neither: band false, antecedent vacuous
          have hr0 : decide (q / d = k / (d - 1)) = false := by rw [decide_eq_false_iff_not]; exact hrow0
          have hr1 : decide (q / d = k / (d - 1) + 1) = false := by rw [decide_eq_false_iff_not]; exact hrow1
          simp only [hr0, hr1, decide_false, Bool.false_eq_true, if_false, reduceIte]
    · -- c ≠ 0: the cZero antecedent is false, so the conclusion is vacuous (`some true`).
      have hcz : decide (decide (k % (d - 1) = 0) = true) = false := by
        rw [decide_eq_false_iff_not]; simp [hc]
      simp only [hc, hcz, decide_false, Bool.false_eq_true, if_false, reduceIte]
      generalize (decide (q / d = k / (d - 1))) = z0
      generalize (decide (q / d = k / (d - 1) + 1)) = z1
      generalize (decide (0 = k % (d - 1))) = z2
      generalize (decide (0 = k % (d - 1) + 1)) = z3
      generalize (decide (k < (d - 1) * (d - 1))) = z4
      cases z0 <;> cases z1 <;> cases z2 <;> cases z3 <;> cases z4 <;> simp
  · simp only [hq, decide_false, Bool.false_eq_true, if_false, reduceIte]

/-! ## Class-(a) two-anti per-`k` commutation -/

/-- Entry-at-`q0` resolves to `Z` (bulk, band-at-q0, kind), given the class-(a)
guard pack extracted at `q0`. -/
def antiZAtA (D : OddSurfaceDistance) {Γ : List (SFormula 1)} (qT : Term 1 .nat)
    (hqpure : SFormula.PureNatTerm qT)
    (hEntry : SFormula.Deriv Γ
      (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed qT))
        (SC.closed (baseLeafTreeTA (dX1 D) kX1 qT))))
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dX1 D) kX1)) (SC.b true)))
    (hBand : SFormula.Deriv Γ (.eqBool (SC.closed (baseBulkBandGuardTA (dX1 D) kX1 qT)) (SC.b true)))
    (hKind : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dX1 D) kX1)) (SC.b true))) :
    SFormula.Deriv Γ (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed qT)) (SC.p Pauli.Z)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ hEntry (baseLeafZ _ _ _ hBulk hBand hKind)

/-- Extract the class-(a) bulk-`Z` pin disjunction at `boundNat`. -/
def classABulkZPinAt {Δ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hW : SFormula.Deriv Δ (classABulkZPinF D).weaken)
    (hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nQ1 D).weaken))
    (hcol : SFormula.Deriv Δ (colGuardRaw2 D))
    (hband : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.b true)))
    (hcz : SFormula.Deriv Δ (cZero2 D true)) :
    SFormula.Deriv Δ
      (.or (.eqNat SFormula.boundNat (SC.closed (qa0_2 D)))
        (.eqNat SFormula.boundNat (SC.closed (qa1_2 D)))) := by
  have hElim := SFormula.Deriv.allNatLtElim (nQ1 D).weaken
    ((classABulkZPinBody D).lift 1) SFormula.boundNat hW hq
  have hBody := SFormula.Deriv.applyNatBoundNatBeta (classABulkZPinBody D) hElim
  exact SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp hBody hcol) hband) hcz

/-- **Class-(a) two-anti per-`k` commutation.**  Given the class conditions and the
supporting packs in `Γ`, the row commutes with `logicalX` by the even-parity rule:
it anticommutes at exactly `q0 = r·d` and `q1 = (r+1)·d`, and commutes elsewhere. -/
def commTwoAntiA {Γ : List (SFormula 1)} (D : OddSurfaceDistance)
    (hBulk : SFormula.Deriv Γ (gBulk1 D true))
    (hCZ : SFormula.Deriv Γ (cZero1 D true))
    (hKind : SFormula.Deriv Γ (gKind1 D true))
    (hClassA : SFormula.Deriv Γ (classAPackF D))
    (hCol : SFormula.Deriv Γ (qaColGuardF D))
    (hPin : SFormula.Deriv Γ (classABulkZPinF D))
    (hEntryF : SFormula.Deriv Γ (entryFlatF1 D))
    (hRBFF : SFormula.Deriv Γ (rightBandFalseF D))
    (hEntry0 : SFormula.Deriv Γ
      (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed (qa0 D)))
        (SC.closed (baseLeafTreeTA (dX1 D) kX1 (qa0 D)))))
    (hEntry1 : SFormula.Deriv Γ
      (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed (qa1 D)))
        (SC.closed (baseLeafTreeTA (dX1 D) kX1 (qa1 D))))) :
    SFormula.Deriv Γ (commGoal1 D) := by
  -- Extract the class-(a) guard facts at q0/q1.
  have hPack := SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp hClassA hBulk) hCZ) hKind
  have hBand0 := SFormula.Deriv.andElimLeft hPack
  have hBand1 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hPack)
  have hNe := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hPack))
  have hLt0 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hPack)))
  have hLt1 := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hPack)))
  -- Entry = Z at q0, q1.
  have hZ0 := antiZAtA D (qa0 D) (qa0_pure D) hEntry0 hBulk hBand0 hKind
  have hZ1 := antiZAtA D (qa1 D) (qa1_pure D) hEntry1 hBulk hBand1 hKind
  -- logicalX = X at q0, q1.
  have hX0 := lxPureEntryX D (qa0 D) (qa0_pure D) (SFormula.Deriv.andElimLeft hCol)
  have hX1 := lxPureEntryX D (qa1 D) (qa1_pure D) (SFormula.Deriv.andElimRight hCol)
  -- The `commutesOfTwoAnti` rule with q0 = qa0, q1 = qa1.
  refine SFormula.Deriv.commutesOfTwoAnti _ _ _ (SC.closed (qa0 D)) (SC.closed (qa1 D))
    ?wlt0 ?wlt1 ?wne ?wanti0 ?wanti1 ?wrest
  case wlt0 => exact hLt0
  case wlt1 => exact hLt1
  case wne =>
    -- q0 ≠ q1 from the `eqNat q0 q1 = false` guard fact.
    refine SFormula.Deriv.notIntro ?_
    refine SFormula.Deriv.notElim
      (SFormula.Deriv.eqNatBoolTrue (Γ := _) (qa0 D) (qa1 D) .assumption) ?_
    exact SFormula.Deriv.eqBoolFalseNotTrue _ (cw1 hNe)
  case wanti0 =>
    exact SFormula.Deriv.anticommutesTransport _ (SC.p Pauli.Z) _ (SC.p Pauli.X) (SC.b true)
      hZ0 hX0 (SFormula.Deriv.pauliAnticommutesLit Pauli.Z Pauli.X)
  case wanti1 =>
    exact SFormula.Deriv.anticommutesTransport _ (SC.p Pauli.Z) _ (SC.p Pauli.X) (SC.b true)
      hZ1 hX1 (SFormula.Deriv.pauliAnticommutesLit Pauli.Z Pauli.X)
  case wrest =>
    -- all-others: introduce qubit binder + two exclusions, boolCases column.
    refine SFormula.Deriv.allNatLtIntroBounded _ _ ?_
    refine SFormula.Deriv.impIntro (SFormula.Deriv.impIntro ?_)
    -- context: ¬q=q1 :: ¬q=q0 :: boundNatLt :: Γ.map weaken
    refine SFormula.Deriv.boolCases (logicalXColGuardAt2 D) _ ?_ ?_
    · -- column TRUE
      -- The dispatcher context (5 leading hyps over `Γ.map weaken`).
      set ΔT : List (SFormula 2) := .eqBool (logicalXColGuardAt2 D) (SC.b true)
        :: .not (.eqNat SFormula.boundNat (SC.closed (qa1 D)).weaken)
        :: .not (.eqNat SFormula.boundNat (SC.closed (qa0 D)).weaken)
        :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ with hΔT
      -- weaken the needed Γ-facts into the dispatcher context Δ.
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
        intro Δ' lift _ hcolΔ hBulkΔ hBandΔ _
        -- bulk-Z: use the pin (col ∧ band ∧ c=0) → q=q0 ∨ q=q1, contradicting exclusions.
        have hcolRaw' : SFormula.Deriv Δ' (colGuardRaw2 D) := by rw [← colGuard2_eq]; exact hcolΔ
        have hczΔ0 : SFormula.Deriv ΔT (cZero2 D true) :=
          cw4 (SFormula.Deriv.weakenFresh (A := cZero1 D true) hCZ)
        have hPinW0 : SFormula.Deriv ΔT (classABulkZPinF D).weaken :=
          cw4 (SFormula.Deriv.weakenFresh (A := classABulkZPinF D) hPin)
        have hdisj := classABulkZPinAt D (lift hPinW0) (lift hq) hcolRaw' hBandΔ (lift hczΔ0)
        -- exclusions, lifted into Δ'
        have hne0 : SFormula.Deriv ΔT (.not (.eqNat SFormula.boundNat (SC.closed (qa0 D)).weaken)) := by
          rw [hΔT]; exact .hyp (by right; right; exact List.mem_cons_self)
        have hne1 : SFormula.Deriv ΔT (.not (.eqNat SFormula.boundNat (SC.closed (qa1 D)).weaken)) := by
          rw [hΔT]; exact .hyp (by right; exact List.mem_cons_self)
        refine SFormula.Deriv.orElim hdisj ?_ ?_
        · exact SFormula.Deriv.botElim (SFormula.Deriv.notElim (.assumption) (cw1 (lift hne0)))
        · exact SFormula.Deriv.botElim (SFormula.Deriv.notElim (.assumption) (cw1 (lift hne1)))
      case hZleft =>
        intro Δ' lift _ _ hBulkFalseΔ _ _ _ _
        -- left-Z: class (a) has bulk TRUE, contradicting cascade bulk FALSE.
        have hBulkTrue0 : SFormula.Deriv ΔT (gBulk D true) :=
          cw4 (SFormula.Deriv.weakenFresh (A := gBulk1 D true) hBulk)
        exact eqBoolContra _ (lift hBulkTrue0) hBulkFalseΔ
    · -- column FALSE → off-column
      exact logicalXOffColumnLocalCommutes D (rowK2 D) .assumption

end QHL.CodeLang.Surface.Verify
