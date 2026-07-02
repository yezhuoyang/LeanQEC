import QStab.QHL.Verify.SurfaceRowsCommute.BulkRight

/-!
# Rows-commute (pairwise generated-row commutation) — BulkLeft

The Bulk–Left overlap class.
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface

set_option maxRecDepth 65536
set_option linter.unusedVariables false

/-! ## Bulk–Left overlap class

The single-class closer for the **bulk–left** overlap, the DIRECT TWIN of
`commRightBulk` (the role-swapped mirror of `commBulkTop`): row A (`k1`) is the X-type
BULK plaquette, row B (`k2`) is the Z-type LEFT-boundary stabilizer.  They overlap at
exactly the two qubits `q0 = d·(2l+1) + 0`, `q1 = d·(2l+2) + 0`, both in grid COLUMN
`0` (rows `2l+1`, `2l+2`), where `l = baseBTA(k2) - 2·half = k2 - (d-1)² - 2·(d-1)/2`
is the left-strip index of `k2`.

The Nat geometry is the proven `overlap_bulk_left` / `overlap_left_range` (in
`SurfaceRowOverlapNat.lean`).  IMPORTANT: that lemma's `k1` IS the bulk plaquette and
its `k2` IS the left boundary — which MATCHES OUR convention (our `k1` = bulk, our
`k2` = left).  So **NO role swap** when invoking them: pass OUR `k1` as ITS `k1` and
OUR `k2` as ITS `k2` (exactly like bulk–right).

DEVIATIONS FROM THE BULK–RIGHT TEMPLATE.
* The boundary strip is the LEFT (third) strip, so the class context on `k2` needs the
  extra `¬rightClass(k2)` guard: `¬bulk(k2) ∧ ¬topClass(k2) ∧ ¬rightClass(k2) ∧
  leftClass(k2)`.  Together `¬rightClass` (`b ≥ 2·half`) and `leftClass`
  (`b < 3·half`) bracket `2·half ≤ b < 3·half`, so `0 ≤ l < half` and `2l+2 < d`
  (odd `d`, `2·half = d-1`) — NO extra strip-validity antecedent is needed (the
  left-class guard supplies the upper bound for free).
* The overlap qubits are in COLUMN `0`: `q/d = 2l+1` (resp. `2l+2`), `q%d = 0`.  The
  eval-certs reconstruct this via `d·m = m·d` then `Nat.mul_div_cancel` /
  `Nat.mul_mod_left`.
* The adjacency pins `k1` (the bulk plaquette) at grid `(2l+1, 0)`, i.e.
  `k1 = (2l+1)·(d-1)`.  The bulk-band pack proves `baseKindGuardTA(k1) = FALSE` (k1 is
  the X-row): with `cellR = 2l+1`, `cellC = 0`, kind `= (2l+1 + 0) % 2 = 1 ≠ 0`.
* The left band uses `orEqPair` on `q/d` (`q/d ∈ {2l+1, 2l+2}`, `q%d = 0`), unlike the
  right band's `orEqSucc` on `q/d` (`q%d = d-1`). -/

/-- Left-strip index of `k2` (arity 2): `l = baseBTA(k2) - 2·half`. -/
abbrev blL (D : OddSurfaceDistance) : Term 2 .nat :=
  .sub (baseBTA (dP2 D) k2P) (.mul (.natLit 2) (baseHalfTA (dP2 D)))
/-- Overlap qubit `q0 = d·(2l+1)` (column `0`, row `2l+1`). -/
abbrev blQ0 (D : OddSurfaceDistance) : Term 2 .nat :=
  .mul (dP2 D) (.add (.mul (.natLit 2) (blL D)) (.natLit 1))
/-- Overlap qubit `q1 = d·(2l+2)` (column `0`, row `2l+2`). -/
abbrev blQ1 (D : OddSurfaceDistance) : Term 2 .nat :=
  .mul (dP2 D) (.add (.mul (.natLit 2) (blL D)) (.natLit 2))

abbrev blRangePackF (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false))
    (.imp (.eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false))
      (.imp (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false))
        (.imp (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b true))
          (.and (SFormula.witnessLt (SC.closed (blQ0 D)) (nP2 D))
            (.and (SFormula.witnessLt (SC.closed (blQ1 D)) (nP2 D))
              (.eqBool (SC.closed (.eqNat (blQ0 D) (blQ1 D))) (SC.b false)))))))

/-- Bulk–Left range pack: under `¬bulk ∧ ¬top ∧ ¬right ∧ left` for `k2`, the overlap
qubits `q0 = d·(2l+1)`, `q1 = d·(2l+2)` are in range and distinct.  Discharged by
`arithBool` whose eval-certificate invokes the proven `overlap_left_range`. -/
def blRangePack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (blRangePackF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd3 : D.distance = 2 * D.index + 3 := rfl
  simp only [blRangePackF, blQ0, blQ1, blL, bulkGuardTA, topClassGuardTA,
    rightClassGuardTA, leftClassGuardTA, baseBTA, baseHalfTA, bulkCountTA, dm1TA, dP2, nP2,
    SFormula.eval, SFormula.witnessLt, SC.closed, SC.b, SC.n, STerm.eval, Term.eval, Term.lift,
    bind, Option.bind, nQubits]
  set k := rho ⟨0, by decide⟩ with hk
  set d := D.distance with hdd
  have hdge : 3 ≤ d := by omega
  by_cases hbulk : k < (d - 1) * (d - 1)
  · have hb : decide (decide (k < (d - 1) * (d - 1)) = false) = false := by
      rw [decide_eq_false_iff_not]; simp [hbulk]
    simp only [hb, Bool.false_eq_true, if_false, reduceIte]
  · by_cases htop : k - (d - 1) * (d - 1) < (d - 1) / 2
    · have hbf : decide (decide (k < (d - 1) * (d - 1)) = false) = true := by
        rw [decide_eq_true_eq]; simp [hbulk]
      have htf : decide (decide (k - (d - 1) * (d - 1) < (d - 1) / 2) = false) = false := by
        rw [decide_eq_false_iff_not]; simp [htop]
      simp only [hbf, htf, Bool.false_eq_true, if_false, reduceIte]
    · by_cases hright : k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)
      · have hbf : decide (decide (k < (d - 1) * (d - 1)) = false) = true := by
          rw [decide_eq_true_eq]; simp [hbulk]
        have htf : decide (decide (k - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
          rw [decide_eq_true_eq]; simp [htop]
        have hrf : decide (decide (k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = false := by
          rw [decide_eq_false_iff_not]; simp [hright]
        simp only [hbf, htf, hrf, Bool.false_eq_true, if_false, reduceIte]
      · by_cases hleft : k - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)
        · -- the genuine left-class case.
          have hbf : decide (decide (k < (d - 1) * (d - 1)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hbulk]
          have htf : decide (decide (k - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
            rw [decide_eq_true_eq]; simp [htop]
          have hrf : decide (decide (k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hright]
          have hlf : decide (decide (k - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)) = true) = true := by
            rw [decide_eq_true_eq]; simp [hleft]
          simp only [hbf, htf, hrf, hlf, if_true]
          set l := k - (d - 1) * (d - 1) - 2 * ((d - 1) / 2) with hl
          have hhalf : 2 * ((d - 1) / 2) = d - 1 := by omega
          have hl2 : 2 * l + 2 < d := by omega
          obtain ⟨hne, hlt0, hlt1⟩ := overlap_left_range d l (by omega) hl2
          have e0 : decide (decide (d * (2 * l + 1) < d * d) = true) = true := by
            rw [decide_eq_true_eq, decide_eq_true_eq]; omega
          have e1 : decide (decide (d * (2 * l + 2) < d * d) = true) = true := by
            rw [decide_eq_true_eq, decide_eq_true_eq]; omega
          have ene : decide (decide (d * (2 * l + 1) = d * (2 * l + 2)) = false) = true := by
            rw [decide_eq_true_eq, decide_eq_false_iff_not]; omega
          simp only [e0, e1, ene, decide_true, if_true]
        · have hbf : decide (decide (k < (d - 1) * (d - 1)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hbulk]
          have htf : decide (decide (k - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
            rw [decide_eq_true_eq]; simp [htop]
          have hrf : decide (decide (k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hright]
          have hlf : decide (decide (k - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)) = true) = false := by
            rw [decide_eq_false_iff_not]; simp [hleft]
          simp only [hbf, htf, hrf, hlf, Bool.false_eq_true, if_false, reduceIte]

abbrev blLeftBandPackF (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false))
    (.imp (.eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false))
      (.imp (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false))
        (.imp (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b true))
          (.and (.eqBool (SC.closed (leftBandGuardTA (dP2 D) k2P (blQ0 D))) (SC.b true))
            (.eqBool (SC.closed (leftBandGuardTA (dP2 D) k2P (blQ1 D))) (SC.b true))))))

/-- Bulk–Left band pack: under `¬bulk ∧ ¬top ∧ ¬right ∧ left` for `k2`, the left-Z band
of `k2` fires at both overlap qubits `q0 = d·(2l+1)`, `q1 = d·(2l+2)` (both in column
`0`, rows `2l+1`, `2l+2`). -/
def blLeftBandPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (blLeftBandPackF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd3 : D.distance = 2 * D.index + 3 := rfl
  simp only [blLeftBandPackF, blQ0, blQ1, blL, bulkGuardTA, topClassGuardTA,
    rightClassGuardTA, leftClassGuardTA, leftBandGuardTA, baseBTA, baseHalfTA, bulkCountTA, dm1TA,
    orEqPair, dP2, SFormula.eval, SC.closed, SC.b, STerm.eval, Term.eval, Term.lift, bind,
    Option.bind]
  set k := rho ⟨0, by decide⟩ with hk
  set d := D.distance with hdd
  have hdge : 3 ≤ d := by omega
  have hdpos : 0 < d := by omega
  by_cases hbulk : k < (d - 1) * (d - 1)
  · have hb : decide (decide (k < (d - 1) * (d - 1)) = false) = false := by
      rw [decide_eq_false_iff_not]; simp [hbulk]
    simp only [hb, Bool.false_eq_true, if_false, reduceIte]
  · by_cases htop : k - (d - 1) * (d - 1) < (d - 1) / 2
    · have hbf : decide (decide (k < (d - 1) * (d - 1)) = false) = true := by
        rw [decide_eq_true_eq]; simp [hbulk]
      have htf : decide (decide (k - (d - 1) * (d - 1) < (d - 1) / 2) = false) = false := by
        rw [decide_eq_false_iff_not]; simp [htop]
      simp only [hbf, htf, Bool.false_eq_true, if_false, reduceIte]
    · by_cases hright : k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)
      · have hbf : decide (decide (k < (d - 1) * (d - 1)) = false) = true := by
          rw [decide_eq_true_eq]; simp [hbulk]
        have htf : decide (decide (k - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
          rw [decide_eq_true_eq]; simp [htop]
        have hrf : decide (decide (k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = false := by
          rw [decide_eq_false_iff_not]; simp [hright]
        simp only [hbf, htf, hrf, Bool.false_eq_true, if_false, reduceIte]
      · by_cases hleft : k - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)
        · have hbf : decide (decide (k < (d - 1) * (d - 1)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hbulk]
          have htf : decide (decide (k - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
            rw [decide_eq_true_eq]; simp [htop]
          have hrf : decide (decide (k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hright]
          have hlf : decide (decide (k - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)) = true) = true := by
            rw [decide_eq_true_eq]; simp [hleft]
          simp only [hbf, htf, hrf, hlf, if_true]
          set l := k - (d - 1) * (d - 1) - 2 * ((d - 1) / 2) with hl
          have hhalf : 2 * ((d - 1) / 2) = d - 1 := by omega
          have hl2 : 2 * l + 2 < d := by omega
          -- column-0 div/mod at q0, q1.
          have hq0d : (d * (2 * l + 1)) / d = 2 * l + 1 := by
            rw [Nat.mul_comm d (2 * l + 1), Nat.mul_div_cancel _ hdpos]
          have hq0m : (d * (2 * l + 1)) % d = 0 := by
            rw [Nat.mul_comm d (2 * l + 1), Nat.mul_mod_left]
          have hq1d : (d * (2 * l + 2)) / d = 2 * l + 2 := by
            rw [Nat.mul_comm d (2 * l + 2), Nat.mul_div_cancel _ hdpos]
          have hq1m : (d * (2 * l + 2)) % d = 0 := by
            rw [Nat.mul_comm d (2 * l + 2), Nat.mul_mod_left]
          rw [hq0d, hq0m, hq1d, hq1m]
          simp
        · have hbf : decide (decide (k < (d - 1) * (d - 1)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hbulk]
          have htf : decide (decide (k - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
            rw [decide_eq_true_eq]; simp [htop]
          have hrf : decide (decide (k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hright]
          have hlf : decide (decide (k - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)) = true) = false := by
            rw [decide_eq_false_iff_not]; simp [hleft]
          simp only [hbf, htf, hrf, hlf, Bool.false_eq_true, if_false, reduceIte]

/-- Adjacency condition for the bulk–left class: the X-type bulk plaquette `k1` sits at
grid `(2l+1, 0)`, i.e. `k1 = (2l+1)·(d-1)` (with `l = baseBTA(k2) - 2·half` the left
index of `k2`). -/
abbrev blAdjF (D : OddSurfaceDistance) : SFormula 2 :=
  .eqBool (SC.closed (.eqNat k1P
    (.mul (.add (.mul (.natLit 2) (blL D)) (.natLit 1)) (dm1TA (dP2 D))))) (SC.b true)

abbrev blBulkBandPackF (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false))
    (.imp (.eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false))
      (.imp (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false))
        (.imp (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b true))
          (.imp (blAdjF D)
            (.and (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true))
              (.and (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k1P)) (SC.b false))
                (.and (.eqBool (SC.closed (baseBulkBandGuardTA (dP2 D) k1P (blQ0 D))) (SC.b true))
                  (.eqBool (SC.closed (baseBulkBandGuardTA (dP2 D) k1P (blQ1 D))) (SC.b true)))))))))

/-- Bulk–Left bulk-band pack: under the left context for `k2` and the adjacency
`k1 = (2l+1)·(d-1)`, the X-type bulk plaquette `k1` (grid `(2l+1, 0)`) is in-bulk,
X-kind (`baseKindGuardTA = FALSE`, since `kind = (2l+1 + 0) % 2 = 1`), and its
plaquette band contains both overlap qubits `q0`, `q1` (the plaquette's left-column
pair). -/
def blBulkBandPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (blBulkBandPackF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd3 : D.distance = 2 * D.index + 3 := rfl
  simp only [blBulkBandPackF, blAdjF, blQ0, blQ1, blL, bulkGuardTA, topClassGuardTA,
    rightClassGuardTA, leftClassGuardTA, baseKindGuardTA, baseBulkBandGuardTA, baseBTA,
    baseHalfTA, bulkCountTA, dm1TA, band3, orEqSucc, dP2, SFormula.eval, SC.closed, SC.b,
    STerm.eval, Term.eval, Term.lift, bind, Option.bind]
  set k1 := rho ⟨1, by decide⟩ with hk1
  set k2 := rho ⟨0, by decide⟩ with hk2
  set d := D.distance with hdd
  have hdge : 3 ≤ d := by omega
  have hdpos : 0 < d := by omega
  by_cases hbulk : k2 < (d - 1) * (d - 1)
  · have hb : decide (decide (k2 < (d - 1) * (d - 1)) = false) = false := by
      rw [decide_eq_false_iff_not]; simp [hbulk]
    simp only [hb, Bool.false_eq_true, if_false, reduceIte]
  · by_cases htop : k2 - (d - 1) * (d - 1) < (d - 1) / 2
    · have hbf : decide (decide (k2 < (d - 1) * (d - 1)) = false) = true := by
        rw [decide_eq_true_eq]; simp [hbulk]
      have htf : decide (decide (k2 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = false := by
        rw [decide_eq_false_iff_not]; simp [htop]
      simp only [hbf, htf, Bool.false_eq_true, if_false, reduceIte]
    · by_cases hright : k2 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)
      · have hbf : decide (decide (k2 < (d - 1) * (d - 1)) = false) = true := by
          rw [decide_eq_true_eq]; simp [hbulk]
        have htf : decide (decide (k2 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
          rw [decide_eq_true_eq]; simp [htop]
        have hrf : decide (decide (k2 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = false := by
          rw [decide_eq_false_iff_not]; simp [hright]
        simp only [hbf, htf, hrf, Bool.false_eq_true, if_false, reduceIte]
      · by_cases hleft : k2 - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)
        · have hbf : decide (decide (k2 < (d - 1) * (d - 1)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hbulk]
          have htf : decide (decide (k2 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
            rw [decide_eq_true_eq]; simp [htop]
          have hrf : decide (decide (k2 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hright]
          have hlf : decide (decide (k2 - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)) = true) = true := by
            rw [decide_eq_true_eq]; simp [hleft]
          set l := k2 - (d - 1) * (d - 1) - 2 * ((d - 1) / 2) with hl
          have hhalf : 2 * ((d - 1) / 2) = d - 1 := by omega
          have hl2 : 2 * l + 2 < d := by omega
          have h2l1 : 2 * l + 1 < d - 1 := by omega
          have hd1pos : 0 < d - 1 := by omega
          by_cases hadj : k1 = (2 * l + 1) * (d - 1)
          · have haf : decide (decide (k1 = (2 * l + 1) * (d - 1)) = true) = true := by
              rw [decide_eq_true_eq]; simp [hadj]
            simp only [hbf, htf, hrf, hlf, haf, if_true]
            -- cellR/cellC of k1: k1/(d-1) = 2l+1, k1%(d-1) = 0.
            have hk1d : k1 / (d - 1) = 2 * l + 1 := by
              rw [hadj, Nat.mul_div_cancel _ hd1pos]
            have hk1m : k1 % (d - 1) = 0 := by
              rw [hadj, Nat.mul_mod_left]
            -- k1 < bulkCount.
            have hbulkk1 : k1 < (d - 1) * (d - 1) := by
              rw [hadj]; exact (Nat.mul_lt_mul_right hd1pos).mpr h2l1
            have hbk1d : decide (k1 < (d - 1) * (d - 1)) = true := by
              rw [decide_eq_true_eq]; exact hbulkk1
            -- column-0 div/mod at q0, q1.
            have hq0d : (d * (2 * l + 1)) / d = 2 * l + 1 := by
              rw [Nat.mul_comm d (2 * l + 1), Nat.mul_div_cancel _ hdpos]
            have hq0m : (d * (2 * l + 1)) % d = 0 := by
              rw [Nat.mul_comm d (2 * l + 1), Nat.mul_mod_left]
            have hq1d : (d * (2 * l + 2)) / d = 2 * l + 2 := by
              rw [Nat.mul_comm d (2 * l + 2), Nat.mul_div_cancel _ hdpos]
            have hq1m : (d * (2 * l + 2)) % d = 0 := by
              rw [Nat.mul_comm d (2 * l + 2), Nat.mul_mod_left]
            rw [hk1d, hk1m, hq0d, hq0m, hq1d, hq1m, hbk1d]
            -- kind = FALSE (X-kind): (2l+1 + 0) % 2 = 1 ≠ 0.
            have hkind : decide (decide ((2 * l + 1 + 0) % 2 = 0) = false) = true := by
              rw [decide_eq_true_eq, decide_eq_false_iff_not]; omega
            rw [hkind]
            -- bulk-band ROW check: q/d ∈ {2l+1, 2l+2} matches cellR=2l+1 (succ branch);
            -- COL check: q%d = 0 matches cellC=0.
            simp
          · have haf : decide (decide (k1 = (2 * l + 1) * (d - 1)) = true) = false := by
              rw [decide_eq_false_iff_not]; simp [hadj]
            simp only [hbf, htf, hrf, hlf, haf, Bool.false_eq_true, if_false, reduceIte]
        · have hbf : decide (decide (k2 < (d - 1) * (d - 1)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hbulk]
          have htf : decide (decide (k2 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
            rw [decide_eq_true_eq]; simp [htop]
          have hrf : decide (decide (k2 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hright]
          have hlf : decide (decide (k2 - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)) = true) = false := by
            rw [decide_eq_false_iff_not]; simp [hleft]
          simp only [hbf, htf, hrf, hlf, Bool.false_eq_true, if_false, reduceIte]

/-! ### Bulk–Left class: the all-others joint pin

Under the bulk–left class context (the left-class guards for `k2` and the adjacency
`k1 = (2l+1)·(d-1)`), the verified overlap geometry `overlap_bulk_left` (with
`k1`/`k2` roles UNCHANGED — there `k1` is the bulk plaquette, `k2` the left boundary,
MATCHING our convention) forces every shared non-`I` slot into `{q0, q1}`.  The slot
`q` is non-`I` for the X-type bulk plaquette `k1` exactly when its bulk band fires at
`q`, and non-`I` for the Z-type left row `k2` exactly when its left band fires at `q`;
under those two band-fired facts the disjunction `q = q0 ∨ q = q1` holds (since then
`q = d·(q/d)` with `q/d ∈ {2l+1, 2l+2}`).  `arithBool` whose eval-certificate invokes
`overlap_bulk_left`. -/

/-- Arity-3 left-strip index of `k2` (`= (blL D).weaken`). -/
abbrev blL3 (D : OddSurfaceDistance) : Term 3 .nat :=
  .sub (baseBTA (dP3 D) k2P3) (.mul (.natLit 2) (baseHalfTA (dP3 D)))
/-- Arity-3 overlap qubit `q0` (`= (blQ0 D).weaken`). -/
abbrev blQ0_3 (D : OddSurfaceDistance) : Term 3 .nat :=
  .mul (dP3 D) (.add (.mul (.natLit 2) (blL3 D)) (.natLit 1))
/-- Arity-3 overlap qubit `q1` (`= (blQ1 D).weaken`). -/
abbrev blQ1_3 (D : OddSurfaceDistance) : Term 3 .nat :=
  .mul (dP3 D) (.add (.mul (.natLit 2) (blL3 D)) (.natLit 2))

theorem blQ0_weaken (D : OddSurfaceDistance) : (blQ0 D).weaken = blQ0_3 D := rfl
theorem blQ1_weaken (D : OddSurfaceDistance) : (blQ1 D).weaken = blQ1_3 D := rfl

/-- The bulk–left joint pin body (arity 3, `k1 = var 2`, `k2 = var 1`, `q = var 0`):
under the class context and the two band-fired facts, `q ∈ {q0, q1}`.  The
position-determining BOUNDARY band (`k2`'s left band, which fixes `q%d = 0` and
`q/d ∈ {2l+1, 2l+2}`) is the OUTER antecedent, mirroring `brPinBody`. -/
abbrev blPinBody (D : OddSurfaceDistance) : SFormula 3 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b false))
    (.imp (.eqBool (SC.closed (topClassGuardTA (dP3 D) k2P3)) (SC.b false))
      (.imp (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k2P3)) (SC.b false))
        (.imp (.eqBool (SC.closed (leftClassGuardTA (dP3 D) k2P3)) (SC.b true))
          (.imp (.eqBool (SC.closed (.eqNat k1P3
              (.mul (.add (.mul (.natLit 2) (blL3 D)) (.natLit 1)) (dm1TA (dP3 D))))) (SC.b true))
            (.imp (.eqBool (SC.closed (leftBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))
              (.imp (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true))
                (.or (.eqNat SFormula.boundNat (SC.closed (blQ0_3 D)))
                  (.eqNat SFormula.boundNat (SC.closed (blQ1_3 D))))))))))

abbrev blPinF (D : OddSurfaceDistance) : SFormula 2 :=
  .allNatLt (nP2 D) (blPinBody D)

/-- Bulk–Left joint pin pack: under the bulk–left class context, every shared non-`I`
slot is one of the two overlap qubits.  `arithBool`, eval-cert via `overlap_bulk_left`
(NO role swap). -/
def blPinPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (blPinF D) := by
  refine PureFamilyDerivA.allNatLtIntro _ ?_
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd3 : D.distance = 2 * D.index + 3 := rfl
  simp only [blPinBody, blQ0_3, blQ1_3, blL3, bulkGuardTA, topClassGuardTA, rightClassGuardTA,
    leftClassGuardTA, baseBulkBandGuardTA, leftBandGuardTA, baseBTA, baseHalfTA, bulkCountTA, dm1TA,
    band3, orEqSucc, orEqPair, dP3, dP2, k1P3, k2P3, qP3, SFormula.eval, SFormula.boundNat,
    SC.closed, SC.b, STerm.eval, Term.eval, Term.lift, bind, Option.bind]
  set q := rho ⟨0, by decide⟩ with hq'
  set k2 := rho ⟨1, by decide⟩ with hk2'
  set k1 := rho ⟨2, by decide⟩ with hk1'
  set d := D.distance with hdd
  have hdge : 3 ≤ d := by omega
  have hdpos : 0 < d := by omega
  by_cases hbulk : k2 < (d - 1) * (d - 1)
  · have hb : decide (decide (k2 < (d - 1) * (d - 1)) = false) = false := by
      rw [decide_eq_false_iff_not]; simp [hbulk]
    simp only [hb, Bool.false_eq_true, if_false, reduceIte]
  · by_cases htop : k2 - (d - 1) * (d - 1) < (d - 1) / 2
    · have hbf : decide (decide (k2 < (d - 1) * (d - 1)) = false) = true := by
        rw [decide_eq_true_eq]; simp [hbulk]
      have htf : decide (decide (k2 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = false := by
        rw [decide_eq_false_iff_not]; simp [htop]
      simp only [hbf, htf, Bool.false_eq_true, if_false, reduceIte]
    · by_cases hright : k2 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)
      · have hbf : decide (decide (k2 < (d - 1) * (d - 1)) = false) = true := by
          rw [decide_eq_true_eq]; simp [hbulk]
        have htf : decide (decide (k2 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
          rw [decide_eq_true_eq]; simp [htop]
        have hrf : decide (decide (k2 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = false := by
          rw [decide_eq_false_iff_not]; simp [hright]
        simp only [hbf, htf, hrf, Bool.false_eq_true, if_false, reduceIte]
      · by_cases hleft : k2 - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)
        · have hbf : decide (decide (k2 < (d - 1) * (d - 1)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hbulk]
          have htf : decide (decide (k2 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
            rw [decide_eq_true_eq]; simp [htop]
          have hrf : decide (decide (k2 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hright]
          have hlf : decide (decide (k2 - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)) = true) = true := by
            rw [decide_eq_true_eq]; simp [hleft]
          set l := k2 - (d - 1) * (d - 1) - 2 * ((d - 1) / 2) with hl
          have hhalf : 2 * ((d - 1) / 2) = d - 1 := by omega
          have hl2 : 2 * l + 2 < d := by omega
          have h2l1 : 2 * l + 1 < d - 1 := by omega
          have hd1pos : 0 < d - 1 := by omega
          by_cases hadj : k1 = (2 * l + 1) * (d - 1)
          · have haf : decide (decide (k1 = (2 * l + 1) * (d - 1)) = true) = true := by
              rw [decide_eq_true_eq]; simp [hadj]
            simp only [hbf, htf, hrf, hlf, haf, if_true]
            -- k1 cellR/cellC (so the bulk-band guard for k1 fully reduces).
            have hk1d : k1 / (d - 1) = 2 * l + 1 := by
              rw [hadj, Nat.mul_div_cancel _ hd1pos]
            have hk1m : k1 % (d - 1) = 0 := by
              rw [hadj, Nat.mul_mod_left]
            -- left-band fired on k2: q%d = 0 and q/d ∈ {2l+1, 2l+2}.
            by_cases hqcol : q % d = 0
            · by_cases hqrow : q / d = 2 * l + 1 ∨ q / d = 2 * l + 2
              · -- left-band fires; q = d·(q/d) ∈ {q0, q1}.
                have hqval : q = d * (q / d) := by
                  have hdm := Nat.div_add_mod q d
                  rw [hqcol] at hdm; omega
                rcases hqrow with hc | hc
                · -- q/d = 2l+1 → q = q0.
                  have hqe : q = d * (2 * l + 1) := by rw [hqval, hc]
                  rw [hqcol, hc, hk1d, hk1m]; simp [hqe]
                · -- q/d = 2l+2 → q = q1.
                  have hqe : q = d * (2 * l + 2) := by rw [hqval, hc]
                  have e0v : ¬ (q = d * (2 * l + 1)) := by
                    rw [hqe]
                    have : d * (2 * l + 1) < d * (2 * l + 2) := (Nat.mul_lt_mul_left hdpos).mpr (by omega)
                    omega
                  rw [hqcol, hc, hk1d, hk1m]; simp [hqe, e0v]
              · -- q/d ∉ {2l+1, 2l+2}: left-band row antecedent false → vacuous.
                push_neg at hqrow
                obtain ⟨hcr0, hcr1⟩ := hqrow
                rw [hqcol]; simp [hcr0, hcr1]
            · -- q%d ≠ 0: left-band col antecedent false → vacuous.
              simp [hqcol]
          · have haf : decide (decide (k1 = (2 * l + 1) * (d - 1)) = true) = false := by
              rw [decide_eq_false_iff_not]; simp [hadj]
            simp only [hbf, htf, hrf, hlf, haf, Bool.false_eq_true, if_false, reduceIte]
        · have hbf : decide (decide (k2 < (d - 1) * (d - 1)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hbulk]
          have htf : decide (decide (k2 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
            rw [decide_eq_true_eq]; simp [htop]
          have hrf : decide (decide (k2 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hright]
          have hlf : decide (decide (k2 - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)) = true) = false := by
            rw [decide_eq_false_iff_not]; simp [hleft]
          simp only [hbf, htf, hrf, hlf, Bool.false_eq_true, if_false, reduceIte]

/-- Extract the bulk–left joint-pin disjunction at `boundNat`. -/
def blPinAt {Δ : List (SFormula 3)} (D : OddSurfaceDistance)
    (hW : SFormula.Deriv Δ (blPinF D).weaken)
    (hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken))
    (hBulkF : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b false)))
    (hTopF : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA (dP3 D) k2P3)) (SC.b false)))
    (hRightF : SFormula.Deriv Δ (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k2P3)) (SC.b false)))
    (hLeftC : SFormula.Deriv Δ (.eqBool (SC.closed (leftClassGuardTA (dP3 D) k2P3)) (SC.b true)))
    (hAdj : SFormula.Deriv Δ (.eqBool (SC.closed (.eqNat k1P3
      (.mul (.add (.mul (.natLit 2) (blL3 D)) (.natLit 1)) (dm1TA (dP3 D))))) (SC.b true)))
    (hLeftB : SFormula.Deriv Δ (.eqBool (SC.closed (leftBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true)))
    (hBulkB : SFormula.Deriv Δ
      (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true))) :
    SFormula.Deriv Δ
      (.or (.eqNat SFormula.boundNat (SC.closed (blQ0_3 D)))
        (.eqNat SFormula.boundNat (SC.closed (blQ1_3 D)))) := by
  have hElim := SFormula.Deriv.allNatLtElim (nP2 D).weaken
    ((blPinBody D).lift 1) SFormula.boundNat hW hq
  have hBody := SFormula.Deriv.applyNatBoundNatBeta (blPinBody D) hElim
  exact SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp
    (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp hBody hBulkF) hTopF) hRightF)
      hLeftC) hAdj) hLeftB) hBulkB

/-! ### Bulk–Left class: reverse-leaf band recovery + the joint pin handler -/

/-- Recover `bulkBand(k1, q) = true` from `baseLeafTreeTA k1 q = X`, given `bulk(k1)`.
Reverse-leaf: the false band branch gives an `I` leaf, contradicting `X`. -/
def blBulkBandFromX {Δ : List (SFormula 3)} (D : OddSurfaceDistance)
    (hBulkT : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b true)))
    (hLeafX : SFormula.Deriv Δ
      (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3)) (SC.p Pauli.X))) :
    SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true)) := by
  refine SFormula.Deriv.boolCases (SC.closed (baseBulkBandGuardTA (dP3 D) k1P3 qP3)) _ .assumption ?_
  refine SFormula.Deriv.botElim ?_
  have hBandF : SFormula.Deriv (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k1P3 qP3)) (SC.b false) :: Δ)
      (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k1P3 qP3)) (SC.b false)) := .assumption
  have hI : SFormula.Deriv (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k1P3 qP3)) (SC.b false) :: Δ)
      (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3)) (SC.p Pauli.I)) :=
    baseLeafBulkIS (dP3 D) k1P3 qP3 (cw1 hBulkT) hBandF
  have hXI : SFormula.Deriv (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k1P3 qP3)) (SC.b false) :: Δ)
      (.eqPauli (SC.p Pauli.X) (SC.p Pauli.I)) :=
    SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.eqPauliSymm _ _ (cw1 hLeafX)) hI
  exact SFormula.Deriv.notElim hXI (SFormula.Deriv.pauliNeqLit Pauli.X Pauli.I (by decide))

/-- Recover `leftBand(k2, q) = true` from `baseLeafTreeTA k2 q = Z`, given the left
class context (`¬bulk ∧ ¬top ∧ ¬right ∧ left`).  Reverse-leaf: the false band branch
gives an `I` leaf (`baseLeafLeftIS`), contradicting `Z`. -/
def blLeftBandFromZ {Δ : List (SFormula 3)} (D : OddSurfaceDistance)
    (hBulkF : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b false)))
    (hTopF : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA (dP3 D) k2P3)) (SC.b false)))
    (hRightF : SFormula.Deriv Δ (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k2P3)) (SC.b false)))
    (hLeftC : SFormula.Deriv Δ (.eqBool (SC.closed (leftClassGuardTA (dP3 D) k2P3)) (SC.b true)))
    (hLeafZ : SFormula.Deriv Δ
      (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p Pauli.Z))) :
    SFormula.Deriv Δ (.eqBool (SC.closed (leftBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true)) := by
  refine SFormula.Deriv.boolCases (SC.closed (leftBandGuardTA (dP3 D) k2P3 qP3)) _ .assumption ?_
  refine SFormula.Deriv.botElim ?_
  have hBandF : SFormula.Deriv (.eqBool (SC.closed (leftBandGuardTA (dP3 D) k2P3 qP3)) (SC.b false) :: Δ)
      (.eqBool (SC.closed (leftBandGuardTA (dP3 D) k2P3 qP3)) (SC.b false)) := .assumption
  have hI : SFormula.Deriv (.eqBool (SC.closed (leftBandGuardTA (dP3 D) k2P3 qP3)) (SC.b false) :: Δ)
      (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p Pauli.I)) :=
    baseLeafLeftIS (dP3 D) k2P3 qP3 (cw1 hBulkF) (cw1 hTopF) (cw1 hRightF) (cw1 hLeftC) hBandF
  have hZI : SFormula.Deriv (.eqBool (SC.closed (leftBandGuardTA (dP3 D) k2P3 qP3)) (SC.b false) :: Δ)
      (.eqPauli (SC.p Pauli.Z) (SC.p Pauli.I)) :=
    SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.eqPauliSymm _ _ (cw1 hLeafZ)) hI
  exact SFormula.Deriv.notElim hZI (SFormula.Deriv.pauliNeqLit Pauli.Z Pauli.I (by decide))

/-- **Bulk–Left overlap class closer.**  Assembles the per-pair commutation goal for
the bulk–left overlap, the direct twin of `commRightBulk`: row A (`k1`) is the X-type
bulk plaquette, row B (`k2`) is the Z-type left-boundary stabilizer.  Consumes the
three arithmetic packs (`blRangePack`/`blLeftBandPack`/`blBulkBandPack`), the joint pin
(`blPinPack`), and the four flat-entry facts at `q0`, `q1`; under the class context
(the four class guards for `k2`, the adjacency pinning `k1`, and `k1`'s in-bulk fact)
it resolves row A to `X` via `baseLeafXS` (X-bulk leaf) and row B to `Z` via
`baseLeafLeftZS` (left-Z leaf), then discharges the all-others premise via the generic
two-anti spine `commBulkTopXZ`. -/
def commLeftBulk {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hEntryA : SFormula.Deriv Γ (entryAQuant D)) (hEntryB : SFormula.Deriv Γ (entryBQuant D))
    (hk1X : SFormula.Deriv Γ (k1IsX D true)) (hExcl1 : SFormula.Deriv Γ (typeExclF D k1P))
    (hbulkFk2 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)))
    (htopFk2 : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false)))
    (hrightFk2 : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false)))
    (hleftCk2 : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b true)))
    (hadj : SFormula.Deriv Γ (blAdjF D))
    (hRange : SFormula.Deriv Γ (blRangePackF D))
    (hLeftBand : SFormula.Deriv Γ (blLeftBandPackF D))
    (hBulkBand : SFormula.Deriv Γ (blBulkBandPackF D))
    (hPin : SFormula.Deriv Γ (blPinF D))
    (hEA0 : SFormula.Deriv Γ (entryAAtQF D (blQ0 D)))
    (hEA1 : SFormula.Deriv Γ (entryAAtQF D (blQ1 D)))
    (hEB0 : SFormula.Deriv Γ (entryBAtQF D (blQ0 D)))
    (hEB1 : SFormula.Deriv Γ (entryBAtQF D (blQ1 D))) :
    SFormula.Deriv Γ (pairGoal D) := by
  -- Range facts at q0/q1.
  have hRangeP := SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp
    (SFormula.Deriv.mp hRange hbulkFk2) htopFk2) hrightFk2) hleftCk2
  have hLt0 := SFormula.Deriv.andElimLeft hRangeP
  have hLt1 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hRangeP)
  have hNe := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hRangeP)
  -- Left-band-fires facts at q0/q1.
  have hLBP := SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp
    (SFormula.Deriv.mp hLeftBand hbulkFk2) htopFk2) hrightFk2) hleftCk2
  have hLB0 := SFormula.Deriv.andElimLeft hLBP
  have hLB1 := SFormula.Deriv.andElimRight hLBP
  -- Bulk-band facts for the X plaquette k1 at q0/q1.
  have hKBP := SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp
    (SFormula.Deriv.mp hBulkBand hbulkFk2) htopFk2) hrightFk2) hleftCk2) hadj
  have hBulkK1 := SFormula.Deriv.andElimLeft hKBP
  have hKindK1 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hKBP)
  have hBB0 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hKBP))
  have hBB1 := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hKBP))
  -- Row A = X at q0/q1 (bulk-X leaf), Row B = Z at q0/q1 (left-Z leaf).
  have hAX0 : SFormula.Deriv Γ (.eqPauli (.stabAt (rowA D) (SC.closed (blQ0 D))) (SC.p Pauli.X)) :=
    SFormula.Deriv.eqPauliTrans _ _ _ hEA0 (baseLeafXS (dP2 D) k1P (blQ0 D) hBulkK1 hBB0 hKindK1)
  have hAX1 : SFormula.Deriv Γ (.eqPauli (.stabAt (rowA D) (SC.closed (blQ1 D))) (SC.p Pauli.X)) :=
    SFormula.Deriv.eqPauliTrans _ _ _ hEA1 (baseLeafXS (dP2 D) k1P (blQ1 D) hBulkK1 hBB1 hKindK1)
  have hBZ0 : SFormula.Deriv Γ (.eqPauli (.stabAt (rowB D) (SC.closed (blQ0 D))) (SC.p Pauli.Z)) :=
    SFormula.Deriv.eqPauliTrans _ _ _ hEB0
      (baseLeafLeftZS (dP2 D) k2P (blQ0 D) hbulkFk2 htopFk2 hrightFk2 hleftCk2 hLB0)
  have hBZ1 : SFormula.Deriv Γ (.eqPauli (.stabAt (rowB D) (SC.closed (blQ1 D))) (SC.p Pauli.Z)) :=
    SFormula.Deriv.eqPauliTrans _ _ _ hEB1
      (baseLeafLeftZS (dP2 D) k2P (blQ1 D) hbulkFk2 htopFk2 hrightFk2 hleftCk2 hLB1)
  -- Assemble via the (generic) two-anti spine; the all-others pin handler closes overlap.
  refine commBulkTopXZ D (blQ0 D) (blQ1 D) hEntryA hEntryB hk1X hExcl1
    hLt0 hLt1 hNe hAX0 hAX1 hBZ0 hBZ1 ?_
  intro Δ' lift hLeafA hLeafB
  -- The class context + adj + k1-bulk fact, lifted into Δ'.
  have hbulkFk2Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b false)) :=
    lift (cw3 (SFormula.Deriv.weakenFresh
      (A := .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)) hbulkFk2))
  have htopFk2Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (topClassGuardTA (dP3 D) k2P3)) (SC.b false)) :=
    lift (cw3 (SFormula.Deriv.weakenFresh
      (A := .eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false)) htopFk2))
  have hrightFk2Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k2P3)) (SC.b false)) :=
    lift (cw3 (SFormula.Deriv.weakenFresh
      (A := .eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false)) hrightFk2))
  have hleftCk2Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (leftClassGuardTA (dP3 D) k2P3)) (SC.b true)) :=
    lift (cw3 (SFormula.Deriv.weakenFresh
      (A := .eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b true)) hleftCk2))
  have hadjΔ : SFormula.Deriv Δ' (.eqBool (SC.closed (.eqNat k1P3
      (.mul (.add (.mul (.natLit 2) (blL3 D)) (.natLit 1)) (dm1TA (dP3 D))))) (SC.b true)) :=
    lift (cw3 (SFormula.Deriv.weakenFresh (A := blAdjF D) hadj))
  have hBulkK1Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b true)) :=
    lift (cw3 (SFormula.Deriv.weakenFresh
      (A := .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true)) hBulkK1))
  have hPinΔ : SFormula.Deriv Δ' (blPinF D).weaken :=
    lift (cw3 (SFormula.Deriv.weakenFresh (A := blPinF D) hPin))
  have hq : SFormula.Deriv Δ' (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken) :=
    lift (.hyp (by right; right; exact List.mem_cons_self))
  -- Recover the band-fired facts at boundNat from the leaves.
  have hBulkB := blBulkBandFromX D hBulkK1Δ hLeafA
  have hLeftB := blLeftBandFromZ D hbulkFk2Δ htopFk2Δ hrightFk2Δ hleftCk2Δ hLeafB
  -- The pin: boundNat ∈ {q0, q1}.
  have hdisj := blPinAt D hPinΔ hq hbulkFk2Δ htopFk2Δ hrightFk2Δ hleftCk2Δ hadjΔ hLeftB hBulkB
  -- The two exclusions in the handler context, lifted into Δ'.
  have hne0 : SFormula.Deriv Δ'
      (.not (.eqNat SFormula.boundNat (SC.closed (blQ0 D)).weaken)) :=
    lift (.hyp (by right; exact List.mem_cons_self))
  have hne1 : SFormula.Deriv Δ'
      (.not (.eqNat SFormula.boundNat (SC.closed (blQ1 D)).weaken)) :=
    lift (.hyp List.mem_cons_self)
  have hne0' : SFormula.Deriv Δ'
      (.not (.eqNat SFormula.boundNat (SC.closed (blQ0_3 D)))) := hne0
  have hne1' : SFormula.Deriv Δ'
      (.not (.eqNat SFormula.boundNat (SC.closed (blQ1_3 D)))) := hne1
  refine SFormula.Deriv.orElim hdisj ?_ ?_
  · exact SFormula.Deriv.botElim (SFormula.Deriv.notElim .assumption (cw1 hne0'))
  · exact SFormula.Deriv.botElim (SFormula.Deriv.notElim .assumption (cw1 hne1'))

end QHL.CodeLang.Surface.Verify
