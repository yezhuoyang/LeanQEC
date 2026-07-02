import QStab.QHL.Verify.SurfaceRowsCommute.BulkTop

/-!
# Rows-commute (pairwise generated-row commutation) — BulkBottom

The Bulk–Bottom overlap class (overlap qubits, joint pin, reverse-leaf recovery + handler).
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface

set_option maxRecDepth 65536
set_option linter.unusedVariables false

/-! ## Bulk–Bottom overlap class

The single-class closer for the **bulk–bottom** overlap, replicating the
`commBulkTop` template exactly with the X/Z ROLES UNCHANGED: row A (`k1 = recCall
k1`) is the X-type BOTTOM-boundary stabilizer, row B (`k2 = recCall k2`) is the
Z-type bulk plaquette sitting just above it (grid row `r = d-2`), adjacent to the
bottom check.  They overlap at exactly the two qubits `q0 = d·(d-1) + (2·bb + 1)`,
`q1 = d·(d-1) + (2·bb + 2)`, both in the LAST grid row `d-1`, where
`bb = baseBTA(k1) - 3·half = k1 - (d-1)² - 3·(d-1)/2` is the bottom-strip index of
`k1`.

The Nat geometry is the proven `overlap_bulk_bottom` / `overlap_bottom_range` (in
`SurfaceRowOverlapNat.lean`).  IMPORTANT: that lemma's `k1` is the BULK plaquette
and its `k2` is the BOTTOM boundary — SWAPPED vs OUR convention (our `k1` = bottom
boundary, our `k2` = bulk).  So when invoking `overlap_bulk_bottom` we pass OUR `k2`
(bulk) as ITS `k1` and OUR `k1` (bottom boundary) as ITS `k2`, exactly as
`btPinPack` does for `overlap_bulk_top`.

DEVIATION FROM THE BULK–TOP TEMPLATE.  Two things differ:
* The class context for `k1` is the LAST strip, so it needs the three PRECEDING
  class guards FALSE in addition to `¬bulk`: `¬bulk ∧ ¬topClass ∧ ¬rightClass ∧
  ¬leftClass`.  These four LOWER-bound the strip index but give no upper bound, so a
  fifth antecedent `bottomStripGuard` (`baseBTA(k1) < 4·half`, i.e. `k1` is a valid
  bottom-strip — not past-the-end — index) is added; it is the one extra range fact
  needed to prove `2·bb + 2 < d` and is mechanically supplied by the (eventual)
  dispatcher's `k1 < numStab` hypothesis.  (Bulk–top's `topClass` already gave its
  upper bound `b < half` for free, so it needed no such antecedent.)
* The overlap qubits are in the LAST grid row, so `q/d = d-1`, `q%d = r` (instead of
  bulk–top's `q/d = 0`, `q%d = q`).  The eval-certs reconstruct this via
  `d·(d-1) + r = r + (d-1)·d` then `Nat.add_mul_div_right` / `Nat.add_mul_mod_self_right`. -/

/-- Bottom-strip index of `k1` (arity 2): `bb = baseBTA(k1) - 3·half`. -/
abbrev bbB (D : OddSurfaceDistance) : Term 2 .nat :=
  .sub (baseBTA (dP2 D) k1P) (.mul (.natLit 3) (baseHalfTA (dP2 D)))
/-- Overlap qubit `q0 = d·(d-1) + (2·bb + 1)` (last grid row). -/
abbrev bbQ0 (D : OddSurfaceDistance) : Term 2 .nat :=
  .add (.mul (dP2 D) (dm1TA (dP2 D))) (.add (.mul (.natLit 2) (bbB D)) (.natLit 1))
/-- Overlap qubit `q1 = d·(d-1) + (2·bb + 2)` (last grid row). -/
abbrev bbQ1 (D : OddSurfaceDistance) : Term 2 .nat :=
  .add (.mul (dP2 D) (dm1TA (dP2 D))) (.add (.mul (.natLit 2) (bbB D)) (.natLit 2))

/-- The bottom-strip validity guard for `k1`: `baseBTA(k1) < 4·half`.  This is the
upper bound placing `k1` inside (not past) the bottom strip, equivalent to
`k1 < numStab`; the one range fact not implied by the four class guards. -/
abbrev bbStripF (D : OddSurfaceDistance) : SFormula 2 :=
  .eqBool (SC.closed (.ltNat (baseBTA (dP2 D) k1P) (.mul (.natLit 4) (baseHalfTA (dP2 D)))))
    (SC.b true)

abbrev bbRangePackF (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false))
    (.imp (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false))
      (.imp (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k1P)) (SC.b false))
        (.imp (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k1P)) (SC.b false))
          (.imp (bbStripF D)
            (.and (SFormula.witnessLt (SC.closed (bbQ0 D)) (nP2 D))
              (.and (SFormula.witnessLt (SC.closed (bbQ1 D)) (nP2 D))
                (.eqBool (SC.closed (.eqNat (bbQ0 D) (bbQ1 D))) (SC.b false))))))))

/-- Bulk–Bottom range pack: under `¬bulk ∧ ¬top ∧ ¬right ∧ ¬left` for `k1` plus the
bottom-strip validity bound, the overlap qubits `q0 = d·(d-1)+(2bb+1)`,
`q1 = d·(d-1)+(2bb+2)` are in range and distinct.  Discharged by `arithBool` whose
eval-certificate invokes the proven `overlap_bottom_range`. -/
def bbRangePack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (bbRangePackF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd3 : D.distance = 2 * D.index + 3 := rfl
  simp only [bbRangePackF, bbStripF, bbQ0, bbQ1, bbB, bulkGuardTA, topClassGuardTA,
    rightClassGuardTA, leftClassGuardTA, baseBTA, baseHalfTA, bulkCountTA, dm1TA, dP2, nP2,
    SFormula.eval, SFormula.witnessLt, SC.closed, SC.b, SC.n, STerm.eval, Term.eval, Term.lift,
    bind, Option.bind, nQubits]
  set k := rho ⟨1, by decide⟩ with hk
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
        · have hbf : decide (decide (k < (d - 1) * (d - 1)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hbulk]
          have htf : decide (decide (k - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
            rw [decide_eq_true_eq]; simp [htop]
          have hrf : decide (decide (k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hright]
          have hlf : decide (decide (k - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)) = false) = false := by
            rw [decide_eq_false_iff_not]; simp [hleft]
          simp only [hbf, htf, hrf, hlf, Bool.false_eq_true, if_false, reduceIte]
        · -- the genuine bottom-class case; now case on the strip-validity bound.
          have hbf : decide (decide (k < (d - 1) * (d - 1)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hbulk]
          have htf : decide (decide (k - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
            rw [decide_eq_true_eq]; simp [htop]
          have hrf : decide (decide (k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hright]
          have hlf : decide (decide (k - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hleft]
          by_cases hub : k - (d - 1) * (d - 1) < 4 * ((d - 1) / 2)
          · have huf : decide (decide (k - (d - 1) * (d - 1) < 4 * ((d - 1) / 2)) = true) = true := by
              rw [decide_eq_true_eq]; simp [hub]
            simp only [hbf, htf, hrf, hlf, huf, if_true]
            set bb := k - (d - 1) * (d - 1) - 3 * ((d - 1) / 2) with hbb
            have hhalf : 2 * ((d - 1) / 2) = d - 1 := by omega
            have hb2 : 2 * bb + 2 < d := by omega
            obtain ⟨hne, hlt0, hlt1⟩ := overlap_bottom_range d bb (by omega) hb2
            have e0 : decide (decide (d * (d - 1) + (2 * bb + 1) < d * d) = true) = true := by
              rw [decide_eq_true_eq, decide_eq_true_eq]; exact hlt0
            have e1 : decide (decide (d * (d - 1) + (2 * bb + 2) < d * d) = true) = true := by
              rw [decide_eq_true_eq, decide_eq_true_eq]; exact hlt1
            have ene : decide (decide (d * (d - 1) + (2 * bb + 1) = d * (d - 1) + (2 * bb + 2)) = false) = true := by
              rw [decide_eq_true_eq, decide_eq_false_iff_not]; exact hne
            simp only [e0, e1, ene, decide_true, if_true]
          · -- strip-validity bound false → antecedent false → vacuous.
            have huf : decide (decide (k - (d - 1) * (d - 1) < 4 * ((d - 1) / 2)) = true) = false := by
              rw [decide_eq_false_iff_not]; simp [hub]
            simp only [hbf, htf, hrf, hlf, huf, Bool.false_eq_true, if_false, reduceIte]

abbrev bbBottomBandPackF (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false))
    (.imp (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false))
      (.imp (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k1P)) (SC.b false))
        (.imp (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k1P)) (SC.b false))
          (.imp (bbStripF D)
            (.and (.eqBool (SC.closed (bottomBandGuardTA (dP2 D) k1P (bbQ0 D))) (SC.b true))
              (.eqBool (SC.closed (bottomBandGuardTA (dP2 D) k1P (bbQ1 D))) (SC.b true)))))))

/-- Bulk–Bottom band pack: under `¬bulk ∧ ¬top ∧ ¬right ∧ ¬left` for `k1` plus the
strip bound, the bottom-X band of `k1` fires at both overlap qubits `q0`, `q1` (both
in the last grid row `d-1`). -/
def bbBottomBandPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (bbBottomBandPackF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd3 : D.distance = 2 * D.index + 3 := rfl
  simp only [bbBottomBandPackF, bbStripF, bbQ0, bbQ1, bbB, bulkGuardTA, topClassGuardTA,
    rightClassGuardTA, leftClassGuardTA, bottomBandGuardTA, baseBTA, baseHalfTA, bulkCountTA,
    dm1TA, orEqPair, dP2, SFormula.eval, SC.closed, SC.b, STerm.eval, Term.eval, Term.lift,
    bind, Option.bind]
  set k := rho ⟨1, by decide⟩ with hk
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
        · have hbf : decide (decide (k < (d - 1) * (d - 1)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hbulk]
          have htf : decide (decide (k - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
            rw [decide_eq_true_eq]; simp [htop]
          have hrf : decide (decide (k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hright]
          have hlf : decide (decide (k - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)) = false) = false := by
            rw [decide_eq_false_iff_not]; simp [hleft]
          simp only [hbf, htf, hrf, hlf, Bool.false_eq_true, if_false, reduceIte]
        · have hbf : decide (decide (k < (d - 1) * (d - 1)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hbulk]
          have htf : decide (decide (k - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
            rw [decide_eq_true_eq]; simp [htop]
          have hrf : decide (decide (k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hright]
          have hlf : decide (decide (k - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hleft]
          by_cases hub : k - (d - 1) * (d - 1) < 4 * ((d - 1) / 2)
          · have huf : decide (decide (k - (d - 1) * (d - 1) < 4 * ((d - 1) / 2)) = true) = true := by
              rw [decide_eq_true_eq]; simp [hub]
            simp only [hbf, htf, hrf, hlf, huf, if_true]
            set bb := k - (d - 1) * (d - 1) - 3 * ((d - 1) / 2) with hbb
            have hhalf : 2 * ((d - 1) / 2) = d - 1 := by omega
            have hb2 : 2 * bb + 2 < d := by omega
            have hr0 : 2 * bb + 1 < d := by omega
            -- last-row div/mod reconstruction at q0, q1.
            have hq0d : (d * (d - 1) + (2 * bb + 1)) / d = d - 1 := by
              have e : d * (d - 1) + (2 * bb + 1) = (2 * bb + 1) + (d - 1) * d := by
                rw [Nat.mul_comm d (d - 1)]; omega
              rw [e, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hr0]; omega
            have hq0m : (d * (d - 1) + (2 * bb + 1)) % d = 2 * bb + 1 := by
              have e : d * (d - 1) + (2 * bb + 1) = (2 * bb + 1) + (d - 1) * d := by
                rw [Nat.mul_comm d (d - 1)]; omega
              rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr0]
            have hq1d : (d * (d - 1) + (2 * bb + 2)) / d = d - 1 := by
              have e : d * (d - 1) + (2 * bb + 2) = (2 * bb + 2) + (d - 1) * d := by
                rw [Nat.mul_comm d (d - 1)]; omega
              rw [e, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hb2]; omega
            have hq1m : (d * (d - 1) + (2 * bb + 2)) % d = 2 * bb + 2 := by
              have e : d * (d - 1) + (2 * bb + 2) = (2 * bb + 2) + (d - 1) * d := by
                rw [Nat.mul_comm d (d - 1)]; omega
              rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb2]
            rw [hq0d, hq0m, hq1d, hq1m]
            simp
          · have huf : decide (decide (k - (d - 1) * (d - 1) < 4 * ((d - 1) / 2)) = true) = false := by
              rw [decide_eq_false_iff_not]; simp [hub]
            simp only [hbf, htf, hrf, hlf, huf, Bool.false_eq_true, if_false, reduceIte]

/-- Adjacency condition for the bulk–bottom class: the Z-type bulk plaquette `k2`
sits at grid `(d-2, 2bb+1)`, i.e. `k2 = (d-2)·(d-1) + (2bb+1)` (with
`bb = baseBTA(k1) - 3·half` the bottom index of `k1`). -/
abbrev bbAdjF (D : OddSurfaceDistance) : SFormula 2 :=
  .eqBool (SC.closed (.eqNat k2P
    (.add (.mul (.sub (dm1TA (dP2 D)) (.natLit 1)) (dm1TA (dP2 D)))
      (.add (.mul (.natLit 2) (bbB D)) (.natLit 1))))) (SC.b true)

abbrev bbBulkBandPackF (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false))
    (.imp (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false))
      (.imp (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k1P)) (SC.b false))
        (.imp (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k1P)) (SC.b false))
          (.imp (bbStripF D)
            (.imp (bbAdjF D)
              (.and (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true))
                (.and (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k2P)) (SC.b true))
                  (.and (.eqBool (SC.closed (baseBulkBandGuardTA (dP2 D) k2P (bbQ0 D))) (SC.b true))
                    (.eqBool (SC.closed (baseBulkBandGuardTA (dP2 D) k2P (bbQ1 D))) (SC.b true))))))))))

/-- Bulk–Bottom bulk-band pack: under the bottom context for `k1`, the strip bound,
and the adjacency `k2 = (d-2)·(d-1)+(2bb+1)`, the Z-type bulk plaquette `k2` (grid
`(d-2, 2bb+1)`) is in-bulk, Z-kind, and its plaquette band contains both overlap
qubits `q0`, `q1` (the plaquette's bottom-row pair). -/
def bbBulkBandPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (bbBulkBandPackF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd3 : D.distance = 2 * D.index + 3 := rfl
  simp only [bbBulkBandPackF, bbAdjF, bbStripF, bbQ0, bbQ1, bbB, bulkGuardTA, topClassGuardTA,
    rightClassGuardTA, leftClassGuardTA, baseKindGuardTA, baseBulkBandGuardTA, baseBTA,
    baseHalfTA, bulkCountTA, dm1TA, band3, orEqSucc, dP2, SFormula.eval, SC.closed, SC.b,
    STerm.eval, Term.eval, Term.lift, bind, Option.bind]
  set k1 := rho ⟨1, by decide⟩ with hk1
  set k2 := rho ⟨0, by decide⟩ with hk2
  set d := D.distance with hdd
  have hdge : 3 ≤ d := by omega
  by_cases hbulk : k1 < (d - 1) * (d - 1)
  · have hb : decide (decide (k1 < (d - 1) * (d - 1)) = false) = false := by
      rw [decide_eq_false_iff_not]; simp [hbulk]
    simp only [hb, Bool.false_eq_true, if_false, reduceIte]
  · by_cases htop : k1 - (d - 1) * (d - 1) < (d - 1) / 2
    · have hbf : decide (decide (k1 < (d - 1) * (d - 1)) = false) = true := by
        rw [decide_eq_true_eq]; simp [hbulk]
      have htf : decide (decide (k1 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = false := by
        rw [decide_eq_false_iff_not]; simp [htop]
      simp only [hbf, htf, Bool.false_eq_true, if_false, reduceIte]
    · by_cases hright : k1 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)
      · have hbf : decide (decide (k1 < (d - 1) * (d - 1)) = false) = true := by
          rw [decide_eq_true_eq]; simp [hbulk]
        have htf : decide (decide (k1 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
          rw [decide_eq_true_eq]; simp [htop]
        have hrf : decide (decide (k1 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = false := by
          rw [decide_eq_false_iff_not]; simp [hright]
        simp only [hbf, htf, hrf, Bool.false_eq_true, if_false, reduceIte]
      · by_cases hleft : k1 - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)
        · have hbf : decide (decide (k1 < (d - 1) * (d - 1)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hbulk]
          have htf : decide (decide (k1 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
            rw [decide_eq_true_eq]; simp [htop]
          have hrf : decide (decide (k1 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hright]
          have hlf : decide (decide (k1 - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)) = false) = false := by
            rw [decide_eq_false_iff_not]; simp [hleft]
          simp only [hbf, htf, hrf, hlf, Bool.false_eq_true, if_false, reduceIte]
        · have hbf : decide (decide (k1 < (d - 1) * (d - 1)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hbulk]
          have htf : decide (decide (k1 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
            rw [decide_eq_true_eq]; simp [htop]
          have hrf : decide (decide (k1 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hright]
          have hlf : decide (decide (k1 - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hleft]
          by_cases hub : k1 - (d - 1) * (d - 1) < 4 * ((d - 1) / 2)
          · have huf : decide (decide (k1 - (d - 1) * (d - 1) < 4 * ((d - 1) / 2)) = true) = true := by
              rw [decide_eq_true_eq]; simp [hub]
            set bb := k1 - (d - 1) * (d - 1) - 3 * ((d - 1) / 2) with hbb
            have hhalf : 2 * ((d - 1) / 2) = d - 1 := by omega
            have hb2 : 2 * bb + 2 < d := by omega
            have hcol1 : 2 * bb + 1 < d - 1 := by omega
            -- `dm1TA - 1` evaluates to `d - 1 - 1`; bridge it to `d - 2`.
            have hd2 : d - 1 - 1 = d - 2 := by omega
            by_cases hadj : k2 = (d - 1 - 1) * (d - 1) + (2 * bb + 1)
            · have haf : decide (decide (k2 = (d - 1 - 1) * (d - 1) + (2 * bb + 1)) = true) = true := by
                rw [decide_eq_true_eq]; simp [hadj]
              simp only [hbf, htf, hrf, hlf, huf, haf, if_true]
              -- cellR/cellC of k2: k2/(d-1) = d-2, k2%(d-1) = 2bb+1.
              have hk2d : k2 / (d - 1) = d - 2 := by
                rw [hadj, hd2]
                have e : (d - 2) * (d - 1) + (2 * bb + 1) = (2 * bb + 1) + (d - 2) * (d - 1) := by
                  omega
                rw [e, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hcol1]; omega
              have hk2m : k2 % (d - 1) = 2 * bb + 1 := by
                rw [hadj, hd2]
                have e : (d - 2) * (d - 1) + (2 * bb + 1) = (2 * bb + 1) + (d - 2) * (d - 1) := by
                  omega
                rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hcol1]
              -- k2 < bulkCount.
              have hbulkk2 : k2 < (d - 1) * (d - 1) := by
                have hsq : (d - 2) * (d - 1) + (d - 1) = (d - 1) * (d - 1) := by
                  have hs : (d - 2) + 1 = d - 1 := by omega
                  rw [← Nat.succ_mul, Nat.succ_eq_add_one, hs]
                rw [hadj, hd2]; omega
              have hbk2d : decide (k2 < (d - 1) * (d - 1)) = true := by
                rw [decide_eq_true_eq]; exact hbulkk2
              -- last-row div/mod at q0, q1.
              have hr0 : 2 * bb + 1 < d := by omega
              have hq0d : (d * (d - 1) + (2 * bb + 1)) / d = d - 1 := by
                have e : d * (d - 1) + (2 * bb + 1) = (2 * bb + 1) + (d - 1) * d := by
                  rw [Nat.mul_comm d (d - 1)]; omega
                rw [e, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hr0]; omega
              have hq0m : (d * (d - 1) + (2 * bb + 1)) % d = 2 * bb + 1 := by
                have e : d * (d - 1) + (2 * bb + 1) = (2 * bb + 1) + (d - 1) * d := by
                  rw [Nat.mul_comm d (d - 1)]; omega
                rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr0]
              have hq1d : (d * (d - 1) + (2 * bb + 2)) / d = d - 1 := by
                have e : d * (d - 1) + (2 * bb + 2) = (2 * bb + 2) + (d - 1) * d := by
                  rw [Nat.mul_comm d (d - 1)]; omega
                rw [e, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hb2]; omega
              have hq1m : (d * (d - 1) + (2 * bb + 2)) % d = 2 * bb + 2 := by
                have e : d * (d - 1) + (2 * bb + 2) = (2 * bb + 2) + (d - 1) * d := by
                  rw [Nat.mul_comm d (d - 1)]; omega
                rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb2]
              rw [hk2d, hk2m, hq0d, hq0m, hq1d, hq1m, hbk2d]
              -- kind = 0 (Z-kind): ((d-2)+(2bb+1)) % 2 = 0 for odd d.
              have hkind : decide (decide ((d - 2 + (2 * bb + 1)) % 2 = 0) = true) = true := by
                rw [decide_eq_true_eq, decide_eq_true_eq]; omega
              rw [hkind]
              -- bulk-band ROW check: q/d = d-1, k2/(d-1) = d-2; `d-1 = (d-2)+1` (succ branch).
              have hrowne : ¬ (d - 1 = d - 2) := by omega
              have hrowsucc : d - 1 = d - 2 + 1 := by omega
              simp [hrowne, hrowsucc]
            · have haf : decide (decide (k2 = (d - 1 - 1) * (d - 1) + (2 * bb + 1)) = true) = false := by
                rw [decide_eq_false_iff_not]; simp [hadj]
              simp only [hbf, htf, hrf, hlf, huf, haf, Bool.false_eq_true, if_false, reduceIte]
          · have huf : decide (decide (k1 - (d - 1) * (d - 1) < 4 * ((d - 1) / 2)) = true) = false := by
              rw [decide_eq_false_iff_not]; simp [hub]
            simp only [hbf, htf, hrf, hlf, huf, Bool.false_eq_true, if_false, reduceIte]

/-! ### Bulk–Bottom class: the all-others joint pin

Under the bulk–bottom class context (the four class guards for `k1`, the strip
bound, and the adjacency `k2 = (d-2)·(d-1)+(2bb+1)`), the verified overlap geometry
`overlap_bulk_bottom` (with `k1`/`k2` roles SWAPPED: there `k1` is the bulk row,
`k2` the bottom row — so OUR `k2` is its `k1`, OUR `k1` its `k2`) forces every shared
non-`I` slot into `{q0, q1}`.  The slot `q` is non-`I` for the X-type bottom row `k1`
exactly when its bottom-X band fires at `q`, and non-`I` for the Z-type bulk
plaquette `k2` exactly when its bulk band fires at `q`; under the bottom-band-fired
fact `q/d = d-1 ∧ q%d ∈ {2bb+1, 2bb+2}` the disjunction `q = q0 ∨ q = q1` holds
(since then `q = d·(d-1) + q%d`).  Discharged by `arithBool`. -/

/-- Arity-3 bottom-strip index of `k1` (`= (bbB D).weaken`). -/
abbrev bbB3 (D : OddSurfaceDistance) : Term 3 .nat :=
  .sub (baseBTA (dP3 D) k1P3) (.mul (.natLit 3) (baseHalfTA (dP3 D)))
/-- Arity-3 overlap qubit `q0` (`= (bbQ0 D).weaken`). -/
abbrev bbQ0_3 (D : OddSurfaceDistance) : Term 3 .nat :=
  .add (.mul (dP3 D) (dm1TA (dP3 D))) (.add (.mul (.natLit 2) (bbB3 D)) (.natLit 1))
/-- Arity-3 overlap qubit `q1` (`= (bbQ1 D).weaken`). -/
abbrev bbQ1_3 (D : OddSurfaceDistance) : Term 3 .nat :=
  .add (.mul (dP3 D) (dm1TA (dP3 D))) (.add (.mul (.natLit 2) (bbB3 D)) (.natLit 2))

theorem bbQ0_weaken (D : OddSurfaceDistance) : (bbQ0 D).weaken = bbQ0_3 D := rfl
theorem bbQ1_weaken (D : OddSurfaceDistance) : (bbQ1 D).weaken = bbQ1_3 D := rfl

/-- The bulk–bottom joint pin body (arity 3, `k1 = var 2`, `k2 = var 1`, `q = var 0`):
under the class context and the two band-fired facts, `q ∈ {q0, q1}`. -/
abbrev bbPinBody (D : OddSurfaceDistance) : SFormula 3 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b false))
    (.imp (.eqBool (SC.closed (topClassGuardTA (dP3 D) k1P3)) (SC.b false))
      (.imp (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k1P3)) (SC.b false))
        (.imp (.eqBool (SC.closed (leftClassGuardTA (dP3 D) k1P3)) (SC.b false))
          (.imp (.eqBool (SC.closed (.ltNat (baseBTA (dP3 D) k1P3)
              (.mul (.natLit 4) (baseHalfTA (dP3 D))))) (SC.b true))
            (.imp (.eqBool (SC.closed (.eqNat k2P3
                (.add (.mul (.sub (dm1TA (dP3 D)) (.natLit 1)) (dm1TA (dP3 D)))
                  (.add (.mul (.natLit 2) (bbB3 D)) (.natLit 1))))) (SC.b true))
              (.imp (.eqBool (SC.closed (bottomBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true))
                (.imp (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))
                  (.or (.eqNat SFormula.boundNat (SC.closed (bbQ0_3 D)))
                    (.eqNat SFormula.boundNat (SC.closed (bbQ1_3 D)))))))))))

abbrev bbPinF (D : OddSurfaceDistance) : SFormula 2 :=
  .allNatLt (nP2 D) (bbPinBody D)

/-- Bulk–Bottom joint pin pack: under the bulk–bottom class context, every shared
non-`I` slot is one of the two overlap qubits.  `arithBool`. -/
def bbPinPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (bbPinF D) := by
  refine PureFamilyDerivA.allNatLtIntro _ ?_
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd3 : D.distance = 2 * D.index + 3 := rfl
  simp only [bbPinBody, bbQ0_3, bbQ1_3, bbB3, bulkGuardTA, topClassGuardTA, rightClassGuardTA,
    leftClassGuardTA, bottomBandGuardTA, baseBulkBandGuardTA, baseBTA, baseHalfTA, bulkCountTA,
    dm1TA, band3, orEqSucc, orEqPair, dP3, dP2, k1P3, k2P3, qP3, SFormula.eval, SFormula.boundNat,
    SC.closed, SC.b, STerm.eval, Term.eval, Term.lift, bind, Option.bind]
  set q := rho ⟨0, by decide⟩ with hq'
  set k2 := rho ⟨1, by decide⟩ with hk2'
  set k1 := rho ⟨2, by decide⟩ with hk1'
  set d := D.distance with hdd
  have hdge : 3 ≤ d := by omega
  have hdpos : 0 < d := by omega
  by_cases hbulk : k1 < (d - 1) * (d - 1)
  · have hb : decide (decide (k1 < (d - 1) * (d - 1)) = false) = false := by
      rw [decide_eq_false_iff_not]; simp [hbulk]
    simp only [hb, Bool.false_eq_true, if_false, reduceIte]
  · by_cases htop : k1 - (d - 1) * (d - 1) < (d - 1) / 2
    · have hbf : decide (decide (k1 < (d - 1) * (d - 1)) = false) = true := by
        rw [decide_eq_true_eq]; simp [hbulk]
      have htf : decide (decide (k1 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = false := by
        rw [decide_eq_false_iff_not]; simp [htop]
      simp only [hbf, htf, Bool.false_eq_true, if_false, reduceIte]
    · by_cases hright : k1 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)
      · have hbf : decide (decide (k1 < (d - 1) * (d - 1)) = false) = true := by
          rw [decide_eq_true_eq]; simp [hbulk]
        have htf : decide (decide (k1 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
          rw [decide_eq_true_eq]; simp [htop]
        have hrf : decide (decide (k1 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = false := by
          rw [decide_eq_false_iff_not]; simp [hright]
        simp only [hbf, htf, hrf, Bool.false_eq_true, if_false, reduceIte]
      · by_cases hleft : k1 - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)
        · have hbf : decide (decide (k1 < (d - 1) * (d - 1)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hbulk]
          have htf : decide (decide (k1 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
            rw [decide_eq_true_eq]; simp [htop]
          have hrf : decide (decide (k1 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hright]
          have hlf : decide (decide (k1 - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)) = false) = false := by
            rw [decide_eq_false_iff_not]; simp [hleft]
          simp only [hbf, htf, hrf, hlf, Bool.false_eq_true, if_false, reduceIte]
        · have hbf : decide (decide (k1 < (d - 1) * (d - 1)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hbulk]
          have htf : decide (decide (k1 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
            rw [decide_eq_true_eq]; simp [htop]
          have hrf : decide (decide (k1 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hright]
          have hlf : decide (decide (k1 - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hleft]
          by_cases hub : k1 - (d - 1) * (d - 1) < 4 * ((d - 1) / 2)
          · have huf : decide (decide (k1 - (d - 1) * (d - 1) < 4 * ((d - 1) / 2)) = true) = true := by
              rw [decide_eq_true_eq]; simp [hub]
            set bb := k1 - (d - 1) * (d - 1) - 3 * ((d - 1) / 2) with hbb
            have hhalf : 2 * ((d - 1) / 2) = d - 1 := by omega
            have hb2 : 2 * bb + 2 < d := by omega
            have hd2 : d - 1 - 1 = d - 2 := by omega
            by_cases hadj : k2 = (d - 1 - 1) * (d - 1) + (2 * bb + 1)
            · have haf : decide (decide (k2 = (d - 1 - 1) * (d - 1) + (2 * bb + 1)) = true) = true := by
                rw [decide_eq_true_eq]; simp [hadj]
              simp only [hbf, htf, hrf, hlf, huf, haf, if_true]
              -- k2 cellR/cellC (so the bulk-band guard for k2 fully reduces).
              have hcol1 : 2 * bb + 1 < d - 1 := by omega
              have hk2d : k2 / (d - 1) = d - 2 := by
                rw [hadj, hd2]
                have e : (d - 2) * (d - 1) + (2 * bb + 1) = (2 * bb + 1) + (d - 2) * (d - 1) := by omega
                rw [e, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hcol1]; omega
              have hk2m : k2 % (d - 1) = 2 * bb + 1 := by
                rw [hadj, hd2]
                have e : (d - 2) * (d - 1) + (2 * bb + 1) = (2 * bb + 1) + (d - 2) * (d - 1) := by omega
                rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hcol1]
              -- bottom-band fired on k1: q/d = d-1 and q%d ∈ {2bb+1, 2bb+2}.
              by_cases hqrow : q / d = d - 1
              · by_cases hqcol : q % d = 2 * bb + 1 ∨ q % d = 2 * bb + 2
                · -- bottom-band fires; q = d·(d-1) + q%d ∈ {q0, q1}.
                  have hqval : q = d * (d - 1) + q % d := by
                    have hdm := Nat.div_add_mod q d
                    rw [hqrow] at hdm; omega
                  -- bulk-band ROW check for k2: `d-1 = (d-2)+1` (succ branch).
                  have hrowne : ¬ (d - 1 = d - 2) := by omega
                  have hrowsucc : d - 1 = d - 2 + 1 := by omega
                  rcases hqcol with hc | hc
                  · -- q%d = 2bb+1 → q = q0.
                    have hqe : q = d * (d - 1) + (2 * bb + 1) := by rw [hqval, hc]
                    rw [hqrow, hc, hk2d, hk2m]; simp [hqe, hrowne, hrowsucc]
                  · -- q%d = 2bb+2 → q = q1.
                    have hqe : q = d * (d - 1) + (2 * bb + 2) := by rw [hqval, hc]
                    have e0v : ¬ (q = d * (d - 1) + (2 * bb + 1)) := by omega
                    rw [hqrow, hc, hk2d, hk2m]; simp [hqe, e0v, hrowne, hrowsucc]
                · -- q%d ∉ {2bb+1, 2bb+2}: bottom-band col antecedent false → vacuous.
                  push_neg at hqcol
                  obtain ⟨hcq0, hcq1⟩ := hqcol
                  rw [hqrow]; simp [hcq0, hcq1]
              · -- q/d ≠ d-1: bottom-band row antecedent false → vacuous.
                simp [hqrow]
            · have haf : decide (decide (k2 = (d - 1 - 1) * (d - 1) + (2 * bb + 1)) = true) = false := by
                rw [decide_eq_false_iff_not]; simp [hadj]
              simp only [hbf, htf, hrf, hlf, huf, haf, Bool.false_eq_true, if_false, reduceIte]
          · have huf : decide (decide (k1 - (d - 1) * (d - 1) < 4 * ((d - 1) / 2)) = true) = false := by
              rw [decide_eq_false_iff_not]; simp [hub]
            simp only [hbf, htf, hrf, hlf, huf, Bool.false_eq_true, if_false, reduceIte]

/-- Extract the bulk–bottom joint-pin disjunction at `boundNat`. -/
def bbPinAt {Δ : List (SFormula 3)} (D : OddSurfaceDistance)
    (hW : SFormula.Deriv Δ (bbPinF D).weaken)
    (hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken))
    (hBulkF : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b false)))
    (hTopF : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA (dP3 D) k1P3)) (SC.b false)))
    (hRightF : SFormula.Deriv Δ (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k1P3)) (SC.b false)))
    (hLeftF : SFormula.Deriv Δ (.eqBool (SC.closed (leftClassGuardTA (dP3 D) k1P3)) (SC.b false)))
    (hStrip : SFormula.Deriv Δ (.eqBool (SC.closed (.ltNat (baseBTA (dP3 D) k1P3)
      (.mul (.natLit 4) (baseHalfTA (dP3 D))))) (SC.b true)))
    (hAdj : SFormula.Deriv Δ (.eqBool (SC.closed (.eqNat k2P3
      (.add (.mul (.sub (dm1TA (dP3 D)) (.natLit 1)) (dm1TA (dP3 D)))
        (.add (.mul (.natLit 2) (bbB3 D)) (.natLit 1))))) (SC.b true)))
    (hBotB : SFormula.Deriv Δ (.eqBool (SC.closed (bottomBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true)))
    (hBulkB : SFormula.Deriv Δ
      (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))) :
    SFormula.Deriv Δ
      (.or (.eqNat SFormula.boundNat (SC.closed (bbQ0_3 D)))
        (.eqNat SFormula.boundNat (SC.closed (bbQ1_3 D)))) := by
  have hElim := SFormula.Deriv.allNatLtElim (nP2 D).weaken
    ((bbPinBody D).lift 1) SFormula.boundNat hW hq
  have hBody := SFormula.Deriv.applyNatBoundNatBeta (bbPinBody D) hElim
  exact SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp
    (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp hBody hBulkF)
      hTopF) hRightF) hLeftF) hStrip) hAdj) hBotB) hBulkB

/-! ### Bulk–Bottom class: reverse-leaf band recovery + the joint pin handler -/

/-- Recover `bottomBand(k1, q) = true` from `baseLeafTreeTA k1 q = X`, given the
bottom class context (`¬bulk ∧ ¬top ∧ ¬right ∧ ¬left`).  Reverse-leaf: the false
band branch gives an `I` leaf, contradicting `X`. -/
def bbBottomBandFromX {Δ : List (SFormula 3)} (D : OddSurfaceDistance)
    (hBulkF : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b false)))
    (hTopF : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA (dP3 D) k1P3)) (SC.b false)))
    (hRightF : SFormula.Deriv Δ (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k1P3)) (SC.b false)))
    (hLeftF : SFormula.Deriv Δ (.eqBool (SC.closed (leftClassGuardTA (dP3 D) k1P3)) (SC.b false)))
    (hLeafX : SFormula.Deriv Δ
      (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3)) (SC.p Pauli.X))) :
    SFormula.Deriv Δ (.eqBool (SC.closed (bottomBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true)) := by
  refine SFormula.Deriv.boolCases (SC.closed (bottomBandGuardTA (dP3 D) k1P3 qP3)) _ .assumption ?_
  refine SFormula.Deriv.botElim ?_
  have hBandF : SFormula.Deriv (.eqBool (SC.closed (bottomBandGuardTA (dP3 D) k1P3 qP3)) (SC.b false) :: Δ)
      (.eqBool (SC.closed (bottomBandGuardTA (dP3 D) k1P3 qP3)) (SC.b false)) := .assumption
  have hI : SFormula.Deriv (.eqBool (SC.closed (bottomBandGuardTA (dP3 D) k1P3 qP3)) (SC.b false) :: Δ)
      (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3)) (SC.p Pauli.I)) :=
    baseLeafBottomIS (dP3 D) k1P3 qP3 (cw1 hBulkF) (cw1 hTopF) (cw1 hRightF) (cw1 hLeftF) hBandF
  have hXZ : SFormula.Deriv (.eqBool (SC.closed (bottomBandGuardTA (dP3 D) k1P3 qP3)) (SC.b false) :: Δ)
      (.eqPauli (SC.p Pauli.X) (SC.p Pauli.I)) :=
    SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.eqPauliSymm _ _ (cw1 hLeafX)) hI
  exact SFormula.Deriv.notElim hXZ (SFormula.Deriv.pauliNeqLit Pauli.X Pauli.I (by decide))

/-- Recover `bulkBand(k2, q) = true` from `baseLeafTreeTA k2 q = Z`, given `bulk(k2)`.
Identical to `btBulkBandFromZ`. -/
def bbBulkBandFromZ {Δ : List (SFormula 3)} (D : OddSurfaceDistance)
    (hBulkT : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b true)))
    (hLeafZ : SFormula.Deriv Δ
      (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p Pauli.Z))) :
    SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true)) :=
  btBulkBandFromZ D hBulkT hLeafZ

/-- **Bulk–Bottom overlap class closer.**  Assembles the per-pair commutation goal
for the bulk–bottom overlap, where row A (`k1`) is the X-type bottom-boundary
stabilizer and row B (`k2`) is the Z-type bulk plaquette at the adjacent grid row
`d-2`.  Mirrors `commBulkTop` exactly: consumes the three arithmetic packs
(`bbRangePack`/`bbBottomBandPack`/`bbBulkBandPack`), the joint pin (`bbPinPack`), and
the four flat-entry facts at `q0`, `q1`; under the class context (the four class
guards FALSE for the last strip, the strip-validity bound, and the adjacency) it
resolves both rows to `X`/`Z` at `q0`/`q1` and discharges the all-others premise via
the proven two-anti spine `commBulkTopXZ` (generic in `q0`/`q1`). -/
def commBottomBulk {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hEntryA : SFormula.Deriv Γ (entryAQuant D)) (hEntryB : SFormula.Deriv Γ (entryBQuant D))
    (hk1X : SFormula.Deriv Γ (k1IsX D true)) (hExcl1 : SFormula.Deriv Γ (typeExclF D k1P))
    (hbulkF : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false)))
    (htopF : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false)))
    (hrightF : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k1P)) (SC.b false)))
    (hleftF : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k1P)) (SC.b false)))
    (hstrip : SFormula.Deriv Γ (bbStripF D))
    (hadj : SFormula.Deriv Γ (bbAdjF D))
    (hRange : SFormula.Deriv Γ (bbRangePackF D))
    (hBottomBand : SFormula.Deriv Γ (bbBottomBandPackF D))
    (hBulkBand : SFormula.Deriv Γ (bbBulkBandPackF D))
    (hPin : SFormula.Deriv Γ (bbPinF D))
    (hEA0 : SFormula.Deriv Γ (entryAAtQF D (bbQ0 D)))
    (hEA1 : SFormula.Deriv Γ (entryAAtQF D (bbQ1 D)))
    (hEB0 : SFormula.Deriv Γ (entryBAtQF D (bbQ0 D)))
    (hEB1 : SFormula.Deriv Γ (entryBAtQF D (bbQ1 D))) :
    SFormula.Deriv Γ (pairGoal D) := by
  -- Range facts at q0/q1.
  have hRangeP := SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp
    (SFormula.Deriv.mp hRange hbulkF) htopF) hrightF) hleftF) hstrip
  have hLt0 := SFormula.Deriv.andElimLeft hRangeP
  have hLt1 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hRangeP)
  have hNe := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hRangeP)
  -- Bottom-band-fires facts at q0/q1.
  have hBBP := SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp
    (SFormula.Deriv.mp hBottomBand hbulkF) htopF) hrightF) hleftF) hstrip
  have hTB0 := SFormula.Deriv.andElimLeft hBBP
  have hTB1 := SFormula.Deriv.andElimRight hBBP
  -- Bulk-band facts for the Z plaquette k2 at q0/q1.
  have hKBP := SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp
    (SFormula.Deriv.mp (SFormula.Deriv.mp hBulkBand hbulkF) htopF) hrightF) hleftF) hstrip) hadj
  have hBulkK2 := SFormula.Deriv.andElimLeft hKBP
  have hKindK2 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hKBP)
  have hBB0 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hKBP))
  have hBB1 := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hKBP))
  -- Row A = X at q0/q1 (bottom-X leaf), Row B = Z at q0/q1 (bulk-Z leaf).
  have hAX0 : SFormula.Deriv Γ (.eqPauli (.stabAt (rowA D) (SC.closed (bbQ0 D))) (SC.p Pauli.X)) :=
    SFormula.Deriv.eqPauliTrans _ _ _ hEA0
      (baseLeafBottomXS (dP2 D) k1P (bbQ0 D) hbulkF htopF hrightF hleftF hTB0)
  have hAX1 : SFormula.Deriv Γ (.eqPauli (.stabAt (rowA D) (SC.closed (bbQ1 D))) (SC.p Pauli.X)) :=
    SFormula.Deriv.eqPauliTrans _ _ _ hEA1
      (baseLeafBottomXS (dP2 D) k1P (bbQ1 D) hbulkF htopF hrightF hleftF hTB1)
  have hBZ0 : SFormula.Deriv Γ (.eqPauli (.stabAt (rowB D) (SC.closed (bbQ0 D))) (SC.p Pauli.Z)) :=
    SFormula.Deriv.eqPauliTrans _ _ _ hEB0 (baseLeafZS (dP2 D) k2P (bbQ0 D) hBulkK2 hBB0 hKindK2)
  have hBZ1 : SFormula.Deriv Γ (.eqPauli (.stabAt (rowB D) (SC.closed (bbQ1 D))) (SC.p Pauli.Z)) :=
    SFormula.Deriv.eqPauliTrans _ _ _ hEB1 (baseLeafZS (dP2 D) k2P (bbQ1 D) hBulkK2 hBB1 hKindK2)
  -- Assemble via the (generic) two-anti spine; the all-others pin handler closes overlap.
  refine commBulkTopXZ D (bbQ0 D) (bbQ1 D) hEntryA hEntryB hk1X hExcl1
    hLt0 hLt1 hNe hAX0 hAX1 hBZ0 hBZ1 ?_
  intro Δ' lift hLeafA hLeafB
  -- The class context + strip + adj + k2-bulk fact, lifted into Δ'.
  have hbulkFΔ : SFormula.Deriv Δ' (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b false)) :=
    lift (cw3 (SFormula.Deriv.weakenFresh
      (A := .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false)) hbulkF))
  have htopFΔ : SFormula.Deriv Δ' (.eqBool (SC.closed (topClassGuardTA (dP3 D) k1P3)) (SC.b false)) :=
    lift (cw3 (SFormula.Deriv.weakenFresh
      (A := .eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false)) htopF))
  have hrightFΔ : SFormula.Deriv Δ' (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k1P3)) (SC.b false)) :=
    lift (cw3 (SFormula.Deriv.weakenFresh
      (A := .eqBool (SC.closed (rightClassGuardTA (dP2 D) k1P)) (SC.b false)) hrightF))
  have hleftFΔ : SFormula.Deriv Δ' (.eqBool (SC.closed (leftClassGuardTA (dP3 D) k1P3)) (SC.b false)) :=
    lift (cw3 (SFormula.Deriv.weakenFresh
      (A := .eqBool (SC.closed (leftClassGuardTA (dP2 D) k1P)) (SC.b false)) hleftF))
  have hstripΔ : SFormula.Deriv Δ' (.eqBool (SC.closed (.ltNat (baseBTA (dP3 D) k1P3)
      (.mul (.natLit 4) (baseHalfTA (dP3 D))))) (SC.b true)) :=
    lift (cw3 (SFormula.Deriv.weakenFresh (A := bbStripF D) hstrip))
  have hadjΔ : SFormula.Deriv Δ' (.eqBool (SC.closed (.eqNat k2P3
      (.add (.mul (.sub (dm1TA (dP3 D)) (.natLit 1)) (dm1TA (dP3 D)))
        (.add (.mul (.natLit 2) (bbB3 D)) (.natLit 1))))) (SC.b true)) :=
    lift (cw3 (SFormula.Deriv.weakenFresh (A := bbAdjF D) hadj))
  have hBulkK2Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b true)) :=
    lift (cw3 (SFormula.Deriv.weakenFresh
      (A := .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true)) hBulkK2))
  have hPinΔ : SFormula.Deriv Δ' (bbPinF D).weaken :=
    lift (cw3 (SFormula.Deriv.weakenFresh (A := bbPinF D) hPin))
  have hq : SFormula.Deriv Δ' (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken) :=
    lift (.hyp (by right; right; exact List.mem_cons_self))
  -- Recover the band-fired facts at boundNat from the leaves.
  have hBotB := bbBottomBandFromX D hbulkFΔ htopFΔ hrightFΔ hleftFΔ hLeafA
  have hBulkB := bbBulkBandFromZ D hBulkK2Δ hLeafB
  -- The pin: boundNat ∈ {q0, q1}.
  have hdisj := bbPinAt D hPinΔ hq hbulkFΔ htopFΔ hrightFΔ hleftFΔ hstripΔ hadjΔ hBotB hBulkB
  -- The two exclusions in the handler context, lifted into Δ'.
  have hne0 : SFormula.Deriv Δ'
      (.not (.eqNat SFormula.boundNat (SC.closed (bbQ0 D)).weaken)) :=
    lift (.hyp (by right; exact List.mem_cons_self))
  have hne1 : SFormula.Deriv Δ'
      (.not (.eqNat SFormula.boundNat (SC.closed (bbQ1 D)).weaken)) :=
    lift (.hyp List.mem_cons_self)
  have hne0' : SFormula.Deriv Δ'
      (.not (.eqNat SFormula.boundNat (SC.closed (bbQ0_3 D)))) := hne0
  have hne1' : SFormula.Deriv Δ'
      (.not (.eqNat SFormula.boundNat (SC.closed (bbQ1_3 D)))) := hne1
  refine SFormula.Deriv.orElim hdisj ?_ ?_
  · exact SFormula.Deriv.botElim (SFormula.Deriv.notElim .assumption (cw1 hne0'))
  · exact SFormula.Deriv.botElim (SFormula.Deriv.notElim .assumption (cw1 hne1'))

end QHL.CodeLang.Surface.Verify
