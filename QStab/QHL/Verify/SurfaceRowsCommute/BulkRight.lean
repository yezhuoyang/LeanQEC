import QStab.QHL.Verify.SurfaceRowsCommute.BulkBottom

/-!
# Rows-commute (pairwise generated-row commutation) — BulkRight

The Bulk–Right overlap class.
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface

set_option maxRecDepth 65536
set_option linter.unusedVariables false

/-! ## Bulk–Right overlap class

The single-class closer for the **bulk–right** overlap, the ROLE-SWAPPED mirror of
`commBulkTop`: row A (`k1`) is the X-type BULK plaquette, row B (`k2`) is the Z-type
RIGHT-boundary stabilizer.  They overlap at exactly the two qubits
`q0 = d·(2r) + (d-1)`, `q1 = d·(2r+1) + (d-1)`, both in grid COLUMN `d-1`
(rows `2r`, `2r+1`), where `r = baseBTA(k2) - half = k2 - (d-1)² - (d-1)/2` is the
right-strip index of `k2`.

The Nat geometry is the proven `overlap_bulk_right` / `overlap_right_range` (in
`SurfaceRowOverlapNat.lean`).  IMPORTANT: that lemma's `k1` IS the bulk plaquette and
its `k2` IS the right boundary — which MATCHES OUR convention (our `k1` = bulk, our
`k2` = right).  So **NO role swap** when invoking them: pass OUR `k1` as ITS `k1` and
OUR `k2` as ITS `k2` (unlike bulk–top/bottom, which swapped).

DEVIATIONS FROM THE BULK–TOP TEMPLATE.
* The "primary index" is now `r = baseBTA(k2) - half`, the right index of `k2`; the
  adjacency pins `k1` (the bulk plaquette) at grid `(2r, d-2)`, i.e.
  `k1 = (2r)·(d-1) + (d-2)`.  (Bulk–top's primary index `b` came from `k1` and the
  adjacency pinned `k2`.)
* The class context lives on `k2` (right boundary): `¬bulk(k2) ∧ ¬top(k2) ∧
  right(k2)`.  Together `¬top(k2)` (`b ≥ half`) and `right(k2)` (`b < 2·half = d-1`,
  odd `d`) bracket `half ≤ b < d-1`, so `0 ≤ r < half` and `2r+1 < d` — NO extra
  strip-validity antecedent is needed (the right-class guard supplies the upper
  bound for free).
* The overlap qubits are in COLUMN `d-1`: `q/d = 2r` (resp. `2r+1`), `q%d = d-1`.
  The eval-certs reconstruct this via `d·m + (d-1) = (d-1) + m·d` then
  `Nat.add_mul_div_left` / `Nat.add_mul_mod_self_left`.
* The bulk-band pack proves `baseKindGuardTA(k1) = FALSE` (k1 is the X-row): with
  `cellR = 2r`, `cellC = d-2`, kind `= (2r + (d-2)) % 2 = (d-2) % 2 = 1 ≠ 0` for odd
  `d`.  (Bulk–top's bulk-band pack proved kind = TRUE for its Z-plaquette `k2`.) -/

/-- Right-strip index of `k2` (arity 2): `r = baseBTA(k2) - half`. -/
abbrev brR (D : OddSurfaceDistance) : Term 2 .nat :=
  .sub (baseBTA (dP2 D) k2P) (baseHalfTA (dP2 D))
/-- Overlap qubit `q0 = d·(2r) + (d-1)` (column `d-1`, row `2r`). -/
abbrev brQ0 (D : OddSurfaceDistance) : Term 2 .nat :=
  .add (.mul (dP2 D) (.mul (.natLit 2) (brR D))) (dm1TA (dP2 D))
/-- Overlap qubit `q1 = d·(2r+1) + (d-1)` (column `d-1`, row `2r+1`). -/
abbrev brQ1 (D : OddSurfaceDistance) : Term 2 .nat :=
  .add (.mul (dP2 D) (.add (.mul (.natLit 2) (brR D)) (.natLit 1))) (dm1TA (dP2 D))

abbrev brRangePackF (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false))
    (.imp (.eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false))
      (.imp (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b true))
        (.and (SFormula.witnessLt (SC.closed (brQ0 D)) (nP2 D))
          (.and (SFormula.witnessLt (SC.closed (brQ1 D)) (nP2 D))
            (.eqBool (SC.closed (.eqNat (brQ0 D) (brQ1 D))) (SC.b false))))))

/-- Bulk–Right range pack: under `¬bulk ∧ ¬top ∧ right` for `k2`, the overlap qubits
`q0 = d·(2r)+(d-1)`, `q1 = d·(2r+1)+(d-1)` are in range and distinct.  Discharged by
`arithBool` whose eval-certificate invokes the proven `overlap_right_range`. -/
def brRangePack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (brRangePackF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd3 : D.distance = 2 * D.index + 3 := rfl
  simp only [brRangePackF, brQ0, brQ1, brR, bulkGuardTA, topClassGuardTA,
    rightClassGuardTA, baseBTA, baseHalfTA, bulkCountTA, dm1TA, dP2, nP2,
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
      · -- the genuine right-class case.
        have hbf : decide (decide (k < (d - 1) * (d - 1)) = false) = true := by
          rw [decide_eq_true_eq]; simp [hbulk]
        have htf : decide (decide (k - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
          rw [decide_eq_true_eq]; simp [htop]
        have hrf : decide (decide (k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = true) = true := by
          rw [decide_eq_true_eq]; simp [hright]
        simp only [hbf, htf, hrf, if_true]
        set r := k - (d - 1) * (d - 1) - (d - 1) / 2 with hr
        have hhalf : 2 * ((d - 1) / 2) = d - 1 := by omega
        have hr1 : 2 * r + 1 < d := by omega
        obtain ⟨hne, hlt0, hlt1⟩ := overlap_right_range d r (by omega) hr1
        have e0 : decide (decide (d * (2 * r) + (d - 1) < d * d) = true) = true := by
          rw [decide_eq_true_eq, decide_eq_true_eq]; exact hlt0
        have e1 : decide (decide (d * (2 * r + 1) + (d - 1) < d * d) = true) = true := by
          rw [decide_eq_true_eq, decide_eq_true_eq]; exact hlt1
        have ene : decide (decide (d * (2 * r) + (d - 1) = d * (2 * r + 1) + (d - 1)) = false) = true := by
          rw [decide_eq_true_eq, decide_eq_false_iff_not]; exact hne
        simp only [e0, e1, ene, decide_true, if_true]
      · have hbf : decide (decide (k < (d - 1) * (d - 1)) = false) = true := by
          rw [decide_eq_true_eq]; simp [hbulk]
        have htf : decide (decide (k - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
          rw [decide_eq_true_eq]; simp [htop]
        have hrf : decide (decide (k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = true) = false := by
          rw [decide_eq_false_iff_not]; simp [hright]
        simp only [hbf, htf, hrf, Bool.false_eq_true, if_false, reduceIte]

abbrev brRightBandPackF (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false))
    (.imp (.eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false))
      (.imp (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b true))
        (.and (.eqBool (SC.closed (rightBandGuardTA (dP2 D) k2P (brQ0 D))) (SC.b true))
          (.eqBool (SC.closed (rightBandGuardTA (dP2 D) k2P (brQ1 D))) (SC.b true)))))

/-- Bulk–Right band pack: under `¬bulk ∧ ¬top ∧ right` for `k2`, the right-Z band of
`k2` fires at both overlap qubits `q0 = d·(2r)+(d-1)`, `q1 = d·(2r+1)+(d-1)` (both in
column `d-1`, rows `2r`, `2r+1`). -/
def brRightBandPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (brRightBandPackF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd3 : D.distance = 2 * D.index + 3 := rfl
  simp only [brRightBandPackF, brQ0, brQ1, brR, bulkGuardTA, topClassGuardTA,
    rightClassGuardTA, rightBandGuardTA, baseBTA, baseHalfTA, bulkCountTA, dm1TA, orEqSucc,
    dP2, SFormula.eval, SC.closed, SC.b, STerm.eval, Term.eval, Term.lift, bind, Option.bind]
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
        have hrf : decide (decide (k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = true) = true := by
          rw [decide_eq_true_eq]; simp [hright]
        simp only [hbf, htf, hrf, if_true]
        set r := k - (d - 1) * (d - 1) - (d - 1) / 2 with hr
        have hhalf : 2 * ((d - 1) / 2) = d - 1 := by omega
        have hr1 : 2 * r + 1 < d := by omega
        have hdm1lt : d - 1 < d := by omega
        -- column-(d-1) div/mod at q0, q1.
        have hq0d : (d * (2 * r) + (d - 1)) / d = 2 * r := by
          have e : d * (2 * r) + (d - 1) = (d - 1) + 2 * r * d := by
            rw [Nat.mul_comm d (2 * r)]; omega
          rw [e, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hdm1lt]; omega
        have hq0m : (d * (2 * r) + (d - 1)) % d = d - 1 := by
          have e : d * (2 * r) + (d - 1) = (d - 1) + 2 * r * d := by
            rw [Nat.mul_comm d (2 * r)]; omega
          rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hdm1lt]
        have hq1d : (d * (2 * r + 1) + (d - 1)) / d = 2 * r + 1 := by
          have e : d * (2 * r + 1) + (d - 1) = (d - 1) + (2 * r + 1) * d := by
            rw [Nat.mul_comm d (2 * r + 1)]; omega
          rw [e, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hdm1lt]; omega
        have hq1m : (d * (2 * r + 1) + (d - 1)) % d = d - 1 := by
          have e : d * (2 * r + 1) + (d - 1) = (d - 1) + (2 * r + 1) * d := by
            rw [Nat.mul_comm d (2 * r + 1)]; omega
          rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hdm1lt]
        rw [hq0d, hq0m, hq1d, hq1m]
        simp
      · have hbf : decide (decide (k < (d - 1) * (d - 1)) = false) = true := by
          rw [decide_eq_true_eq]; simp [hbulk]
        have htf : decide (decide (k - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
          rw [decide_eq_true_eq]; simp [htop]
        have hrf : decide (decide (k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = true) = false := by
          rw [decide_eq_false_iff_not]; simp [hright]
        simp only [hbf, htf, hrf, Bool.false_eq_true, if_false, reduceIte]

/-- Adjacency condition for the bulk–right class: the X-type bulk plaquette `k1` sits
at grid `(2r, d-2)`, i.e. `k1 = (2r)·(d-1) + (d-2)` (with `r = baseBTA(k2) - half` the
right index of `k2`).  `d-2` is expressed as `(dm1TA) - 1`. -/
abbrev brAdjF (D : OddSurfaceDistance) : SFormula 2 :=
  .eqBool (SC.closed (.eqNat k1P
    (.add (.mul (.mul (.natLit 2) (brR D)) (dm1TA (dP2 D)))
      (.sub (dm1TA (dP2 D)) (.natLit 1))))) (SC.b true)

abbrev brBulkBandPackF (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false))
    (.imp (.eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false))
      (.imp (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b true))
        (.imp (brAdjF D)
          (.and (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true))
            (.and (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k1P)) (SC.b false))
              (.and (.eqBool (SC.closed (baseBulkBandGuardTA (dP2 D) k1P (brQ0 D))) (SC.b true))
                (.eqBool (SC.closed (baseBulkBandGuardTA (dP2 D) k1P (brQ1 D))) (SC.b true))))))))

/-- Bulk–Right bulk-band pack: under the right context for `k2` and the adjacency
`k1 = (2r)·(d-1)+(d-2)`, the X-type bulk plaquette `k1` (grid `(2r,d-2)`) is in-bulk,
X-kind (`baseKindGuardTA = FALSE`, since `kind = (2r + (d-2)) % 2 = (d-2) % 2 = 1` for
odd `d`), and its plaquette band contains both overlap qubits `q0`, `q1` (the
plaquette's right-column pair). -/
def brBulkBandPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (brBulkBandPackF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd3 : D.distance = 2 * D.index + 3 := rfl
  simp only [brBulkBandPackF, brAdjF, brQ0, brQ1, brR, bulkGuardTA, topClassGuardTA,
    rightClassGuardTA, baseKindGuardTA, baseBulkBandGuardTA, baseBTA, baseHalfTA, bulkCountTA,
    dm1TA, band3, orEqSucc, dP2, SFormula.eval, SC.closed, SC.b, STerm.eval, Term.eval, Term.lift,
    bind, Option.bind]
  set k1 := rho ⟨1, by decide⟩ with hk1
  set k2 := rho ⟨0, by decide⟩ with hk2
  set d := D.distance with hdd
  have hdge : 3 ≤ d := by omega
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
        have hrf : decide (decide (k2 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = true) = true := by
          rw [decide_eq_true_eq]; simp [hright]
        set r := k2 - (d - 1) * (d - 1) - (d - 1) / 2 with hr
        have hhalf : 2 * ((d - 1) / 2) = d - 1 := by omega
        have hr1 : 2 * r + 1 < d := by omega
        have h2rd1 : 2 * r < d - 1 := by omega
        have hd2 : d - 1 - 1 = d - 2 := by omega
        by_cases hadj : k1 = 2 * r * (d - 1) + (d - 1 - 1)
        · have haf : decide (decide (k1 = 2 * r * (d - 1) + (d - 1 - 1)) = true) = true := by
            rw [decide_eq_true_eq]; simp [hadj]
          simp only [hbf, htf, hrf, haf, if_true]
          -- cellR/cellC of k1: k1/(d-1) = 2r, k1%(d-1) = d-2.
          have hcol1 : d - 2 < d - 1 := by omega
          have hk1d : k1 / (d - 1) = 2 * r := by
            rw [hadj, hd2]
            have e : 2 * r * (d - 1) + (d - 2) = (d - 2) + 2 * r * (d - 1) := by omega
            rw [e, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hcol1]; omega
          have hk1m : k1 % (d - 1) = d - 2 := by
            rw [hadj, hd2]
            have e : 2 * r * (d - 1) + (d - 2) = (d - 2) + 2 * r * (d - 1) := by omega
            rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hcol1]
          -- k1 < bulkCount.
          have hbulkk1 : k1 < (d - 1) * (d - 1) := by
            have hsm : (2 * r + 1) * (d - 1) = 2 * r * (d - 1) + (d - 1) := by
              rw [Nat.succ_mul]
            have hle : (2 * r + 1) * (d - 1) ≤ (d - 1) * (d - 1) :=
              Nat.mul_le_mul_right _ (by omega)
            rw [hadj, hd2]; omega
          have hbk1d : decide (k1 < (d - 1) * (d - 1)) = true := by
            rw [decide_eq_true_eq]; exact hbulkk1
          -- column-(d-1) div/mod at q0, q1.
          have hdm1lt : d - 1 < d := by omega
          have hq0d : (d * (2 * r) + (d - 1)) / d = 2 * r := by
            have e : d * (2 * r) + (d - 1) = (d - 1) + 2 * r * d := by
              rw [Nat.mul_comm d (2 * r)]; omega
            rw [e, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hdm1lt]; omega
          have hq0m : (d * (2 * r) + (d - 1)) % d = d - 1 := by
            have e : d * (2 * r) + (d - 1) = (d - 1) + 2 * r * d := by
              rw [Nat.mul_comm d (2 * r)]; omega
            rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hdm1lt]
          have hq1d : (d * (2 * r + 1) + (d - 1)) / d = 2 * r + 1 := by
            have e : d * (2 * r + 1) + (d - 1) = (d - 1) + (2 * r + 1) * d := by
              rw [Nat.mul_comm d (2 * r + 1)]; omega
            rw [e, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hdm1lt]; omega
          have hq1m : (d * (2 * r + 1) + (d - 1)) % d = d - 1 := by
            have e : d * (2 * r + 1) + (d - 1) = (d - 1) + (2 * r + 1) * d := by
              rw [Nat.mul_comm d (2 * r + 1)]; omega
            rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hdm1lt]
          rw [hk1d, hk1m, hq0d, hq0m, hq1d, hq1m, hbk1d]
          -- kind = FALSE (X-kind): (2r + (d-2)) % 2 = 1 ≠ 0 for odd d.
          have hkind : decide (decide ((2 * r + (d - 2)) % 2 = 0) = false) = true := by
            rw [decide_eq_true_eq, decide_eq_false_iff_not]; omega
          rw [hkind]
          -- bulk-band COL check at q0/q1: q%d = d-1, k1%(d-1) = d-2; `d-1 = (d-2)+1` (succ branch).
          have hcolne : ¬ (d - 1 = d - 2) := by omega
          have hcolsucc : d - 1 = d - 2 + 1 := by omega
          simp [hcolne, hcolsucc]
        · have haf : decide (decide (k1 = 2 * r * (d - 1) + (d - 1 - 1)) = true) = false := by
            rw [decide_eq_false_iff_not]; simp [hadj]
          simp only [hbf, htf, hrf, haf, Bool.false_eq_true, if_false, reduceIte]
      · have hbf : decide (decide (k2 < (d - 1) * (d - 1)) = false) = true := by
          rw [decide_eq_true_eq]; simp [hbulk]
        have htf : decide (decide (k2 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
          rw [decide_eq_true_eq]; simp [htop]
        have hrf : decide (decide (k2 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = true) = false := by
          rw [decide_eq_false_iff_not]; simp [hright]
        simp only [hbf, htf, hrf, Bool.false_eq_true, if_false, reduceIte]

/-! ### Bulk–Right class: the all-others joint pin

Under the bulk–right class context (the right-class guards for `k2` and the adjacency
`k1 = (2r)·(d-1)+(d-2)`), the verified overlap geometry `overlap_bulk_right` (with
`k1`/`k2` roles UNCHANGED — there `k1` is the bulk plaquette, `k2` the right
boundary, MATCHING our convention) forces every shared non-`I` slot into `{q0, q1}`.
The slot `q` is non-`I` for the X-type bulk plaquette `k1` exactly when its bulk band
fires at `q`, and non-`I` for the Z-type right row `k2` exactly when its right band
fires at `q`; under those two band-fired facts the disjunction `q = q0 ∨ q = q1`
holds (since then `q = d·(q/d) + (d-1)` with `q/d ∈ {2r, 2r+1}`).  `arithBool` whose
eval-certificate invokes `overlap_bulk_right`. -/

/-- Arity-3 right-strip index of `k2` (`= (brR D).weaken`). -/
abbrev brR3 (D : OddSurfaceDistance) : Term 3 .nat :=
  .sub (baseBTA (dP3 D) k2P3) (baseHalfTA (dP3 D))
/-- Arity-3 overlap qubit `q0` (`= (brQ0 D).weaken`). -/
abbrev brQ0_3 (D : OddSurfaceDistance) : Term 3 .nat :=
  .add (.mul (dP3 D) (.mul (.natLit 2) (brR3 D))) (dm1TA (dP3 D))
/-- Arity-3 overlap qubit `q1` (`= (brQ1 D).weaken`). -/
abbrev brQ1_3 (D : OddSurfaceDistance) : Term 3 .nat :=
  .add (.mul (dP3 D) (.add (.mul (.natLit 2) (brR3 D)) (.natLit 1))) (dm1TA (dP3 D))

theorem brQ0_weaken (D : OddSurfaceDistance) : (brQ0 D).weaken = brQ0_3 D := rfl
theorem brQ1_weaken (D : OddSurfaceDistance) : (brQ1 D).weaken = brQ1_3 D := rfl

/-- The bulk–right joint pin body (arity 3, `k1 = var 2`, `k2 = var 1`, `q = var 0`):
under the class context and the two band-fired facts, `q ∈ {q0, q1}`. -/
abbrev brPinBody (D : OddSurfaceDistance) : SFormula 3 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b false))
    (.imp (.eqBool (SC.closed (topClassGuardTA (dP3 D) k2P3)) (SC.b false))
      (.imp (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k2P3)) (SC.b true))
        (.imp (.eqBool (SC.closed (.eqNat k1P3
            (.add (.mul (.mul (.natLit 2) (brR3 D)) (dm1TA (dP3 D)))
              (.sub (dm1TA (dP3 D)) (.natLit 1))))) (SC.b true))
          (.imp (.eqBool (SC.closed (rightBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))
            (.imp (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true))
              (.or (.eqNat SFormula.boundNat (SC.closed (brQ0_3 D)))
                (.eqNat SFormula.boundNat (SC.closed (brQ1_3 D)))))))))

abbrev brPinF (D : OddSurfaceDistance) : SFormula 2 :=
  .allNatLt (nP2 D) (brPinBody D)

/-- Bulk–Right joint pin pack: under the bulk–right class context, every shared
non-`I` slot is one of the two overlap qubits.  `arithBool`, eval-cert via
`overlap_bulk_right` (NO role swap). -/
def brPinPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (brPinF D) := by
  refine PureFamilyDerivA.allNatLtIntro _ ?_
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd3 : D.distance = 2 * D.index + 3 := rfl
  simp only [brPinBody, brQ0_3, brQ1_3, brR3, bulkGuardTA, topClassGuardTA, rightClassGuardTA,
    baseBulkBandGuardTA, rightBandGuardTA, baseBTA, baseHalfTA, bulkCountTA, dm1TA, band3,
    orEqSucc, dP3, dP2, k1P3, k2P3, qP3, SFormula.eval, SFormula.boundNat, SC.closed, SC.b,
    STerm.eval, Term.eval, Term.lift, bind, Option.bind]
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
        have hrf : decide (decide (k2 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = true) = true := by
          rw [decide_eq_true_eq]; simp [hright]
        set r := k2 - (d - 1) * (d - 1) - (d - 1) / 2 with hr
        have hhalf : 2 * ((d - 1) / 2) = d - 1 := by omega
        have hr1 : 2 * r + 1 < d := by omega
        have hd2 : d - 1 - 1 = d - 2 := by omega
        by_cases hadj : k1 = 2 * r * (d - 1) + (d - 1 - 1)
        · have haf : decide (decide (k1 = 2 * r * (d - 1) + (d - 1 - 1)) = true) = true := by
            rw [decide_eq_true_eq]; simp [hadj]
          simp only [hbf, htf, hrf, haf, if_true]
          -- k1 cellR/cellC (so the bulk-band guard for k1 fully reduces).
          have hcol1 : d - 2 < d - 1 := by omega
          have hk1d : k1 / (d - 1) = 2 * r := by
            rw [hadj, hd2]
            have e : 2 * r * (d - 1) + (d - 2) = (d - 2) + 2 * r * (d - 1) := by omega
            rw [e, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hcol1]; omega
          have hk1m : k1 % (d - 1) = d - 2 := by
            rw [hadj, hd2]
            have e : 2 * r * (d - 1) + (d - 2) = (d - 2) + 2 * r * (d - 1) := by omega
            rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hcol1]
          -- right-band fired on k2: q%d = d-1 and q/d ∈ {2r, 2r+1}.
          by_cases hqcol : q % d = d - 1
          · by_cases hqrow : q / d = 2 * r ∨ q / d = 2 * r + 1
            · -- right-band fires; q = d·(q/d) + (d-1) ∈ {q0, q1}.
              have hqval : q = d * (q / d) + (d - 1) := by
                have hdm := Nat.div_add_mod q d
                rw [hqcol] at hdm; omega
              -- bulk-band COL check for k1: `d-1 = (d-2)+1` (succ branch).
              have hcolne : ¬ (d - 1 = d - 2) := by omega
              have hcolsucc : d - 1 = d - 2 + 1 := by omega
              rcases hqrow with hc | hc
              · -- q/d = 2r → q = q0.
                have hqe : q = d * (2 * r) + (d - 1) := by rw [hqval, hc]
                rw [hqcol, hc, hk1d, hk1m]; simp [hqe, hcolne, hcolsucc]
              · -- q/d = 2r+1 → q = q1.
                have hqe : q = d * (2 * r + 1) + (d - 1) := by rw [hqval, hc]
                have hms : d * (2 * r) + d = d * (2 * r + 1) := (Nat.mul_succ d (2 * r)).symm
                have e0v : ¬ (q = d * (2 * r) + (d - 1)) := by rw [hqe]; omega
                rw [hqcol, hc, hk1d, hk1m]; simp [hqe, e0v, hcolne, hcolsucc]
            · -- q/d ∉ {2r, 2r+1}: right-band row antecedent false → vacuous.
              push_neg at hqrow
              obtain ⟨hcr0, hcr1⟩ := hqrow
              rw [hqcol]; simp [hcr0, hcr1]
          · -- q%d ≠ d-1: right-band col antecedent false → vacuous.
            simp [hqcol]
        · have haf : decide (decide (k1 = 2 * r * (d - 1) + (d - 1 - 1)) = true) = false := by
            rw [decide_eq_false_iff_not]; simp [hadj]
          simp only [hbf, htf, hrf, haf, Bool.false_eq_true, if_false, reduceIte]
      · have hbf : decide (decide (k2 < (d - 1) * (d - 1)) = false) = true := by
          rw [decide_eq_true_eq]; simp [hbulk]
        have htf : decide (decide (k2 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
          rw [decide_eq_true_eq]; simp [htop]
        have hrf : decide (decide (k2 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = true) = false := by
          rw [decide_eq_false_iff_not]; simp [hright]
        simp only [hbf, htf, hrf, Bool.false_eq_true, if_false, reduceIte]

/-- Extract the bulk–right joint-pin disjunction at `boundNat`. -/
def brPinAt {Δ : List (SFormula 3)} (D : OddSurfaceDistance)
    (hW : SFormula.Deriv Δ (brPinF D).weaken)
    (hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken))
    (hBulkF : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b false)))
    (hTopF : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA (dP3 D) k2P3)) (SC.b false)))
    (hRightC : SFormula.Deriv Δ (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k2P3)) (SC.b true)))
    (hAdj : SFormula.Deriv Δ (.eqBool (SC.closed (.eqNat k1P3
      (.add (.mul (.mul (.natLit 2) (brR3 D)) (dm1TA (dP3 D)))
        (.sub (dm1TA (dP3 D)) (.natLit 1))))) (SC.b true)))
    (hBulkB : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true)))
    (hRightB : SFormula.Deriv Δ
      (.eqBool (SC.closed (rightBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))) :
    SFormula.Deriv Δ
      (.or (.eqNat SFormula.boundNat (SC.closed (brQ0_3 D)))
        (.eqNat SFormula.boundNat (SC.closed (brQ1_3 D)))) := by
  have hElim := SFormula.Deriv.allNatLtElim (nP2 D).weaken
    ((brPinBody D).lift 1) SFormula.boundNat hW hq
  have hBody := SFormula.Deriv.applyNatBoundNatBeta (brPinBody D) hElim
  exact SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp
    (SFormula.Deriv.mp (SFormula.Deriv.mp hBody hBulkF) hTopF) hRightC) hAdj) hRightB) hBulkB

/-! ### Bulk–Right class: reverse-leaf band recovery + the joint pin handler -/

/-- Recover `bulkBand(k1, q) = true` from `baseLeafTreeTA k1 q = X`, given `bulk(k1)`.
Reverse-leaf: the false band branch gives an `I` leaf, contradicting `X`. -/
def brBulkBandFromX {Δ : List (SFormula 3)} (D : OddSurfaceDistance)
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

/-- Recover `rightBand(k2, q) = true` from `baseLeafTreeTA k2 q = Z`, given the right
class context (`¬bulk ∧ ¬top ∧ right`).  Reverse-leaf: the false band branch gives an
`I` leaf (`baseLeafRightIS`), contradicting `Z`. -/
def brRightBandFromZ {Δ : List (SFormula 3)} (D : OddSurfaceDistance)
    (hBulkF : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b false)))
    (hTopF : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA (dP3 D) k2P3)) (SC.b false)))
    (hRightC : SFormula.Deriv Δ (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k2P3)) (SC.b true)))
    (hLeafZ : SFormula.Deriv Δ
      (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p Pauli.Z))) :
    SFormula.Deriv Δ (.eqBool (SC.closed (rightBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true)) := by
  refine SFormula.Deriv.boolCases (SC.closed (rightBandGuardTA (dP3 D) k2P3 qP3)) _ .assumption ?_
  refine SFormula.Deriv.botElim ?_
  have hBandF : SFormula.Deriv (.eqBool (SC.closed (rightBandGuardTA (dP3 D) k2P3 qP3)) (SC.b false) :: Δ)
      (.eqBool (SC.closed (rightBandGuardTA (dP3 D) k2P3 qP3)) (SC.b false)) := .assumption
  have hI : SFormula.Deriv (.eqBool (SC.closed (rightBandGuardTA (dP3 D) k2P3 qP3)) (SC.b false) :: Δ)
      (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p Pauli.I)) :=
    baseLeafRightIS (dP3 D) k2P3 qP3 (cw1 hBulkF) (cw1 hTopF) (cw1 hRightC) hBandF
  have hZI : SFormula.Deriv (.eqBool (SC.closed (rightBandGuardTA (dP3 D) k2P3 qP3)) (SC.b false) :: Δ)
      (.eqPauli (SC.p Pauli.Z) (SC.p Pauli.I)) :=
    SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.eqPauliSymm _ _ (cw1 hLeafZ)) hI
  exact SFormula.Deriv.notElim hZI (SFormula.Deriv.pauliNeqLit Pauli.Z Pauli.I (by decide))

/-- **Bulk–Right overlap class closer.**  Assembles the per-pair commutation goal for
the bulk–right overlap, the role-swapped mirror of `commBulkTop`: row A (`k1`) is the
X-type bulk plaquette, row B (`k2`) is the Z-type right-boundary stabilizer.  Consumes
the three arithmetic packs (`brRangePack`/`brRightBandPack`/`brBulkBandPack`), the
joint pin (`brPinPack`), and the four flat-entry facts at `q0`, `q1`; under the class
context (the right-class guards for `k2`, the adjacency pinning `k1`, and `k1`'s
in-bulk fact) it resolves row A to `X` via `baseLeafXS` (X-bulk leaf) and row B to `Z`
via `baseLeafRightZS` (right-Z leaf), then discharges the all-others premise via the
generic two-anti spine `commBulkTopXZ`. -/
def commRightBulk {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hEntryA : SFormula.Deriv Γ (entryAQuant D)) (hEntryB : SFormula.Deriv Γ (entryBQuant D))
    (hk1X : SFormula.Deriv Γ (k1IsX D true)) (hExcl1 : SFormula.Deriv Γ (typeExclF D k1P))
    (hbulkFk2 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)))
    (htopFk2 : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false)))
    (hrightCk2 : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b true)))
    (hadj : SFormula.Deriv Γ (brAdjF D))
    (hRange : SFormula.Deriv Γ (brRangePackF D))
    (hRightBand : SFormula.Deriv Γ (brRightBandPackF D))
    (hBulkBand : SFormula.Deriv Γ (brBulkBandPackF D))
    (hPin : SFormula.Deriv Γ (brPinF D))
    (hEA0 : SFormula.Deriv Γ (entryAAtQF D (brQ0 D)))
    (hEA1 : SFormula.Deriv Γ (entryAAtQF D (brQ1 D)))
    (hEB0 : SFormula.Deriv Γ (entryBAtQF D (brQ0 D)))
    (hEB1 : SFormula.Deriv Γ (entryBAtQF D (brQ1 D))) :
    SFormula.Deriv Γ (pairGoal D) := by
  -- Range facts at q0/q1.
  have hRangeP := SFormula.Deriv.mp (SFormula.Deriv.mp
    (SFormula.Deriv.mp hRange hbulkFk2) htopFk2) hrightCk2
  have hLt0 := SFormula.Deriv.andElimLeft hRangeP
  have hLt1 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hRangeP)
  have hNe := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hRangeP)
  -- Right-band-fires facts at q0/q1.
  have hRBP := SFormula.Deriv.mp (SFormula.Deriv.mp
    (SFormula.Deriv.mp hRightBand hbulkFk2) htopFk2) hrightCk2
  have hRB0 := SFormula.Deriv.andElimLeft hRBP
  have hRB1 := SFormula.Deriv.andElimRight hRBP
  -- Bulk-band facts for the X plaquette k1 at q0/q1.
  have hKBP := SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp
    (SFormula.Deriv.mp hBulkBand hbulkFk2) htopFk2) hrightCk2) hadj
  have hBulkK1 := SFormula.Deriv.andElimLeft hKBP
  have hKindK1 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hKBP)
  have hBB0 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hKBP))
  have hBB1 := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hKBP))
  -- Row A = X at q0/q1 (bulk-X leaf), Row B = Z at q0/q1 (right-Z leaf).
  have hAX0 : SFormula.Deriv Γ (.eqPauli (.stabAt (rowA D) (SC.closed (brQ0 D))) (SC.p Pauli.X)) :=
    SFormula.Deriv.eqPauliTrans _ _ _ hEA0 (baseLeafXS (dP2 D) k1P (brQ0 D) hBulkK1 hBB0 hKindK1)
  have hAX1 : SFormula.Deriv Γ (.eqPauli (.stabAt (rowA D) (SC.closed (brQ1 D))) (SC.p Pauli.X)) :=
    SFormula.Deriv.eqPauliTrans _ _ _ hEA1 (baseLeafXS (dP2 D) k1P (brQ1 D) hBulkK1 hBB1 hKindK1)
  have hBZ0 : SFormula.Deriv Γ (.eqPauli (.stabAt (rowB D) (SC.closed (brQ0 D))) (SC.p Pauli.Z)) :=
    SFormula.Deriv.eqPauliTrans _ _ _ hEB0
      (baseLeafRightZS (dP2 D) k2P (brQ0 D) hbulkFk2 htopFk2 hrightCk2 hRB0)
  have hBZ1 : SFormula.Deriv Γ (.eqPauli (.stabAt (rowB D) (SC.closed (brQ1 D))) (SC.p Pauli.Z)) :=
    SFormula.Deriv.eqPauliTrans _ _ _ hEB1
      (baseLeafRightZS (dP2 D) k2P (brQ1 D) hbulkFk2 htopFk2 hrightCk2 hRB1)
  -- Assemble via the (generic) two-anti spine; the all-others pin handler closes overlap.
  refine commBulkTopXZ D (brQ0 D) (brQ1 D) hEntryA hEntryB hk1X hExcl1
    hLt0 hLt1 hNe hAX0 hAX1 hBZ0 hBZ1 ?_
  intro Δ' lift hLeafA hLeafB
  -- The class context + adj + k1-bulk fact, lifted into Δ'.
  have hbulkFk2Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b false)) :=
    lift (cw3 (SFormula.Deriv.weakenFresh
      (A := .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)) hbulkFk2))
  have htopFk2Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (topClassGuardTA (dP3 D) k2P3)) (SC.b false)) :=
    lift (cw3 (SFormula.Deriv.weakenFresh
      (A := .eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false)) htopFk2))
  have hrightCk2Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k2P3)) (SC.b true)) :=
    lift (cw3 (SFormula.Deriv.weakenFresh
      (A := .eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b true)) hrightCk2))
  have hadjΔ : SFormula.Deriv Δ' (.eqBool (SC.closed (.eqNat k1P3
      (.add (.mul (.mul (.natLit 2) (brR3 D)) (dm1TA (dP3 D)))
        (.sub (dm1TA (dP3 D)) (.natLit 1))))) (SC.b true)) :=
    lift (cw3 (SFormula.Deriv.weakenFresh (A := brAdjF D) hadj))
  have hBulkK1Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b true)) :=
    lift (cw3 (SFormula.Deriv.weakenFresh
      (A := .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true)) hBulkK1))
  have hPinΔ : SFormula.Deriv Δ' (brPinF D).weaken :=
    lift (cw3 (SFormula.Deriv.weakenFresh (A := brPinF D) hPin))
  have hq : SFormula.Deriv Δ' (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken) :=
    lift (.hyp (by right; right; exact List.mem_cons_self))
  -- Recover the band-fired facts at boundNat from the leaves.
  have hBulkB := brBulkBandFromX D hBulkK1Δ hLeafA
  have hRightB := brRightBandFromZ D hbulkFk2Δ htopFk2Δ hrightCk2Δ hLeafB
  -- The pin: boundNat ∈ {q0, q1}.
  have hdisj := brPinAt D hPinΔ hq hbulkFk2Δ htopFk2Δ hrightCk2Δ hadjΔ hBulkB hRightB
  -- The two exclusions in the handler context, lifted into Δ'.
  have hne0 : SFormula.Deriv Δ'
      (.not (.eqNat SFormula.boundNat (SC.closed (brQ0 D)).weaken)) :=
    lift (.hyp (by right; exact List.mem_cons_self))
  have hne1 : SFormula.Deriv Δ'
      (.not (.eqNat SFormula.boundNat (SC.closed (brQ1 D)).weaken)) :=
    lift (.hyp List.mem_cons_self)
  have hne0' : SFormula.Deriv Δ'
      (.not (.eqNat SFormula.boundNat (SC.closed (brQ0_3 D)))) := hne0
  have hne1' : SFormula.Deriv Δ'
      (.not (.eqNat SFormula.boundNat (SC.closed (brQ1_3 D)))) := hne1
  refine SFormula.Deriv.orElim hdisj ?_ ?_
  · exact SFormula.Deriv.botElim (SFormula.Deriv.notElim .assumption (cw1 hne0'))
  · exact SFormula.Deriv.botElim (SFormula.Deriv.notElim .assumption (cw1 hne1'))

end QHL.CodeLang.Surface.Verify
