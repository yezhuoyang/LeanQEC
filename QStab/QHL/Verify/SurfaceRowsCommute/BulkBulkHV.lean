import QStab.QHL.Verify.SurfaceRowsCommute.BulkLeft

/-!
# Rows-commute (pairwise generated-row commutation) — BulkBulkHV

The Bulk–Bulk overlap classes: horizontal and vertical edge-adjacency.
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface

set_option maxRecDepth 65536
set_option linter.unusedVariables false

/-! ## Bulk–Bulk overlap class (horizontal edge-adjacency)

The single-class closer for the **bulk–bulk horizontal** overlap: BOTH rows are bulk
plaquettes.  Row A (`k1`) is the X-type bulk plaquette at grid `(r1, c1)`
(`r1 = k1/(d-1)`, `c1 = k1%(d-1)`); row B (`k2 = k1+1`) is the Z-type bulk plaquette
ONE COLUMN to its right, at grid `(r1, c1+1)` (same grid row).  They overlap at exactly
the two qubits of their shared vertical edge (column `c1+1`, rows `r1`, `r1+1`):
`q0 = d·r1 + (c1+1)`, `q1 = d·(r1+1) + (c1+1)`.

The Nat geometry is the proven `overlap_bulk_bulk_horiz` / `overlap_bulk_bulk_horiz_range`
(in `SurfaceRowOverlapNat.lean`).  IMPORTANT: that lemma's `k1` IS our X-bulk plaquette
and its `k2` IS our Z-bulk plaquette — which MATCHES OUR convention.  So **NO role swap**:
pass OUR `k1` as ITS `k1` and OUR `k2` as ITS `k2`.

DEVIATIONS FROM THE BULK–RIGHT TEMPLATE.
* BOTH rows are bulk, so there is no boundary "index": the positions are the div/mod of
  `k1`'s own coordinates (`r1 = k1/(d-1)`, `c1 = k1%(d-1)`) and of `k2 = k1+1`.  The
  class-context cascade is a single `by_cases hBulkK1` (no top/right/left class guards),
  but the div/mod of `k1` (and of `k1+1`) must be threaded explicitly.
* The kind facts are taken as EXPLICIT hypotheses to the closer (`hKindK1 = FALSE`,
  `hKindK2 = TRUE`) — the band packs only assert the band-fired facts, not kind.
* There are TWO bulk-band packs (one per bulk row), and BOTH reverse-leaves go through
  `baseLeafBulkIS`.
* The same-row validity antecedent `hrow` (`c1+1 < d-1`, so `k1+1` stays in the SAME bulk
  row, not wrapping) is supplied by the dispatcher; it is a true geometric fact (the
  dispatcher routes here only when `k1` has a right-neighbour in the same bulk row). -/

/-- Cell row of `k1` (arity 2): `r1 = k1/(d-1)`. -/
abbrev bhR1 (D : OddSurfaceDistance) : Term 2 .nat := .div k1P (dm1TA (dP2 D))
/-- Cell col of `k1` (arity 2): `c1 = k1%(d-1)`. -/
abbrev bhC1 (D : OddSurfaceDistance) : Term 2 .nat := .mod k1P (dm1TA (dP2 D))
/-- Overlap qubit `q0 = d·r1 + (c1+1)` (column `c1+1`, row `r1`). -/
abbrev bhQ0 (D : OddSurfaceDistance) : Term 2 .nat :=
  .add (.mul (dP2 D) (bhR1 D)) (.add (bhC1 D) (.natLit 1))
/-- Overlap qubit `q1 = d·(r1+1) + (c1+1)` (column `c1+1`, row `r1+1`). -/
abbrev bhQ1 (D : OddSurfaceDistance) : Term 2 .nat :=
  .add (.mul (dP2 D) (.add (bhR1 D) (.natLit 1))) (.add (bhC1 D) (.natLit 1))

/-- Same-row validity guard: `c1 + 1 < d - 1` (so `k2 = k1+1` stays in the same bulk
row).  True geometric fact, supplied by the dispatcher. -/
abbrev bhRowF (D : OddSurfaceDistance) : SFormula 2 :=
  .eqBool (SC.closed (.ltNat (.add (.mod k1P (dm1TA (dP2 D))) (.natLit 1)) (dm1TA (dP2 D))))
    (SC.b true)

abbrev bhRangePackF (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true))
    (.imp (bhRowF D)
      (.and (SFormula.witnessLt (SC.closed (bhQ0 D)) (nP2 D))
        (.and (SFormula.witnessLt (SC.closed (bhQ1 D)) (nP2 D))
          (.eqBool (SC.closed (.eqNat (bhQ0 D) (bhQ1 D))) (SC.b false)))))

/-- Bulk–Bulk-horiz range pack: under `bulk(k1)` and the same-row validity bound, the
overlap qubits `q0 = d·r1+(c1+1)`, `q1 = d·(r1+1)+(c1+1)` are in range and distinct.
Discharged by `arithBool` whose eval-certificate invokes `overlap_bulk_bulk_horiz_range`. -/
def bhRangePack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (bhRangePackF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd3 : D.distance = 2 * D.index + 3 := rfl
  simp only [bhRangePackF, bhRowF, bhQ0, bhQ1, bhR1, bhC1, bulkGuardTA, bulkCountTA, dm1TA,
    dP2, nP2, SFormula.eval, SFormula.witnessLt, SC.closed, SC.b, SC.n, STerm.eval, Term.eval,
    Term.lift, bind, Option.bind, nQubits]
  set k := rho ⟨1, by decide⟩ with hk
  set d := D.distance with hdd
  have hdge : 3 ≤ d := by omega
  by_cases hbulk : k < (d - 1) * (d - 1)
  · have hbt : decide (decide (k < (d - 1) * (d - 1)) = true) = true := by
      rw [decide_eq_true_eq]; simp [hbulk]
    set r1 := k / (d - 1) with hr1
    set c1 := k % (d - 1) with hc1
    have hr1lt : r1 < d - 1 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hbulk)
    by_cases hrow : c1 + 1 < d - 1
    · have hrt : decide (decide (c1 + 1 < d - 1) = true) = true := by
        rw [decide_eq_true_eq]; simp [hrow]
      simp only [hbt, hrt, if_true]
      have hr1d : r1 + 1 < d := by omega
      have hc1d : c1 + 1 < d := by omega
      obtain ⟨hne, hlt0, hlt1⟩ := overlap_bulk_bulk_horiz_range d r1 c1 (by omega) hr1d hc1d
      have e0 : decide (decide (d * r1 + (c1 + 1) < d * d) = true) = true := by
        rw [decide_eq_true_eq, decide_eq_true_eq]; exact hlt0
      have e1 : decide (decide (d * (r1 + 1) + (c1 + 1) < d * d) = true) = true := by
        rw [decide_eq_true_eq, decide_eq_true_eq]; exact hlt1
      have ene : decide (decide (d * r1 + (c1 + 1) = d * (r1 + 1) + (c1 + 1)) = false) = true := by
        rw [decide_eq_true_eq, decide_eq_false_iff_not]; exact hne
      simp only [e0, e1, ene, decide_true, if_true]
    · have hrf : decide (decide (c1 + 1 < d - 1) = true) = false := by
        rw [decide_eq_false_iff_not]; simp [hrow]
      simp only [hbt, hrf, Bool.false_eq_true, if_false, reduceIte]
  · have hbf : decide (decide (k < (d - 1) * (d - 1)) = true) = false := by
      rw [decide_eq_false_iff_not]; simp [hbulk]
    simp only [hbf, Bool.false_eq_true, if_false, reduceIte]

abbrev bhBandK1PackF (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true))
    (.imp (bhRowF D)
      (.and (.eqBool (SC.closed (baseBulkBandGuardTA (dP2 D) k1P (bhQ0 D))) (SC.b true))
        (.eqBool (SC.closed (baseBulkBandGuardTA (dP2 D) k1P (bhQ1 D))) (SC.b true))))

/-- Bulk–Bulk-horiz band pack for `k1`: under `bulk(k1)` and the same-row bound, the
X-bulk plaquette band of `k1` (grid `(r1,c1)`) fires at both overlap qubits
`q0 = d·r1+(c1+1)`, `q1 = d·(r1+1)+(c1+1)` (its right-column pair, rows `r1`, `r1+1`). -/
def bhBandK1Pack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (bhBandK1PackF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd3 : D.distance = 2 * D.index + 3 := rfl
  simp only [bhBandK1PackF, bhRowF, bhQ0, bhQ1, bhR1, bhC1, bulkGuardTA, baseBulkBandGuardTA,
    bulkCountTA, dm1TA, band3, orEqSucc, dP2, SFormula.eval, SC.closed, SC.b, STerm.eval,
    Term.eval, Term.lift, bind, Option.bind]
  set k := rho ⟨1, by decide⟩ with hk
  set d := D.distance with hdd
  have hdge : 3 ≤ d := by omega
  by_cases hbulk : k < (d - 1) * (d - 1)
  · have hbt : decide (decide (k < (d - 1) * (d - 1)) = true) = true := by
      rw [decide_eq_true_eq]; simp [hbulk]
    set r1 := k / (d - 1) with hr1
    set c1 := k % (d - 1) with hc1
    have hr1lt : r1 < d - 1 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hbulk)
    by_cases hrow : c1 + 1 < d - 1
    · have hrt : decide (decide (c1 + 1 < d - 1) = true) = true := by
        rw [decide_eq_true_eq]; simp [hrow]
      simp only [hbt, hrt, if_true]
      have hc1d : c1 + 1 < d := by omega
      have hr1d : r1 + 1 < d := by omega
      -- div/mod of q0, q1 (column c1+1; rows r1, r1+1).
      have hq0d : (d * r1 + (c1 + 1)) / d = r1 := by
        have e : d * r1 + (c1 + 1) = (c1 + 1) + r1 * d := by rw [Nat.mul_comm d r1]; omega
        rw [e, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc1d]; omega
      have hq0m : (d * r1 + (c1 + 1)) % d = c1 + 1 := by
        have e : d * r1 + (c1 + 1) = (c1 + 1) + r1 * d := by rw [Nat.mul_comm d r1]; omega
        rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc1d]
      have hq1d : (d * (r1 + 1) + (c1 + 1)) / d = r1 + 1 := by
        have e : d * (r1 + 1) + (c1 + 1) = (c1 + 1) + (r1 + 1) * d := by
          rw [Nat.mul_comm d (r1 + 1)]; omega
        rw [e, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc1d]; omega
      have hq1m : (d * (r1 + 1) + (c1 + 1)) % d = c1 + 1 := by
        have e : d * (r1 + 1) + (c1 + 1) = (c1 + 1) + (r1 + 1) * d := by
          rw [Nat.mul_comm d (r1 + 1)]; omega
        rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc1d]
      have hbk1d : decide (k < (d - 1) * (d - 1)) = true := by
        rw [decide_eq_true_eq]; exact hbulk
      rw [hq0d, hq0m, hq1d, hq1m, hbk1d]
      -- bulk-band: row {r1,r1+1} ∋ r1, r1+1; col {c1,c1+1} ∋ c1+1 (the succ branch).
      have hcolne : ¬ (c1 + 1 = c1) := by omega
      have hcolsucc : c1 + 1 = c1 + 1 := rfl
      simp [hcolne]
    · have hrf : decide (decide (c1 + 1 < d - 1) = true) = false := by
        rw [decide_eq_false_iff_not]; simp [hrow]
      simp only [hbt, hrf, Bool.false_eq_true, if_false, reduceIte]
  · have hbf : decide (decide (k < (d - 1) * (d - 1)) = true) = false := by
      rw [decide_eq_false_iff_not]; simp [hbulk]
    simp only [hbf, Bool.false_eq_true, if_false, reduceIte]

/-- Adjacency condition for the bulk–bulk-horiz class: `k2 = k1 + 1` (horizontal
neighbour, same bulk row). -/
abbrev bhAdjF (D : OddSurfaceDistance) : SFormula 2 :=
  .eqBool (SC.closed (.eqNat k2P (.add k1P (.natLit 1)))) (SC.b true)

abbrev bhBandK2PackF (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true))
    (.imp (bhRowF D)
      (.imp (bhAdjF D)
        (.and (.eqBool (SC.closed (baseBulkBandGuardTA (dP2 D) k2P (bhQ0 D))) (SC.b true))
          (.eqBool (SC.closed (baseBulkBandGuardTA (dP2 D) k2P (bhQ1 D))) (SC.b true)))))

/-- Bulk–Bulk-horiz band pack for `k2`: under `bulk(k1)`, the same-row bound, and the
adjacency `k2 = k1+1`, the Z-bulk plaquette band of `k2` (grid `(r1,c1+1)`, since
`(k1+1)/(d-1)=r1` and `(k1+1)%(d-1)=c1+1` when `c1+1<d-1`) fires at both overlap qubits
`q0`, `q1` (its left-column pair, column `c1+1`, rows `r1`, `r1+1`). -/
def bhBandK2Pack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (bhBandK2PackF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd3 : D.distance = 2 * D.index + 3 := rfl
  simp only [bhBandK2PackF, bhRowF, bhAdjF, bhQ0, bhQ1, bhR1, bhC1, bulkGuardTA,
    baseBulkBandGuardTA, bulkCountTA, dm1TA, band3, orEqSucc, dP2, SFormula.eval, SC.closed,
    SC.b, STerm.eval, Term.eval, Term.lift, bind, Option.bind]
  set k1 := rho ⟨1, by decide⟩ with hk1
  set k2 := rho ⟨0, by decide⟩ with hk2
  set d := D.distance with hdd
  have hdge : 3 ≤ d := by omega
  by_cases hbulk : k1 < (d - 1) * (d - 1)
  · have hbt : decide (decide (k1 < (d - 1) * (d - 1)) = true) = true := by
      rw [decide_eq_true_eq]; simp [hbulk]
    set r1 := k1 / (d - 1) with hr1
    set c1 := k1 % (d - 1) with hc1
    have hr1lt : r1 < d - 1 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hbulk)
    -- k1 = r1·(d-1) + c1.
    have hkdm : k1 = r1 * (d - 1) + c1 := by
      rw [hr1, hc1, Nat.mul_comm]; exact (Nat.div_add_mod k1 (d - 1)).symm
    have hc1lt : c1 < d - 1 := Nat.mod_lt k1 (by omega)
    by_cases hrow : c1 + 1 < d - 1
    · have hrt : decide (decide (c1 + 1 < d - 1) = true) = true := by
        rw [decide_eq_true_eq]; simp [hrow]
      by_cases hadj : k2 = k1 + 1
      · have hat : decide (decide (k2 = k1 + 1) = true) = true := by
          rw [decide_eq_true_eq]; simp [hadj]
        simp only [hbt, hrt, hat, if_true]
        have hc1d : c1 + 1 < d := by omega
        have hr1d : r1 + 1 < d := by omega
        -- coordinates of k2 = k1+1: (k1+1)/(d-1)=r1, (k1+1)%(d-1)=c1+1.
        have hk2d : k2 / (d - 1) = r1 := by
          rw [hadj, hkdm]
          have e : r1 * (d - 1) + c1 + 1 = (c1 + 1) + r1 * (d - 1) := by omega
          rw [e, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hrow]; omega
        have hk2m : k2 % (d - 1) = c1 + 1 := by
          rw [hadj, hkdm]
          have e : r1 * (d - 1) + c1 + 1 = (c1 + 1) + r1 * (d - 1) := by omega
          rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hrow]
        -- k2 < bulkCount.
        have hbulkk2 : k2 < (d - 1) * (d - 1) := by
          have hsm : (r1 + 1) * (d - 1) = r1 * (d - 1) + (d - 1) := by rw [Nat.succ_mul]
          have hle : (r1 + 1) * (d - 1) ≤ (d - 1) * (d - 1) := Nat.mul_le_mul_right _ (by omega)
          rw [hadj, hkdm]; omega
        have hbk2d : decide (k2 < (d - 1) * (d - 1)) = true := by
          rw [decide_eq_true_eq]; exact hbulkk2
        -- div/mod of q0, q1 (column c1+1).
        have hq0d : (d * r1 + (c1 + 1)) / d = r1 := by
          have e : d * r1 + (c1 + 1) = (c1 + 1) + r1 * d := by rw [Nat.mul_comm d r1]; omega
          rw [e, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc1d]; omega
        have hq0m : (d * r1 + (c1 + 1)) % d = c1 + 1 := by
          have e : d * r1 + (c1 + 1) = (c1 + 1) + r1 * d := by rw [Nat.mul_comm d r1]; omega
          rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc1d]
        have hq1d : (d * (r1 + 1) + (c1 + 1)) / d = r1 + 1 := by
          have e : d * (r1 + 1) + (c1 + 1) = (c1 + 1) + (r1 + 1) * d := by
            rw [Nat.mul_comm d (r1 + 1)]; omega
          rw [e, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc1d]; omega
        have hq1m : (d * (r1 + 1) + (c1 + 1)) % d = c1 + 1 := by
          have e : d * (r1 + 1) + (c1 + 1) = (c1 + 1) + (r1 + 1) * d := by
            rw [Nat.mul_comm d (r1 + 1)]; omega
          rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc1d]
        rw [hk2d, hk2m, hq0d, hq0m, hq1d, hq1m, hbk2d]
        -- bulk-band of k2 (col {c1+1, c1+2} ∋ c1+1 the eq branch; row {r1,r1+1}).
        simp
      · have haf : decide (decide (k2 = k1 + 1) = true) = false := by
          rw [decide_eq_false_iff_not]; simp [hadj]
        simp only [hbt, hrt, haf, Bool.false_eq_true, if_false, reduceIte]
    · have hrf : decide (decide (c1 + 1 < d - 1) = true) = false := by
        rw [decide_eq_false_iff_not]; simp [hrow]
      simp only [hbt, hrf, Bool.false_eq_true, if_false, reduceIte]
  · have hbf : decide (decide (k1 < (d - 1) * (d - 1)) = true) = false := by
      rw [decide_eq_false_iff_not]; simp [hbulk]
    simp only [hbf, Bool.false_eq_true, if_false, reduceIte]

/-! ### Bulk–Bulk-horiz class: the all-others joint pin

Under the bulk–bulk-horiz class context (`bulk(k1)`, `c1+1<d-1`, `k2=k1+1`), the verified
overlap geometry `overlap_bulk_bulk_horiz` (NO role swap — its `k1`/`k2` match ours)
forces every shared non-`I` slot into `{q0, q1}`.  The slot `q` is non-`I` for the X-bulk
plaquette `k1` exactly when its bulk band fires at `q`, and non-`I` for the Z-bulk
plaquette `k2` exactly when ITS bulk band fires at `q`; under those two band-fired facts
the disjunction `q = q0 ∨ q = q1` holds.  `arithBool` whose eval-certificate invokes
`overlap_bulk_bulk_horiz`. -/

/-- Arity-3 cell row of `k1` (`= (bhR1 D).weaken`). -/
abbrev bhR1_3 (D : OddSurfaceDistance) : Term 3 .nat := .div k1P3 (dm1TA (dP3 D))
/-- Arity-3 cell col of `k1` (`= (bhC1 D).weaken`). -/
abbrev bhC1_3 (D : OddSurfaceDistance) : Term 3 .nat := .mod k1P3 (dm1TA (dP3 D))
/-- Arity-3 overlap qubit `q0` (`= (bhQ0 D).weaken`). -/
abbrev bhQ0_3 (D : OddSurfaceDistance) : Term 3 .nat :=
  .add (.mul (dP3 D) (bhR1_3 D)) (.add (bhC1_3 D) (.natLit 1))
/-- Arity-3 overlap qubit `q1` (`= (bhQ1 D).weaken`). -/
abbrev bhQ1_3 (D : OddSurfaceDistance) : Term 3 .nat :=
  .add (.mul (dP3 D) (.add (bhR1_3 D) (.natLit 1))) (.add (bhC1_3 D) (.natLit 1))

theorem bhQ0_weaken (D : OddSurfaceDistance) : (bhQ0 D).weaken = bhQ0_3 D := rfl
theorem bhQ1_weaken (D : OddSurfaceDistance) : (bhQ1 D).weaken = bhQ1_3 D := rfl

/-- The bulk–bulk-horiz joint pin body (arity 3, `k1 = var 2`, `k2 = var 1`, `q = var 0`):
under the class context and the two bulk-band-fired facts, `q ∈ {q0, q1}`. -/
abbrev bhPinBody (D : OddSurfaceDistance) : SFormula 3 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b true))
    (.imp (.eqBool (SC.closed (.ltNat (.add (.mod k1P3 (dm1TA (dP3 D))) (.natLit 1))
        (dm1TA (dP3 D)))) (SC.b true))
      (.imp (.eqBool (SC.closed (.eqNat k2P3 (.add k1P3 (.natLit 1)))) (SC.b true))
        (.imp (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true))
          (.imp (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))
            (.or (.eqNat SFormula.boundNat (SC.closed (bhQ0_3 D)))
              (.eqNat SFormula.boundNat (SC.closed (bhQ1_3 D))))))))

abbrev bhPinF (D : OddSurfaceDistance) : SFormula 2 :=
  .allNatLt (nP2 D) (bhPinBody D)

/-- Bulk–Bulk-horiz joint pin pack: under the class context, every shared non-`I` slot
is one of the two overlap qubits.  `arithBool`, eval-cert via `overlap_bulk_bulk_horiz`
(NO role swap). -/
def bhPinPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (bhPinF D) := by
  refine PureFamilyDerivA.allNatLtIntro _ ?_
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd3 : D.distance = 2 * D.index + 3 := rfl
  simp only [bhPinBody, bhQ0_3, bhQ1_3, bhR1_3, bhC1_3, bulkGuardTA, baseBulkBandGuardTA,
    bulkCountTA, dm1TA, band3, orEqSucc, dP3, dP2, k1P3, k2P3, qP3, SFormula.eval,
    SFormula.boundNat, SC.closed, SC.b, STerm.eval, Term.eval, Term.lift, bind, Option.bind]
  set q := rho ⟨0, by decide⟩ with hq'
  set k2 := rho ⟨1, by decide⟩ with hk2'
  set k1 := rho ⟨2, by decide⟩ with hk1'
  set d := D.distance with hdd
  have hdge : 3 ≤ d := by omega
  have hdpos : 0 < d := by omega
  by_cases hbulk : k1 < (d - 1) * (d - 1)
  · have hbt : decide (decide (k1 < (d - 1) * (d - 1)) = true) = true := by
      rw [decide_eq_true_eq]; simp [hbulk]
    set r1 := k1 / (d - 1) with hr1
    set c1 := k1 % (d - 1) with hc1
    have hr1lt : r1 < d - 1 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hbulk)
    have hkdm : k1 = r1 * (d - 1) + c1 := by
      rw [hr1, hc1, Nat.mul_comm]; exact (Nat.div_add_mod k1 (d - 1)).symm
    have hc1lt : c1 < d - 1 := Nat.mod_lt k1 (by omega)
    by_cases hrow : c1 + 1 < d - 1
    · have hrt : decide (decide (c1 + 1 < d - 1) = true) = true := by
        rw [decide_eq_true_eq]; simp [hrow]
      by_cases hadj : k2 = k1 + 1
      · have hat : decide (decide (k2 = k1 + 1) = true) = true := by
          rw [decide_eq_true_eq]; simp [hadj]
        simp only [hbt, hrt, hat, if_true]
        have hc1d : c1 + 1 < d := by omega
        -- coordinates of k2 = k1+1.
        have hk2d : k2 / (d - 1) = r1 := by
          rw [hadj, hkdm]
          have e : r1 * (d - 1) + c1 + 1 = (c1 + 1) + r1 * (d - 1) := by omega
          rw [e, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hrow]; omega
        have hk2m : k2 % (d - 1) = c1 + 1 := by
          rw [hadj, hkdm]
          have e : r1 * (d - 1) + c1 + 1 = (c1 + 1) + r1 * (d - 1) := by omega
          rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hrow]
        -- The two bulk-band antecedents share the row guard `q/d ∈ {r1,r1+1}`; case on
        -- it FIRST (so a failing row collapses both bands to `false` immediately), then
        -- the column.  k1-band needs q%d∈{c1,c1+1}; k2-band needs q%d∈{c1+1,c1+2};
        -- jointly q%d = c1+1.
        rw [hk2d, hk2m]
        by_cases hqrow : q / d = r1 ∨ q / d = r1 + 1
        · by_cases hqcol : q % d = c1 + 1
          · -- both bands fire; q = d·(q/d) + (c1+1) ∈ {q0, q1}.
            have hqval : q = d * (q / d) + (c1 + 1) := by
              have hdm := Nat.div_add_mod q d
              rw [hqcol] at hdm; omega
            rcases hqrow with hc | hc
            · -- q/d = r1 → q = q0.
              have hqe : q = d * r1 + (c1 + 1) := by rw [hqval, hc]
              rw [hqcol, hc]; simp [hqe]
            · -- q/d = r1+1 → q = q1.
              have hqe : q = d * (r1 + 1) + (c1 + 1) := by rw [hqval, hc]
              have e0v : ¬ (q = d * r1 + (c1 + 1)) := by
                rw [hqe]
                have hms : d * r1 + d = d * (r1 + 1) := (Nat.mul_succ d r1).symm
                omega
              rw [hqcol, hc]; simp [hqe, e0v]
          · -- q%d ≠ c1+1: k2-band col antecedent {c1+1,c1+2} false at c1+1; the c1+2
            -- disjunct is excluded by the k1-band col {c1,c1+1}.  Either way vacuous.
            by_cases hqc2 : q % d = c1 + 2
            · -- q%d = c1+2: k1-band col {c1,c1+1} false → k1 band fails → vacuous.
              have hne0 : ¬ (q % d = c1) := by omega
              have hne1 : ¬ (q % d = c1 + 1) := by omega
              rcases hqrow with hc | hc <;> simp [hc, hne0, hne1]
            · -- q%d ∉ {c1+1, c1+2}: k2-band col antecedent {c1+1,c1+2} false → k2-band
              -- fails.  The k1-band col {c1,c1+1} may still fire (q%d=c1), but then the
              -- outer bind reaches the (failing) k2-band; split on q%d=c1 to determine the
              -- k1-band so both nested binds reduce.
              have hqc2' : ¬ (q % d = c1 + 1 + 1) := by omega
              have hcc : ¬ (c1 = c1 + 1 + 1) := by omega
              by_cases hqc0 : q % d = c1
              · rcases hqrow with hc | hc <;> simp [hc, hqc0, hqcol, hqc2', hcc]
              · rcases hqrow with hc | hc <;> simp [hc, hqc0, hqcol, hqc2']
        · -- q/d ∉ {r1, r1+1}: both band row antecedents false → both bands false → vacuous.
          push_neg at hqrow
          obtain ⟨hr0, hr1'⟩ := hqrow
          simp [hr0, hr1']
      · have haf : decide (decide (k2 = k1 + 1) = true) = false := by
          rw [decide_eq_false_iff_not]; simp [hadj]
        simp only [hbt, hrt, haf, Bool.false_eq_true, if_false, reduceIte]
    · have hrf : decide (decide (c1 + 1 < d - 1) = true) = false := by
        rw [decide_eq_false_iff_not]; simp [hrow]
      simp only [hbt, hrf, Bool.false_eq_true, if_false, reduceIte]
  · have hbf : decide (decide (k1 < (d - 1) * (d - 1)) = true) = false := by
      rw [decide_eq_false_iff_not]; simp [hbulk]
    simp only [hbf, Bool.false_eq_true, if_false, reduceIte]

/-- Extract the bulk–bulk-horiz joint-pin disjunction at `boundNat`. -/
def bhPinAt {Δ : List (SFormula 3)} (D : OddSurfaceDistance)
    (hW : SFormula.Deriv Δ (bhPinF D).weaken)
    (hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken))
    (hBulkK1 : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b true)))
    (hRow : SFormula.Deriv Δ (.eqBool (SC.closed (.ltNat
      (.add (.mod k1P3 (dm1TA (dP3 D))) (.natLit 1)) (dm1TA (dP3 D)))) (SC.b true)))
    (hAdj : SFormula.Deriv Δ
      (.eqBool (SC.closed (.eqNat k2P3 (.add k1P3 (.natLit 1)))) (SC.b true)))
    (hBandK1 : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true)))
    (hBandK2 : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))) :
    SFormula.Deriv Δ
      (.or (.eqNat SFormula.boundNat (SC.closed (bhQ0_3 D)))
        (.eqNat SFormula.boundNat (SC.closed (bhQ1_3 D)))) := by
  have hElim := SFormula.Deriv.allNatLtElim (nP2 D).weaken
    ((bhPinBody D).lift 1) SFormula.boundNat hW hq
  have hBody := SFormula.Deriv.applyNatBoundNatBeta (bhPinBody D) hElim
  exact SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp
    (SFormula.Deriv.mp hBody hBulkK1) hRow) hAdj) hBandK1) hBandK2

/-! ### Bulk–Bulk-horiz class: reverse-leaf band recovery (both via `baseLeafBulkIS`) -/

/-- Recover `bulkBand(k1, q) = true` from `baseLeafTreeTA k1 q = X`, given `bulk(k1)`.
Reverse-leaf: the false band branch gives an `I` leaf, contradicting `X`. -/
def bhBandK1FromX {Δ : List (SFormula 3)} (D : OddSurfaceDistance)
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

/-- Recover `bulkBand(k2, q) = true` from `baseLeafTreeTA k2 q = Z`, given `bulk(k2)`.
Reverse-leaf: the false band branch gives an `I` leaf, contradicting `Z`. -/
def bhBandK2FromZ {Δ : List (SFormula 3)} (D : OddSurfaceDistance)
    (hBulkT : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b true)))
    (hLeafZ : SFormula.Deriv Δ
      (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p Pauli.Z))) :
    SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true)) := by
  refine SFormula.Deriv.boolCases (SC.closed (baseBulkBandGuardTA (dP3 D) k2P3 qP3)) _ .assumption ?_
  refine SFormula.Deriv.botElim ?_
  have hBandF : SFormula.Deriv (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k2P3 qP3)) (SC.b false) :: Δ)
      (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k2P3 qP3)) (SC.b false)) := .assumption
  have hI : SFormula.Deriv (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k2P3 qP3)) (SC.b false) :: Δ)
      (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p Pauli.I)) :=
    baseLeafBulkIS (dP3 D) k2P3 qP3 (cw1 hBulkT) hBandF
  have hZI : SFormula.Deriv (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k2P3 qP3)) (SC.b false) :: Δ)
      (.eqPauli (SC.p Pauli.Z) (SC.p Pauli.I)) :=
    SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.eqPauliSymm _ _ (cw1 hLeafZ)) hI
  exact SFormula.Deriv.notElim hZI (SFormula.Deriv.pauliNeqLit Pauli.Z Pauli.I (by decide))

/-- **Bulk–Bulk overlap class closer (horizontal edge-adjacency).**  Assembles the
per-pair commutation goal for the bulk–bulk-horizontal overlap, where BOTH rows are bulk
plaquettes: row A (`k1`) is the X-type bulk plaquette at `(r1,c1)`, row B (`k2 = k1+1`)
is the Z-type bulk plaquette ONE COLUMN to its right at `(r1,c1+1)`.  Consumes the range
pack (`bhRangePack`), the two bulk-band packs (`bhBandK1Pack`/`bhBandK2Pack`), the joint
pin (`bhPinPack`), and the four flat-entry facts at `q0`, `q1`; under the class context
(`bulk(k1)`, `bulk(k2)`, the two kind facts, the same-row bound, and `k2 = k1+1`) it
resolves row A to `X` via `baseLeafXS` (X-bulk leaf) and row B to `Z` via `baseLeafZS`
(Z-bulk leaf), then discharges the all-others premise via the generic two-anti spine
`commBulkTopXZ`. -/
def commBulkBulkHoriz {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hEntryA : SFormula.Deriv Γ (entryAQuant D)) (hEntryB : SFormula.Deriv Γ (entryBQuant D))
    (hk1X : SFormula.Deriv Γ (k1IsX D true)) (hExcl1 : SFormula.Deriv Γ (typeExclF D k1P))
    (hBulkK1 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true)))
    (hKindK1 : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k1P)) (SC.b false)))
    (hBulkK2 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true)))
    (hKindK2 : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k2P)) (SC.b true)))
    (hadj : SFormula.Deriv Γ (bhAdjF D))
    (hrow : SFormula.Deriv Γ (bhRowF D))
    (hRange : SFormula.Deriv Γ (bhRangePackF D))
    (hBandK1 : SFormula.Deriv Γ (bhBandK1PackF D))
    (hBandK2 : SFormula.Deriv Γ (bhBandK2PackF D))
    (hPin : SFormula.Deriv Γ (bhPinF D))
    (hEA0 : SFormula.Deriv Γ (entryAAtQF D (bhQ0 D)))
    (hEA1 : SFormula.Deriv Γ (entryAAtQF D (bhQ1 D)))
    (hEB0 : SFormula.Deriv Γ (entryBAtQF D (bhQ0 D)))
    (hEB1 : SFormula.Deriv Γ (entryBAtQF D (bhQ1 D))) :
    SFormula.Deriv Γ (pairGoal D) := by
  -- Range facts at q0/q1.
  have hRangeP := SFormula.Deriv.mp (SFormula.Deriv.mp hRange hBulkK1) hrow
  have hLt0 := SFormula.Deriv.andElimLeft hRangeP
  have hLt1 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hRangeP)
  have hNe := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hRangeP)
  -- k1 bulk-band-fires facts at q0/q1.
  have hK1BP := SFormula.Deriv.mp (SFormula.Deriv.mp hBandK1 hBulkK1) hrow
  have hBB1_0 := SFormula.Deriv.andElimLeft hK1BP
  have hBB1_1 := SFormula.Deriv.andElimRight hK1BP
  -- k2 bulk-band-fires facts at q0/q1.
  have hK2BP := SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp hBandK2 hBulkK1) hrow) hadj
  have hBB2_0 := SFormula.Deriv.andElimLeft hK2BP
  have hBB2_1 := SFormula.Deriv.andElimRight hK2BP
  -- Row A = X at q0/q1 (X-bulk leaf), Row B = Z at q0/q1 (Z-bulk leaf).
  have hAX0 : SFormula.Deriv Γ (.eqPauli (.stabAt (rowA D) (SC.closed (bhQ0 D))) (SC.p Pauli.X)) :=
    SFormula.Deriv.eqPauliTrans _ _ _ hEA0 (baseLeafXS (dP2 D) k1P (bhQ0 D) hBulkK1 hBB1_0 hKindK1)
  have hAX1 : SFormula.Deriv Γ (.eqPauli (.stabAt (rowA D) (SC.closed (bhQ1 D))) (SC.p Pauli.X)) :=
    SFormula.Deriv.eqPauliTrans _ _ _ hEA1 (baseLeafXS (dP2 D) k1P (bhQ1 D) hBulkK1 hBB1_1 hKindK1)
  have hBZ0 : SFormula.Deriv Γ (.eqPauli (.stabAt (rowB D) (SC.closed (bhQ0 D))) (SC.p Pauli.Z)) :=
    SFormula.Deriv.eqPauliTrans _ _ _ hEB0 (baseLeafZS (dP2 D) k2P (bhQ0 D) hBulkK2 hBB2_0 hKindK2)
  have hBZ1 : SFormula.Deriv Γ (.eqPauli (.stabAt (rowB D) (SC.closed (bhQ1 D))) (SC.p Pauli.Z)) :=
    SFormula.Deriv.eqPauliTrans _ _ _ hEB1 (baseLeafZS (dP2 D) k2P (bhQ1 D) hBulkK2 hBB2_1 hKindK2)
  -- Assemble via the (generic) two-anti spine; the all-others pin handler closes overlap.
  refine commBulkTopXZ D (bhQ0 D) (bhQ1 D) hEntryA hEntryB hk1X hExcl1
    hLt0 hLt1 hNe hAX0 hAX1 hBZ0 hBZ1 ?_
  intro Δ' lift hLeafA hLeafB
  -- The class context + adj + both bulk facts, lifted into Δ'.
  have hBulkK1Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b true)) :=
    lift (cw3 (SFormula.Deriv.weakenFresh
      (A := .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true)) hBulkK1))
  have hBulkK2Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b true)) :=
    lift (cw3 (SFormula.Deriv.weakenFresh
      (A := .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true)) hBulkK2))
  have hrowΔ : SFormula.Deriv Δ' (.eqBool (SC.closed (.ltNat
      (.add (.mod k1P3 (dm1TA (dP3 D))) (.natLit 1)) (dm1TA (dP3 D)))) (SC.b true)) :=
    lift (cw3 (SFormula.Deriv.weakenFresh (A := bhRowF D) hrow))
  have hadjΔ : SFormula.Deriv Δ'
      (.eqBool (SC.closed (.eqNat k2P3 (.add k1P3 (.natLit 1)))) (SC.b true)) :=
    lift (cw3 (SFormula.Deriv.weakenFresh (A := bhAdjF D) hadj))
  have hPinΔ : SFormula.Deriv Δ' (bhPinF D).weaken :=
    lift (cw3 (SFormula.Deriv.weakenFresh (A := bhPinF D) hPin))
  have hq : SFormula.Deriv Δ' (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken) :=
    lift (.hyp (by right; right; exact List.mem_cons_self))
  -- Recover the bulk-band-fired facts at boundNat from the leaves.
  have hBandK1B := bhBandK1FromX D hBulkK1Δ hLeafA
  have hBandK2B := bhBandK2FromZ D hBulkK2Δ hLeafB
  -- The pin: boundNat ∈ {q0, q1}.
  have hdisj := bhPinAt D hPinΔ hq hBulkK1Δ hrowΔ hadjΔ hBandK1B hBandK2B
  -- The two exclusions in the handler context, lifted into Δ'.
  have hne0 : SFormula.Deriv Δ'
      (.not (.eqNat SFormula.boundNat (SC.closed (bhQ0 D)).weaken)) :=
    lift (.hyp (by right; exact List.mem_cons_self))
  have hne1 : SFormula.Deriv Δ'
      (.not (.eqNat SFormula.boundNat (SC.closed (bhQ1 D)).weaken)) :=
    lift (.hyp List.mem_cons_self)
  have hne0' : SFormula.Deriv Δ'
      (.not (.eqNat SFormula.boundNat (SC.closed (bhQ0_3 D)))) := hne0
  have hne1' : SFormula.Deriv Δ'
      (.not (.eqNat SFormula.boundNat (SC.closed (bhQ1_3 D)))) := hne1
  refine SFormula.Deriv.orElim hdisj ?_ ?_
  · exact SFormula.Deriv.botElim (SFormula.Deriv.notElim .assumption (cw1 hne0'))
  · exact SFormula.Deriv.botElim (SFormula.Deriv.notElim .assumption (cw1 hne1'))

#print axioms bhRangePack
#print axioms bhBandK1Pack
#print axioms bhBandK2Pack
#print axioms bhPinPack
#print axioms bhPinAt
#print axioms bhBandK1FromX
#print axioms bhBandK2FromZ
#print axioms commBulkBulkHoriz

/-! ## Bulk–Bulk overlap class (vertical edge-adjacency)

The single-class closer for the **bulk–bulk vertical** overlap: BOTH rows are bulk
plaquettes.  Row A (`k1`) is the X-type bulk plaquette at grid `(r1, c1)`
(`r1 = k1/(d-1)`, `c1 = k1%(d-1)`); row B (`k2 = k1+(d-1)`) is the Z-type bulk plaquette
ONE ROW BELOW it, at grid `(r1+1, c1)` (same grid column).  They overlap at exactly the
two qubits of their shared HORIZONTAL edge (row `r1+1`, columns `c1`, `c1+1`):
`q0 = d·(r1+1) + c1`, `q1 = d·(r1+1) + (c1+1)`.

The Nat geometry is the proven `overlap_bulk_bulk_vert` / `overlap_bulk_bulk_vert_range`
(in `SurfaceRowOverlapNat.lean`).  IMPORTANT: that lemma's `k1` IS our X-bulk plaquette
and its `k2` IS our Z-bulk plaquette — which MATCHES OUR convention.  So **NO role swap**:
pass OUR `k1` as ITS `k1` and OUR `k2` as ITS `k2`.

DEVIATIONS FROM THE BULK–BULK-HORIZ TEMPLATE.
* This is the DIRECT TWIN of `commBulkBulkHoriz`: the only change is `k2`'s position —
  here `k2 = k1 + (d-1)` (one grid ROW below) instead of `k1 + 1` (one column right).
* The overlap qubits share a ROW (`r1+1`) instead of a column.  Consequently the joint
  pin cases on the shared COLUMN (`q%d ∈ {c1,c1+1}`) FIRST (so a failing column collapses
  both bands), then the shared ROW (`q/d = r1+1`); this is the mirror of horiz's
  row-first/column-second split.
* The next-row validity antecedent `hrow` (`r1+1 < d-1`, so `k2 = k1+(d-1)` stays a valid
  bulk plaquette in the row below) is supplied by the dispatcher; it is a true geometric
  fact (the dispatcher routes here only when `k1` has a bulk row below it). -/

/-- Cell row of `k1` (arity 2): `r1 = k1/(d-1)`. -/
abbrev bvR1 (D : OddSurfaceDistance) : Term 2 .nat := .div k1P (dm1TA (dP2 D))
/-- Cell col of `k1` (arity 2): `c1 = k1%(d-1)`. -/
abbrev bvC1 (D : OddSurfaceDistance) : Term 2 .nat := .mod k1P (dm1TA (dP2 D))
/-- Overlap qubit `q0 = d·(r1+1) + c1` (row `r1+1`, column `c1`). -/
abbrev bvQ0 (D : OddSurfaceDistance) : Term 2 .nat :=
  .add (.mul (dP2 D) (.add (bvR1 D) (.natLit 1))) (bvC1 D)
/-- Overlap qubit `q1 = d·(r1+1) + (c1+1)` (row `r1+1`, column `c1+1`). -/
abbrev bvQ1 (D : OddSurfaceDistance) : Term 2 .nat :=
  .add (.mul (dP2 D) (.add (bvR1 D) (.natLit 1))) (.add (bvC1 D) (.natLit 1))

/-- Next-row validity guard: `r1 + 1 < d - 1` (so `k2 = k1+(d-1)` is a valid bulk
plaquette in the row below).  True geometric fact, supplied by the dispatcher. -/
abbrev bvRowF (D : OddSurfaceDistance) : SFormula 2 :=
  .eqBool (SC.closed (.ltNat (.add (.div k1P (dm1TA (dP2 D))) (.natLit 1)) (dm1TA (dP2 D))))
    (SC.b true)

abbrev bvRangePackF (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true))
    (.imp (bvRowF D)
      (.and (SFormula.witnessLt (SC.closed (bvQ0 D)) (nP2 D))
        (.and (SFormula.witnessLt (SC.closed (bvQ1 D)) (nP2 D))
          (.eqBool (SC.closed (.eqNat (bvQ0 D) (bvQ1 D))) (SC.b false)))))

/-- Bulk–Bulk-vert range pack: under `bulk(k1)` and the next-row validity bound, the
overlap qubits `q0 = d·(r1+1)+c1`, `q1 = d·(r1+1)+(c1+1)` are in range and distinct.
Discharged by `arithBool` whose eval-certificate invokes `overlap_bulk_bulk_vert_range`. -/
def bvRangePack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (bvRangePackF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd3 : D.distance = 2 * D.index + 3 := rfl
  simp only [bvRangePackF, bvRowF, bvQ0, bvQ1, bvR1, bvC1, bulkGuardTA, bulkCountTA, dm1TA,
    dP2, nP2, SFormula.eval, SFormula.witnessLt, SC.closed, SC.b, SC.n, STerm.eval, Term.eval,
    Term.lift, bind, Option.bind, nQubits]
  set k := rho ⟨1, by decide⟩ with hk
  set d := D.distance with hdd
  have hdge : 3 ≤ d := by omega
  by_cases hbulk : k < (d - 1) * (d - 1)
  · have hbt : decide (decide (k < (d - 1) * (d - 1)) = true) = true := by
      rw [decide_eq_true_eq]; simp [hbulk]
    set r1 := k / (d - 1) with hr1
    set c1 := k % (d - 1) with hc1
    have hr1lt : r1 < d - 1 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hbulk)
    have hc1lt : c1 < d - 1 := Nat.mod_lt k (by omega)
    by_cases hrow : r1 + 1 < d - 1
    · have hrt : decide (decide (r1 + 1 < d - 1) = true) = true := by
        rw [decide_eq_true_eq]; simp [hrow]
      simp only [hbt, hrt, if_true]
      have hr1d : r1 + 1 < d := by omega
      have hc1d : c1 + 1 < d := by omega
      obtain ⟨hne, hlt0, hlt1⟩ := overlap_bulk_bulk_vert_range d r1 c1 (by omega) hr1d hc1d
      have e0 : decide (decide (d * (r1 + 1) + c1 < d * d) = true) = true := by
        rw [decide_eq_true_eq, decide_eq_true_eq]; exact hlt0
      have e1 : decide (decide (d * (r1 + 1) + (c1 + 1) < d * d) = true) = true := by
        rw [decide_eq_true_eq, decide_eq_true_eq]; exact hlt1
      have ene : decide (decide (d * (r1 + 1) + c1 = d * (r1 + 1) + (c1 + 1)) = false) = true := by
        rw [decide_eq_true_eq, decide_eq_false_iff_not]; exact hne
      simp only [e0, e1, ene, decide_true, if_true]
    · have hrf : decide (decide (r1 + 1 < d - 1) = true) = false := by
        rw [decide_eq_false_iff_not]; simp [hrow]
      simp only [hbt, hrf, Bool.false_eq_true, if_false, reduceIte]
  · have hbf : decide (decide (k < (d - 1) * (d - 1)) = true) = false := by
      rw [decide_eq_false_iff_not]; simp [hbulk]
    simp only [hbf, Bool.false_eq_true, if_false, reduceIte]

abbrev bvBandK1PackF (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true))
    (.imp (bvRowF D)
      (.and (.eqBool (SC.closed (baseBulkBandGuardTA (dP2 D) k1P (bvQ0 D))) (SC.b true))
        (.eqBool (SC.closed (baseBulkBandGuardTA (dP2 D) k1P (bvQ1 D))) (SC.b true))))

/-- Bulk–Bulk-vert band pack for `k1`: under `bulk(k1)` and the next-row bound, the
X-bulk plaquette band of `k1` (grid `(r1,c1)`) fires at both overlap qubits
`q0 = d·(r1+1)+c1`, `q1 = d·(r1+1)+(c1+1)` (its bottom-row pair, row `r1+1`, columns
`c1`, `c1+1`). -/
def bvBandK1Pack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (bvBandK1PackF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd3 : D.distance = 2 * D.index + 3 := rfl
  simp only [bvBandK1PackF, bvRowF, bvQ0, bvQ1, bvR1, bvC1, bulkGuardTA, baseBulkBandGuardTA,
    bulkCountTA, dm1TA, band3, orEqSucc, dP2, SFormula.eval, SC.closed, SC.b, STerm.eval,
    Term.eval, Term.lift, bind, Option.bind]
  set k := rho ⟨1, by decide⟩ with hk
  set d := D.distance with hdd
  have hdge : 3 ≤ d := by omega
  by_cases hbulk : k < (d - 1) * (d - 1)
  · have hbt : decide (decide (k < (d - 1) * (d - 1)) = true) = true := by
      rw [decide_eq_true_eq]; simp [hbulk]
    set r1 := k / (d - 1) with hr1
    set c1 := k % (d - 1) with hc1
    have hr1lt : r1 < d - 1 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hbulk)
    have hc1lt : c1 < d - 1 := Nat.mod_lt k (by omega)
    by_cases hrow : r1 + 1 < d - 1
    · have hrt : decide (decide (r1 + 1 < d - 1) = true) = true := by
        rw [decide_eq_true_eq]; simp [hrow]
      simp only [hbt, hrt, if_true]
      have hc1d : c1 + 1 < d := by omega
      have hr1d : r1 + 1 < d := by omega
      -- div/mod of q0, q1 (row r1+1; columns c1, c1+1).
      have hq0d : (d * (r1 + 1) + c1) / d = r1 + 1 := by
        have e : d * (r1 + 1) + c1 = c1 + (r1 + 1) * d := by rw [Nat.mul_comm d (r1 + 1)]; omega
        rw [e, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega)]; omega
      have hq0m : (d * (r1 + 1) + c1) % d = c1 := by
        have e : d * (r1 + 1) + c1 = c1 + (r1 + 1) * d := by rw [Nat.mul_comm d (r1 + 1)]; omega
        rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      have hq1d : (d * (r1 + 1) + (c1 + 1)) / d = r1 + 1 := by
        have e : d * (r1 + 1) + (c1 + 1) = (c1 + 1) + (r1 + 1) * d := by
          rw [Nat.mul_comm d (r1 + 1)]; omega
        rw [e, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc1d]; omega
      have hq1m : (d * (r1 + 1) + (c1 + 1)) % d = c1 + 1 := by
        have e : d * (r1 + 1) + (c1 + 1) = (c1 + 1) + (r1 + 1) * d := by
          rw [Nat.mul_comm d (r1 + 1)]; omega
        rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc1d]
      have hbk1d : decide (k < (d - 1) * (d - 1)) = true := by
        rw [decide_eq_true_eq]; exact hbulk
      rw [hq0d, hq0m, hq1d, hq1m, hbk1d]
      -- bulk-band: row {r1,r1+1} ∋ r1+1 (the succ branch); col {c1,c1+1} ∋ c1, c1+1.
      have hrowne : ¬ (r1 + 1 = r1) := by omega
      simp [hrowne]
    · have hrf : decide (decide (r1 + 1 < d - 1) = true) = false := by
        rw [decide_eq_false_iff_not]; simp [hrow]
      simp only [hbt, hrf, Bool.false_eq_true, if_false, reduceIte]
  · have hbf : decide (decide (k < (d - 1) * (d - 1)) = true) = false := by
      rw [decide_eq_false_iff_not]; simp [hbulk]
    simp only [hbf, Bool.false_eq_true, if_false, reduceIte]

/-- Adjacency condition for the bulk–bulk-vert class: `k2 = k1 + (d-1)` (vertical
neighbour, one bulk row below, same column). -/
abbrev bvAdjF (D : OddSurfaceDistance) : SFormula 2 :=
  .eqBool (SC.closed (.eqNat k2P (.add k1P (dm1TA (dP2 D))))) (SC.b true)

abbrev bvBandK2PackF (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true))
    (.imp (bvRowF D)
      (.imp (bvAdjF D)
        (.and (.eqBool (SC.closed (baseBulkBandGuardTA (dP2 D) k2P (bvQ0 D))) (SC.b true))
          (.eqBool (SC.closed (baseBulkBandGuardTA (dP2 D) k2P (bvQ1 D))) (SC.b true)))))

/-- Bulk–Bulk-vert band pack for `k2`: under `bulk(k1)`, the next-row bound, and the
adjacency `k2 = k1+(d-1)`, the Z-bulk plaquette band of `k2` (grid `(r1+1,c1)`, since
`(k1+(d-1))/(d-1)=r1+1` and `(k1+(d-1))%(d-1)=c1`) fires at both overlap qubits
`q0`, `q1` (its top-row pair, row `r1+1`, columns `c1`, `c1+1`). -/
def bvBandK2Pack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (bvBandK2PackF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd3 : D.distance = 2 * D.index + 3 := rfl
  simp only [bvBandK2PackF, bvRowF, bvAdjF, bvQ0, bvQ1, bvR1, bvC1, bulkGuardTA,
    baseBulkBandGuardTA, bulkCountTA, dm1TA, band3, orEqSucc, dP2, SFormula.eval, SC.closed,
    SC.b, STerm.eval, Term.eval, Term.lift, bind, Option.bind]
  set k1 := rho ⟨1, by decide⟩ with hk1
  set k2 := rho ⟨0, by decide⟩ with hk2
  set d := D.distance with hdd
  have hdge : 3 ≤ d := by omega
  by_cases hbulk : k1 < (d - 1) * (d - 1)
  · have hbt : decide (decide (k1 < (d - 1) * (d - 1)) = true) = true := by
      rw [decide_eq_true_eq]; simp [hbulk]
    set r1 := k1 / (d - 1) with hr1
    set c1 := k1 % (d - 1) with hc1
    have hr1lt : r1 < d - 1 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hbulk)
    -- k1 = r1·(d-1) + c1.
    have hkdm : k1 = r1 * (d - 1) + c1 := by
      rw [hr1, hc1, Nat.mul_comm]; exact (Nat.div_add_mod k1 (d - 1)).symm
    have hc1lt : c1 < d - 1 := Nat.mod_lt k1 (by omega)
    by_cases hrow : r1 + 1 < d - 1
    · have hrt : decide (decide (r1 + 1 < d - 1) = true) = true := by
        rw [decide_eq_true_eq]; simp [hrow]
      by_cases hadj : k2 = k1 + (d - 1)
      · have hat : decide (decide (k2 = k1 + (d - 1)) = true) = true := by
          rw [decide_eq_true_eq]; simp [hadj]
        simp only [hbt, hrt, hat, if_true]
        have hc1d : c1 + 1 < d := by omega
        have hr1d : r1 + 1 < d := by omega
        -- coordinates of k2 = k1+(d-1): (k1+(d-1))/(d-1)=r1+1, (k1+(d-1))%(d-1)=c1.
        have hk2d : k2 / (d - 1) = r1 + 1 := by
          rw [hadj, hkdm]
          have e : r1 * (d - 1) + c1 + (d - 1) = c1 + (r1 + 1) * (d - 1) := by
            rw [Nat.succ_mul]; omega
          rw [e, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc1lt]; omega
        have hk2m : k2 % (d - 1) = c1 := by
          rw [hadj, hkdm]
          have e : r1 * (d - 1) + c1 + (d - 1) = c1 + (r1 + 1) * (d - 1) := by
            rw [Nat.succ_mul]; omega
          rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc1lt]
        -- k2 < bulkCount.
        have hbulkk2 : k2 < (d - 1) * (d - 1) := by
          have hsm : (r1 + 1) * (d - 1) = r1 * (d - 1) + (d - 1) := by rw [Nat.succ_mul]
          have hle : (r1 + 1 + 1) * (d - 1) ≤ (d - 1) * (d - 1) :=
            Nat.mul_le_mul_right _ (by omega)
          rw [hadj, hkdm]
          have e2 : (r1 + 1 + 1) * (d - 1) = r1 * (d - 1) + (d - 1) + (d - 1) := by
            rw [Nat.succ_mul, Nat.succ_mul]
          omega
        have hbk2d : decide (k2 < (d - 1) * (d - 1)) = true := by
          rw [decide_eq_true_eq]; exact hbulkk2
        -- div/mod of q0, q1 (row r1+1).
        have hq0d : (d * (r1 + 1) + c1) / d = r1 + 1 := by
          have e : d * (r1 + 1) + c1 = c1 + (r1 + 1) * d := by rw [Nat.mul_comm d (r1 + 1)]; omega
          rw [e, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega)]; omega
        have hq0m : (d * (r1 + 1) + c1) % d = c1 := by
          have e : d * (r1 + 1) + c1 = c1 + (r1 + 1) * d := by rw [Nat.mul_comm d (r1 + 1)]; omega
          rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
        have hq1d : (d * (r1 + 1) + (c1 + 1)) / d = r1 + 1 := by
          have e : d * (r1 + 1) + (c1 + 1) = (c1 + 1) + (r1 + 1) * d := by
            rw [Nat.mul_comm d (r1 + 1)]; omega
          rw [e, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc1d]; omega
        have hq1m : (d * (r1 + 1) + (c1 + 1)) % d = c1 + 1 := by
          have e : d * (r1 + 1) + (c1 + 1) = (c1 + 1) + (r1 + 1) * d := by
            rw [Nat.mul_comm d (r1 + 1)]; omega
          rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc1d]
        rw [hk2d, hk2m, hq0d, hq0m, hq1d, hq1m, hbk2d]
        -- bulk-band of k2 (row {r1+1, r1+2} ∋ r1+1 the eq branch; col {c1,c1+1}).
        simp
      · have haf : decide (decide (k2 = k1 + (d - 1)) = true) = false := by
          rw [decide_eq_false_iff_not]; simp [hadj]
        simp only [hbt, hrt, haf, Bool.false_eq_true, if_false, reduceIte]
    · have hrf : decide (decide (r1 + 1 < d - 1) = true) = false := by
        rw [decide_eq_false_iff_not]; simp [hrow]
      simp only [hbt, hrf, Bool.false_eq_true, if_false, reduceIte]
  · have hbf : decide (decide (k1 < (d - 1) * (d - 1)) = true) = false := by
      rw [decide_eq_false_iff_not]; simp [hbulk]
    simp only [hbf, Bool.false_eq_true, if_false, reduceIte]

/-! ### Bulk–Bulk-vert class: the all-others joint pin

Under the bulk–bulk-vert class context (`bulk(k1)`, `r1+1<d-1`, `k2=k1+(d-1)`), the
verified overlap geometry `overlap_bulk_bulk_vert` (NO role swap — its `k1`/`k2` match
ours) forces every shared non-`I` slot into `{q0, q1}`.  The slot `q` is non-`I` for the
X-bulk plaquette `k1` exactly when its bulk band fires at `q`, and non-`I` for the Z-bulk
plaquette `k2` exactly when ITS bulk band fires at `q`; under those two band-fired facts
the disjunction `q = q0 ∨ q = q1` holds.  `arithBool` whose eval-certificate invokes
`overlap_bulk_bulk_vert`. -/

/-- Arity-3 cell row of `k1` (`= (bvR1 D).weaken`). -/
abbrev bvR1_3 (D : OddSurfaceDistance) : Term 3 .nat := .div k1P3 (dm1TA (dP3 D))
/-- Arity-3 cell col of `k1` (`= (bvC1 D).weaken`). -/
abbrev bvC1_3 (D : OddSurfaceDistance) : Term 3 .nat := .mod k1P3 (dm1TA (dP3 D))
/-- Arity-3 overlap qubit `q0` (`= (bvQ0 D).weaken`). -/
abbrev bvQ0_3 (D : OddSurfaceDistance) : Term 3 .nat :=
  .add (.mul (dP3 D) (.add (bvR1_3 D) (.natLit 1))) (bvC1_3 D)
/-- Arity-3 overlap qubit `q1` (`= (bvQ1 D).weaken`). -/
abbrev bvQ1_3 (D : OddSurfaceDistance) : Term 3 .nat :=
  .add (.mul (dP3 D) (.add (bvR1_3 D) (.natLit 1))) (.add (bvC1_3 D) (.natLit 1))

theorem bvQ0_weaken (D : OddSurfaceDistance) : (bvQ0 D).weaken = bvQ0_3 D := rfl
theorem bvQ1_weaken (D : OddSurfaceDistance) : (bvQ1 D).weaken = bvQ1_3 D := rfl

/-- The bulk–bulk-vert joint pin body (arity 3, `k1 = var 2`, `k2 = var 1`, `q = var 0`):
under the class context and the two bulk-band-fired facts, `q ∈ {q0, q1}`. -/
abbrev bvPinBody (D : OddSurfaceDistance) : SFormula 3 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b true))
    (.imp (.eqBool (SC.closed (.ltNat (.add (.div k1P3 (dm1TA (dP3 D))) (.natLit 1))
        (dm1TA (dP3 D)))) (SC.b true))
      (.imp (.eqBool (SC.closed (.eqNat k2P3 (.add k1P3 (dm1TA (dP3 D))))) (SC.b true))
        (.imp (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true))
          (.imp (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))
            (.or (.eqNat SFormula.boundNat (SC.closed (bvQ0_3 D)))
              (.eqNat SFormula.boundNat (SC.closed (bvQ1_3 D))))))))

abbrev bvPinF (D : OddSurfaceDistance) : SFormula 2 :=
  .allNatLt (nP2 D) (bvPinBody D)

/-- Bulk–Bulk-vert joint pin pack: under the class context, every shared non-`I` slot
is one of the two overlap qubits.  `arithBool`, eval-cert via `overlap_bulk_bulk_vert`
(NO role swap). -/
def bvPinPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (bvPinF D) := by
  refine PureFamilyDerivA.allNatLtIntro _ ?_
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd3 : D.distance = 2 * D.index + 3 := rfl
  simp only [bvPinBody, bvQ0_3, bvQ1_3, bvR1_3, bvC1_3, bulkGuardTA, baseBulkBandGuardTA,
    bulkCountTA, dm1TA, band3, orEqSucc, dP3, dP2, k1P3, k2P3, qP3, SFormula.eval,
    SFormula.boundNat, SC.closed, SC.b, STerm.eval, Term.eval, Term.lift, bind, Option.bind]
  set q := rho ⟨0, by decide⟩ with hq'
  set k2 := rho ⟨1, by decide⟩ with hk2'
  set k1 := rho ⟨2, by decide⟩ with hk1'
  set d := D.distance with hdd
  have hdge : 3 ≤ d := by omega
  have hdpos : 0 < d := by omega
  by_cases hbulk : k1 < (d - 1) * (d - 1)
  · have hbt : decide (decide (k1 < (d - 1) * (d - 1)) = true) = true := by
      rw [decide_eq_true_eq]; simp [hbulk]
    set r1 := k1 / (d - 1) with hr1
    set c1 := k1 % (d - 1) with hc1
    have hr1lt : r1 < d - 1 := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hbulk)
    have hkdm : k1 = r1 * (d - 1) + c1 := by
      rw [hr1, hc1, Nat.mul_comm]; exact (Nat.div_add_mod k1 (d - 1)).symm
    have hc1lt : c1 < d - 1 := Nat.mod_lt k1 (by omega)
    by_cases hrow : r1 + 1 < d - 1
    · have hrt : decide (decide (r1 + 1 < d - 1) = true) = true := by
        rw [decide_eq_true_eq]; simp [hrow]
      by_cases hadj : k2 = k1 + (d - 1)
      · have hat : decide (decide (k2 = k1 + (d - 1)) = true) = true := by
          rw [decide_eq_true_eq]; simp [hadj]
        simp only [hbt, hrt, hat, if_true]
        have hc1d : c1 + 1 < d := by omega
        -- coordinates of k2 = k1+(d-1).
        have hk2d : k2 / (d - 1) = r1 + 1 := by
          rw [hadj, hkdm]
          have e : r1 * (d - 1) + c1 + (d - 1) = c1 + (r1 + 1) * (d - 1) := by
            rw [Nat.succ_mul]; omega
          rw [e, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc1lt]; omega
        have hk2m : k2 % (d - 1) = c1 := by
          rw [hadj, hkdm]
          have e : r1 * (d - 1) + c1 + (d - 1) = c1 + (r1 + 1) * (d - 1) := by
            rw [Nat.succ_mul]; omega
          rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc1lt]
        -- The two bulk-band antecedents share the col guard `q%d ∈ {c1,c1+1}`; case on
        -- it FIRST (so a failing col collapses both bands to `false` immediately), then
        -- the row.  k1-band needs q/d∈{r1,r1+1}; k2-band needs q/d∈{r1+1,r1+2};
        -- jointly q/d = r1+1.
        rw [hk2d, hk2m]
        by_cases hqcol : q % d = c1 ∨ q % d = c1 + 1
        · by_cases hqrow : q / d = r1 + 1
          · -- both bands fire; q = d·(r1+1) + (q%d) ∈ {q0, q1}.
            have hqval : q = d * (r1 + 1) + q % d := by
              have hdm := Nat.div_add_mod q d
              rw [hqrow] at hdm; omega
            rcases hqcol with hc | hc
            · -- q%d = c1 → q = q0.
              have hqe : q = d * (r1 + 1) + c1 := by rw [hqval, hc]
              rw [hqrow, hc]; simp [hqe]
            · -- q%d = c1+1 → q = q1.
              have hqe : q = d * (r1 + 1) + (c1 + 1) := by rw [hqval, hc]
              have e0v : ¬ (q = d * (r1 + 1) + c1) := by rw [hqe]; omega
              rw [hqrow, hc]; simp [hqe, e0v]
          · -- q/d ≠ r1+1: k2-band row antecedent {r1+1,r1+2} false at r1+1; the r1+2
            -- disjunct is excluded by the k1-band row {r1,r1+1}.  Either way vacuous.
            by_cases hqr2 : q / d = r1 + 2
            · -- q/d = r1+2: k1-band row {r1,r1+1} false → k1 band fails → vacuous.
              have hne0 : ¬ (q / d = r1) := by omega
              have hne1 : ¬ (q / d = r1 + 1) := by omega
              rcases hqcol with hc | hc <;> simp [hc, hne0, hne1]
            · -- q/d ∉ {r1+1, r1+2}: k2-band row antecedent {r1+1,r1+2} false → k2-band
              -- fails.  The k1-band row {r1,r1+1} may still fire (q/d=r1), but then the
              -- outer bind reaches the (failing) k2-band; split on q/d=r1 to determine the
              -- k1-band so both nested binds reduce.
              have hqr2' : ¬ (q / d = r1 + 1 + 1) := by omega
              have hrr : ¬ (r1 = r1 + 1 + 1) := by omega
              by_cases hqr0 : q / d = r1
              · rcases hqcol with hc | hc <;> simp [hc, hqr0, hqrow, hqr2', hrr]
              · rcases hqcol with hc | hc <;> simp [hc, hqr0, hqrow, hqr2']
        · -- q%d ∉ {c1, c1+1}: both band col antecedents false → both bands false → vacuous.
          -- The shared dim here is the COLUMN (inner band3 component), so a failed column
          -- collapses col∧bulk to `some false`; splitting the OUTER row guards concrete
          -- lets simp drive the option-bind machinery to `some true` in every branch.
          push_neg at hqcol
          obtain ⟨hc0, hc1'⟩ := hqcol
          by_cases hqr : q / d = r1 <;> by_cases hqr1 : q / d = r1 + 1 <;>
            simp [hc0, hc1', hqr, hqr1]
      · have haf : decide (decide (k2 = k1 + (d - 1)) = true) = false := by
          rw [decide_eq_false_iff_not]; simp [hadj]
        simp only [hbt, hrt, haf, Bool.false_eq_true, if_false, reduceIte]
    · have hrf : decide (decide (r1 + 1 < d - 1) = true) = false := by
        rw [decide_eq_false_iff_not]; simp [hrow]
      simp only [hbt, hrf, Bool.false_eq_true, if_false, reduceIte]
  · have hbf : decide (decide (k1 < (d - 1) * (d - 1)) = true) = false := by
      rw [decide_eq_false_iff_not]; simp [hbulk]
    simp only [hbf, Bool.false_eq_true, if_false, reduceIte]

/-- Extract the bulk–bulk-vert joint-pin disjunction at `boundNat`. -/
def bvPinAt {Δ : List (SFormula 3)} (D : OddSurfaceDistance)
    (hW : SFormula.Deriv Δ (bvPinF D).weaken)
    (hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken))
    (hBulkK1 : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b true)))
    (hRow : SFormula.Deriv Δ (.eqBool (SC.closed (.ltNat
      (.add (.div k1P3 (dm1TA (dP3 D))) (.natLit 1)) (dm1TA (dP3 D)))) (SC.b true)))
    (hAdj : SFormula.Deriv Δ
      (.eqBool (SC.closed (.eqNat k2P3 (.add k1P3 (dm1TA (dP3 D))))) (SC.b true)))
    (hBandK1 : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true)))
    (hBandK2 : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))) :
    SFormula.Deriv Δ
      (.or (.eqNat SFormula.boundNat (SC.closed (bvQ0_3 D)))
        (.eqNat SFormula.boundNat (SC.closed (bvQ1_3 D)))) := by
  have hElim := SFormula.Deriv.allNatLtElim (nP2 D).weaken
    ((bvPinBody D).lift 1) SFormula.boundNat hW hq
  have hBody := SFormula.Deriv.applyNatBoundNatBeta (bvPinBody D) hElim
  exact SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp
    (SFormula.Deriv.mp hBody hBulkK1) hRow) hAdj) hBandK1) hBandK2

/-! ### Bulk–Bulk-vert class: reverse-leaf band recovery (both via `baseLeafBulkIS`) -/

/-- Recover `bulkBand(k1, q) = true` from `baseLeafTreeTA k1 q = X`, given `bulk(k1)`.
Reverse-leaf: the false band branch gives an `I` leaf, contradicting `X`. -/
def bvBandK1FromX {Δ : List (SFormula 3)} (D : OddSurfaceDistance)
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

/-- Recover `bulkBand(k2, q) = true` from `baseLeafTreeTA k2 q = Z`, given `bulk(k2)`.
Reverse-leaf: the false band branch gives an `I` leaf, contradicting `Z`. -/
def bvBandK2FromZ {Δ : List (SFormula 3)} (D : OddSurfaceDistance)
    (hBulkT : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b true)))
    (hLeafZ : SFormula.Deriv Δ
      (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p Pauli.Z))) :
    SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true)) := by
  refine SFormula.Deriv.boolCases (SC.closed (baseBulkBandGuardTA (dP3 D) k2P3 qP3)) _ .assumption ?_
  refine SFormula.Deriv.botElim ?_
  have hBandF : SFormula.Deriv (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k2P3 qP3)) (SC.b false) :: Δ)
      (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k2P3 qP3)) (SC.b false)) := .assumption
  have hI : SFormula.Deriv (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k2P3 qP3)) (SC.b false) :: Δ)
      (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p Pauli.I)) :=
    baseLeafBulkIS (dP3 D) k2P3 qP3 (cw1 hBulkT) hBandF
  have hZI : SFormula.Deriv (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k2P3 qP3)) (SC.b false) :: Δ)
      (.eqPauli (SC.p Pauli.Z) (SC.p Pauli.I)) :=
    SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.eqPauliSymm _ _ (cw1 hLeafZ)) hI
  exact SFormula.Deriv.notElim hZI (SFormula.Deriv.pauliNeqLit Pauli.Z Pauli.I (by decide))

/-- **Bulk–Bulk overlap class closer (vertical edge-adjacency).**  Assembles the
per-pair commutation goal for the bulk–bulk-vertical overlap, where BOTH rows are bulk
plaquettes: row A (`k1`) is the X-type bulk plaquette at `(r1,c1)`, row B (`k2 = k1+(d-1)`)
is the Z-type bulk plaquette ONE ROW BELOW it at `(r1+1,c1)`.  Consumes the range pack
(`bvRangePack`), the two bulk-band packs (`bvBandK1Pack`/`bvBandK2Pack`), the joint pin
(`bvPinPack`), and the four flat-entry facts at `q0`, `q1`; under the class context
(`bulk(k1)`, `bulk(k2)`, the two kind facts, the next-row bound, and `k2 = k1+(d-1)`) it
resolves row A to `X` via `baseLeafXS` (X-bulk leaf) and row B to `Z` via `baseLeafZS`
(Z-bulk leaf), then discharges the all-others premise via the generic two-anti spine
`commBulkTopXZ`. -/
def commBulkBulkVert {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hEntryA : SFormula.Deriv Γ (entryAQuant D)) (hEntryB : SFormula.Deriv Γ (entryBQuant D))
    (hk1X : SFormula.Deriv Γ (k1IsX D true)) (hExcl1 : SFormula.Deriv Γ (typeExclF D k1P))
    (hBulkK1 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true)))
    (hKindK1 : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k1P)) (SC.b false)))
    (hBulkK2 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true)))
    (hKindK2 : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k2P)) (SC.b true)))
    (hadj : SFormula.Deriv Γ (bvAdjF D))
    (hrow : SFormula.Deriv Γ (bvRowF D))
    (hRange : SFormula.Deriv Γ (bvRangePackF D))
    (hBandK1 : SFormula.Deriv Γ (bvBandK1PackF D))
    (hBandK2 : SFormula.Deriv Γ (bvBandK2PackF D))
    (hPin : SFormula.Deriv Γ (bvPinF D))
    (hEA0 : SFormula.Deriv Γ (entryAAtQF D (bvQ0 D)))
    (hEA1 : SFormula.Deriv Γ (entryAAtQF D (bvQ1 D)))
    (hEB0 : SFormula.Deriv Γ (entryBAtQF D (bvQ0 D)))
    (hEB1 : SFormula.Deriv Γ (entryBAtQF D (bvQ1 D))) :
    SFormula.Deriv Γ (pairGoal D) := by
  -- Range facts at q0/q1.
  have hRangeP := SFormula.Deriv.mp (SFormula.Deriv.mp hRange hBulkK1) hrow
  have hLt0 := SFormula.Deriv.andElimLeft hRangeP
  have hLt1 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hRangeP)
  have hNe := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hRangeP)
  -- k1 bulk-band-fires facts at q0/q1.
  have hK1BP := SFormula.Deriv.mp (SFormula.Deriv.mp hBandK1 hBulkK1) hrow
  have hBB1_0 := SFormula.Deriv.andElimLeft hK1BP
  have hBB1_1 := SFormula.Deriv.andElimRight hK1BP
  -- k2 bulk-band-fires facts at q0/q1.
  have hK2BP := SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp hBandK2 hBulkK1) hrow) hadj
  have hBB2_0 := SFormula.Deriv.andElimLeft hK2BP
  have hBB2_1 := SFormula.Deriv.andElimRight hK2BP
  -- Row A = X at q0/q1 (X-bulk leaf), Row B = Z at q0/q1 (Z-bulk leaf).
  have hAX0 : SFormula.Deriv Γ (.eqPauli (.stabAt (rowA D) (SC.closed (bvQ0 D))) (SC.p Pauli.X)) :=
    SFormula.Deriv.eqPauliTrans _ _ _ hEA0 (baseLeafXS (dP2 D) k1P (bvQ0 D) hBulkK1 hBB1_0 hKindK1)
  have hAX1 : SFormula.Deriv Γ (.eqPauli (.stabAt (rowA D) (SC.closed (bvQ1 D))) (SC.p Pauli.X)) :=
    SFormula.Deriv.eqPauliTrans _ _ _ hEA1 (baseLeafXS (dP2 D) k1P (bvQ1 D) hBulkK1 hBB1_1 hKindK1)
  have hBZ0 : SFormula.Deriv Γ (.eqPauli (.stabAt (rowB D) (SC.closed (bvQ0 D))) (SC.p Pauli.Z)) :=
    SFormula.Deriv.eqPauliTrans _ _ _ hEB0 (baseLeafZS (dP2 D) k2P (bvQ0 D) hBulkK2 hBB2_0 hKindK2)
  have hBZ1 : SFormula.Deriv Γ (.eqPauli (.stabAt (rowB D) (SC.closed (bvQ1 D))) (SC.p Pauli.Z)) :=
    SFormula.Deriv.eqPauliTrans _ _ _ hEB1 (baseLeafZS (dP2 D) k2P (bvQ1 D) hBulkK2 hBB2_1 hKindK2)
  -- Assemble via the (generic) two-anti spine; the all-others pin handler closes overlap.
  refine commBulkTopXZ D (bvQ0 D) (bvQ1 D) hEntryA hEntryB hk1X hExcl1
    hLt0 hLt1 hNe hAX0 hAX1 hBZ0 hBZ1 ?_
  intro Δ' lift hLeafA hLeafB
  -- The class context + adj + both bulk facts, lifted into Δ'.
  have hBulkK1Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b true)) :=
    lift (cw3 (SFormula.Deriv.weakenFresh
      (A := .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true)) hBulkK1))
  have hBulkK2Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b true)) :=
    lift (cw3 (SFormula.Deriv.weakenFresh
      (A := .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true)) hBulkK2))
  have hrowΔ : SFormula.Deriv Δ' (.eqBool (SC.closed (.ltNat
      (.add (.div k1P3 (dm1TA (dP3 D))) (.natLit 1)) (dm1TA (dP3 D)))) (SC.b true)) :=
    lift (cw3 (SFormula.Deriv.weakenFresh (A := bvRowF D) hrow))
  have hadjΔ : SFormula.Deriv Δ'
      (.eqBool (SC.closed (.eqNat k2P3 (.add k1P3 (dm1TA (dP3 D))))) (SC.b true)) :=
    lift (cw3 (SFormula.Deriv.weakenFresh (A := bvAdjF D) hadj))
  have hPinΔ : SFormula.Deriv Δ' (bvPinF D).weaken :=
    lift (cw3 (SFormula.Deriv.weakenFresh (A := bvPinF D) hPin))
  have hq : SFormula.Deriv Δ' (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken) :=
    lift (.hyp (by right; right; exact List.mem_cons_self))
  -- Recover the bulk-band-fired facts at boundNat from the leaves.
  have hBandK1B := bvBandK1FromX D hBulkK1Δ hLeafA
  have hBandK2B := bvBandK2FromZ D hBulkK2Δ hLeafB
  -- The pin: boundNat ∈ {q0, q1}.
  have hdisj := bvPinAt D hPinΔ hq hBulkK1Δ hrowΔ hadjΔ hBandK1B hBandK2B
  -- The two exclusions in the handler context, lifted into Δ'.
  have hne0 : SFormula.Deriv Δ'
      (.not (.eqNat SFormula.boundNat (SC.closed (bvQ0 D)).weaken)) :=
    lift (.hyp (by right; exact List.mem_cons_self))
  have hne1 : SFormula.Deriv Δ'
      (.not (.eqNat SFormula.boundNat (SC.closed (bvQ1 D)).weaken)) :=
    lift (.hyp List.mem_cons_self)
  have hne0' : SFormula.Deriv Δ'
      (.not (.eqNat SFormula.boundNat (SC.closed (bvQ0_3 D)))) := hne0
  have hne1' : SFormula.Deriv Δ'
      (.not (.eqNat SFormula.boundNat (SC.closed (bvQ1_3 D)))) := hne1
  refine SFormula.Deriv.orElim hdisj ?_ ?_
  · exact SFormula.Deriv.botElim (SFormula.Deriv.notElim .assumption (cw1 hne0'))
  · exact SFormula.Deriv.botElim (SFormula.Deriv.notElim .assumption (cw1 hne1'))

#print axioms bvRangePack
#print axioms bvBandK1Pack
#print axioms bvBandK2Pack
#print axioms bvPinPack
#print axioms bvPinAt
#print axioms bvBandK1FromX
#print axioms bvBandK2FromZ
#print axioms commBulkBulkVert

end QHL.CodeLang.Surface.Verify
