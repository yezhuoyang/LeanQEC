import QStab.QHL.Verify.SurfaceRowsCommute.BulkBulkHV

/-!
# Rows-commute (pairwise generated-row commutation) — BulkBulkLU

The Bulk–Bulk overlap classes: horizontal-LEFT and vertical-UP edge-adjacency.
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface

set_option maxRecDepth 65536
set_option linter.unusedVariables false

/-! ## Bulk–Bulk overlap class (horizontal edge-adjacency, LEFT)

The MIRROR of `commBulkBulkHoriz`: BOTH rows are bulk plaquettes.  Row A (`k1`) is the
X-type bulk plaquette at grid `(r1, c1)` (`r1 = k1/(d-1)`, `c1 = k1%(d-1)`); row B
(`k2 = k1-1`) is the Z-type bulk plaquette ONE COLUMN to its LEFT, at grid `(r1, c1-1)`
(same grid row).  They overlap at exactly the two qubits of their shared VERTICAL edge —
the LEFT edge of `k1`'s stencil (column `c1`, rows `r1`, `r1+1`):
`q0 = d·r1 + c1`, `q1 = d·(r1+1) + c1`.

DEVIATIONS FROM THE BULK–BULK-HORIZ TEMPLATE.
* `k2 = k1 - 1` (one column LEFT) instead of `k1 + 1`.
* The shared column is `c1` (the LEFT edge) instead of `c1+1` (the RIGHT edge).
* Validity guard `hrow` is `0 < c1` (so `k1-1` stays in the SAME bulk row, with
  `cellC(k1-1) = c1-1`), instead of `c1+1 < d-1`.
* SWAPPED overlap-lemma roles for the range pack: the proven `overlap_bulk_bulk_horiz_range`
  takes `(d, r, c)` and emits `q0 = d·r+(c+1)`, `q1 = d·(r+1)+(c+1)`.  We invoke it at
  `c := c1-1` (OUR k2's column), so its emitted `q0 = d·r1+((c1-1)+1) = d·r1+c1 = our q0`,
  matching OUR forms (since `c1 ≥ 1`).  The pin pack proves the joint disjunction directly
  (no geometry-lemma call), as in `bhPinPack`.
* The k1-band column antecedent is `{c1, c1+1}`, the k2-band column antecedent is
  `{c1-1, c1}`; jointly `q%d = c1` (the LEFT shared edge). -/

/-- Cell row of `k1` (arity 2): `r1 = k1/(d-1)`. -/
abbrev bhlR1 (D : OddSurfaceDistance) : Term 2 .nat := .div k1P (dm1TA (dP2 D))
/-- Cell col of `k1` (arity 2): `c1 = k1%(d-1)`. -/
abbrev bhlC1 (D : OddSurfaceDistance) : Term 2 .nat := .mod k1P (dm1TA (dP2 D))
/-- Overlap qubit `q0 = d·r1 + c1` (column `c1`, row `r1`). -/
abbrev bhlQ0 (D : OddSurfaceDistance) : Term 2 .nat :=
  .add (.mul (dP2 D) (bhlR1 D)) (bhlC1 D)
/-- Overlap qubit `q1 = d·(r1+1) + c1` (column `c1`, row `r1+1`). -/
abbrev bhlQ1 (D : OddSurfaceDistance) : Term 2 .nat :=
  .add (.mul (dP2 D) (.add (bhlR1 D) (.natLit 1))) (bhlC1 D)

/-- Same-row validity guard: `0 < c1` (so `k2 = k1-1` stays in the same bulk row).
True geometric fact, supplied by the dispatcher. -/
abbrev bhlColF (D : OddSurfaceDistance) : SFormula 2 :=
  .eqBool (SC.closed (.ltNat (.natLit 0) (.mod k1P (dm1TA (dP2 D))))) (SC.b true)

abbrev bhlRangePackF (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true))
    (.imp (bhlColF D)
      (.and (SFormula.witnessLt (SC.closed (bhlQ0 D)) (nP2 D))
        (.and (SFormula.witnessLt (SC.closed (bhlQ1 D)) (nP2 D))
          (.eqBool (SC.closed (.eqNat (bhlQ0 D) (bhlQ1 D))) (SC.b false)))))

/-- Bulk–Bulk-horizL range pack: under `bulk(k1)` and the same-row validity bound `0<c1`,
the overlap qubits `q0 = d·r1+c1`, `q1 = d·(r1+1)+c1` are in range and distinct.
Discharged by `arithBool` whose eval-certificate invokes `overlap_bulk_bulk_horiz_range`
applied at column `c1-1` (SWAPPED role: OUR k2's column). -/
def bhlRangePack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (bhlRangePackF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd3 : D.distance = 2 * D.index + 3 := rfl
  simp only [bhlRangePackF, bhlColF, bhlQ0, bhlQ1, bhlR1, bhlC1, bulkGuardTA, bulkCountTA, dm1TA,
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
    by_cases hcol : 0 < c1
    · have hct : decide (decide (0 < c1) = true) = true := by
        rw [decide_eq_true_eq]; simp [hcol]
      simp only [hbt, hct, if_true]
      have hr1d : r1 + 1 < d := by omega
      have hc1d : (c1 - 1) + 1 < d := by omega
      obtain ⟨hne, hlt0, hlt1⟩ := overlap_bulk_bulk_horiz_range d r1 (c1 - 1) (by omega) hr1d hc1d
      -- rewrite (c1-1)+1 = c1 in the emitted facts.
      have hcc : (c1 - 1) + 1 = c1 := by omega
      rw [hcc] at hne hlt0 hlt1
      have e0 : decide (decide (d * r1 + c1 < d * d) = true) = true := by
        rw [decide_eq_true_eq, decide_eq_true_eq]; exact hlt0
      have e1 : decide (decide (d * (r1 + 1) + c1 < d * d) = true) = true := by
        rw [decide_eq_true_eq, decide_eq_true_eq]; exact hlt1
      have ene : decide (decide (d * r1 + c1 = d * (r1 + 1) + c1) = false) = true := by
        rw [decide_eq_true_eq, decide_eq_false_iff_not]; exact hne
      simp only [e0, e1, ene, decide_true, if_true]
    · have hcf : decide (decide (0 < c1) = true) = false := by
        rw [decide_eq_false_iff_not]; simp [hcol]
      simp only [hbt, hcf, Bool.false_eq_true, if_false, reduceIte]
  · have hbf : decide (decide (k < (d - 1) * (d - 1)) = true) = false := by
      rw [decide_eq_false_iff_not]; simp [hbulk]
    simp only [hbf, Bool.false_eq_true, if_false, reduceIte]

abbrev bhlBandK1PackF (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true))
    (.imp (bhlColF D)
      (.and (.eqBool (SC.closed (baseBulkBandGuardTA (dP2 D) k1P (bhlQ0 D))) (SC.b true))
        (.eqBool (SC.closed (baseBulkBandGuardTA (dP2 D) k1P (bhlQ1 D))) (SC.b true))))

/-- Bulk–Bulk-horizL band pack for `k1`: under `bulk(k1)` and `0<c1`, the X-bulk plaquette
band of `k1` (grid `(r1,c1)`) fires at both overlap qubits `q0 = d·r1+c1`,
`q1 = d·(r1+1)+c1` (its LEFT-column pair, column `c1`, rows `r1`, `r1+1`). -/
def bhlBandK1Pack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (bhlBandK1PackF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd3 : D.distance = 2 * D.index + 3 := rfl
  simp only [bhlBandK1PackF, bhlColF, bhlQ0, bhlQ1, bhlR1, bhlC1, bulkGuardTA, baseBulkBandGuardTA,
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
    by_cases hcol : 0 < c1
    · have hct : decide (decide (0 < c1) = true) = true := by
        rw [decide_eq_true_eq]; simp [hcol]
      simp only [hbt, hct, if_true]
      have hc1d : c1 < d := by omega
      have hr1d : r1 + 1 < d := by omega
      -- div/mod of q0, q1 (column c1; rows r1, r1+1).
      have hq0d : (d * r1 + c1) / d = r1 := by
        have e : d * r1 + c1 = c1 + r1 * d := by rw [Nat.mul_comm d r1]; omega
        rw [e, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc1d]; omega
      have hq0m : (d * r1 + c1) % d = c1 := by
        have e : d * r1 + c1 = c1 + r1 * d := by rw [Nat.mul_comm d r1]; omega
        rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc1d]
      have hq1d : (d * (r1 + 1) + c1) / d = r1 + 1 := by
        have e : d * (r1 + 1) + c1 = c1 + (r1 + 1) * d := by rw [Nat.mul_comm d (r1 + 1)]; omega
        rw [e, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc1d]; omega
      have hq1m : (d * (r1 + 1) + c1) % d = c1 := by
        have e : d * (r1 + 1) + c1 = c1 + (r1 + 1) * d := by rw [Nat.mul_comm d (r1 + 1)]; omega
        rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc1d]
      have hbk1d : decide (k < (d - 1) * (d - 1)) = true := by
        rw [decide_eq_true_eq]; exact hbulk
      rw [hq0d, hq0m, hq1d, hq1m, hbk1d]
      -- bulk-band: row {r1,r1+1} ∋ r1, r1+1; col {c1,c1+1} ∋ c1 (the eq branch).
      simp
    · have hcf : decide (decide (0 < c1) = true) = false := by
        rw [decide_eq_false_iff_not]; simp [hcol]
      simp only [hbt, hcf, Bool.false_eq_true, if_false, reduceIte]
  · have hbf : decide (decide (k < (d - 1) * (d - 1)) = true) = false := by
      rw [decide_eq_false_iff_not]; simp [hbulk]
    simp only [hbf, Bool.false_eq_true, if_false, reduceIte]

/-- Adjacency condition for the bulk–bulk-horizL class: `k2 = k1 - 1` (horizontal
neighbour to the LEFT, same bulk row). -/
abbrev bhlAdjF (D : OddSurfaceDistance) : SFormula 2 :=
  .eqBool (SC.closed (.eqNat k2P (.sub k1P (.natLit 1)))) (SC.b true)

abbrev bhlBandK2PackF (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true))
    (.imp (bhlColF D)
      (.imp (bhlAdjF D)
        (.and (.eqBool (SC.closed (baseBulkBandGuardTA (dP2 D) k2P (bhlQ0 D))) (SC.b true))
          (.eqBool (SC.closed (baseBulkBandGuardTA (dP2 D) k2P (bhlQ1 D))) (SC.b true)))))

/-- Bulk–Bulk-horizL band pack for `k2`: under `bulk(k1)`, `0<c1`, and the adjacency
`k2 = k1-1`, the Z-bulk plaquette band of `k2` (grid `(r1,c1-1)`, since `(k1-1)/(d-1)=r1`
and `(k1-1)%(d-1)=c1-1` when `0<c1`) fires at both overlap qubits `q0`, `q1` (its
RIGHT-column pair, column `c1`, rows `r1`, `r1+1`). -/
def bhlBandK2Pack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (bhlBandK2PackF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd3 : D.distance = 2 * D.index + 3 := rfl
  simp only [bhlBandK2PackF, bhlColF, bhlAdjF, bhlQ0, bhlQ1, bhlR1, bhlC1, bulkGuardTA,
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
    by_cases hcol : 0 < c1
    · have hct : decide (decide (0 < c1) = true) = true := by
        rw [decide_eq_true_eq]; simp [hcol]
      by_cases hadj : k2 = k1 - 1
      · have hat : decide (decide (k2 = k1 - 1) = true) = true := by
          rw [decide_eq_true_eq]; simp [hadj]
        simp only [hbt, hct, hat, if_true]
        have hc1d : c1 < d := by omega
        have hr1d : r1 + 1 < d := by omega
        -- coordinates of k2 = k1-1: (k1-1)/(d-1)=r1, (k1-1)%(d-1)=c1-1.
        have hk2d : k2 / (d - 1) = r1 := by
          rw [hadj, hkdm]
          have e : r1 * (d - 1) + c1 - 1 = (c1 - 1) + r1 * (d - 1) := by omega
          rw [e, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega)]; omega
        have hk2m : k2 % (d - 1) = c1 - 1 := by
          rw [hadj, hkdm]
          have e : r1 * (d - 1) + c1 - 1 = (c1 - 1) + r1 * (d - 1) := by omega
          rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
        -- k2 < bulkCount.
        have hbulkk2 : k2 < (d - 1) * (d - 1) := by
          rw [hadj, hkdm]; omega
        have hbk2d : decide (k2 < (d - 1) * (d - 1)) = true := by
          rw [decide_eq_true_eq]; exact hbulkk2
        -- div/mod of q0, q1 (column c1).
        have hq0d : (d * r1 + c1) / d = r1 := by
          have e : d * r1 + c1 = c1 + r1 * d := by rw [Nat.mul_comm d r1]; omega
          rw [e, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc1d]; omega
        have hq0m : (d * r1 + c1) % d = c1 := by
          have e : d * r1 + c1 = c1 + r1 * d := by rw [Nat.mul_comm d r1]; omega
          rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc1d]
        have hq1d : (d * (r1 + 1) + c1) / d = r1 + 1 := by
          have e : d * (r1 + 1) + c1 = c1 + (r1 + 1) * d := by rw [Nat.mul_comm d (r1 + 1)]; omega
          rw [e, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc1d]; omega
        have hq1m : (d * (r1 + 1) + c1) % d = c1 := by
          have e : d * (r1 + 1) + c1 = c1 + (r1 + 1) * d := by rw [Nat.mul_comm d (r1 + 1)]; omega
          rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc1d]
        rw [hk2d, hk2m, hq0d, hq0m, hq1d, hq1m, hbk2d]
        -- bulk-band of k2 (col {c1-1, c1} ∋ c1 the succ branch; row {r1,r1+1}).
        have hcsucc : (c1 - 1) + 1 = c1 := by omega
        have hcolne : ¬ (c1 = c1 - 1) := by omega
        simp [hcsucc, hcolne]
      · have haf : decide (decide (k2 = k1 - 1) = true) = false := by
          rw [decide_eq_false_iff_not]; simp [hadj]
        simp only [hbt, hct, haf, Bool.false_eq_true, if_false, reduceIte]
    · have hcf : decide (decide (0 < c1) = true) = false := by
        rw [decide_eq_false_iff_not]; simp [hcol]
      simp only [hbt, hcf, Bool.false_eq_true, if_false, reduceIte]
  · have hbf : decide (decide (k1 < (d - 1) * (d - 1)) = true) = false := by
      rw [decide_eq_false_iff_not]; simp [hbulk]
    simp only [hbf, Bool.false_eq_true, if_false, reduceIte]

/-! ### Bulk–Bulk-horizL class: the all-others joint pin -/

/-- Arity-3 cell row of `k1` (`= (bhlR1 D).weaken`). -/
abbrev bhlR1_3 (D : OddSurfaceDistance) : Term 3 .nat := .div k1P3 (dm1TA (dP3 D))
/-- Arity-3 cell col of `k1` (`= (bhlC1 D).weaken`). -/
abbrev bhlC1_3 (D : OddSurfaceDistance) : Term 3 .nat := .mod k1P3 (dm1TA (dP3 D))
/-- Arity-3 overlap qubit `q0` (`= (bhlQ0 D).weaken`). -/
abbrev bhlQ0_3 (D : OddSurfaceDistance) : Term 3 .nat :=
  .add (.mul (dP3 D) (bhlR1_3 D)) (bhlC1_3 D)
/-- Arity-3 overlap qubit `q1` (`= (bhlQ1 D).weaken`). -/
abbrev bhlQ1_3 (D : OddSurfaceDistance) : Term 3 .nat :=
  .add (.mul (dP3 D) (.add (bhlR1_3 D) (.natLit 1))) (bhlC1_3 D)

theorem bhlQ0_weaken (D : OddSurfaceDistance) : (bhlQ0 D).weaken = bhlQ0_3 D := rfl
theorem bhlQ1_weaken (D : OddSurfaceDistance) : (bhlQ1 D).weaken = bhlQ1_3 D := rfl

/-- The bulk–bulk-horizL joint pin body (arity 3, `k1 = var 2`, `k2 = var 1`, `q = var 0`):
under the class context and the two bulk-band-fired facts, `q ∈ {q0, q1}`. -/
abbrev bhlPinBody (D : OddSurfaceDistance) : SFormula 3 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b true))
    (.imp (.eqBool (SC.closed (.ltNat (.natLit 0) (.mod k1P3 (dm1TA (dP3 D))))) (SC.b true))
      (.imp (.eqBool (SC.closed (.eqNat k2P3 (.sub k1P3 (.natLit 1)))) (SC.b true))
        (.imp (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true))
          (.imp (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))
            (.or (.eqNat SFormula.boundNat (SC.closed (bhlQ0_3 D)))
              (.eqNat SFormula.boundNat (SC.closed (bhlQ1_3 D))))))))

abbrev bhlPinF (D : OddSurfaceDistance) : SFormula 2 :=
  .allNatLt (nP2 D) (bhlPinBody D)

/-- Bulk–Bulk-horizL joint pin pack: under the class context, every shared non-`I` slot
is one of the two overlap qubits.  `arithBool`, proven directly (joint column is `c1`). -/
def bhlPinPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (bhlPinF D) := by
  refine PureFamilyDerivA.allNatLtIntro _ ?_
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd3 : D.distance = 2 * D.index + 3 := rfl
  simp only [bhlPinBody, bhlQ0_3, bhlQ1_3, bhlR1_3, bhlC1_3, bulkGuardTA, baseBulkBandGuardTA,
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
    by_cases hcol : 0 < c1
    · have hct : decide (decide (0 < c1) = true) = true := by
        rw [decide_eq_true_eq]; simp [hcol]
      by_cases hadj : k2 = k1 - 1
      · have hat : decide (decide (k2 = k1 - 1) = true) = true := by
          rw [decide_eq_true_eq]; simp [hadj]
        simp only [hbt, hct, hat, if_true]
        have hc1d : c1 < d := by omega
        -- coordinates of k2 = k1-1.
        have hk2d : k2 / (d - 1) = r1 := by
          rw [hadj, hkdm]
          have e : r1 * (d - 1) + c1 - 1 = (c1 - 1) + r1 * (d - 1) := by omega
          rw [e, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega)]; omega
        have hk2m : k2 % (d - 1) = c1 - 1 := by
          rw [hadj, hkdm]
          have e : r1 * (d - 1) + c1 - 1 = (c1 - 1) + r1 * (d - 1) := by omega
          rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
        -- The two bulk-band antecedents share the row guard `q/d ∈ {r1,r1+1}`; case on
        -- it FIRST, then the column.  k1-band needs q%d∈{c1,c1+1}; k2-band needs
        -- q%d∈{c1-1,c1}; jointly q%d = c1.
        rw [hk2d, hk2m]
        have hcsucc : (c1 - 1) + 1 = c1 := by omega
        by_cases hqrow : q / d = r1 ∨ q / d = r1 + 1
        · by_cases hqcol : q % d = c1
          · -- both bands fire; q = d·(q/d) + c1 ∈ {q0, q1}.
            have hqval : q = d * (q / d) + c1 := by
              have hdm := Nat.div_add_mod q d
              rw [hqcol] at hdm; omega
            rcases hqrow with hc | hc
            · -- q/d = r1 → q = q0.
              have hqe : q = d * r1 + c1 := by rw [hqval, hc]
              rw [hqcol, hc, hcsucc]; simp [hqe]
            · -- q/d = r1+1 → q = q1.
              have hqe : q = d * (r1 + 1) + c1 := by rw [hqval, hc]
              have e0v : ¬ (q = d * r1 + c1) := by
                rw [hqe]
                have hms : d * r1 + d = d * (r1 + 1) := (Nat.mul_succ d r1).symm
                omega
              rw [hqcol, hc, hcsucc]; simp [hqe, e0v]
          · -- q%d ≠ c1.  Split to show at least one band fails everywhere.
            by_cases hqc1 : q % d = c1 - 1
            · -- q%d = c1-1: k1-band col {c1,c1+1} false (since c1-1 ≠ c1, c1-1 ≠ c1+1).
              have hne0 : ¬ (q % d = c1) := by omega
              have hne1 : ¬ (q % d = c1 + 1) := by omega
              rcases hqrow with hc | hc <;> simp [hc, hne0, hne1]
            · -- q%d ∉ {c1-1, c1}: k2-band col {c1-1,c1} false → k2-band fails.  The k1-band
              -- col {c1,c1+1} may fire (q%d=c1+1); split on it so both binds reduce.
              have hqc1' : ¬ (q % d = c1 - 1 + 1) := by omega
              have hcc : ¬ (c1 + 1 = c1 - 1) := by omega
              have hcc2 : ¬ (c1 + 1 = c1 - 1 + 1) := by omega
              by_cases hqc2 : q % d = c1 + 1
              · rcases hqrow with hc | hc <;>
                  simp [hc, hqc2, hcc, (show ¬ (c1 = c1 - 1) by omega)]
              · rcases hqrow with hc | hc <;> simp [hc, hqc2, hqcol, hqc1']
        · -- q/d ∉ {r1, r1+1}: both band row antecedents false → both bands false → vacuous.
          push_neg at hqrow
          obtain ⟨hr0, hr1'⟩ := hqrow
          simp [hr0, hr1']
      · have haf : decide (decide (k2 = k1 - 1) = true) = false := by
          rw [decide_eq_false_iff_not]; simp [hadj]
        simp only [hbt, hct, haf, Bool.false_eq_true, if_false, reduceIte]
    · have hcf : decide (decide (0 < c1) = true) = false := by
        rw [decide_eq_false_iff_not]; simp [hcol]
      simp only [hbt, hcf, Bool.false_eq_true, if_false, reduceIte]
  · have hbf : decide (decide (k1 < (d - 1) * (d - 1)) = true) = false := by
      rw [decide_eq_false_iff_not]; simp [hbulk]
    simp only [hbf, Bool.false_eq_true, if_false, reduceIte]

/-- Extract the bulk–bulk-horizL joint-pin disjunction at `boundNat`. -/
def bhlPinAt {Δ : List (SFormula 3)} (D : OddSurfaceDistance)
    (hW : SFormula.Deriv Δ (bhlPinF D).weaken)
    (hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken))
    (hBulkK1 : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b true)))
    (hCol : SFormula.Deriv Δ (.eqBool (SC.closed (.ltNat
      (.natLit 0) (.mod k1P3 (dm1TA (dP3 D))))) (SC.b true)))
    (hAdj : SFormula.Deriv Δ
      (.eqBool (SC.closed (.eqNat k2P3 (.sub k1P3 (.natLit 1)))) (SC.b true)))
    (hBandK1 : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true)))
    (hBandK2 : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))) :
    SFormula.Deriv Δ
      (.or (.eqNat SFormula.boundNat (SC.closed (bhlQ0_3 D)))
        (.eqNat SFormula.boundNat (SC.closed (bhlQ1_3 D)))) := by
  have hElim := SFormula.Deriv.allNatLtElim (nP2 D).weaken
    ((bhlPinBody D).lift 1) SFormula.boundNat hW hq
  have hBody := SFormula.Deriv.applyNatBoundNatBeta (bhlPinBody D) hElim
  exact SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp
    (SFormula.Deriv.mp hBody hBulkK1) hCol) hAdj) hBandK1) hBandK2

/-! ### Bulk–Bulk-horizL class: reverse-leaf band recovery (both via `baseLeafBulkIS`) -/

/-- Recover `bulkBand(k1, q) = true` from `baseLeafTreeTA k1 q = X`, given `bulk(k1)`. -/
def bhlBandK1FromX {Δ : List (SFormula 3)} (D : OddSurfaceDistance)
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

/-- Recover `bulkBand(k2, q) = true` from `baseLeafTreeTA k2 q = Z`, given `bulk(k2)`. -/
def bhlBandK2FromZ {Δ : List (SFormula 3)} (D : OddSurfaceDistance)
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

/-- **Bulk–Bulk overlap class closer (horizontal edge-adjacency, LEFT).**  Mirror of
`commBulkBulkHoriz`: row A (`k1`) is the X-type bulk plaquette at `(r1,c1)`, row B
(`k2 = k1-1`) is the Z-type bulk plaquette ONE COLUMN to its LEFT at `(r1,c1-1)`.  They
overlap at the two qubits of `k1`'s LEFT edge `q0 = d·r1+c1`, `q1 = d·(r1+1)+c1`. -/
def commBulkBulkHorizL {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hEntryA : SFormula.Deriv Γ (entryAQuant D)) (hEntryB : SFormula.Deriv Γ (entryBQuant D))
    (hk1X : SFormula.Deriv Γ (k1IsX D true)) (hExcl1 : SFormula.Deriv Γ (typeExclF D k1P))
    (hBulkK1 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true)))
    (hKindK1 : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k1P)) (SC.b false)))
    (hBulkK2 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true)))
    (hKindK2 : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k2P)) (SC.b true)))
    (hadj : SFormula.Deriv Γ (bhlAdjF D))
    (hcol : SFormula.Deriv Γ (bhlColF D))
    (hRange : SFormula.Deriv Γ (bhlRangePackF D))
    (hBandK1 : SFormula.Deriv Γ (bhlBandK1PackF D))
    (hBandK2 : SFormula.Deriv Γ (bhlBandK2PackF D))
    (hPin : SFormula.Deriv Γ (bhlPinF D))
    (hEA0 : SFormula.Deriv Γ (entryAAtQF D (bhlQ0 D)))
    (hEA1 : SFormula.Deriv Γ (entryAAtQF D (bhlQ1 D)))
    (hEB0 : SFormula.Deriv Γ (entryBAtQF D (bhlQ0 D)))
    (hEB1 : SFormula.Deriv Γ (entryBAtQF D (bhlQ1 D))) :
    SFormula.Deriv Γ (pairGoal D) := by
  -- Range facts at q0/q1.
  have hRangeP := SFormula.Deriv.mp (SFormula.Deriv.mp hRange hBulkK1) hcol
  have hLt0 := SFormula.Deriv.andElimLeft hRangeP
  have hLt1 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hRangeP)
  have hNe := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hRangeP)
  -- k1 bulk-band-fires facts at q0/q1.
  have hK1BP := SFormula.Deriv.mp (SFormula.Deriv.mp hBandK1 hBulkK1) hcol
  have hBB1_0 := SFormula.Deriv.andElimLeft hK1BP
  have hBB1_1 := SFormula.Deriv.andElimRight hK1BP
  -- k2 bulk-band-fires facts at q0/q1.
  have hK2BP := SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp hBandK2 hBulkK1) hcol) hadj
  have hBB2_0 := SFormula.Deriv.andElimLeft hK2BP
  have hBB2_1 := SFormula.Deriv.andElimRight hK2BP
  -- Row A = X at q0/q1 (X-bulk leaf), Row B = Z at q0/q1 (Z-bulk leaf).
  have hAX0 : SFormula.Deriv Γ (.eqPauli (.stabAt (rowA D) (SC.closed (bhlQ0 D))) (SC.p Pauli.X)) :=
    SFormula.Deriv.eqPauliTrans _ _ _ hEA0 (baseLeafXS (dP2 D) k1P (bhlQ0 D) hBulkK1 hBB1_0 hKindK1)
  have hAX1 : SFormula.Deriv Γ (.eqPauli (.stabAt (rowA D) (SC.closed (bhlQ1 D))) (SC.p Pauli.X)) :=
    SFormula.Deriv.eqPauliTrans _ _ _ hEA1 (baseLeafXS (dP2 D) k1P (bhlQ1 D) hBulkK1 hBB1_1 hKindK1)
  have hBZ0 : SFormula.Deriv Γ (.eqPauli (.stabAt (rowB D) (SC.closed (bhlQ0 D))) (SC.p Pauli.Z)) :=
    SFormula.Deriv.eqPauliTrans _ _ _ hEB0 (baseLeafZS (dP2 D) k2P (bhlQ0 D) hBulkK2 hBB2_0 hKindK2)
  have hBZ1 : SFormula.Deriv Γ (.eqPauli (.stabAt (rowB D) (SC.closed (bhlQ1 D))) (SC.p Pauli.Z)) :=
    SFormula.Deriv.eqPauliTrans _ _ _ hEB1 (baseLeafZS (dP2 D) k2P (bhlQ1 D) hBulkK2 hBB2_1 hKindK2)
  -- Assemble via the (generic) two-anti spine; the all-others pin handler closes overlap.
  refine commBulkTopXZ D (bhlQ0 D) (bhlQ1 D) hEntryA hEntryB hk1X hExcl1
    hLt0 hLt1 hNe hAX0 hAX1 hBZ0 hBZ1 ?_
  intro Δ' lift hLeafA hLeafB
  -- The class context + adj + both bulk facts, lifted into Δ'.
  have hBulkK1Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b true)) :=
    lift (cw3 (SFormula.Deriv.weakenFresh
      (A := .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true)) hBulkK1))
  have hBulkK2Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b true)) :=
    lift (cw3 (SFormula.Deriv.weakenFresh
      (A := .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true)) hBulkK2))
  have hcolΔ : SFormula.Deriv Δ' (.eqBool (SC.closed (.ltNat
      (.natLit 0) (.mod k1P3 (dm1TA (dP3 D))))) (SC.b true)) :=
    lift (cw3 (SFormula.Deriv.weakenFresh (A := bhlColF D) hcol))
  have hadjΔ : SFormula.Deriv Δ'
      (.eqBool (SC.closed (.eqNat k2P3 (.sub k1P3 (.natLit 1)))) (SC.b true)) :=
    lift (cw3 (SFormula.Deriv.weakenFresh (A := bhlAdjF D) hadj))
  have hPinΔ : SFormula.Deriv Δ' (bhlPinF D).weaken :=
    lift (cw3 (SFormula.Deriv.weakenFresh (A := bhlPinF D) hPin))
  have hq : SFormula.Deriv Δ' (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken) :=
    lift (.hyp (by right; right; exact List.mem_cons_self))
  -- Recover the bulk-band-fired facts at boundNat from the leaves.
  have hBandK1B := bhlBandK1FromX D hBulkK1Δ hLeafA
  have hBandK2B := bhlBandK2FromZ D hBulkK2Δ hLeafB
  -- The pin: boundNat ∈ {q0, q1}.
  have hdisj := bhlPinAt D hPinΔ hq hBulkK1Δ hcolΔ hadjΔ hBandK1B hBandK2B
  -- The two exclusions in the handler context, lifted into Δ'.
  have hne0 : SFormula.Deriv Δ'
      (.not (.eqNat SFormula.boundNat (SC.closed (bhlQ0 D)).weaken)) :=
    lift (.hyp (by right; exact List.mem_cons_self))
  have hne1 : SFormula.Deriv Δ'
      (.not (.eqNat SFormula.boundNat (SC.closed (bhlQ1 D)).weaken)) :=
    lift (.hyp List.mem_cons_self)
  have hne0' : SFormula.Deriv Δ'
      (.not (.eqNat SFormula.boundNat (SC.closed (bhlQ0_3 D)))) := hne0
  have hne1' : SFormula.Deriv Δ'
      (.not (.eqNat SFormula.boundNat (SC.closed (bhlQ1_3 D)))) := hne1
  refine SFormula.Deriv.orElim hdisj ?_ ?_
  · exact SFormula.Deriv.botElim (SFormula.Deriv.notElim .assumption (cw1 hne0'))
  · exact SFormula.Deriv.botElim (SFormula.Deriv.notElim .assumption (cw1 hne1'))

#print axioms bhlRangePack
#print axioms bhlBandK1Pack
#print axioms bhlBandK2Pack
#print axioms bhlPinPack
#print axioms bhlPinAt
#print axioms bhlBandK1FromX
#print axioms bhlBandK2FromZ
#print axioms commBulkBulkHorizL

/-! ## Bulk–Bulk overlap class (vertical edge-adjacency, UP)

The MIRROR of `commBulkBulkVert`: BOTH rows are bulk plaquettes.  Row A (`k1`) is the
X-type bulk plaquette at grid `(r1, c1)`; row B (`k2 = k1-(d-1)`) is the Z-type bulk
plaquette ONE ROW ABOVE it, at grid `(r1-1, c1)` (same grid column).  They overlap at
exactly the two qubits of their shared HORIZONTAL edge — the TOP edge of `k1`'s stencil
(row `r1`, columns `c1`, `c1+1`): `q0 = d·r1 + c1`, `q1 = d·r1 + (c1+1)`.

DEVIATIONS FROM THE BULK–BULK-VERT TEMPLATE.
* `k2 = k1 - (d-1)` (one grid ROW above) instead of `k1 + (d-1)`.
* The shared row is `r1` (the TOP edge) instead of `r1+1` (the BOTTOM edge).
* Validity guard `hrow` is `0 < r1` (so `k1-(d-1)` is a valid bulk plaquette in row
  `r1-1`, with `cellR(k1-(d-1)) = r1-1`), instead of `r1+1 < d-1`.
* SWAPPED overlap-lemma roles for the range pack: `overlap_bulk_bulk_vert_range` takes
  `(d, r, c)` and emits `q0 = d·(r+1)+c`, `q1 = d·(r+1)+(c+1)`.  We invoke it at
  `r := r1-1` (OUR k2's row), so its emitted `q0 = d·((r1-1)+1)+c1 = d·r1+c1 = our q0`,
  matching OUR forms (since `r1 ≥ 1`).  The pin pack proves the joint disjunction directly.
* The k1-band row antecedent is `{r1, r1+1}`, the k2-band row antecedent is `{r1-1, r1}`;
  jointly `q/d = r1` (the TOP shared edge). -/

/-- Cell row of `k1` (arity 2): `r1 = k1/(d-1)`. -/
abbrev bvuR1 (D : OddSurfaceDistance) : Term 2 .nat := .div k1P (dm1TA (dP2 D))
/-- Cell col of `k1` (arity 2): `c1 = k1%(d-1)`. -/
abbrev bvuC1 (D : OddSurfaceDistance) : Term 2 .nat := .mod k1P (dm1TA (dP2 D))
/-- Overlap qubit `q0 = d·r1 + c1` (row `r1`, column `c1`). -/
abbrev bvuQ0 (D : OddSurfaceDistance) : Term 2 .nat :=
  .add (.mul (dP2 D) (bvuR1 D)) (bvuC1 D)
/-- Overlap qubit `q1 = d·r1 + (c1+1)` (row `r1`, column `c1+1`). -/
abbrev bvuQ1 (D : OddSurfaceDistance) : Term 2 .nat :=
  .add (.mul (dP2 D) (bvuR1 D)) (.add (bvuC1 D) (.natLit 1))

/-- Prev-row validity guard: `0 < r1` (so `k2 = k1-(d-1)` is a valid bulk plaquette in
the row above).  True geometric fact, supplied by the dispatcher. -/
abbrev bvuRowF (D : OddSurfaceDistance) : SFormula 2 :=
  .eqBool (SC.closed (.ltNat (.natLit 0) (.div k1P (dm1TA (dP2 D))))) (SC.b true)

abbrev bvuRangePackF (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true))
    (.imp (bvuRowF D)
      (.and (SFormula.witnessLt (SC.closed (bvuQ0 D)) (nP2 D))
        (.and (SFormula.witnessLt (SC.closed (bvuQ1 D)) (nP2 D))
          (.eqBool (SC.closed (.eqNat (bvuQ0 D) (bvuQ1 D))) (SC.b false)))))

/-- Bulk–Bulk-vertU range pack: under `bulk(k1)` and the prev-row validity bound `0<r1`,
the overlap qubits `q0 = d·r1+c1`, `q1 = d·r1+(c1+1)` are in range and distinct.
Discharged by `arithBool` whose eval-certificate invokes `overlap_bulk_bulk_vert_range`
applied at row `r1-1` (SWAPPED role: OUR k2's row). -/
def bvuRangePack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (bvuRangePackF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd3 : D.distance = 2 * D.index + 3 := rfl
  simp only [bvuRangePackF, bvuRowF, bvuQ0, bvuQ1, bvuR1, bvuC1, bulkGuardTA, bulkCountTA, dm1TA,
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
    by_cases hrow : 0 < r1
    · have hrt : decide (decide (0 < r1) = true) = true := by
        rw [decide_eq_true_eq]; simp [hrow]
      simp only [hbt, hrt, if_true]
      have hr1d : (r1 - 1) + 1 < d := by omega
      have hc1d : c1 + 1 < d := by omega
      obtain ⟨hne, hlt0, hlt1⟩ := overlap_bulk_bulk_vert_range d (r1 - 1) c1 (by omega) hr1d hc1d
      -- rewrite (r1-1)+1 = r1 in the emitted facts.
      have hrr : (r1 - 1) + 1 = r1 := by omega
      rw [hrr] at hne hlt0 hlt1
      have e0 : decide (decide (d * r1 + c1 < d * d) = true) = true := by
        rw [decide_eq_true_eq, decide_eq_true_eq]; exact hlt0
      have e1 : decide (decide (d * r1 + (c1 + 1) < d * d) = true) = true := by
        rw [decide_eq_true_eq, decide_eq_true_eq]; exact hlt1
      have ene : decide (decide (d * r1 + c1 = d * r1 + (c1 + 1)) = false) = true := by
        rw [decide_eq_true_eq, decide_eq_false_iff_not]; exact hne
      simp only [e0, e1, ene, decide_true, if_true]
    · have hrf : decide (decide (0 < r1) = true) = false := by
        rw [decide_eq_false_iff_not]; simp [hrow]
      simp only [hbt, hrf, Bool.false_eq_true, if_false, reduceIte]
  · have hbf : decide (decide (k < (d - 1) * (d - 1)) = true) = false := by
      rw [decide_eq_false_iff_not]; simp [hbulk]
    simp only [hbf, Bool.false_eq_true, if_false, reduceIte]

abbrev bvuBandK1PackF (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true))
    (.imp (bvuRowF D)
      (.and (.eqBool (SC.closed (baseBulkBandGuardTA (dP2 D) k1P (bvuQ0 D))) (SC.b true))
        (.eqBool (SC.closed (baseBulkBandGuardTA (dP2 D) k1P (bvuQ1 D))) (SC.b true))))

/-- Bulk–Bulk-vertU band pack for `k1`: under `bulk(k1)` and `0<r1`, the X-bulk plaquette
band of `k1` (grid `(r1,c1)`) fires at both overlap qubits `q0 = d·r1+c1`,
`q1 = d·r1+(c1+1)` (its TOP-row pair, row `r1`, columns `c1`, `c1+1`). -/
def bvuBandK1Pack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (bvuBandK1PackF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd3 : D.distance = 2 * D.index + 3 := rfl
  simp only [bvuBandK1PackF, bvuRowF, bvuQ0, bvuQ1, bvuR1, bvuC1, bulkGuardTA, baseBulkBandGuardTA,
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
    by_cases hrow : 0 < r1
    · have hrt : decide (decide (0 < r1) = true) = true := by
        rw [decide_eq_true_eq]; simp [hrow]
      simp only [hbt, hrt, if_true]
      have hc1d : c1 + 1 < d := by omega
      have hr1d : r1 < d := by omega
      -- div/mod of q0, q1 (row r1; columns c1, c1+1).
      have hq0d : (d * r1 + c1) / d = r1 := by
        have e : d * r1 + c1 = c1 + r1 * d := by rw [Nat.mul_comm d r1]; omega
        rw [e, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega)]; omega
      have hq0m : (d * r1 + c1) % d = c1 := by
        have e : d * r1 + c1 = c1 + r1 * d := by rw [Nat.mul_comm d r1]; omega
        rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      have hq1d : (d * r1 + (c1 + 1)) / d = r1 := by
        have e : d * r1 + (c1 + 1) = (c1 + 1) + r1 * d := by rw [Nat.mul_comm d r1]; omega
        rw [e, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc1d]; omega
      have hq1m : (d * r1 + (c1 + 1)) % d = c1 + 1 := by
        have e : d * r1 + (c1 + 1) = (c1 + 1) + r1 * d := by rw [Nat.mul_comm d r1]; omega
        rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc1d]
      have hbk1d : decide (k < (d - 1) * (d - 1)) = true := by
        rw [decide_eq_true_eq]; exact hbulk
      rw [hq0d, hq0m, hq1d, hq1m, hbk1d]
      -- bulk-band: row {r1,r1+1} ∋ r1 (the eq branch); col {c1,c1+1} ∋ c1, c1+1.
      simp
    · have hrf : decide (decide (0 < r1) = true) = false := by
        rw [decide_eq_false_iff_not]; simp [hrow]
      simp only [hbt, hrf, Bool.false_eq_true, if_false, reduceIte]
  · have hbf : decide (decide (k < (d - 1) * (d - 1)) = true) = false := by
      rw [decide_eq_false_iff_not]; simp [hbulk]
    simp only [hbf, Bool.false_eq_true, if_false, reduceIte]

/-- Adjacency condition for the bulk–bulk-vertU class: `k2 = k1 - (d-1)` (vertical
neighbour, one bulk row above, same column). -/
abbrev bvuAdjF (D : OddSurfaceDistance) : SFormula 2 :=
  .eqBool (SC.closed (.eqNat k2P (.sub k1P (dm1TA (dP2 D))))) (SC.b true)

abbrev bvuBandK2PackF (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true))
    (.imp (bvuRowF D)
      (.imp (bvuAdjF D)
        (.and (.eqBool (SC.closed (baseBulkBandGuardTA (dP2 D) k2P (bvuQ0 D))) (SC.b true))
          (.eqBool (SC.closed (baseBulkBandGuardTA (dP2 D) k2P (bvuQ1 D))) (SC.b true)))))

/-- Bulk–Bulk-vertU band pack for `k2`: under `bulk(k1)`, `0<r1`, and the adjacency
`k2 = k1-(d-1)`, the Z-bulk plaquette band of `k2` (grid `(r1-1,c1)`, since
`(k1-(d-1))/(d-1)=r1-1` and `(k1-(d-1))%(d-1)=c1` when `0<r1`) fires at both overlap
qubits `q0`, `q1` (its BOTTOM-row pair, row `r1`, columns `c1`, `c1+1`). -/
def bvuBandK2Pack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (bvuBandK2PackF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd3 : D.distance = 2 * D.index + 3 := rfl
  simp only [bvuBandK2PackF, bvuRowF, bvuAdjF, bvuQ0, bvuQ1, bvuR1, bvuC1, bulkGuardTA,
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
    by_cases hrow : 0 < r1
    · have hrt : decide (decide (0 < r1) = true) = true := by
        rw [decide_eq_true_eq]; simp [hrow]
      by_cases hadj : k2 = k1 - (d - 1)
      · have hat : decide (decide (k2 = k1 - (d - 1)) = true) = true := by
          rw [decide_eq_true_eq]; simp [hadj]
        simp only [hbt, hrt, hat, if_true]
        have hc1d : c1 + 1 < d := by omega
        have hr1d : r1 < d := by omega
        -- coordinates of k2 = k1-(d-1): (k1-(d-1))/(d-1)=r1-1, (k1-(d-1))%(d-1)=c1.
        -- `r1·(d-1) = (r1-1)·(d-1) + (d-1)` since `r1 ≥ 1` (via `Nat.succ_mul`).
        have hsm : r1 * (d - 1) = (r1 - 1) * (d - 1) + (d - 1) := by
          conv_lhs => rw [show r1 = (r1 - 1) + 1 by omega]
          rw [Nat.succ_mul]
        have hk2d : k2 / (d - 1) = r1 - 1 := by
          rw [hadj, hkdm]
          have e : r1 * (d - 1) + c1 - (d - 1) = c1 + (r1 - 1) * (d - 1) := by omega
          rw [e, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc1lt]; omega
        have hk2m : k2 % (d - 1) = c1 := by
          rw [hadj, hkdm]
          have e : r1 * (d - 1) + c1 - (d - 1) = c1 + (r1 - 1) * (d - 1) := by omega
          rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc1lt]
        -- k2 < bulkCount (since k2 = k1 - (d-1) ≤ k1 < bulkCount).
        have hbulkk2 : k2 < (d - 1) * (d - 1) := by rw [hadj]; omega
        have hbk2d : decide (k2 < (d - 1) * (d - 1)) = true := by
          rw [decide_eq_true_eq]; exact hbulkk2
        -- div/mod of q0, q1 (row r1).
        have hq0d : (d * r1 + c1) / d = r1 := by
          have e : d * r1 + c1 = c1 + r1 * d := by rw [Nat.mul_comm d r1]; omega
          rw [e, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega)]; omega
        have hq0m : (d * r1 + c1) % d = c1 := by
          have e : d * r1 + c1 = c1 + r1 * d := by rw [Nat.mul_comm d r1]; omega
          rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
        have hq1d : (d * r1 + (c1 + 1)) / d = r1 := by
          have e : d * r1 + (c1 + 1) = (c1 + 1) + r1 * d := by rw [Nat.mul_comm d r1]; omega
          rw [e, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc1d]; omega
        have hq1m : (d * r1 + (c1 + 1)) % d = c1 + 1 := by
          have e : d * r1 + (c1 + 1) = (c1 + 1) + r1 * d := by rw [Nat.mul_comm d r1]; omega
          rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc1d]
        rw [hk2d, hk2m, hq0d, hq0m, hq1d, hq1m, hbk2d]
        -- bulk-band of k2 (row {r1-1, r1} ∋ r1 the succ branch; col {c1,c1+1}).
        have hrsucc : (r1 - 1) + 1 = r1 := by omega
        have hrowne : ¬ (r1 = r1 - 1) := by omega
        simp [hrsucc, hrowne]
      · have haf : decide (decide (k2 = k1 - (d - 1)) = true) = false := by
          rw [decide_eq_false_iff_not]; simp [hadj]
        simp only [hbt, hrt, haf, Bool.false_eq_true, if_false, reduceIte]
    · have hrf : decide (decide (0 < r1) = true) = false := by
        rw [decide_eq_false_iff_not]; simp [hrow]
      simp only [hbt, hrf, Bool.false_eq_true, if_false, reduceIte]
  · have hbf : decide (decide (k1 < (d - 1) * (d - 1)) = true) = false := by
      rw [decide_eq_false_iff_not]; simp [hbulk]
    simp only [hbf, Bool.false_eq_true, if_false, reduceIte]

/-! ### Bulk–Bulk-vertU class: the all-others joint pin -/

/-- Arity-3 cell row of `k1` (`= (bvuR1 D).weaken`). -/
abbrev bvuR1_3 (D : OddSurfaceDistance) : Term 3 .nat := .div k1P3 (dm1TA (dP3 D))
/-- Arity-3 cell col of `k1` (`= (bvuC1 D).weaken`). -/
abbrev bvuC1_3 (D : OddSurfaceDistance) : Term 3 .nat := .mod k1P3 (dm1TA (dP3 D))
/-- Arity-3 overlap qubit `q0` (`= (bvuQ0 D).weaken`). -/
abbrev bvuQ0_3 (D : OddSurfaceDistance) : Term 3 .nat :=
  .add (.mul (dP3 D) (bvuR1_3 D)) (bvuC1_3 D)
/-- Arity-3 overlap qubit `q1` (`= (bvuQ1 D).weaken`). -/
abbrev bvuQ1_3 (D : OddSurfaceDistance) : Term 3 .nat :=
  .add (.mul (dP3 D) (bvuR1_3 D)) (.add (bvuC1_3 D) (.natLit 1))

theorem bvuQ0_weaken (D : OddSurfaceDistance) : (bvuQ0 D).weaken = bvuQ0_3 D := rfl
theorem bvuQ1_weaken (D : OddSurfaceDistance) : (bvuQ1 D).weaken = bvuQ1_3 D := rfl

/-- The bulk–bulk-vertU joint pin body (arity 3, `k1 = var 2`, `k2 = var 1`, `q = var 0`):
under the class context and the two bulk-band-fired facts, `q ∈ {q0, q1}`. -/
abbrev bvuPinBody (D : OddSurfaceDistance) : SFormula 3 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b true))
    (.imp (.eqBool (SC.closed (.ltNat (.natLit 0) (.div k1P3 (dm1TA (dP3 D))))) (SC.b true))
      (.imp (.eqBool (SC.closed (.eqNat k2P3 (.sub k1P3 (dm1TA (dP3 D))))) (SC.b true))
        (.imp (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true))
          (.imp (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))
            (.or (.eqNat SFormula.boundNat (SC.closed (bvuQ0_3 D)))
              (.eqNat SFormula.boundNat (SC.closed (bvuQ1_3 D))))))))

abbrev bvuPinF (D : OddSurfaceDistance) : SFormula 2 :=
  .allNatLt (nP2 D) (bvuPinBody D)

/-- Bulk–Bulk-vertU joint pin pack: under the class context, every shared non-`I` slot
is one of the two overlap qubits.  `arithBool`, proven directly (joint row is `r1`). -/
def bvuPinPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (bvuPinF D) := by
  refine PureFamilyDerivA.allNatLtIntro _ ?_
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd3 : D.distance = 2 * D.index + 3 := rfl
  simp only [bvuPinBody, bvuQ0_3, bvuQ1_3, bvuR1_3, bvuC1_3, bulkGuardTA, baseBulkBandGuardTA,
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
    by_cases hrow : 0 < r1
    · have hrt : decide (decide (0 < r1) = true) = true := by
        rw [decide_eq_true_eq]; simp [hrow]
      by_cases hadj : k2 = k1 - (d - 1)
      · have hat : decide (decide (k2 = k1 - (d - 1)) = true) = true := by
          rw [decide_eq_true_eq]; simp [hadj]
        simp only [hbt, hrt, hat, if_true]
        have hc1d : c1 + 1 < d := by omega
        -- coordinates of k2 = k1-(d-1).
        have hsm : r1 * (d - 1) = (r1 - 1) * (d - 1) + (d - 1) := by
          conv_lhs => rw [show r1 = (r1 - 1) + 1 by omega]
          rw [Nat.succ_mul]
        have hk2d : k2 / (d - 1) = r1 - 1 := by
          rw [hadj, hkdm]
          have e : r1 * (d - 1) + c1 - (d - 1) = c1 + (r1 - 1) * (d - 1) := by omega
          rw [e, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc1lt]; omega
        have hk2m : k2 % (d - 1) = c1 := by
          rw [hadj, hkdm]
          have e : r1 * (d - 1) + c1 - (d - 1) = c1 + (r1 - 1) * (d - 1) := by omega
          rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc1lt]
        -- The two bulk-band antecedents share the col guard `q%d ∈ {c1,c1+1}`; case on
        -- it FIRST, then the row.  k1-band needs q/d∈{r1,r1+1}; k2-band needs
        -- q/d∈{r1-1,r1}; jointly q/d = r1.
        rw [hk2d, hk2m]
        have hrsucc : (r1 - 1) + 1 = r1 := by omega
        by_cases hqcol : q % d = c1 ∨ q % d = c1 + 1
        · by_cases hqrow : q / d = r1
          · -- both bands fire; q = d·r1 + (q%d) ∈ {q0, q1}.
            have hqval : q = d * r1 + q % d := by
              have hdm := Nat.div_add_mod q d
              rw [hqrow] at hdm; omega
            rcases hqcol with hc | hc
            · -- q%d = c1 → q = q0.
              have hqe : q = d * r1 + c1 := by rw [hqval, hc]
              rw [hqrow, hc, hrsucc]; simp [hqe]
            · -- q%d = c1+1 → q = q1.
              have hqe : q = d * r1 + (c1 + 1) := by rw [hqval, hc]
              have e0v : ¬ (q = d * r1 + c1) := by rw [hqe]; omega
              rw [hqrow, hc, hrsucc]; simp [hqe, e0v]
          · -- q/d ≠ r1.  Split to show at least one band fails everywhere.
            by_cases hqr1 : q / d = r1 - 1
            · -- q/d = r1-1: k1-band row {r1,r1+1} false (since r1-1 ≠ r1, r1-1 ≠ r1+1).
              have hne0 : ¬ (q / d = r1) := by omega
              have hne1 : ¬ (q / d = r1 + 1) := by omega
              rcases hqcol with hc | hc <;> simp [hc, hne0, hne1]
            · -- q/d ∉ {r1-1, r1}: k2-band row {r1-1,r1} false → k2-band fails.  The k1-band
              -- row {r1,r1+1} may fire (q/d=r1+1); split on it so both binds reduce.
              have hqr1' : ¬ (q / d = r1 - 1 + 1) := by omega
              by_cases hqr2 : q / d = r1 + 1
              · rcases hqcol with hc | hc <;>
                  simp [hc, hqr2, (show ¬ (r1 + 1 = r1 - 1) by omega),
                    (show ¬ (r1 = r1 - 1) by omega)]
              · rcases hqcol with hc | hc <;> simp [hc, hqr2, hqrow, hqr1']
        · -- q%d ∉ {c1, c1+1}: both band col antecedents false → both bands false → vacuous.
          push_neg at hqcol
          obtain ⟨hc0, hc1'⟩ := hqcol
          by_cases hqr : q / d = r1 <;> by_cases hqrm : q / d = r1 - 1 <;>
            simp [hc0, hc1', hqr, hqrm, (show ¬ (r1 - 1 = r1) by omega)]
      · have haf : decide (decide (k2 = k1 - (d - 1)) = true) = false := by
          rw [decide_eq_false_iff_not]; simp [hadj]
        simp only [hbt, hrt, haf, Bool.false_eq_true, if_false, reduceIte]
    · have hrf : decide (decide (0 < r1) = true) = false := by
        rw [decide_eq_false_iff_not]; simp [hrow]
      simp only [hbt, hrf, Bool.false_eq_true, if_false, reduceIte]
  · have hbf : decide (decide (k1 < (d - 1) * (d - 1)) = true) = false := by
      rw [decide_eq_false_iff_not]; simp [hbulk]
    simp only [hbf, Bool.false_eq_true, if_false, reduceIte]

/-- Extract the bulk–bulk-vertU joint-pin disjunction at `boundNat`. -/
def bvuPinAt {Δ : List (SFormula 3)} (D : OddSurfaceDistance)
    (hW : SFormula.Deriv Δ (bvuPinF D).weaken)
    (hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken))
    (hBulkK1 : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b true)))
    (hRow : SFormula.Deriv Δ (.eqBool (SC.closed (.ltNat
      (.natLit 0) (.div k1P3 (dm1TA (dP3 D))))) (SC.b true)))
    (hAdj : SFormula.Deriv Δ
      (.eqBool (SC.closed (.eqNat k2P3 (.sub k1P3 (dm1TA (dP3 D))))) (SC.b true)))
    (hBandK1 : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true)))
    (hBandK2 : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))) :
    SFormula.Deriv Δ
      (.or (.eqNat SFormula.boundNat (SC.closed (bvuQ0_3 D)))
        (.eqNat SFormula.boundNat (SC.closed (bvuQ1_3 D)))) := by
  have hElim := SFormula.Deriv.allNatLtElim (nP2 D).weaken
    ((bvuPinBody D).lift 1) SFormula.boundNat hW hq
  have hBody := SFormula.Deriv.applyNatBoundNatBeta (bvuPinBody D) hElim
  exact SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp
    (SFormula.Deriv.mp hBody hBulkK1) hRow) hAdj) hBandK1) hBandK2

/-! ### Bulk–Bulk-vertU class: reverse-leaf band recovery (both via `baseLeafBulkIS`) -/

/-- Recover `bulkBand(k1, q) = true` from `baseLeafTreeTA k1 q = X`, given `bulk(k1)`. -/
def bvuBandK1FromX {Δ : List (SFormula 3)} (D : OddSurfaceDistance)
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

/-- Recover `bulkBand(k2, q) = true` from `baseLeafTreeTA k2 q = Z`, given `bulk(k2)`. -/
def bvuBandK2FromZ {Δ : List (SFormula 3)} (D : OddSurfaceDistance)
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

/-- **Bulk–Bulk overlap class closer (vertical edge-adjacency, UP).**  Mirror of
`commBulkBulkVert`: row A (`k1`) is the X-type bulk plaquette at `(r1,c1)`, row B
(`k2 = k1-(d-1)`) is the Z-type bulk plaquette ONE ROW ABOVE it at `(r1-1,c1)`.  They
overlap at the two qubits of `k1`'s TOP edge `q0 = d·r1+c1`, `q1 = d·r1+(c1+1)`. -/
def commBulkBulkVertU {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hEntryA : SFormula.Deriv Γ (entryAQuant D)) (hEntryB : SFormula.Deriv Γ (entryBQuant D))
    (hk1X : SFormula.Deriv Γ (k1IsX D true)) (hExcl1 : SFormula.Deriv Γ (typeExclF D k1P))
    (hBulkK1 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true)))
    (hKindK1 : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k1P)) (SC.b false)))
    (hBulkK2 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true)))
    (hKindK2 : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k2P)) (SC.b true)))
    (hadj : SFormula.Deriv Γ (bvuAdjF D))
    (hrow : SFormula.Deriv Γ (bvuRowF D))
    (hRange : SFormula.Deriv Γ (bvuRangePackF D))
    (hBandK1 : SFormula.Deriv Γ (bvuBandK1PackF D))
    (hBandK2 : SFormula.Deriv Γ (bvuBandK2PackF D))
    (hPin : SFormula.Deriv Γ (bvuPinF D))
    (hEA0 : SFormula.Deriv Γ (entryAAtQF D (bvuQ0 D)))
    (hEA1 : SFormula.Deriv Γ (entryAAtQF D (bvuQ1 D)))
    (hEB0 : SFormula.Deriv Γ (entryBAtQF D (bvuQ0 D)))
    (hEB1 : SFormula.Deriv Γ (entryBAtQF D (bvuQ1 D))) :
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
  have hAX0 : SFormula.Deriv Γ (.eqPauli (.stabAt (rowA D) (SC.closed (bvuQ0 D))) (SC.p Pauli.X)) :=
    SFormula.Deriv.eqPauliTrans _ _ _ hEA0 (baseLeafXS (dP2 D) k1P (bvuQ0 D) hBulkK1 hBB1_0 hKindK1)
  have hAX1 : SFormula.Deriv Γ (.eqPauli (.stabAt (rowA D) (SC.closed (bvuQ1 D))) (SC.p Pauli.X)) :=
    SFormula.Deriv.eqPauliTrans _ _ _ hEA1 (baseLeafXS (dP2 D) k1P (bvuQ1 D) hBulkK1 hBB1_1 hKindK1)
  have hBZ0 : SFormula.Deriv Γ (.eqPauli (.stabAt (rowB D) (SC.closed (bvuQ0 D))) (SC.p Pauli.Z)) :=
    SFormula.Deriv.eqPauliTrans _ _ _ hEB0 (baseLeafZS (dP2 D) k2P (bvuQ0 D) hBulkK2 hBB2_0 hKindK2)
  have hBZ1 : SFormula.Deriv Γ (.eqPauli (.stabAt (rowB D) (SC.closed (bvuQ1 D))) (SC.p Pauli.Z)) :=
    SFormula.Deriv.eqPauliTrans _ _ _ hEB1 (baseLeafZS (dP2 D) k2P (bvuQ1 D) hBulkK2 hBB2_1 hKindK2)
  -- Assemble via the (generic) two-anti spine; the all-others pin handler closes overlap.
  refine commBulkTopXZ D (bvuQ0 D) (bvuQ1 D) hEntryA hEntryB hk1X hExcl1
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
      (.natLit 0) (.div k1P3 (dm1TA (dP3 D))))) (SC.b true)) :=
    lift (cw3 (SFormula.Deriv.weakenFresh (A := bvuRowF D) hrow))
  have hadjΔ : SFormula.Deriv Δ'
      (.eqBool (SC.closed (.eqNat k2P3 (.sub k1P3 (dm1TA (dP3 D))))) (SC.b true)) :=
    lift (cw3 (SFormula.Deriv.weakenFresh (A := bvuAdjF D) hadj))
  have hPinΔ : SFormula.Deriv Δ' (bvuPinF D).weaken :=
    lift (cw3 (SFormula.Deriv.weakenFresh (A := bvuPinF D) hPin))
  have hq : SFormula.Deriv Δ' (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken) :=
    lift (.hyp (by right; right; exact List.mem_cons_self))
  -- Recover the bulk-band-fired facts at boundNat from the leaves.
  have hBandK1B := bvuBandK1FromX D hBulkK1Δ hLeafA
  have hBandK2B := bvuBandK2FromZ D hBulkK2Δ hLeafB
  -- The pin: boundNat ∈ {q0, q1}.
  have hdisj := bvuPinAt D hPinΔ hq hBulkK1Δ hrowΔ hadjΔ hBandK1B hBandK2B
  -- The two exclusions in the handler context, lifted into Δ'.
  have hne0 : SFormula.Deriv Δ'
      (.not (.eqNat SFormula.boundNat (SC.closed (bvuQ0 D)).weaken)) :=
    lift (.hyp (by right; exact List.mem_cons_self))
  have hne1 : SFormula.Deriv Δ'
      (.not (.eqNat SFormula.boundNat (SC.closed (bvuQ1 D)).weaken)) :=
    lift (.hyp List.mem_cons_self)
  have hne0' : SFormula.Deriv Δ'
      (.not (.eqNat SFormula.boundNat (SC.closed (bvuQ0_3 D)))) := hne0
  have hne1' : SFormula.Deriv Δ'
      (.not (.eqNat SFormula.boundNat (SC.closed (bvuQ1_3 D)))) := hne1
  refine SFormula.Deriv.orElim hdisj ?_ ?_
  · exact SFormula.Deriv.botElim (SFormula.Deriv.notElim .assumption (cw1 hne0'))
  · exact SFormula.Deriv.botElim (SFormula.Deriv.notElim .assumption (cw1 hne1'))

#print axioms bvuRangePack
#print axioms bvuBandK1Pack
#print axioms bvuBandK2Pack
#print axioms bvuPinPack
#print axioms bvuPinAt
#print axioms bvuBandK1FromX
#print axioms bvuBandK2FromZ
#print axioms commBulkBulkVertU

end QHL.CodeLang.Surface.Verify
