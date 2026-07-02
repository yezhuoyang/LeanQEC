import QStab.QHL.Verify.SurfaceRowsCommute.TypeClosers

/-!
# Rows-commute (pairwise generated-row commutation) — BulkTop

The Bulk–Top overlap class: overlap qubits + range pack, the all-others joint pin, and the
reverse-leaf band recovery + joint-pin handler.
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface

set_option maxRecDepth 65536
set_option linter.unusedVariables false

/-! ## Bulk–Top overlap class (the simplest overlap case)

The single-class closer for the **bulk–top** overlap: row A (`k1 = recCall k1`) is
the X-type top-boundary stabilizer, row B (`k2 = recCall k2`) is the Z-type bulk
plaquette sitting at top row `r = 0`, adjacent to the top check.  They overlap at
exactly the two qubits `q0 = 2·b`, `q1 = 2·b + 1` (with `b = k1 - (d-1)²` the top
boundary index of `k1`), both in grid row 0.

The Nat geometry of this overlap is the proven `overlap_bulk_top` /
`overlap_top_range` (in `SurfaceRowOverlapNat.lean`): the shared non-`I` slots are
exactly `{2b, 2b+1}` and these two qubits are distinct, in range.  This lemma is
the *object-logic* assembly: it plumbs the per-class arithmetic facts (`q0`/`q1`
range + distinctness, the `X`-resolution of row A and the `Z`-resolution of row B
at `q0`/`q1`, and the all-others pin) into the proven two-anti spine
`commTwoAntiXZ` + `twoAntiRestXZ`.  It is the direct two-generated-row analogue of
`commTwoAntiB` in `SurfaceNormalizers.lean`.

The five remaining overlap classes (bulk–right, bulk–left, bulk–bottom, and the two
bulk–bulk edge-adjacencies) follow this exact template, swapping in
`overlap_bulk_right` / `overlap_bulk_left` / `overlap_bulk_bottom` /
`overlap_bulk_bulk_{horiz,vert}` and their `*_range` lemmas, and the matching band
guards for the Z-type row's leaf (right/left bulk-band etc.). -/

/-- **Bulk–Top overlap class closer.**  Row A is the X-type top-boundary stabilizer,
row B the Z-type bulk plaquette at the adjacent top row; they overlap at the two
qubits `q0`, `q1` of the shared top edge.  Given the verified overlap geometry as
the assembler-level facts — `q0`/`q1` in range and distinct, row A resolving to `X`
and row B to `Z` at both `q0` and `q1`, and the all-others pin handler `hXZpin`
forcing every shared non-`I` slot into `{q0, q1}` — the two rows commute via the
proven two-anti spine `commTwoAntiXZ` + `twoAntiRestXZ`. -/
def commBulkTopXZ {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (q0 q1 : Term 2 .nat)
    (hEntryAF : SFormula.Deriv Γ (entryAQuant D))
    (hEntryBF : SFormula.Deriv Γ (entryBQuant D))
    (hk1X : SFormula.Deriv Γ (k1IsX D true))
    (hExcl1 : SFormula.Deriv Γ (typeExclF D k1P))
    (hLt0 : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed q0) (nP2 D)))
    (hLt1 : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed q1) (nP2 D)))
    (hNe : SFormula.Deriv Γ (.eqBool (SC.closed (.eqNat q0 q1)) (SC.b false)))
    (hAX0 : SFormula.Deriv Γ
      (.eqPauli (.stabAt (rowA D) (SC.closed q0)) (SC.p Pauli.X)))
    (hAX1 : SFormula.Deriv Γ
      (.eqPauli (.stabAt (rowA D) (SC.closed q1)) (SC.p Pauli.X)))
    (hBZ0 : SFormula.Deriv Γ
      (.eqPauli (.stabAt (rowB D) (SC.closed q0)) (SC.p Pauli.Z)))
    (hBZ1 : SFormula.Deriv Γ
      (.eqPauli (.stabAt (rowB D) (SC.closed q1)) (SC.p Pauli.Z)))
    (hXZpin : ∀ (Δ' : List (SFormula 3)),
      (∀ {A : SFormula 3}, SFormula.Deriv
        (.not (.eqNat SFormula.boundNat (SC.closed q1).weaken)
          :: .not (.eqNat SFormula.boundNat (SC.closed q0).weaken)
          :: SFormula.boundNatLt (nP2 D) :: List.map (fun G => G.weaken) Γ) A →
        SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3)) (SC.p Pauli.X)) →
      SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p Pauli.Z)) →
        SFormula.Deriv Δ' (lcGoalP D)) :
    SFormula.Deriv Γ (pairGoal D) :=
  commTwoAntiXZ D q0 q1 hLt0 hLt1 hNe hAX0 hAX1 hBZ0 hBZ1
    (twoAntiRestXZ D q0 q1 hEntryAF hEntryBF hk1X hExcl1 hXZpin)

/-! ### Bulk–Top class: the overlap qubits and their range pack

`k1` is the X-type top-boundary stabilizer (`¬bulk`, `topClass`, i.e.
`b = k1 - (d-1)² < half = (d-1)/2`).  Its top check covers grid row 0 columns
`{2b, 2b+1}`, so the overlap with the adjacent Z-type bulk plaquette is at
`q0 = 2b`, `q1 = 2b+1`.  The range pack discharges (under the top-class context)
that `q0, q1 < nQubits` and `q0 ≠ q1`, via the proven Nat lemma `overlap_top_range`. -/

abbrev btB (D : OddSurfaceDistance) : Term 2 .nat := baseBTA (dP2 D) k1P
abbrev btQ0 (D : OddSurfaceDistance) : Term 2 .nat := .mul (.natLit 2) (btB D)
abbrev btQ1 (D : OddSurfaceDistance) : Term 2 .nat :=
  .add (.mul (.natLit 2) (btB D)) (.natLit 1)

abbrev btRangePackF (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false))
    (.imp (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b true))
      (.and (SFormula.witnessLt (SC.closed (btQ0 D)) (nP2 D))
        (.and (SFormula.witnessLt (SC.closed (btQ1 D)) (nP2 D))
          (.eqBool (SC.closed (.eqNat (btQ0 D) (btQ1 D))) (SC.b false)))))

/-- Bulk–Top range pack: under `¬bulk ∧ topClass` for `k1`, the overlap qubits
`q0 = 2b`, `q1 = 2b+1` are in range and distinct.  Discharged by `arithBool` whose
eval-certificate invokes the proven `overlap_top_range`. -/
def btRangePack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (btRangePackF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd3 : D.distance = 2 * D.index + 3 := rfl
  simp only [btRangePackF, btQ0, btQ1, btB, bulkGuardTA, topClassGuardTA, baseBTA,
    baseHalfTA, bulkCountTA, dm1TA, dP2, nP2, SFormula.eval, SFormula.witnessLt,
    SC.closed, SC.b, SC.n, STerm.eval, Term.eval, Term.lift, bind, Option.bind,
    nQubits]
  set k := rho ⟨1, by decide⟩ with hk
  set d := D.distance with hdd
  have hdge : 3 ≤ d := by omega
  by_cases hbulk : k < (d - 1) * (d - 1)
  · -- bulk true → antecedent `bulk = false` is false → vacuous.
    have hb : decide (decide (k < (d - 1) * (d - 1)) = false) = false := by
      rw [decide_eq_false_iff_not]; simp [hbulk]
    simp only [hb, Bool.false_eq_true, if_false, reduceIte]
  · by_cases htop : k - (d - 1) * (d - 1) < (d - 1) / 2
    · -- the genuine top-class case.
      have hbf : decide (decide (k < (d - 1) * (d - 1)) = false) = true := by
        rw [decide_eq_true_eq]; simp [hbulk]
      have htf : decide (decide (k - (d - 1) * (d - 1) < (d - 1) / 2) = true) = true := by
        rw [decide_eq_true_eq]; simp [htop]
      simp only [hbf, htf, if_true]
      set b := k - (d - 1) * (d - 1) with hb
      have hb2 : 2 * b + 1 < d := by omega
      obtain ⟨hne, hlt0, hlt1⟩ := overlap_top_range d b (by omega) hb2
      have e0 : decide (decide (2 * b < d * d) = true) = true := by
        rw [decide_eq_true_eq, decide_eq_true_eq]; exact hlt0
      have e1 : decide (decide (2 * b + 1 < d * d) = true) = true := by
        rw [decide_eq_true_eq, decide_eq_true_eq]; exact hlt1
      have ene : decide (decide (2 * b = 2 * b + 1) = false) = true := by
        rw [decide_eq_true_eq, decide_eq_false_iff_not]; omega
      simp only [e0, e1, ene, decide_true, if_true]
    · -- topClass false → antecedent `topClass = true` is false → vacuous.
      have hbf : decide (decide (k < (d - 1) * (d - 1)) = false) = true := by
        rw [decide_eq_true_eq]; simp [hbulk]
      have htf : decide (decide (k - (d - 1) * (d - 1) < (d - 1) / 2) = true) = false := by
        rw [decide_eq_false_iff_not]; simp [htop]
      simp only [hbf, htf, Bool.false_eq_true, if_false, reduceIte]

abbrev btTopBandPackF (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false))
    (.imp (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b true))
      (.and (.eqBool (SC.closed (topBandGuardTA (dP2 D) k1P (btQ0 D))) (SC.b true))
        (.eqBool (SC.closed (topBandGuardTA (dP2 D) k1P (btQ1 D))) (SC.b true))))

/-- Bulk–Top band pack: under `¬bulk ∧ topClass` for `k1`, the top-X band of `k1`
fires at both overlap qubits `q0 = 2b`, `q1 = 2b+1` (both in grid row 0). -/
def btTopBandPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (btTopBandPackF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd3 : D.distance = 2 * D.index + 3 := rfl
  simp only [btTopBandPackF, btQ0, btQ1, btB, bulkGuardTA, topClassGuardTA, topBandGuardTA,
    baseBTA, baseHalfTA, bulkCountTA, dm1TA, band3, orEqSucc, dP2, SFormula.eval,
    SC.closed, SC.b, STerm.eval, Term.eval, Term.lift, bind, Option.bind]
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
      have htf : decide (decide (k - (d - 1) * (d - 1) < (d - 1) / 2) = true) = true := by
        rw [decide_eq_true_eq]; simp [htop]
      simp only [hbf, htf, if_true]
      set b := k - (d - 1) * (d - 1) with hb
      have hb2 : 2 * b + 1 < d := by omega
      have h2bd : 2 * b < d := by omega
      have hdiv0 : 2 * b / d = 0 := Nat.div_eq_of_lt h2bd
      have hmod0 : 2 * b % d = 2 * b := Nat.mod_eq_of_lt h2bd
      have hdiv1 : (2 * b + 1) / d = 0 := Nat.div_eq_of_lt hb2
      have hmod1 : (2 * b + 1) % d = 2 * b + 1 := Nat.mod_eq_of_lt hb2
      have hsq2 : (d - 1) * (d - 1) + 2 * (d - 1) = d * d - 1 := by
        have e1 : (d - 1) * (d - 1) + 2 * (d - 1) = (d - 1) * (d - 1) + (d - 1) * 2 := by
          rw [Nat.mul_comm 2 (d - 1)]
        have e2 : (d - 1) * (d - 1) + (d - 1) * 2 = (d - 1) * ((d - 1) + 2) := by
          rw [Nat.mul_add]
        have e3 : (d - 1) + 2 = d + 1 := by omega
        rw [e1, e2, e3, Nat.sub_mul, Nat.one_mul, Nat.mul_succ]; omega
      have hklt : k < d * d - 1 := by omega
      have hkltd : decide (k < d * d - 1) = true := by rw [decide_eq_true_eq]; exact hklt
      rw [hdiv0, hmod0, hdiv1, hmod1, hkltd]
      simp
    · have hbf : decide (decide (k < (d - 1) * (d - 1)) = false) = true := by
        rw [decide_eq_true_eq]; simp [hbulk]
      have htf : decide (decide (k - (d - 1) * (d - 1) < (d - 1) / 2) = true) = false := by
        rw [decide_eq_false_iff_not]; simp [htop]
      simp only [hbf, htf, Bool.false_eq_true, if_false, reduceIte]

/-- Adjacency condition for the bulk–top class: the Z-type bulk plaquette `k2` sits
at grid `(0, 2b)`, i.e. `k2 = 2b` (with `b = k1 - (d-1)²` the top index of `k1`). -/
abbrev btAdjF (D : OddSurfaceDistance) : SFormula 2 :=
  .eqBool (SC.closed (.eqNat k2P (.mul (.natLit 2) (btB D)))) (SC.b true)

abbrev btBulkBandPackF (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false))
    (.imp (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b true))
      (.imp (btAdjF D)
        (.and (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true))
          (.and (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k2P)) (SC.b true))
            (.and (.eqBool (SC.closed (baseBulkBandGuardTA (dP2 D) k2P (btQ0 D))) (SC.b true))
              (.eqBool (SC.closed (baseBulkBandGuardTA (dP2 D) k2P (btQ1 D))) (SC.b true)))))))

/-- Bulk–Top bulk-band pack: under the top context for `k1` and the adjacency
`k2 = 2b`, the Z-type bulk plaquette `k2` (grid `(0,2b)`) is in-bulk, Z-kind, and
its plaquette band contains both overlap qubits `q0 = 2b`, `q1 = 2b+1`. -/
def btBulkBandPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (btBulkBandPackF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd3 : D.distance = 2 * D.index + 3 := rfl
  simp only [btBulkBandPackF, btAdjF, btQ0, btQ1, btB, bulkGuardTA, topClassGuardTA,
    baseKindGuardTA, baseBulkBandGuardTA, baseBTA, baseHalfTA, bulkCountTA, dm1TA, band3,
    orEqSucc, dP2, SFormula.eval, SC.closed, SC.b, STerm.eval, Term.eval, Term.lift,
    bind, Option.bind]
  set k1 := rho ⟨1, by decide⟩ with hk1
  set k2 := rho ⟨0, by decide⟩ with hk2
  set d := D.distance with hdd
  have hdge : 3 ≤ d := by omega
  by_cases hbulk : k1 < (d - 1) * (d - 1)
  · have hb : decide (decide (k1 < (d - 1) * (d - 1)) = false) = false := by
      rw [decide_eq_false_iff_not]; simp [hbulk]
    simp only [hb, Bool.false_eq_true, if_false, reduceIte]
  · by_cases htop : k1 - (d - 1) * (d - 1) < (d - 1) / 2
    · set b := k1 - (d - 1) * (d - 1) with hb
      have hbf : decide (decide (k1 < (d - 1) * (d - 1)) = false) = true := by
        rw [decide_eq_true_eq]; simp [hbulk]
      have htf : decide (decide (b < (d - 1) / 2) = true) = true := by
        rw [decide_eq_true_eq]; simp [htop]
      by_cases hadj : k2 = 2 * b
      · have haf : decide (decide (k2 = 2 * b) = true) = true := by
          rw [decide_eq_true_eq]; simp [hadj]
        simp only [hbf, htf, haf, if_true]
        have h2bd1 : 2 * b < d - 1 := by omega
        have h2bd : 2 * b < d := by omega
        have hb2 : 2 * b + 1 < d := by omega
        have hbulkk2 : 2 * b < (d - 1) * (d - 1) := by
          have h1 : d - 1 ≤ (d - 1) * (d - 1) := Nat.le_mul_of_pos_left _ (by omega)
          omega
        have hkd0 : (2 * b) / (d - 1) = 0 := Nat.div_eq_of_lt h2bd1
        have hkm0 : (2 * b) % (d - 1) = 2 * b := Nat.mod_eq_of_lt h2bd1
        have hq0d : (2 * b) / d = 0 := Nat.div_eq_of_lt h2bd
        have hq0m : (2 * b) % d = 2 * b := Nat.mod_eq_of_lt h2bd
        have hq1d : (2 * b + 1) / d = 0 := Nat.div_eq_of_lt hb2
        have hq1m : (2 * b + 1) % d = 2 * b + 1 := Nat.mod_eq_of_lt hb2
        have hkind : (0 + 2 * b) % 2 = 0 := by omega
        have hbk2d : decide (2 * b < (d - 1) * (d - 1)) = true := by
          rw [decide_eq_true_eq]; exact hbulkk2
        rw [hadj, hkd0, hkm0, hq0d, hq0m, hq1d, hq1m, hkind, hbk2d]
        simp
      · have haf : decide (decide (k2 = 2 * b) = true) = false := by
          rw [decide_eq_false_iff_not]; simp [hadj]
        simp only [hbf, htf, haf, Bool.false_eq_true, if_false, reduceIte]
    · have hbf : decide (decide (k1 < (d - 1) * (d - 1)) = false) = true := by
        rw [decide_eq_true_eq]; simp [hbulk]
      have htf : decide (decide (k1 - (d - 1) * (d - 1) < (d - 1) / 2) = true) = false := by
        rw [decide_eq_false_iff_not]; simp [htop]
      simp only [hbf, htf, Bool.false_eq_true, if_false, reduceIte]

/-! ### Bulk–Top class: the all-others joint pin

The two-generated-row analogue of `classABulkZPin` in `SurfaceNormalizers`.  Under
the bulk–top class context (`¬bulk(k1) ∧ topClass(k1) ∧ k2 = 2b`), the verified
overlap geometry `overlap_bulk_top` (in `SurfaceRowOverlapNat.lean`, with `k1`/`k2`
roles SWAPPED: there `k1` is the bulk row, `k2` the top row — so we pass OUR `k2` as
its `k1` and OUR `k1` as its `k2`) forces every shared non-`I` slot into `{q0, q1}`.
The slot `q` is non-`I` for the X-type top row `k1` exactly when its top-X band
fires at `q`, and non-`I` for the Z-type bulk plaquette `k2` exactly when its bulk
band fires at `q`; under those two band-fired facts the disjunction `q = 2b ∨
q = 2b+1` holds.  Quantified over `q < nQubits`, discharged by `arithBool` whose
eval-certificate invokes `overlap_bulk_top`. -/

/-- Arity-3 top boundary index of `k1` (`= (btB D).weaken`). -/
abbrev btB3 (D : OddSurfaceDistance) : Term 3 .nat := baseBTA (dP3 D) k1P3
/-- Arity-3 overlap qubit `q0 = 2b` (`= (btQ0 D).weaken`). -/
abbrev btQ0_3 (D : OddSurfaceDistance) : Term 3 .nat := .mul (.natLit 2) (btB3 D)
/-- Arity-3 overlap qubit `q1 = 2b+1` (`= (btQ1 D).weaken`). -/
abbrev btQ1_3 (D : OddSurfaceDistance) : Term 3 .nat :=
  .add (.mul (.natLit 2) (btB3 D)) (.natLit 1)

theorem btQ0_weaken (D : OddSurfaceDistance) : (btQ0 D).weaken = btQ0_3 D := rfl
theorem btQ1_weaken (D : OddSurfaceDistance) : (btQ1 D).weaken = btQ1_3 D := rfl

/-- The bulk–top joint pin body (arity 3, `k1 = var 2`, `k2 = var 1`, `q = var 0`):
under the class context and the two band-fired facts, `q ∈ {q0, q1}`. -/
abbrev btPinBody (D : OddSurfaceDistance) : SFormula 3 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b false))
    (.imp (.eqBool (SC.closed (topClassGuardTA (dP3 D) k1P3)) (SC.b true))
      (.imp (.eqBool (SC.closed (.eqNat k2P3 (.mul (.natLit 2) (btB3 D)))) (SC.b true))
        (.imp (.eqBool (SC.closed (topBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true))
          (.imp (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))
            (.or (.eqNat SFormula.boundNat (SC.closed (btQ0_3 D)))
              (.eqNat SFormula.boundNat (SC.closed (btQ1_3 D))))))))

abbrev btPinF (D : OddSurfaceDistance) : SFormula 2 :=
  .allNatLt (nP2 D) (btPinBody D)

/-- Bulk–Top joint pin pack: under the bulk–top class context, every shared non-`I`
slot is one of the two overlap qubits.  `arithBool`, eval-cert via `overlap_bulk_top`. -/
def btPinPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (btPinF D) := by
  refine PureFamilyDerivA.allNatLtIntro _ ?_
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd3 : D.distance = 2 * D.index + 3 := rfl
  simp only [btPinBody, btQ0_3, btQ1_3, btB3, bulkGuardTA, topClassGuardTA, topBandGuardTA,
    baseBulkBandGuardTA, baseBTA, baseHalfTA, bulkCountTA, dm1TA, band3, orEqSucc, dP3, dP2,
    k1P3, k2P3, qP3, SFormula.eval, SFormula.boundNat, SC.closed, SC.b, STerm.eval, Term.eval,
    Term.lift, bind, Option.bind]
  set q := rho ⟨0, by decide⟩ with hq'
  set k2 := rho ⟨1, by decide⟩ with hk2'
  set k1 := rho ⟨2, by decide⟩ with hk1'
  set d := D.distance with hdd
  have hdpos : 0 < d := by omega
  -- The class context: `¬bulk(k1)`, `topClass(k1)`, `k2 = 2b`.
  by_cases hbulk : k1 < (d - 1) * (d - 1)
  · -- bulk(k1) true → antecedent `bulk = false` false → vacuous.
    have hb : decide (decide (k1 < (d - 1) * (d - 1)) = false) = false := by
      rw [decide_eq_false_iff_not]; simp [hbulk]
    simp only [hb, Bool.false_eq_true, if_false, reduceIte]
  · by_cases htop : k1 - (d - 1) * (d - 1) < (d - 1) / 2
    · set b := k1 - (d - 1) * (d - 1) with hb
      have hbf : decide (decide (k1 < (d - 1) * (d - 1)) = false) = true := by
        rw [decide_eq_true_eq]; simp [hbulk]
      have htf : decide (decide (b < (d - 1) / 2) = true) = true := by
        rw [decide_eq_true_eq]; simp [htop]
      by_cases hadj : k2 = 2 * b
      · have haf : decide (decide (k2 = 2 * b) = true) = true := by
          rw [decide_eq_true_eq]; simp [hadj]
        simp only [hbf, htf, haf, if_true]
        -- Now the two band-fired antecedents.  Use overlap_bulk_top (roles swapped).
        have h2bd : 2 * b + 1 < d := by omega
        have h2lt : k2 < d * d - 1 := by
          have hbulkk2 : 2 * b < (d - 1) * (d - 1) := by
            have h1 : d - 1 ≤ (d - 1) * (d - 1) := Nat.le_mul_of_pos_left _ (by omega)
            omega
          have : d ≤ d * d := Nat.le_mul_of_pos_left d hdpos
          omega
        -- Concrete bulk-band coordinates of the Z-plaquette `k2 = 2b` (row 0, col 2b).
        have hk2d : k2 / (d - 1) = 0 := by rw [hadj]; exact Nat.div_eq_of_lt (by omega)
        have hk2m : k2 % (d - 1) = 2 * b := by rw [hadj]; exact Nat.mod_eq_of_lt (by omega)
        -- top-band fired: k1 < d²-1, q/d = 0, q%d ∈ {2b, 2b+1}.
        by_cases htb1 : k1 < d * d - 1
        · by_cases hq0 : q / d = 0
          · by_cases hqcol : q % d = 2 * b ∨ q % d = 2 * b + 1
            · -- top-band fires.  q = q%d (since q/d = 0), so q ∈ {2b, 2b+1}.
              have hqval : q = q % d := by
                have hdm := Nat.div_add_mod q d
                rw [hq0, Nat.mul_zero, Nat.zero_add] at hdm; exact hdm.symm
              rcases hqcol with hc | hc
              · -- q%d = 2b → q = 2b = q0.
                have hqe : q = 2 * b := by rw [hqval, hc]
                rw [hq0, hc, hk2d, hk2m]; simp [htb1, hqe]
              · -- q%d = 2b+1 → q = 2b+1 = q1.
                have hqe : q = 2 * b + 1 := by rw [hqval, hc]
                have e0v : ¬ (q = 2 * b) := by omega
                rw [hq0, hc, hk2d, hk2m]; simp [htb1, hqe, e0v]
            · -- q%d ∉ {2b, 2b+1}: top-band col antecedent false → vacuous.
              push_neg at hqcol
              obtain ⟨hcq0, hcq1⟩ := hqcol
              rw [hq0]; simp [hcq0, hcq1]
          · -- q/d ≠ 0: top-band row antecedent false → vacuous.
            simp [hq0]
        · -- k1 ≥ d²-1: top-band guard false → vacuous.
          simp [htb1]
      · -- k2 ≠ 2b: adjacency antecedent false → vacuous.
        have haf : decide (decide (k2 = 2 * b) = true) = false := by
          rw [decide_eq_false_iff_not]; simp [hadj]
        simp only [hbf, htf, haf, Bool.false_eq_true, if_false, reduceIte]
    · -- topClass(k1) false → antecedent `topClass = true` false → vacuous.
      have hbf : decide (decide (k1 < (d - 1) * (d - 1)) = false) = true := by
        rw [decide_eq_true_eq]; simp [hbulk]
      have htf : decide (decide (k1 - (d - 1) * (d - 1) < (d - 1) / 2) = true) = false := by
        rw [decide_eq_false_iff_not]; simp [htop]
      simp only [hbf, htf, Bool.false_eq_true, if_false, reduceIte]

/-- Extract the bulk–top joint-pin disjunction at `boundNat`: under the class context
and both band-fired facts, `boundNat ∈ {q0, q1}`.  Mirrors `classABulkZPinAt`. -/
def btPinAt {Δ : List (SFormula 3)} (D : OddSurfaceDistance)
    (hW : SFormula.Deriv Δ (btPinF D).weaken)
    (hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken))
    (hBulkF : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b false)))
    (hTopC : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA (dP3 D) k1P3)) (SC.b true)))
    (hAdj : SFormula.Deriv Δ
      (.eqBool (SC.closed (.eqNat k2P3 (.mul (.natLit 2) (btB3 D)))) (SC.b true)))
    (hTopB : SFormula.Deriv Δ (.eqBool (SC.closed (topBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true)))
    (hBulkB : SFormula.Deriv Δ
      (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))) :
    SFormula.Deriv Δ
      (.or (.eqNat SFormula.boundNat (SC.closed (btQ0_3 D)))
        (.eqNat SFormula.boundNat (SC.closed (btQ1_3 D)))) := by
  have hElim := SFormula.Deriv.allNatLtElim (nP2 D).weaken
    ((btPinBody D).lift 1) SFormula.boundNat hW hq
  have hBody := SFormula.Deriv.applyNatBoundNatBeta (btPinBody D) hElim
  exact SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp
    (SFormula.Deriv.mp hBody hBulkF) hTopC) hAdj) hTopB) hBulkB

/-! ### Bulk–Top class: reverse-leaf band recovery + the joint pin handler

The `hXZpin` handler for `commBulkTopXZ` receives the resolved leaf facts
`baseLeafTreeTA k1 boundNat = X` and `baseLeafTreeTA k2 boundNat = Z`.  To feed the
joint pin we must recover the band-fired facts (`topBand(k1) = true`,
`bulkBand(k2) = true`).  We do this by reverse-leaf `boolCases` on each band guard:
the FALSE branch produces an `I` leaf (`baseLeafTopIS` / `baseLeafBulkIS`),
contradicting the `X` / `Z` leaf via `pauliNeqLit`. -/

/-- Recover `topBand(k1, q) = true` from `baseLeafTreeTA k1 q = X`, given the top
class context (`¬bulk(k1)`, `topClass(k1)`).  Reverse-leaf: the false band branch
gives an `I` leaf, contradicting `X`. -/
def btTopBandFromX {Δ : List (SFormula 3)} (D : OddSurfaceDistance)
    (hBulkF : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b false)))
    (hTopC : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA (dP3 D) k1P3)) (SC.b true)))
    (hLeafX : SFormula.Deriv Δ
      (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3)) (SC.p Pauli.X))) :
    SFormula.Deriv Δ (.eqBool (SC.closed (topBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true)) := by
  refine SFormula.Deriv.boolCases (SC.closed (topBandGuardTA (dP3 D) k1P3 qP3)) _ .assumption ?_
  -- band = false → leaf = I, contradicting leaf = X.
  refine SFormula.Deriv.botElim ?_
  have hBandF : SFormula.Deriv (.eqBool (SC.closed (topBandGuardTA (dP3 D) k1P3 qP3)) (SC.b false) :: Δ)
      (.eqBool (SC.closed (topBandGuardTA (dP3 D) k1P3 qP3)) (SC.b false)) := .assumption
  have hI : SFormula.Deriv (.eqBool (SC.closed (topBandGuardTA (dP3 D) k1P3 qP3)) (SC.b false) :: Δ)
      (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3)) (SC.p Pauli.I)) :=
    baseLeafTopIS (dP3 D) k1P3 qP3 (cw1 hBulkF) (cw1 hTopC) hBandF
  have hXZ : SFormula.Deriv (.eqBool (SC.closed (topBandGuardTA (dP3 D) k1P3 qP3)) (SC.b false) :: Δ)
      (.eqPauli (SC.p Pauli.X) (SC.p Pauli.I)) :=
    SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.eqPauliSymm _ _ (cw1 hLeafX)) hI
  exact SFormula.Deriv.notElim hXZ (SFormula.Deriv.pauliNeqLit Pauli.X Pauli.I (by decide))

/-- Recover `bulkBand(k2, q) = true` from `baseLeafTreeTA k2 q = Z`, given `bulk(k2)`.
Reverse-leaf: the false band branch gives an `I` leaf, contradicting `Z`. -/
def btBulkBandFromZ {Δ : List (SFormula 3)} (D : OddSurfaceDistance)
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

/-- Row-A flat-entry equality at a concrete qubit `qT` (arity 2), as a formula. -/
abbrev entryAAtQF (D : OddSurfaceDistance) (qT : Term 2 .nat) : SFormula 2 :=
  .eqPauli (.stabAt (SC.closed (.recCall (dP2 D) k1P)) (SC.closed qT))
    (SC.closed (baseLeafTreeTA (dP2 D) k1P qT))
/-- Row-B flat-entry equality at a concrete qubit `qT` (arity 2), as a formula. -/
abbrev entryBAtQF (D : OddSurfaceDistance) (qT : Term 2 .nat) : SFormula 2 :=
  .eqPauli (.stabAt (SC.closed (.recCall (dP2 D) k2P)) (SC.closed qT))
    (SC.closed (baseLeafTreeTA (dP2 D) k2P qT))

/-- **Bulk–Top overlap class closer.**  Assembles the per-pair commutation goal for
the bulk–top overlap, where row A (`k1`) is the X-type top-boundary stabilizer and
row B (`k2`) is the Z-type bulk plaquette at the adjacent top row.  Consumes the
three landed arithmetic packs (`btRangePack` / `btTopBandPack` / `btBulkBandPack` as
`hRange` / `hTopBand` / `hBulkBand`), the joint pin (`btPinPack` as `hPin`), and the
four flat-entry facts at the overlap qubits `q0 = 2b`, `q1 = 2b+1`; under the class
context (`hbulkF` : `¬bulk(k1)`, `htopC` : `topClass(k1)`, `hadj` : `k2 = 2b`) it
resolves both rows to `X`/`Z` at `q0`/`q1` and discharges the all-others premise via
the proven two-anti spine `commBulkTopXZ`. -/
def commBulkTop {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hEntryA : SFormula.Deriv Γ (entryAQuant D)) (hEntryB : SFormula.Deriv Γ (entryBQuant D))
    (hk1X : SFormula.Deriv Γ (k1IsX D true)) (hExcl1 : SFormula.Deriv Γ (typeExclF D k1P))
    (hbulkF : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false)))
    (htopC : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b true)))
    (hadj : SFormula.Deriv Γ (btAdjF D))
    (hRange : SFormula.Deriv Γ (btRangePackF D))
    (hTopBand : SFormula.Deriv Γ (btTopBandPackF D))
    (hBulkBand : SFormula.Deriv Γ (btBulkBandPackF D))
    (hPin : SFormula.Deriv Γ (btPinF D))
    (hEA0 : SFormula.Deriv Γ (entryAAtQF D (btQ0 D)))
    (hEA1 : SFormula.Deriv Γ (entryAAtQF D (btQ1 D)))
    (hEB0 : SFormula.Deriv Γ (entryBAtQF D (btQ0 D)))
    (hEB1 : SFormula.Deriv Γ (entryBAtQF D (btQ1 D))) :
    SFormula.Deriv Γ (pairGoal D) := by
  -- Range facts at q0/q1.
  have hRangeP := SFormula.Deriv.mp (SFormula.Deriv.mp hRange hbulkF) htopC
  have hLt0 := SFormula.Deriv.andElimLeft hRangeP
  have hLt1 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hRangeP)
  have hNe := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hRangeP)
  -- Top-band-fires facts at q0/q1.
  have hTBP := SFormula.Deriv.mp (SFormula.Deriv.mp hTopBand hbulkF) htopC
  have hTB0 := SFormula.Deriv.andElimLeft hTBP
  have hTB1 := SFormula.Deriv.andElimRight hTBP
  -- Bulk-band facts for the Z plaquette k2 at q0/q1.
  have hBBP := SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp hBulkBand hbulkF) htopC) hadj
  have hBulkK2 := SFormula.Deriv.andElimLeft hBBP
  have hKindK2 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hBBP)
  have hBB0 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hBBP))
  have hBB1 := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hBBP))
  -- Row A = X at q0/q1 (top-X leaf), Row B = Z at q0/q1 (bulk-Z leaf).
  have hAX0 : SFormula.Deriv Γ (.eqPauli (.stabAt (rowA D) (SC.closed (btQ0 D))) (SC.p Pauli.X)) :=
    SFormula.Deriv.eqPauliTrans _ _ _ hEA0 (baseLeafTopXS (dP2 D) k1P (btQ0 D) hbulkF htopC hTB0)
  have hAX1 : SFormula.Deriv Γ (.eqPauli (.stabAt (rowA D) (SC.closed (btQ1 D))) (SC.p Pauli.X)) :=
    SFormula.Deriv.eqPauliTrans _ _ _ hEA1 (baseLeafTopXS (dP2 D) k1P (btQ1 D) hbulkF htopC hTB1)
  have hBZ0 : SFormula.Deriv Γ (.eqPauli (.stabAt (rowB D) (SC.closed (btQ0 D))) (SC.p Pauli.Z)) :=
    SFormula.Deriv.eqPauliTrans _ _ _ hEB0 (baseLeafZS (dP2 D) k2P (btQ0 D) hBulkK2 hBB0 hKindK2)
  have hBZ1 : SFormula.Deriv Γ (.eqPauli (.stabAt (rowB D) (SC.closed (btQ1 D))) (SC.p Pauli.Z)) :=
    SFormula.Deriv.eqPauliTrans _ _ _ hEB1 (baseLeafZS (dP2 D) k2P (btQ1 D) hBulkK2 hBB1 hKindK2)
  -- Assemble via the two-anti spine; the all-others pin handler closes the genuine overlap.
  refine commBulkTopXZ D (btQ0 D) (btQ1 D) hEntryA hEntryB hk1X hExcl1
    hLt0 hLt1 hNe hAX0 hAX1 hBZ0 hBZ1 ?_
  -- The `(X,Z)` joint pin handler.
  intro Δ' lift hLeafA hLeafB
  -- The class context + k2-bulk fact, lifted into the qubit-binder context Δ'.
  have hbulkFΔ : SFormula.Deriv Δ' (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b false)) :=
    lift (cw3 (SFormula.Deriv.weakenFresh
      (A := .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false)) hbulkF))
  have htopCΔ : SFormula.Deriv Δ' (.eqBool (SC.closed (topClassGuardTA (dP3 D) k1P3)) (SC.b true)) :=
    lift (cw3 (SFormula.Deriv.weakenFresh
      (A := .eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b true)) htopC))
  have hadjΔ : SFormula.Deriv Δ'
      (.eqBool (SC.closed (.eqNat k2P3 (.mul (.natLit 2) (btB3 D)))) (SC.b true)) :=
    lift (cw3 (SFormula.Deriv.weakenFresh (A := btAdjF D) hadj))
  have hBulkK2Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b true)) :=
    lift (cw3 (SFormula.Deriv.weakenFresh
      (A := .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true)) hBulkK2))
  have hPinΔ : SFormula.Deriv Δ' (btPinF D).weaken :=
    lift (cw3 (SFormula.Deriv.weakenFresh (A := btPinF D) hPin))
  -- in-range witness for boundNat (the `boundNatLt` hyp, third in the handler context).
  have hq : SFormula.Deriv Δ' (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken) :=
    lift (.hyp (by right; right; exact List.mem_cons_self))
  -- Recover the band-fired facts at boundNat from the leaves.
  have hTopB := btTopBandFromX D hbulkFΔ htopCΔ hLeafA
  have hBulkB := btBulkBandFromZ D hBulkK2Δ hLeafB
  -- The pin: boundNat ∈ {q0, q1}.
  have hdisj := btPinAt D hPinΔ hq hbulkFΔ htopCΔ hadjΔ hTopB hBulkB
  -- The two exclusions in the handler context (first two hyps), lifted into Δ'.
  have hne0 : SFormula.Deriv Δ'
      (.not (.eqNat SFormula.boundNat (SC.closed (btQ0 D)).weaken)) :=
    lift (.hyp (by right; exact List.mem_cons_self))
  have hne1 : SFormula.Deriv Δ'
      (.not (.eqNat SFormula.boundNat (SC.closed (btQ1 D)).weaken)) :=
    lift (.hyp List.mem_cons_self)
  -- `(SC.closed (btQ0 D)).weaken = SC.closed (btQ0_3 D)` definitionally; `show` retypes.
  have hne0' : SFormula.Deriv Δ'
      (.not (.eqNat SFormula.boundNat (SC.closed (btQ0_3 D)))) := hne0
  have hne1' : SFormula.Deriv Δ'
      (.not (.eqNat SFormula.boundNat (SC.closed (btQ1_3 D)))) := hne1
  refine SFormula.Deriv.orElim hdisj ?_ ?_
  · exact SFormula.Deriv.botElim (SFormula.Deriv.notElim .assumption (cw1 hne0'))
  · exact SFormula.Deriv.botElim (SFormula.Deriv.notElim .assumption (cw1 hne1'))

end QHL.CodeLang.Surface.Verify
