import QStab.QHL.Verify.SurfaceRowsCommute.NonAdjacentBoundary

/-!
# Rows-commute (pairwise generated-row commutation) — Dispatchers

The boundary↔boundary non-overlap pairs (top-right/left, bottom-right/left) and the
class-combo dispatchers (bulk–bulk, bulk–boundary stages 1-2, boundary–boundary stage 3).
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface

set_option maxRecDepth 65536
set_option linter.unusedVariables false

/-! ## Top–Right BOUNDARY↔BOUNDARY (non-overlap) different-type pair

Row A (`k1`) is an X-type TOP-boundary stabilizer, row B (`k2`) a Z-type RIGHT-boundary
stabilizer.  An X-boundary check and a Z-boundary check ALWAYS share NO qubit — the
disjointness is UNCONDITIONAL (no adjacency hypothesis at all).  The top boundary `k1`
occupies row `0`, cols `{2·topIdx, 2·topIdx+1}` with `topIdx < half`, so its col is at
most `2·half−1 = d−2 < d−1`; the right boundary `k2` occupies column `d−1`.  A common
qubit would need col `≤ d−2` (top) AND col `= d−1` (right): impossible. -/

/-- **Core geometric contradiction** (pure `Nat`) for top–right.  A top boundary at row
`0`, cols `{2·t, 2·t+1}` with `t < half` (and `2·half ≤ d−1`), and a right boundary at
column `d−1`, rows `{2·r, 2·r+1}`, sharing a slot `(qr, qc)`: top forces
`qc ∈ {2·t, 2·t+1}`, so `qc ≤ 2·half−1 ≤ d−2`; right forces `qc = d−1`.  Contradiction. -/
private theorem trnaCellContra
    {qr qc t r half d : Nat}
    (hhalf : 2 * half ≤ d - 1) (htlt : t < half)
    (hTopR : qr = 0) (hTopC : qc = 2 * t ∨ qc = 2 * t + 1)
    (hRightC : qc = d - 1) (hRightR : qr = 2 * r ∨ qr = 2 * r + 1) : False := by
  rcases hTopC with h | h <;> omega

/-- The top–right disjointness-pin body (arity 3, `k1 = var 2`, `k2 = var 1`,
`q = var 0`): under the top class context for `k1` (`¬bulk ∧ topClass`), the right class
context for `k2` (`¬bulk ∧ ¬top ∧ rightClass`), and both bands firing at `q`, derive
`⊥` — the top boundary and the right boundary cannot share a qubit. -/
abbrev trnaPinBody (D : OddSurfaceDistance) : SFormula 3 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b false))
    (.imp (.eqBool (SC.closed (topClassGuardTA (dP3 D) k1P3)) (SC.b true))
      (.imp (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b false))
        (.imp (.eqBool (SC.closed (topClassGuardTA (dP3 D) k2P3)) (SC.b false))
          (.imp (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k2P3)) (SC.b true))
            (.imp (.eqBool (SC.closed (topBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true))
              (.imp (.eqBool (SC.closed (rightBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))
                .bot))))))

abbrev trnaPinF (D : OddSurfaceDistance) : SFormula 2 :=
  .allNatLt (nP2 D) (trnaPinBody D)

/-- Top–Right disjointness pin pack: a top boundary and right boundary share no qubit
(UNCONDITIONAL — no adjacency hypothesis).  `arithBool`; the eval-cert unfolds the top
band to `suppMem_top_prop`'s `(row,col)` RHS and the right band to
`suppMem_right_prop`'s, then the geometric core lemma `trnaCellContra` refutes a common
qubit. -/
def trnaPinPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (trnaPinF D) := by
  refine PureFamilyDerivA.allNatLtIntro _ ?_
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd3 : D.distance = 2 * D.index + 3 := rfl
  simp only [bulkGuardTA, topClassGuardTA, rightClassGuardTA, topBandGuardTA, rightBandGuardTA,
    baseBTA, baseHalfTA, bulkCountTA, dm1TA, band3, orEqSucc, dP3, dP2, k1P3, k2P3, qP3,
    SFormula.eval, SC.closed, SC.b, STerm.eval, Term.eval, Term.lift, bind, Option.bind]
  set q := rho ⟨0, by decide⟩ with hq'
  set k2 := rho ⟨1, by decide⟩ with hk2'
  set k1 := rho ⟨2, by decide⟩ with hk1'
  set d := D.distance with hdd
  have hdge : 3 ≤ d := by omega
  have hdpos : 0 < d := by omega
  by_cases hbulk1 : k1 < (d - 1) * (d - 1)
  · have hb : decide (decide (k1 < (d - 1) * (d - 1)) = false) = false := by
      rw [decide_eq_false_iff_not]; simp [hbulk1]
    simp only [hb, Bool.false_eq_true, if_false, reduceIte]
  · by_cases htop1 : k1 - (d - 1) * (d - 1) < (d - 1) / 2
    · have hbf : decide (decide (k1 < (d - 1) * (d - 1)) = false) = true := by
        rw [decide_eq_true_eq]; simp [hbulk1]
      have htf : decide (decide (k1 - (d - 1) * (d - 1) < (d - 1) / 2) = true) = true := by
        rw [decide_eq_true_eq]; simp [htop1]
      by_cases hbulk2 : k2 < (d - 1) * (d - 1)
      · have hb2f : decide (decide (k2 < (d - 1) * (d - 1)) = false) = false := by
          rw [decide_eq_false_iff_not]; simp [hbulk2]
        simp only [hbf, htf, hb2f, Bool.false_eq_true, if_false, reduceIte]
      · by_cases htop2 : k2 - (d - 1) * (d - 1) < (d - 1) / 2
        · have hb2f : decide (decide (k2 < (d - 1) * (d - 1)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hbulk2]
          have ht2f : decide (decide (k2 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = false := by
            rw [decide_eq_false_iff_not]; simp [htop2]
          simp only [hbf, htf, hb2f, ht2f, Bool.false_eq_true, if_false, reduceIte]
        · by_cases hright2 : k2 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)
          · have hb2f : decide (decide (k2 < (d - 1) * (d - 1)) = false) = true := by
              rw [decide_eq_true_eq]; simp [hbulk2]
            have ht2f : decide (decide (k2 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
              rw [decide_eq_true_eq]; simp [htop2]
            have hr2t : decide (decide (k2 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = true) = true := by
              rw [decide_eq_true_eq]; simp [hright2]
            simp only [hbf, htf, hb2f, ht2f, hr2t, if_true]
            set t := k1 - (d - 1) * (d - 1) with ht
            set r := k2 - (d - 1) * (d - 1) - (d - 1) / 2 with hr
            have hhalf : 2 * ((d - 1) / 2) ≤ d - 1 := by omega
            simp only [← apply_ite Option.some, Option.some.injEq, Bool.if_true_left,
              Bool.if_true_right, Bool.if_false_right,
              Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, Bool.not_eq_false,
              decide_eq_true_eq, decide_eq_false_iff_not]
            by_contra hcon
            push_neg at hcon
            obtain ⟨⟨_, hb1r, hb1c⟩, ⟨hcol, hb2r⟩, _⟩ := hcon
            exact trnaCellContra hhalf htop1 hb1r hb1c hcol hb2r
          · have hb2f : decide (decide (k2 < (d - 1) * (d - 1)) = false) = true := by
              rw [decide_eq_true_eq]; simp [hbulk2]
            have ht2f : decide (decide (k2 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
              rw [decide_eq_true_eq]; simp [htop2]
            have hr2f : decide (decide (k2 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = true) = false := by
              rw [decide_eq_false_iff_not]; simp [hright2]
            simp only [hbf, htf, hb2f, ht2f, hr2f, Bool.false_eq_true, if_false, reduceIte]
    · have hbf : decide (decide (k1 < (d - 1) * (d - 1)) = false) = true := by
        rw [decide_eq_true_eq]; simp [hbulk1]
      have htf : decide (decide (k1 - (d - 1) * (d - 1) < (d - 1) / 2) = true) = false := by
        rw [decide_eq_false_iff_not]; simp [htop1]
      simp only [hbf, htf, Bool.false_eq_true, if_false, reduceIte]

/-- Extract the top–right disjointness-pin `⊥` at `boundNat`: under the class context,
the top band and right band cannot both fire. -/
def trnaPinAt {Δ : List (SFormula 3)} (D : OddSurfaceDistance)
    (hW : SFormula.Deriv Δ (trnaPinF D).weaken)
    (hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken))
    (hBulkFk1 : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b false)))
    (hTopCk1 : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA (dP3 D) k1P3)) (SC.b true)))
    (hBulkFk2 : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b false)))
    (hTopFk2 : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA (dP3 D) k2P3)) (SC.b false)))
    (hRightCk2 : SFormula.Deriv Δ (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k2P3)) (SC.b true)))
    (hTopB : SFormula.Deriv Δ (.eqBool (SC.closed (topBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true)))
    (hRightB : SFormula.Deriv Δ (.eqBool (SC.closed (rightBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))) :
    SFormula.Deriv Δ .bot := by
  have hElim := SFormula.Deriv.allNatLtElim (nP2 D).weaken
    ((trnaPinBody D).lift 1) SFormula.boundNat hW hq
  have hBody := SFormula.Deriv.applyNatBoundNatBeta (trnaPinBody D) hElim
  exact SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp
    (SFormula.Deriv.mp (SFormula.Deriv.mp hBody hBulkFk1) hTopCk1) hBulkFk2) hTopFk2)
      hRightCk2) hTopB |>.mp hRightB

#print axioms trnaCellContra
#print axioms trnaPinPack
#print axioms trnaPinAt

/-- **Top–Right boundary↔boundary (non-overlap) closer.**  Row A is the X-type
top-boundary stabilizer, row B the Z-type right-boundary stabilizer.  They share no
qubit UNCONDITIONALLY, so the pair commutes.  Routed through the non-overlap path
`pairCommutePointwise`: the `(X,Z)` leaf-pair is closed by the disjointness pin
`trnaPinAt` (→ `⊥`), the `(Z,X)` leaf-pair by the X-type exclusion `hExcl1`. -/
def pairCommuteTopRightNonAdj {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hEntryA : SFormula.Deriv Γ (entryAQuant D)) (hEntryB : SFormula.Deriv Γ (entryBQuant D))
    (hk1X : SFormula.Deriv Γ (k1IsX D true))
    (hExcl1 : SFormula.Deriv Γ (typeExclF D k1P))
    (hbulkFk1 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false)))
    (htopCk1 : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b true)))
    (hbulkFk2 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)))
    (htopFk2 : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false)))
    (hrightCk2 : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b true)))
    (hPin : SFormula.Deriv Γ (trnaPinF D)) :
    SFormula.Deriv Γ (pairGoal D) := by
  refine pairCommutePointwise D hEntryA hEntryB ?hXZ ?hZX
  · -- (X, Z): both leaves genuinely fire; the disjointness pin forces ⊥.
    intro Δ' lift hLeafA hLeafB
    have hbulkFk1Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b false)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false)) hbulkFk1))
    have htopCk1Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (topClassGuardTA (dP3 D) k1P3)) (SC.b true)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b true)) htopCk1))
    have hbulkFk2Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b false)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)) hbulkFk2))
    have htopFk2Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (topClassGuardTA (dP3 D) k2P3)) (SC.b false)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false)) htopFk2))
    have hrightCk2Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k2P3)) (SC.b true)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b true)) hrightCk2))
    have hPinΔ : SFormula.Deriv Δ' (trnaPinF D).weaken :=
      lift (cw1 (SFormula.Deriv.weakenFresh (A := trnaPinF D) hPin))
    have hq : SFormula.Deriv Δ' (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken) :=
      lift (.hyp List.mem_cons_self)
    have hTopB := btTopBandFromX D hbulkFk1Δ htopCk1Δ hLeafA
    have hRightB := brRightBandFromZ D hbulkFk2Δ htopFk2Δ hrightCk2Δ hLeafB
    have hBot := trnaPinAt D hPinΔ hq hbulkFk1Δ htopCk1Δ hbulkFk2Δ htopFk2Δ hrightCk2Δ hTopB hRightB
    exact SFormula.Deriv.botElim hBot
  · -- (Z, X): A leaf = Z impossible since A is X-type → type-exclusion contradiction.
    intro Δ' lift hLeafA hLeafB
    have hk1Xd : SFormula.Deriv Δ' (k1IsX D true).weaken :=
      lift (cw1 (SFormula.Deriv.weakenFresh (A := k1IsX D true) hk1X))
    have hExcl1d : SFormula.Deriv Δ' (typeExclF D k1P).weaken :=
      lift (cw1 (SFormula.Deriv.weakenFresh (A := typeExclF D k1P) hExcl1))
    have hxnbz := SFormula.Deriv.andElimLeft hExcl1d
    have hxnrz := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hExcl1d)
    have hxnlz := SFormula.Deriv.andElimLeft
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hExcl1d))
    refine withLeafG D k1P3 _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro Δ'' lift2 hI
      exact leafNotPandZ D k1P3 Pauli.I rfl hI (lift2 hLeafA)
    · intro Δ'' lift2 _ hbulk hkind
      have hkindF := SFormula.Deriv.mp (SFormula.Deriv.mp (lift2 hxnbz) (lift2 hk1Xd)) hbulk
      exact eqBoolContra _ hkind hkindF
    · intro Δ'' lift2 hX _ _
      exact leafNotPandZ D k1P3 Pauli.X rfl hX (lift2 hLeafA)
    · intro Δ'' lift2 hX _ _
      exact leafNotPandZ D k1P3 Pauli.X rfl hX (lift2 hLeafA)
    · intro Δ'' lift2 _ hbulk htop hright
      have hrightF := SFormula.Deriv.mp (SFormula.Deriv.mp
        (SFormula.Deriv.mp (lift2 hxnrz) (lift2 hk1Xd)) hbulk) htop
      exact eqBoolContra _ hright hrightF
    · intro Δ'' lift2 _ hbulk htop hright hleft
      have hleftF := SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp
        (SFormula.Deriv.mp (lift2 hxnlz) (lift2 hk1Xd)) hbulk) htop) hright
      exact eqBoolContra _ hleft hleftF
    · intro Δ'' lift2 hX _ _ _ _
      exact leafNotPandZ D k1P3 Pauli.X rfl hX (lift2 hLeafA)

#print axioms pairCommuteTopRightNonAdj

/-! ## Top–Left BOUNDARY↔BOUNDARY (non-overlap) different-type pair

Row A (`k1`) is an X-type TOP-boundary stabilizer, row B (`k2`) a Z-type LEFT-boundary
stabilizer.  Disjointness is UNCONDITIONAL.  The top boundary `k1` occupies row `0`;
the left boundary `k2` occupies column `0`, rows `{2·leftIdx+1, 2·leftIdx+2}`, so its
row is `≥ 1`.  A common qubit would need row `0` (top) AND row `≥ 1` (left): impossible. -/

/-- **Core geometric contradiction** (pure `Nat`) for top–left.  A top boundary at row
`0`, cols `{2·t, 2·t+1}`, and a left boundary at column `0`, rows `{2·l+1, 2·l+2}`,
sharing a slot `(qr, qc)`: top forces `qr = 0`; left forces `qr ∈ {2·l+1, 2·l+2}`, so
`qr ≥ 1`.  Contradiction. -/
private theorem tlnaCellContra
    {qr qc t l : Nat}
    (hTopR : qr = 0) (hTopC : qc = 2 * t ∨ qc = 2 * t + 1)
    (hLeftC : qc = 0) (hLeftR : qr = 2 * l + 1 ∨ qr = 2 * l + 2) : False := by
  rcases hLeftR with h | h <;> omega

/-- The top–left disjointness-pin body (arity 3, `k1 = var 2`, `k2 = var 1`,
`q = var 0`): under the top class context for `k1` (`¬bulk ∧ topClass`), the left class
context for `k2` (`¬bulk ∧ ¬top ∧ ¬right ∧ leftClass`), and both bands firing at `q`,
derive `⊥` — the top boundary and the left boundary cannot share a qubit. -/
abbrev tlnaPinBody (D : OddSurfaceDistance) : SFormula 3 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b false))
    (.imp (.eqBool (SC.closed (topClassGuardTA (dP3 D) k1P3)) (SC.b true))
      (.imp (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b false))
        (.imp (.eqBool (SC.closed (topClassGuardTA (dP3 D) k2P3)) (SC.b false))
          (.imp (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k2P3)) (SC.b false))
            (.imp (.eqBool (SC.closed (leftClassGuardTA (dP3 D) k2P3)) (SC.b true))
              (.imp (.eqBool (SC.closed (topBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true))
                (.imp (.eqBool (SC.closed (leftBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))
                  .bot)))))))

abbrev tlnaPinF (D : OddSurfaceDistance) : SFormula 2 :=
  .allNatLt (nP2 D) (tlnaPinBody D)

/-- Top–Left disjointness pin pack: a top boundary and left boundary share no qubit
(UNCONDITIONAL).  `arithBool`; the eval-cert unfolds the top band to
`suppMem_top_prop`'s `(row,col)` RHS and the left band to `suppMem_left_prop`'s, then
the geometric core lemma `tlnaCellContra` refutes a common qubit. -/
def tlnaPinPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (tlnaPinF D) := by
  refine PureFamilyDerivA.allNatLtIntro _ ?_
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd3 : D.distance = 2 * D.index + 3 := rfl
  simp only [bulkGuardTA, topClassGuardTA, rightClassGuardTA, leftClassGuardTA, topBandGuardTA,
    leftBandGuardTA, baseBTA, baseHalfTA, bulkCountTA, dm1TA, band3, orEqSucc, orEqPair, dP3, dP2,
    k1P3, k2P3, qP3, SFormula.eval, SC.closed, SC.b, STerm.eval, Term.eval, Term.lift, bind,
    Option.bind]
  set q := rho ⟨0, by decide⟩ with hq'
  set k2 := rho ⟨1, by decide⟩ with hk2'
  set k1 := rho ⟨2, by decide⟩ with hk1'
  set d := D.distance with hdd
  have hdge : 3 ≤ d := by omega
  have hdpos : 0 < d := by omega
  by_cases hbulk1 : k1 < (d - 1) * (d - 1)
  · have hb : decide (decide (k1 < (d - 1) * (d - 1)) = false) = false := by
      rw [decide_eq_false_iff_not]; simp [hbulk1]
    simp only [hb, Bool.false_eq_true, if_false, reduceIte]
  · by_cases htop1 : k1 - (d - 1) * (d - 1) < (d - 1) / 2
    · have hbf : decide (decide (k1 < (d - 1) * (d - 1)) = false) = true := by
        rw [decide_eq_true_eq]; simp [hbulk1]
      have htf : decide (decide (k1 - (d - 1) * (d - 1) < (d - 1) / 2) = true) = true := by
        rw [decide_eq_true_eq]; simp [htop1]
      by_cases hbulk2 : k2 < (d - 1) * (d - 1)
      · have hb2f : decide (decide (k2 < (d - 1) * (d - 1)) = false) = false := by
          rw [decide_eq_false_iff_not]; simp [hbulk2]
        simp only [hbf, htf, hb2f, Bool.false_eq_true, if_false, reduceIte]
      · by_cases htop2 : k2 - (d - 1) * (d - 1) < (d - 1) / 2
        · have hb2f : decide (decide (k2 < (d - 1) * (d - 1)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hbulk2]
          have ht2f : decide (decide (k2 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = false := by
            rw [decide_eq_false_iff_not]; simp [htop2]
          simp only [hbf, htf, hb2f, ht2f, Bool.false_eq_true, if_false, reduceIte]
        · by_cases hright2 : k2 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)
          · have hb2f : decide (decide (k2 < (d - 1) * (d - 1)) = false) = true := by
              rw [decide_eq_true_eq]; simp [hbulk2]
            have ht2f : decide (decide (k2 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
              rw [decide_eq_true_eq]; simp [htop2]
            have hr2f : decide (decide (k2 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = false := by
              rw [decide_eq_false_iff_not]; simp [hright2]
            simp only [hbf, htf, hb2f, ht2f, hr2f, Bool.false_eq_true, if_false, reduceIte]
          · by_cases hleft2 : k2 - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)
            · have hb2f : decide (decide (k2 < (d - 1) * (d - 1)) = false) = true := by
                rw [decide_eq_true_eq]; simp [hbulk2]
              have ht2f : decide (decide (k2 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
                rw [decide_eq_true_eq]; simp [htop2]
              have hr2f : decide (decide (k2 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = true := by
                rw [decide_eq_true_eq]; simp [hright2]
              have hl2t : decide (decide (k2 - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)) = true) = true := by
                rw [decide_eq_true_eq]; simp [hleft2]
              simp only [hbf, htf, hb2f, ht2f, hr2f, hl2t, if_true]
              set t := k1 - (d - 1) * (d - 1) with ht
              set l := k2 - (d - 1) * (d - 1) - 2 * ((d - 1) / 2) with hl
              simp only [← apply_ite Option.some, Option.some.injEq, Bool.if_true_left,
                Bool.if_true_right, Bool.if_false_right,
                Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, Bool.not_eq_false,
                decide_eq_true_eq, decide_eq_false_iff_not]
              by_contra hcon
              push_neg at hcon
              obtain ⟨⟨_, hb1r, hb1c⟩, ⟨hcol, hb2r⟩, _⟩ := hcon
              exact tlnaCellContra hb1r hb1c hcol hb2r
            · have hb2f : decide (decide (k2 < (d - 1) * (d - 1)) = false) = true := by
                rw [decide_eq_true_eq]; simp [hbulk2]
              have ht2f : decide (decide (k2 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
                rw [decide_eq_true_eq]; simp [htop2]
              have hr2f : decide (decide (k2 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = true := by
                rw [decide_eq_true_eq]; simp [hright2]
              have hl2f : decide (decide (k2 - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)) = true) = false := by
                rw [decide_eq_false_iff_not]; simp [hleft2]
              simp only [hbf, htf, hb2f, ht2f, hr2f, hl2f, Bool.false_eq_true, if_false, reduceIte]
    · have hbf : decide (decide (k1 < (d - 1) * (d - 1)) = false) = true := by
        rw [decide_eq_true_eq]; simp [hbulk1]
      have htf : decide (decide (k1 - (d - 1) * (d - 1) < (d - 1) / 2) = true) = false := by
        rw [decide_eq_false_iff_not]; simp [htop1]
      simp only [hbf, htf, Bool.false_eq_true, if_false, reduceIte]

/-- Extract the top–left disjointness-pin `⊥` at `boundNat`: under the class context,
the top band and left band cannot both fire. -/
def tlnaPinAt {Δ : List (SFormula 3)} (D : OddSurfaceDistance)
    (hW : SFormula.Deriv Δ (tlnaPinF D).weaken)
    (hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken))
    (hBulkFk1 : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b false)))
    (hTopCk1 : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA (dP3 D) k1P3)) (SC.b true)))
    (hBulkFk2 : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b false)))
    (hTopFk2 : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA (dP3 D) k2P3)) (SC.b false)))
    (hRightFk2 : SFormula.Deriv Δ (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k2P3)) (SC.b false)))
    (hLeftCk2 : SFormula.Deriv Δ (.eqBool (SC.closed (leftClassGuardTA (dP3 D) k2P3)) (SC.b true)))
    (hTopB : SFormula.Deriv Δ (.eqBool (SC.closed (topBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true)))
    (hLeftB : SFormula.Deriv Δ (.eqBool (SC.closed (leftBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))) :
    SFormula.Deriv Δ .bot := by
  have hElim := SFormula.Deriv.allNatLtElim (nP2 D).weaken
    ((tlnaPinBody D).lift 1) SFormula.boundNat hW hq
  have hBody := SFormula.Deriv.applyNatBoundNatBeta (tlnaPinBody D) hElim
  exact SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp
    (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp hBody hBulkFk1) hTopCk1) hBulkFk2)
      hTopFk2) hRightFk2) hLeftCk2) hTopB |>.mp hLeftB

#print axioms tlnaCellContra
#print axioms tlnaPinPack
#print axioms tlnaPinAt

/-- **Top–Left boundary↔boundary (non-overlap) closer.**  Row A is the X-type
top-boundary stabilizer, row B the Z-type left-boundary stabilizer.  They share no qubit
UNCONDITIONALLY, so the pair commutes.  Routed through the non-overlap path
`pairCommutePointwise`: the `(X,Z)` leaf-pair is closed by the disjointness pin
`tlnaPinAt` (→ `⊥`), the `(Z,X)` leaf-pair by the X-type exclusion `hExcl1`. -/
def pairCommuteTopLeftNonAdj {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hEntryA : SFormula.Deriv Γ (entryAQuant D)) (hEntryB : SFormula.Deriv Γ (entryBQuant D))
    (hk1X : SFormula.Deriv Γ (k1IsX D true))
    (hExcl1 : SFormula.Deriv Γ (typeExclF D k1P))
    (hbulkFk1 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false)))
    (htopCk1 : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b true)))
    (hbulkFk2 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)))
    (htopFk2 : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false)))
    (hrightFk2 : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false)))
    (hleftCk2 : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b true)))
    (hPin : SFormula.Deriv Γ (tlnaPinF D)) :
    SFormula.Deriv Γ (pairGoal D) := by
  refine pairCommutePointwise D hEntryA hEntryB ?hXZ ?hZX
  · -- (X, Z): both leaves genuinely fire; the disjointness pin forces ⊥.
    intro Δ' lift hLeafA hLeafB
    have hbulkFk1Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b false)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false)) hbulkFk1))
    have htopCk1Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (topClassGuardTA (dP3 D) k1P3)) (SC.b true)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b true)) htopCk1))
    have hbulkFk2Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b false)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)) hbulkFk2))
    have htopFk2Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (topClassGuardTA (dP3 D) k2P3)) (SC.b false)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false)) htopFk2))
    have hrightFk2Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k2P3)) (SC.b false)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false)) hrightFk2))
    have hleftCk2Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (leftClassGuardTA (dP3 D) k2P3)) (SC.b true)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b true)) hleftCk2))
    have hPinΔ : SFormula.Deriv Δ' (tlnaPinF D).weaken :=
      lift (cw1 (SFormula.Deriv.weakenFresh (A := tlnaPinF D) hPin))
    have hq : SFormula.Deriv Δ' (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken) :=
      lift (.hyp List.mem_cons_self)
    have hTopB := btTopBandFromX D hbulkFk1Δ htopCk1Δ hLeafA
    have hLeftB := blLeftBandFromZ D hbulkFk2Δ htopFk2Δ hrightFk2Δ hleftCk2Δ hLeafB
    have hBot := tlnaPinAt D hPinΔ hq hbulkFk1Δ htopCk1Δ hbulkFk2Δ htopFk2Δ hrightFk2Δ hleftCk2Δ
      hTopB hLeftB
    exact SFormula.Deriv.botElim hBot
  · -- (Z, X): A leaf = Z impossible since A is X-type → type-exclusion contradiction.
    intro Δ' lift hLeafA hLeafB
    have hk1Xd : SFormula.Deriv Δ' (k1IsX D true).weaken :=
      lift (cw1 (SFormula.Deriv.weakenFresh (A := k1IsX D true) hk1X))
    have hExcl1d : SFormula.Deriv Δ' (typeExclF D k1P).weaken :=
      lift (cw1 (SFormula.Deriv.weakenFresh (A := typeExclF D k1P) hExcl1))
    have hxnbz := SFormula.Deriv.andElimLeft hExcl1d
    have hxnrz := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hExcl1d)
    have hxnlz := SFormula.Deriv.andElimLeft
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hExcl1d))
    refine withLeafG D k1P3 _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro Δ'' lift2 hI
      exact leafNotPandZ D k1P3 Pauli.I rfl hI (lift2 hLeafA)
    · intro Δ'' lift2 _ hbulk hkind
      have hkindF := SFormula.Deriv.mp (SFormula.Deriv.mp (lift2 hxnbz) (lift2 hk1Xd)) hbulk
      exact eqBoolContra _ hkind hkindF
    · intro Δ'' lift2 hX _ _
      exact leafNotPandZ D k1P3 Pauli.X rfl hX (lift2 hLeafA)
    · intro Δ'' lift2 hX _ _
      exact leafNotPandZ D k1P3 Pauli.X rfl hX (lift2 hLeafA)
    · intro Δ'' lift2 _ hbulk htop hright
      have hrightF := SFormula.Deriv.mp (SFormula.Deriv.mp
        (SFormula.Deriv.mp (lift2 hxnrz) (lift2 hk1Xd)) hbulk) htop
      exact eqBoolContra _ hright hrightF
    · intro Δ'' lift2 _ hbulk htop hright hleft
      have hleftF := SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp
        (SFormula.Deriv.mp (lift2 hxnlz) (lift2 hk1Xd)) hbulk) htop) hright
      exact eqBoolContra _ hleft hleftF
    · intro Δ'' lift2 hX _ _ _ _
      exact leafNotPandZ D k1P3 Pauli.X rfl hX (lift2 hLeafA)

#print axioms pairCommuteTopLeftNonAdj

/-! ## Bottom–Right BOUNDARY↔BOUNDARY (non-overlap) different-type pair

Row A (`k1`) is an X-type BOTTOM-boundary stabilizer, row B (`k2`) a Z-type
RIGHT-boundary stabilizer.  Disjointness is UNCONDITIONAL.  The bottom boundary `k1`
occupies row `d−1`; the right boundary `k2` occupies column `d−1`, rows
`{2·rightIdx, 2·rightIdx+1}` with `rightIdx < half`, so its row is at most
`2·half−1 = d−2 < d−1`.  A common qubit would need row `d−1` (bottom) AND row `≤ d−2`
(right): impossible. -/

/-- **Core geometric contradiction** (pure `Nat`) for bottom–right.  A bottom boundary
at row `d−1`, cols `{2·b+1, 2·b+2}`, and a right boundary at column `d−1`, rows
`{2·r, 2·r+1}` with `r < half` (and `2·half ≤ d−1`), sharing a slot `(qr, qc)`: bottom
forces `qr = d−1`; right forces `qr ∈ {2·r, 2·r+1}`, so `qr ≤ 2·half−1 ≤ d−2`.
Contradiction. -/
private theorem brbnaCellContra
    {qr qc b r half d : Nat}
    (hhalf : 2 * half ≤ d - 1) (hrlt : r < half)
    (hBotR : qr = d - 1) (hBotC : qc = 2 * b + 1 ∨ qc = 2 * b + 2)
    (hRightC : qc = d - 1) (hRightR : qr = 2 * r ∨ qr = 2 * r + 1) : False := by
  rcases hRightR with h | h <;> omega

/-- The bottom–right disjointness-pin body (arity 3, `k1 = var 2`, `k2 = var 1`,
`q = var 0`): under the bottom class context for `k1` (`¬bulk ∧ ¬top ∧ ¬right ∧
¬left`), the right class context for `k2` (`¬bulk ∧ ¬top ∧ rightClass`), and both bands
firing at `q`, derive `⊥` — the bottom boundary and the right boundary cannot share a
qubit. -/
abbrev brbnaPinBody (D : OddSurfaceDistance) : SFormula 3 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b false))
    (.imp (.eqBool (SC.closed (topClassGuardTA (dP3 D) k1P3)) (SC.b false))
      (.imp (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k1P3)) (SC.b false))
        (.imp (.eqBool (SC.closed (leftClassGuardTA (dP3 D) k1P3)) (SC.b false))
          (.imp (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b false))
            (.imp (.eqBool (SC.closed (topClassGuardTA (dP3 D) k2P3)) (SC.b false))
              (.imp (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k2P3)) (SC.b true))
                (.imp (.eqBool (SC.closed (bottomBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true))
                  (.imp (.eqBool (SC.closed (rightBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))
                    .bot))))))))

abbrev brbnaPinF (D : OddSurfaceDistance) : SFormula 2 :=
  .allNatLt (nP2 D) (brbnaPinBody D)

/-- Bottom–Right disjointness pin pack: a bottom boundary and right boundary share no
qubit (UNCONDITIONAL).  `arithBool`; the eval-cert unfolds the bottom band to
`suppMem_bottom_prop`'s `(row,col)` RHS and the right band to `suppMem_right_prop`'s,
then the geometric core lemma `brbnaCellContra` refutes a common qubit. -/
def brbnaPinPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (brbnaPinF D) := by
  refine PureFamilyDerivA.allNatLtIntro _ ?_
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd3 : D.distance = 2 * D.index + 3 := rfl
  simp only [bulkGuardTA, topClassGuardTA, rightClassGuardTA, leftClassGuardTA, bottomBandGuardTA,
    rightBandGuardTA, baseBTA, baseHalfTA, bulkCountTA, dm1TA, band3, orEqSucc, orEqPair, dP3, dP2,
    k1P3, k2P3, qP3, SFormula.eval, SC.closed, SC.b, STerm.eval, Term.eval, Term.lift, bind,
    Option.bind]
  set q := rho ⟨0, by decide⟩ with hq'
  set k2 := rho ⟨1, by decide⟩ with hk2'
  set k1 := rho ⟨2, by decide⟩ with hk1'
  set d := D.distance with hdd
  have hdge : 3 ≤ d := by omega
  have hdpos : 0 < d := by omega
  by_cases hbulk1 : k1 < (d - 1) * (d - 1)
  · have hb : decide (decide (k1 < (d - 1) * (d - 1)) = false) = false := by
      rw [decide_eq_false_iff_not]; simp [hbulk1]
    simp only [hb, Bool.false_eq_true, if_false, reduceIte]
  · by_cases htop1 : k1 - (d - 1) * (d - 1) < (d - 1) / 2
    · have hb1f : decide (decide (k1 < (d - 1) * (d - 1)) = false) = true := by
        rw [decide_eq_true_eq]; simp [hbulk1]
      have ht1f : decide (decide (k1 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = false := by
        rw [decide_eq_false_iff_not]; simp [htop1]
      simp only [hb1f, ht1f, Bool.false_eq_true, if_false, reduceIte]
    · by_cases hright1 : k1 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)
      · have hb1f : decide (decide (k1 < (d - 1) * (d - 1)) = false) = true := by
          rw [decide_eq_true_eq]; simp [hbulk1]
        have ht1f : decide (decide (k1 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
          rw [decide_eq_true_eq]; simp [htop1]
        have hr1f : decide (decide (k1 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = false := by
          rw [decide_eq_false_iff_not]; simp [hright1]
        simp only [hb1f, ht1f, hr1f, Bool.false_eq_true, if_false, reduceIte]
      · by_cases hleft1 : k1 - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)
        · have hb1f : decide (decide (k1 < (d - 1) * (d - 1)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hbulk1]
          have ht1f : decide (decide (k1 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
            rw [decide_eq_true_eq]; simp [htop1]
          have hr1f : decide (decide (k1 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hright1]
          have hl1f : decide (decide (k1 - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)) = false) = false := by
            rw [decide_eq_false_iff_not]; simp [hleft1]
          simp only [hb1f, ht1f, hr1f, hl1f, Bool.false_eq_true, if_false, reduceIte]
        · have hb1f : decide (decide (k1 < (d - 1) * (d - 1)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hbulk1]
          have ht1f : decide (decide (k1 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
            rw [decide_eq_true_eq]; simp [htop1]
          have hr1f : decide (decide (k1 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hright1]
          have hl1f : decide (decide (k1 - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hleft1]
          by_cases hbulk2 : k2 < (d - 1) * (d - 1)
          · have hb2f : decide (decide (k2 < (d - 1) * (d - 1)) = false) = false := by
              rw [decide_eq_false_iff_not]; simp [hbulk2]
            simp only [hb1f, ht1f, hr1f, hl1f, hb2f, Bool.false_eq_true, if_false, reduceIte]
          · by_cases htop2 : k2 - (d - 1) * (d - 1) < (d - 1) / 2
            · have hb2f : decide (decide (k2 < (d - 1) * (d - 1)) = false) = true := by
                rw [decide_eq_true_eq]; simp [hbulk2]
              have ht2f : decide (decide (k2 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = false := by
                rw [decide_eq_false_iff_not]; simp [htop2]
              simp only [hb1f, ht1f, hr1f, hl1f, hb2f, ht2f, Bool.false_eq_true, if_false, reduceIte]
            · by_cases hright2 : k2 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)
              · have hb2f : decide (decide (k2 < (d - 1) * (d - 1)) = false) = true := by
                  rw [decide_eq_true_eq]; simp [hbulk2]
                have ht2f : decide (decide (k2 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
                  rw [decide_eq_true_eq]; simp [htop2]
                have hr2t : decide (decide (k2 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = true) = true := by
                  rw [decide_eq_true_eq]; simp [hright2]
                simp only [hb1f, ht1f, hr1f, hl1f, hb2f, ht2f, hr2t, if_true]
                set b := k1 - (d - 1) * (d - 1) - 3 * ((d - 1) / 2) with hb
                set r := k2 - (d - 1) * (d - 1) - (d - 1) / 2 with hr
                have hhalf : 2 * ((d - 1) / 2) ≤ d - 1 := by omega
                have hrlt : r < (d - 1) / 2 := by rw [hr]; omega
                simp only [← apply_ite Option.some, Option.some.injEq, Bool.if_true_left,
                  Bool.if_true_right, Bool.if_false_right,
                  Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, Bool.not_eq_false,
                  decide_eq_true_eq, decide_eq_false_iff_not]
                by_contra hcon
                push_neg at hcon
                obtain ⟨⟨hb1r, hb1c⟩, ⟨hcol, hb2r⟩, _⟩ := hcon
                exact brbnaCellContra hhalf hrlt hb1r hb1c hcol hb2r
              · have hb2f : decide (decide (k2 < (d - 1) * (d - 1)) = false) = true := by
                  rw [decide_eq_true_eq]; simp [hbulk2]
                have ht2f : decide (decide (k2 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
                  rw [decide_eq_true_eq]; simp [htop2]
                have hr2f : decide (decide (k2 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = true) = false := by
                  rw [decide_eq_false_iff_not]; simp [hright2]
                simp only [hb1f, ht1f, hr1f, hl1f, hb2f, ht2f, hr2f, Bool.false_eq_true, if_false,
                  reduceIte]

/-- Extract the bottom–right disjointness-pin `⊥` at `boundNat`: under the class
context, the bottom band and right band cannot both fire. -/
def brbnaPinAt {Δ : List (SFormula 3)} (D : OddSurfaceDistance)
    (hW : SFormula.Deriv Δ (brbnaPinF D).weaken)
    (hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken))
    (hBulkFk1 : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b false)))
    (hTopFk1 : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA (dP3 D) k1P3)) (SC.b false)))
    (hRightFk1 : SFormula.Deriv Δ (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k1P3)) (SC.b false)))
    (hLeftFk1 : SFormula.Deriv Δ (.eqBool (SC.closed (leftClassGuardTA (dP3 D) k1P3)) (SC.b false)))
    (hBulkFk2 : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b false)))
    (hTopFk2 : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA (dP3 D) k2P3)) (SC.b false)))
    (hRightCk2 : SFormula.Deriv Δ (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k2P3)) (SC.b true)))
    (hBotB : SFormula.Deriv Δ (.eqBool (SC.closed (bottomBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true)))
    (hRightB : SFormula.Deriv Δ (.eqBool (SC.closed (rightBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))) :
    SFormula.Deriv Δ .bot := by
  have hElim := SFormula.Deriv.allNatLtElim (nP2 D).weaken
    ((brbnaPinBody D).lift 1) SFormula.boundNat hW hq
  have hBody := SFormula.Deriv.applyNatBoundNatBeta (brbnaPinBody D) hElim
  exact SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp
    (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp hBody hBulkFk1)
      hTopFk1) hRightFk1) hLeftFk1) hBulkFk2) hTopFk2) hRightCk2) hBotB |>.mp hRightB

#print axioms brbnaCellContra
#print axioms brbnaPinPack
#print axioms brbnaPinAt

/-- **Bottom–Right boundary↔boundary (non-overlap) closer.**  Row A is the X-type
bottom-boundary stabilizer, row B the Z-type right-boundary stabilizer.  They share no
qubit UNCONDITIONALLY, so the pair commutes.  Routed through the non-overlap path
`pairCommutePointwise`: the `(X,Z)` leaf-pair is closed by the disjointness pin
`brbnaPinAt` (→ `⊥`), the `(Z,X)` leaf-pair by the X-type exclusion `hExcl1`. -/
def pairCommuteBottomRightNonAdj {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hEntryA : SFormula.Deriv Γ (entryAQuant D)) (hEntryB : SFormula.Deriv Γ (entryBQuant D))
    (hk1X : SFormula.Deriv Γ (k1IsX D true))
    (hExcl1 : SFormula.Deriv Γ (typeExclF D k1P))
    (hbulkFk1 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false)))
    (htopFk1 : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false)))
    (hrightFk1 : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k1P)) (SC.b false)))
    (hleftFk1 : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k1P)) (SC.b false)))
    (hbulkFk2 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)))
    (htopFk2 : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false)))
    (hrightCk2 : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b true)))
    (hPin : SFormula.Deriv Γ (brbnaPinF D)) :
    SFormula.Deriv Γ (pairGoal D) := by
  refine pairCommutePointwise D hEntryA hEntryB ?hXZ ?hZX
  · -- (X, Z): both leaves genuinely fire; the disjointness pin forces ⊥.
    intro Δ' lift hLeafA hLeafB
    have hbulkFk1Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b false)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false)) hbulkFk1))
    have htopFk1Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (topClassGuardTA (dP3 D) k1P3)) (SC.b false)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false)) htopFk1))
    have hrightFk1Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k1P3)) (SC.b false)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (rightClassGuardTA (dP2 D) k1P)) (SC.b false)) hrightFk1))
    have hleftFk1Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (leftClassGuardTA (dP3 D) k1P3)) (SC.b false)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (leftClassGuardTA (dP2 D) k1P)) (SC.b false)) hleftFk1))
    have hbulkFk2Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b false)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)) hbulkFk2))
    have htopFk2Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (topClassGuardTA (dP3 D) k2P3)) (SC.b false)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false)) htopFk2))
    have hrightCk2Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k2P3)) (SC.b true)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b true)) hrightCk2))
    have hPinΔ : SFormula.Deriv Δ' (brbnaPinF D).weaken :=
      lift (cw1 (SFormula.Deriv.weakenFresh (A := brbnaPinF D) hPin))
    have hq : SFormula.Deriv Δ' (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken) :=
      lift (.hyp List.mem_cons_self)
    have hBotB := bbBottomBandFromX D hbulkFk1Δ htopFk1Δ hrightFk1Δ hleftFk1Δ hLeafA
    have hRightB := brRightBandFromZ D hbulkFk2Δ htopFk2Δ hrightCk2Δ hLeafB
    have hBot := brbnaPinAt D hPinΔ hq hbulkFk1Δ htopFk1Δ hrightFk1Δ hleftFk1Δ hbulkFk2Δ htopFk2Δ
      hrightCk2Δ hBotB hRightB
    exact SFormula.Deriv.botElim hBot
  · -- (Z, X): A leaf = Z impossible since A is X-type → type-exclusion contradiction.
    intro Δ' lift hLeafA hLeafB
    have hk1Xd : SFormula.Deriv Δ' (k1IsX D true).weaken :=
      lift (cw1 (SFormula.Deriv.weakenFresh (A := k1IsX D true) hk1X))
    have hExcl1d : SFormula.Deriv Δ' (typeExclF D k1P).weaken :=
      lift (cw1 (SFormula.Deriv.weakenFresh (A := typeExclF D k1P) hExcl1))
    have hxnbz := SFormula.Deriv.andElimLeft hExcl1d
    have hxnrz := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hExcl1d)
    have hxnlz := SFormula.Deriv.andElimLeft
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hExcl1d))
    refine withLeafG D k1P3 _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro Δ'' lift2 hI
      exact leafNotPandZ D k1P3 Pauli.I rfl hI (lift2 hLeafA)
    · intro Δ'' lift2 _ hbulk hkind
      have hkindF := SFormula.Deriv.mp (SFormula.Deriv.mp (lift2 hxnbz) (lift2 hk1Xd)) hbulk
      exact eqBoolContra _ hkind hkindF
    · intro Δ'' lift2 hX _ _
      exact leafNotPandZ D k1P3 Pauli.X rfl hX (lift2 hLeafA)
    · intro Δ'' lift2 hX _ _
      exact leafNotPandZ D k1P3 Pauli.X rfl hX (lift2 hLeafA)
    · intro Δ'' lift2 _ hbulk htop hright
      have hrightF := SFormula.Deriv.mp (SFormula.Deriv.mp
        (SFormula.Deriv.mp (lift2 hxnrz) (lift2 hk1Xd)) hbulk) htop
      exact eqBoolContra _ hright hrightF
    · intro Δ'' lift2 _ hbulk htop hright hleft
      have hleftF := SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp
        (SFormula.Deriv.mp (lift2 hxnlz) (lift2 hk1Xd)) hbulk) htop) hright
      exact eqBoolContra _ hleft hleftF
    · intro Δ'' lift2 hX _ _ _ _
      exact leafNotPandZ D k1P3 Pauli.X rfl hX (lift2 hLeafA)

#print axioms pairCommuteBottomRightNonAdj

/-! ## Bottom–Left BOUNDARY↔BOUNDARY (non-overlap) different-type pair

Row A (`k1`) is an X-type BOTTOM-boundary stabilizer, row B (`k2`) a Z-type
LEFT-boundary stabilizer.  Disjointness is UNCONDITIONAL.  The bottom boundary `k1`
occupies row `d−1`, cols `{2·botIdx+1, 2·botIdx+2}`, so its col is `≥ 1`; the left
boundary `k2` occupies column `0`.  A common qubit would need col `≥ 1` (bottom) AND col
`0` (left): impossible. -/

/-- **Core geometric contradiction** (pure `Nat`) for bottom–left.  A bottom boundary at
row `d−1`, cols `{2·b+1, 2·b+2}`, and a left boundary at column `0`, rows
`{2·l+1, 2·l+2}`, sharing a slot `(qr, qc)`: bottom forces `qc ∈ {2·b+1, 2·b+2}`, so
`qc ≥ 1`; left forces `qc = 0`.  Contradiction. -/
private theorem blbnaCellContra
    {qr qc b l d : Nat}
    (hBotR : qr = d - 1) (hBotC : qc = 2 * b + 1 ∨ qc = 2 * b + 2)
    (hLeftC : qc = 0) (hLeftR : qr = 2 * l + 1 ∨ qr = 2 * l + 2) : False := by
  rcases hBotC with h | h <;> omega

/-- The bottom–left disjointness-pin body (arity 3, `k1 = var 2`, `k2 = var 1`,
`q = var 0`): under the bottom class context for `k1` (`¬bulk ∧ ¬top ∧ ¬right ∧
¬left`), the left class context for `k2` (`¬bulk ∧ ¬top ∧ ¬right ∧ leftClass`), and both
bands firing at `q`, derive `⊥` — the bottom boundary and the left boundary cannot share
a qubit. -/
abbrev blbnaPinBody (D : OddSurfaceDistance) : SFormula 3 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b false))
    (.imp (.eqBool (SC.closed (topClassGuardTA (dP3 D) k1P3)) (SC.b false))
      (.imp (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k1P3)) (SC.b false))
        (.imp (.eqBool (SC.closed (leftClassGuardTA (dP3 D) k1P3)) (SC.b false))
          (.imp (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b false))
            (.imp (.eqBool (SC.closed (topClassGuardTA (dP3 D) k2P3)) (SC.b false))
              (.imp (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k2P3)) (SC.b false))
                (.imp (.eqBool (SC.closed (leftClassGuardTA (dP3 D) k2P3)) (SC.b true))
                  (.imp (.eqBool (SC.closed (bottomBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true))
                    (.imp (.eqBool (SC.closed (leftBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))
                      .bot)))))))))

abbrev blbnaPinF (D : OddSurfaceDistance) : SFormula 2 :=
  .allNatLt (nP2 D) (blbnaPinBody D)

/-- Bottom–Left disjointness pin pack: a bottom boundary and left boundary share no
qubit (UNCONDITIONAL).  `arithBool`; the eval-cert unfolds the bottom band to
`suppMem_bottom_prop`'s `(row,col)` RHS and the left band to `suppMem_left_prop`'s, then
the geometric core lemma `blbnaCellContra` refutes a common qubit. -/
def blbnaPinPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (blbnaPinF D) := by
  refine PureFamilyDerivA.allNatLtIntro _ ?_
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd3 : D.distance = 2 * D.index + 3 := rfl
  simp only [bulkGuardTA, topClassGuardTA, rightClassGuardTA, leftClassGuardTA, bottomBandGuardTA,
    leftBandGuardTA, baseBTA, baseHalfTA, bulkCountTA, dm1TA, band3, orEqSucc, orEqPair, dP3, dP2,
    k1P3, k2P3, qP3, SFormula.eval, SC.closed, SC.b, STerm.eval, Term.eval, Term.lift, bind,
    Option.bind]
  set q := rho ⟨0, by decide⟩ with hq'
  set k2 := rho ⟨1, by decide⟩ with hk2'
  set k1 := rho ⟨2, by decide⟩ with hk1'
  set d := D.distance with hdd
  have hdge : 3 ≤ d := by omega
  have hdpos : 0 < d := by omega
  by_cases hbulk1 : k1 < (d - 1) * (d - 1)
  · have hb : decide (decide (k1 < (d - 1) * (d - 1)) = false) = false := by
      rw [decide_eq_false_iff_not]; simp [hbulk1]
    simp only [hb, Bool.false_eq_true, if_false, reduceIte]
  · by_cases htop1 : k1 - (d - 1) * (d - 1) < (d - 1) / 2
    · have hb1f : decide (decide (k1 < (d - 1) * (d - 1)) = false) = true := by
        rw [decide_eq_true_eq]; simp [hbulk1]
      have ht1f : decide (decide (k1 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = false := by
        rw [decide_eq_false_iff_not]; simp [htop1]
      simp only [hb1f, ht1f, Bool.false_eq_true, if_false, reduceIte]
    · by_cases hright1 : k1 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)
      · have hb1f : decide (decide (k1 < (d - 1) * (d - 1)) = false) = true := by
          rw [decide_eq_true_eq]; simp [hbulk1]
        have ht1f : decide (decide (k1 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
          rw [decide_eq_true_eq]; simp [htop1]
        have hr1f : decide (decide (k1 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = false := by
          rw [decide_eq_false_iff_not]; simp [hright1]
        simp only [hb1f, ht1f, hr1f, Bool.false_eq_true, if_false, reduceIte]
      · by_cases hleft1 : k1 - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)
        · have hb1f : decide (decide (k1 < (d - 1) * (d - 1)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hbulk1]
          have ht1f : decide (decide (k1 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
            rw [decide_eq_true_eq]; simp [htop1]
          have hr1f : decide (decide (k1 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hright1]
          have hl1f : decide (decide (k1 - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)) = false) = false := by
            rw [decide_eq_false_iff_not]; simp [hleft1]
          simp only [hb1f, ht1f, hr1f, hl1f, Bool.false_eq_true, if_false, reduceIte]
        · have hb1f : decide (decide (k1 < (d - 1) * (d - 1)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hbulk1]
          have ht1f : decide (decide (k1 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
            rw [decide_eq_true_eq]; simp [htop1]
          have hr1f : decide (decide (k1 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hright1]
          have hl1f : decide (decide (k1 - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hleft1]
          by_cases hbulk2 : k2 < (d - 1) * (d - 1)
          · have hb2f : decide (decide (k2 < (d - 1) * (d - 1)) = false) = false := by
              rw [decide_eq_false_iff_not]; simp [hbulk2]
            simp only [hb1f, ht1f, hr1f, hl1f, hb2f, Bool.false_eq_true, if_false, reduceIte]
          · by_cases htop2 : k2 - (d - 1) * (d - 1) < (d - 1) / 2
            · have hb2f : decide (decide (k2 < (d - 1) * (d - 1)) = false) = true := by
                rw [decide_eq_true_eq]; simp [hbulk2]
              have ht2f : decide (decide (k2 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = false := by
                rw [decide_eq_false_iff_not]; simp [htop2]
              simp only [hb1f, ht1f, hr1f, hl1f, hb2f, ht2f, Bool.false_eq_true, if_false, reduceIte]
            · by_cases hright2 : k2 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)
              · have hb2f : decide (decide (k2 < (d - 1) * (d - 1)) = false) = true := by
                  rw [decide_eq_true_eq]; simp [hbulk2]
                have ht2f : decide (decide (k2 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
                  rw [decide_eq_true_eq]; simp [htop2]
                have hr2f : decide (decide (k2 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = false := by
                  rw [decide_eq_false_iff_not]; simp [hright2]
                simp only [hb1f, ht1f, hr1f, hl1f, hb2f, ht2f, hr2f, Bool.false_eq_true, if_false,
                  reduceIte]
              · by_cases hleft2 : k2 - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)
                · have hb2f : decide (decide (k2 < (d - 1) * (d - 1)) = false) = true := by
                    rw [decide_eq_true_eq]; simp [hbulk2]
                  have ht2f : decide (decide (k2 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
                    rw [decide_eq_true_eq]; simp [htop2]
                  have hr2f : decide (decide (k2 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = true := by
                    rw [decide_eq_true_eq]; simp [hright2]
                  have hl2t : decide (decide (k2 - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)) = true) = true := by
                    rw [decide_eq_true_eq]; simp [hleft2]
                  simp only [hb1f, ht1f, hr1f, hl1f, hb2f, ht2f, hr2f, hl2t, if_true]
                  set b := k1 - (d - 1) * (d - 1) - 3 * ((d - 1) / 2) with hb
                  set l := k2 - (d - 1) * (d - 1) - 2 * ((d - 1) / 2) with hl
                  simp only [← apply_ite Option.some, Option.some.injEq, Bool.if_true_left,
                    Bool.if_true_right, Bool.if_false_right,
                    Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, Bool.not_eq_false,
                    decide_eq_true_eq, decide_eq_false_iff_not]
                  by_contra hcon
                  push_neg at hcon
                  obtain ⟨⟨hb1r, hb1c⟩, ⟨hcol, hb2r⟩, _⟩ := hcon
                  exact blbnaCellContra hb1r hb1c hcol hb2r
                · have hb2f : decide (decide (k2 < (d - 1) * (d - 1)) = false) = true := by
                    rw [decide_eq_true_eq]; simp [hbulk2]
                  have ht2f : decide (decide (k2 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
                    rw [decide_eq_true_eq]; simp [htop2]
                  have hr2f : decide (decide (k2 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = true := by
                    rw [decide_eq_true_eq]; simp [hright2]
                  have hl2f : decide (decide (k2 - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)) = true) = false := by
                    rw [decide_eq_false_iff_not]; simp [hleft2]
                  simp only [hb1f, ht1f, hr1f, hl1f, hb2f, ht2f, hr2f, hl2f, Bool.false_eq_true,
                    if_false, reduceIte]

/-- Extract the bottom–left disjointness-pin `⊥` at `boundNat`: under the class context,
the bottom band and left band cannot both fire. -/
def blbnaPinAt {Δ : List (SFormula 3)} (D : OddSurfaceDistance)
    (hW : SFormula.Deriv Δ (blbnaPinF D).weaken)
    (hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken))
    (hBulkFk1 : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b false)))
    (hTopFk1 : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA (dP3 D) k1P3)) (SC.b false)))
    (hRightFk1 : SFormula.Deriv Δ (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k1P3)) (SC.b false)))
    (hLeftFk1 : SFormula.Deriv Δ (.eqBool (SC.closed (leftClassGuardTA (dP3 D) k1P3)) (SC.b false)))
    (hBulkFk2 : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b false)))
    (hTopFk2 : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA (dP3 D) k2P3)) (SC.b false)))
    (hRightFk2 : SFormula.Deriv Δ (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k2P3)) (SC.b false)))
    (hLeftCk2 : SFormula.Deriv Δ (.eqBool (SC.closed (leftClassGuardTA (dP3 D) k2P3)) (SC.b true)))
    (hBotB : SFormula.Deriv Δ (.eqBool (SC.closed (bottomBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true)))
    (hLeftB : SFormula.Deriv Δ (.eqBool (SC.closed (leftBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))) :
    SFormula.Deriv Δ .bot := by
  have hElim := SFormula.Deriv.allNatLtElim (nP2 D).weaken
    ((blbnaPinBody D).lift 1) SFormula.boundNat hW hq
  have hBody := SFormula.Deriv.applyNatBoundNatBeta (blbnaPinBody D) hElim
  exact SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp
    (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp
      (SFormula.Deriv.mp hBody hBulkFk1) hTopFk1) hRightFk1) hLeftFk1) hBulkFk2) hTopFk2)
        hRightFk2) hLeftCk2) hBotB |>.mp hLeftB

#print axioms blbnaCellContra
#print axioms blbnaPinPack
#print axioms blbnaPinAt

/-- **Bottom–Left boundary↔boundary (non-overlap) closer.**  Row A is the X-type
bottom-boundary stabilizer, row B the Z-type left-boundary stabilizer.  They share no
qubit UNCONDITIONALLY, so the pair commutes.  Routed through the non-overlap path
`pairCommutePointwise`: the `(X,Z)` leaf-pair is closed by the disjointness pin
`blbnaPinAt` (→ `⊥`), the `(Z,X)` leaf-pair by the X-type exclusion `hExcl1`. -/
def pairCommuteBottomLeftNonAdj {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hEntryA : SFormula.Deriv Γ (entryAQuant D)) (hEntryB : SFormula.Deriv Γ (entryBQuant D))
    (hk1X : SFormula.Deriv Γ (k1IsX D true))
    (hExcl1 : SFormula.Deriv Γ (typeExclF D k1P))
    (hbulkFk1 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false)))
    (htopFk1 : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false)))
    (hrightFk1 : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k1P)) (SC.b false)))
    (hleftFk1 : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k1P)) (SC.b false)))
    (hbulkFk2 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)))
    (htopFk2 : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false)))
    (hrightFk2 : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false)))
    (hleftCk2 : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b true)))
    (hPin : SFormula.Deriv Γ (blbnaPinF D)) :
    SFormula.Deriv Γ (pairGoal D) := by
  refine pairCommutePointwise D hEntryA hEntryB ?hXZ ?hZX
  · -- (X, Z): both leaves genuinely fire; the disjointness pin forces ⊥.
    intro Δ' lift hLeafA hLeafB
    have hbulkFk1Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b false)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false)) hbulkFk1))
    have htopFk1Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (topClassGuardTA (dP3 D) k1P3)) (SC.b false)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false)) htopFk1))
    have hrightFk1Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k1P3)) (SC.b false)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (rightClassGuardTA (dP2 D) k1P)) (SC.b false)) hrightFk1))
    have hleftFk1Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (leftClassGuardTA (dP3 D) k1P3)) (SC.b false)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (leftClassGuardTA (dP2 D) k1P)) (SC.b false)) hleftFk1))
    have hbulkFk2Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b false)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)) hbulkFk2))
    have htopFk2Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (topClassGuardTA (dP3 D) k2P3)) (SC.b false)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false)) htopFk2))
    have hrightFk2Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k2P3)) (SC.b false)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false)) hrightFk2))
    have hleftCk2Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (leftClassGuardTA (dP3 D) k2P3)) (SC.b true)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b true)) hleftCk2))
    have hPinΔ : SFormula.Deriv Δ' (blbnaPinF D).weaken :=
      lift (cw1 (SFormula.Deriv.weakenFresh (A := blbnaPinF D) hPin))
    have hq : SFormula.Deriv Δ' (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken) :=
      lift (.hyp List.mem_cons_self)
    have hBotB := bbBottomBandFromX D hbulkFk1Δ htopFk1Δ hrightFk1Δ hleftFk1Δ hLeafA
    have hLeftB := blLeftBandFromZ D hbulkFk2Δ htopFk2Δ hrightFk2Δ hleftCk2Δ hLeafB
    have hBot := blbnaPinAt D hPinΔ hq hbulkFk1Δ htopFk1Δ hrightFk1Δ hleftFk1Δ hbulkFk2Δ htopFk2Δ
      hrightFk2Δ hleftCk2Δ hBotB hLeftB
    exact SFormula.Deriv.botElim hBot
  · -- (Z, X): A leaf = Z impossible since A is X-type → type-exclusion contradiction.
    intro Δ' lift hLeafA hLeafB
    have hk1Xd : SFormula.Deriv Δ' (k1IsX D true).weaken :=
      lift (cw1 (SFormula.Deriv.weakenFresh (A := k1IsX D true) hk1X))
    have hExcl1d : SFormula.Deriv Δ' (typeExclF D k1P).weaken :=
      lift (cw1 (SFormula.Deriv.weakenFresh (A := typeExclF D k1P) hExcl1))
    have hxnbz := SFormula.Deriv.andElimLeft hExcl1d
    have hxnrz := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hExcl1d)
    have hxnlz := SFormula.Deriv.andElimLeft
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hExcl1d))
    refine withLeafG D k1P3 _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro Δ'' lift2 hI
      exact leafNotPandZ D k1P3 Pauli.I rfl hI (lift2 hLeafA)
    · intro Δ'' lift2 _ hbulk hkind
      have hkindF := SFormula.Deriv.mp (SFormula.Deriv.mp (lift2 hxnbz) (lift2 hk1Xd)) hbulk
      exact eqBoolContra _ hkind hkindF
    · intro Δ'' lift2 hX _ _
      exact leafNotPandZ D k1P3 Pauli.X rfl hX (lift2 hLeafA)
    · intro Δ'' lift2 hX _ _
      exact leafNotPandZ D k1P3 Pauli.X rfl hX (lift2 hLeafA)
    · intro Δ'' lift2 _ hbulk htop hright
      have hrightF := SFormula.Deriv.mp (SFormula.Deriv.mp
        (SFormula.Deriv.mp (lift2 hxnrz) (lift2 hk1Xd)) hbulk) htop
      exact eqBoolContra _ hright hrightF
    · intro Δ'' lift2 _ hbulk htop hright hleft
      have hleftF := SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp
        (SFormula.Deriv.mp (lift2 hxnlz) (lift2 hk1Xd)) hbulk) htop) hright
      exact eqBoolContra _ hleft hleftF
    · intro Δ'' lift2 hX _ _ _ _
      exact leafNotPandZ D k1P3 Pauli.X rfl hX (lift2 hLeafA)

#print axioms pairCommuteBottomLeftNonAdj

/-- The supporting fact bundle for the pair goal: both flat-entry packs and both
type-exclusion packs. -/
abbrev pairBundleF (D : OddSurfaceDistance) : SFormula 2 :=
  .and (entryAQuant D) (.and (entryBQuant D)
    (.and (typeExclF D k1P) (typeExclF D k2P)))

def pairBundle (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (pairBundleF D) :=
  pfdaAnd2 (entryAQuantPack D) (pfdaAnd2 (entryBQuantPack D)
    (pfdaAnd2 (typeExclPackK1 D) (typeExclPackK2 D)))

/-! ## Bulk–Bulk class-combo dispatcher (VALIDATION SPIKE)

`dispatchBulkBulk` routes the BOTH-rows-bulk case (necessarily different CSS type)
to the four overlap closers (`commBulkBulkHoriz`/`HorizL`/`Vert`/`VertU`) or the
non-overlap handler (`pairCommuteBulkBulkNonAdj`), by a nested `boolCases` cascade
on the four relative-index conditions `k2 = k1±1`, `k2 = k1±(d−1)`.

The kind facts (`kind k1 = false` X-kind, `kind k2 = true` Z-kind) come FOR FREE
from the existing `typeExclF` packs: `xtNotBulkZF` (`isXType → bulk → ¬kind`) and
`ztNotBulkXF` (`¬isXType → bulk → kind`) are already conjuncts of `typeExclF`.

The validity guards (`bhRowF` etc.) and the non-adjacency (`bbnaNonAdjTA2`) are the
genuinely-new pieces: each is a `k`-only conditional `arithBool` fact whose proof
uses the KIND-PARITY of two adjacent/non-adjacent bulk cells.

Because the band/pin/range `arithBool` packs and the four flat-entries per route are
`PureFamilyDerivA` (the `Deriv` calculus has NO `arithBool`/`recUnfold` leaf, so they
can NEVER be re-derived inside an arbitrary context `Γ`), they are gathered — with
all four routes' packs/entries, the bbna pin, and the validity/non-adjacency facts —
into ONE super-bundle `dbbBundleF`, proved `dbbBundle : PureFamilyDerivA … dbbBundleF`
by `pfdaAnd2`-chaining (the same "cut-in" pattern `pairBundle` uses).  The dispatcher
then extracts every closer input via `andElim` on `hbundle : Deriv Γ (dbbBundleF D)`. -/

/-- Kind of `k1` is X-kind (`baseKindGuardTA = false`) from `isXType(k1)=true` and
`bulk(k1)=true`, via the existing `xtNotBulkZF` conjunct of `typeExclF k1`. -/
def dbbKindK1OfIsX {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hExcl1 : SFormula.Deriv Γ (typeExclF D k1P))
    (hk1X : SFormula.Deriv Γ (k1IsX D true))
    (hBulkK1 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true))) :
    SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k1P)) (SC.b false)) :=
  SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.andElimLeft hExcl1) hk1X) hBulkK1

/-- Kind of `k2` is Z-kind (`baseKindGuardTA = true`) from `isXType(k2)=false` and
`bulk(k2)=true`, via the existing `ztNotBulkXF` conjunct of `typeExclF k2`. -/
def dbbKindK2OfNotIsX {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hExcl2 : SFormula.Deriv Γ (typeExclF D k2P))
    (hk2Z : SFormula.Deriv Γ (k2IsX D false))
    (hBulkK2 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true))) :
    SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k2P)) (SC.b true)) :=
  SFormula.Deriv.mp (SFormula.Deriv.mp
    (SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hExcl2)))) hk2Z) hBulkK2

/-! ### Validity guards from kind-parity (conditional `arithBool` facts)

Each of the four adjacency routes needs a VALIDITY guard (`bhRowF` etc.) that the
closer consumes.  Under DIFFERENT kind (X-kind `k1`, Z-kind `k2`) plus the route's
adjacency, the wrap case is impossible (a wrap would preserve the cell-parity, hence
the kind, contradicting different kind).  Each is a `k`-only conditional `arithBool`
fact: `kind k1 = false → kind k2 = true → bulk k1 = true → <adj> → <guard>`. -/

/-- Horizontal-right validity (`k2 = k1+1`): `cellC k1 + 1 < d−1` (no column wrap). -/
abbrev dbbBhRowImpF (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k1P)) (SC.b false))
    (.imp (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k2P)) (SC.b true))
      (.imp (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true))
        (.imp (bhAdjF D) (bhRowF D))))

def dbbBhRowImp (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (dbbBhRowImpF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [baseKindGuardTA, bulkGuardTA, bulkCountTA, dm1TA,
    dP2, k1P, k2P, SFormula.eval, SC.closed, SC.b, STerm.eval, Term.eval, Term.lift,
    bind, Option.bind]
  set k1 := rho ⟨1, by decide⟩ with hk1
  set k2 := rho ⟨0, by decide⟩ with hk2
  set d := D.distance with hdd
  have hdge : 3 ≤ d := by omega
  set m := d - 1 with hm
  have hm2 : 2 ≤ m := by omega
  have hmeven : m % 2 = 0 := by omega
  -- The wrap-impossible core: under different kind and `k2 = k1+1`, `c1+1 < m`.
  have hcore : (k1 / m + k1 % m) % 2 ≠ 0 → (k2 / m + k2 % m) % 2 = 0 →
      k1 < m * m → k2 = k1 + 1 → k1 % m + 1 < m := by
    intro hkind1 hkind2 hbulk1 hadj
    set r1 := k1 / m with hr1
    set c1 := k1 % m with hc1
    have hc1lt : c1 < m := Nat.mod_lt k1 (by omega)
    have hkdec : k1 = m * r1 + c1 := (Nat.div_add_mod k1 m).symm
    by_contra hge
    push_neg at hge
    have hc1eq : c1 = m - 1 := by omega
    have hk2val : k2 = m * (r1 + 1) := by
      rw [Nat.mul_succ, hadj, hkdec, hc1eq]; omega
    have hc2 : k2 % m = 0 := by rw [hk2val]; exact Nat.mul_mod_right m (r1 + 1)
    have hr2 : k2 / m = r1 + 1 := by
      rw [hk2val]; exact Nat.mul_div_cancel_left (r1 + 1) (by omega)
    rw [hc2, hr2] at hkind2
    rw [hc1eq] at hkind1
    omega
  -- Reduce the nested `if`-chain by casing on each guard.
  by_cases hkind1 : (k1 / m + k1 % m) % 2 = 0
  · rw [hkind1]; simp
  · by_cases hkind2 : (k2 / m + k2 % m) % 2 = 0
    · by_cases hbulk1 : k1 < m * m
      · by_cases hadj : k2 = k1 + 1
        · have hres := hcore hkind1 hkind2 hbulk1 hadj
          simp only [decide_eq_false_iff_not.mpr hkind1, decide_eq_true_eq.mpr hkind2,
            decide_eq_true_eq.mpr hbulk1, decide_eq_true_eq.mpr hadj,
            decide_eq_true_eq.mpr hres]
          simp
        · simp only [decide_eq_false_iff_not.mpr hadj]; simp
      · simp only [decide_eq_false_iff_not.mpr hbulk1]; simp
    · simp only [decide_eq_false_iff_not.mpr hkind2]; simp

/-- Vertical-down validity (`k2 = k1+(d−1)`): `cellR k1 + 1 < d−1` (so `k2` is a
valid bulk row).  Follows from `bulk(k2)=true` alone (no kind-parity needed):
`k2 = m·(r1+1) + c1 < m·m` forces `r1+1 < m`. -/
abbrev dbbBvRowImpF (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true))
    (.imp (bvAdjF D) (bvRowF D))

def dbbBvRowImp (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (dbbBvRowImpF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [bvAdjF, bvRowF, bulkGuardTA, bulkCountTA, dm1TA,
    dP2, k1P, k2P, SFormula.eval, SC.closed, SC.b, STerm.eval, Term.eval, Term.lift,
    bind, Option.bind]
  set k1 := rho ⟨1, by decide⟩ with hk1
  set k2 := rho ⟨0, by decide⟩ with hk2
  set d := D.distance with hdd
  have hdge : 3 ≤ d := by omega
  set m := d - 1 with hm
  have hm2 : 2 ≤ m := by omega
  -- Core: bulk(k2) ∧ k2 = k1+m ⟹ r1+1 < m.
  have hcore : k2 < m * m → k2 = k1 + m → k1 / m + 1 < m := by
    intro hbulk2 hadj
    set r1 := k1 / m with hr1
    set c1 := k1 % m with hc1
    have hc1lt : c1 < m := Nat.mod_lt k1 (by omega)
    have hkdec : k1 = m * r1 + c1 := (Nat.div_add_mod k1 m).symm
    by_contra hge
    push_neg at hge
    -- r1+1 ≥ m, so k2 = m*r1+c1+m = m*(r1+1)+c1 ≥ m*m, contradicting bulk(k2).
    have hk2val : k2 = m * (r1 + 1) + c1 := by rw [hadj, hkdec, Nat.mul_succ]; omega
    have : m * m ≤ m * (r1 + 1) := Nat.mul_le_mul_left m (by omega)
    omega
  by_cases hbulk2 : k2 < m * m
  · by_cases hadj : k2 = k1 + m
    · have hres := hcore hbulk2 hadj
      simp only [decide_eq_true_eq.mpr hbulk2, decide_eq_true_eq.mpr hadj,
        decide_eq_true_eq.mpr hres]
      simp
    · simp only [decide_eq_false_iff_not.mpr hadj]; simp
  · simp only [decide_eq_false_iff_not.mpr hbulk2]; simp

/-- Horizontal-left validity (`k2 = k1−1`): `0 < cellC k1` (so `k2` is the genuine
left neighbour in the SAME row).  When `cellC k1 = 0`, `k2 = k1−1` would land in the
previous row (or `k1 = k2 = 0`), which under different kind is impossible — so this
is the routing GUARD: if it fails, the pair is non-overlapping. -/
abbrev dbbBhlColImpF (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k1P)) (SC.b false))
    (.imp (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k2P)) (SC.b true))
      (.imp (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true))
        (.imp (bhlAdjF D) (bhlColF D))))

def dbbBhlColImp (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (dbbBhlColImpF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [bhlAdjF, bhlColF, baseKindGuardTA, bulkGuardTA, bulkCountTA, dm1TA,
    dP2, k1P, k2P, SFormula.eval, SC.closed, SC.b, STerm.eval, Term.eval, Term.lift,
    bind, Option.bind]
  set k1 := rho ⟨1, by decide⟩ with hk1
  set k2 := rho ⟨0, by decide⟩ with hk2
  set d := D.distance with hdd
  have hdge : 3 ≤ d := by omega
  set m := d - 1 with hm
  have hm2 : 2 ≤ m := by omega
  have hmeven : m % 2 = 0 := by omega
  -- Core: different kind ∧ k2 = k1−1 ⟹ 0 < c1.
  have hcore : (k1 / m + k1 % m) % 2 ≠ 0 → (k2 / m + k2 % m) % 2 = 0 →
      k1 < m * m → k2 = k1 - 1 → 0 < k1 % m := by
    intro hkind1 hkind2 hbulk1 hadj
    have hc1lt : k1 % m < m := Nat.mod_lt k1 (by omega)
    have hkdec : k1 = m * (k1 / m) + k1 % m := (Nat.div_add_mod k1 m).symm
    by_contra hge
    push_neg at hge
    have hc1eq : k1 % m = 0 := by omega
    have hk1val : k1 = m * (k1 / m) := by omega
    rcases Nat.eq_zero_or_pos (k1 / m) with hr0 | hr1pos
    · -- k1 = 0, k2 = k1 - 1 = 0; kind(k1) = kind(k2), contradiction.
      have hk1z : k1 = 0 := by rw [hk1val, hr0, Nat.mul_zero]
      have hk2z : k2 = 0 := by omega
      rw [hk1z] at hkind1; rw [hk2z] at hkind2; exact hkind1 hkind2
    · -- k1 = m·r1 (r1 ≥ 1): k2 = m·r1 − 1 = (m−1) + m·(r1−1).
      set r1 := k1 / m with hr1d
      have hk2val : k2 = (m - 1) + m * (r1 - 1) := by
        have hmr : m * r1 = m * (r1 - 1) + m := by
          conv_lhs => rw [show r1 = (r1 - 1) + 1 by omega]
          rw [Nat.mul_succ]
        omega
      have hc2 : k2 % m = m - 1 := by
        rw [hk2val, Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt (by omega)
      have hr2 : k2 / m = r1 - 1 := by
        rw [hk2val, Nat.add_mul_div_left _ _ (by omega : 0 < m),
          Nat.div_eq_of_lt (by omega), Nat.zero_add]
      rw [hc2, hr2] at hkind2
      rw [hc1eq, Nat.add_zero] at hkind1
      omega
  by_cases hkind1 : (k1 / m + k1 % m) % 2 = 0
  · rw [hkind1]; simp
  · by_cases hkind2 : (k2 / m + k2 % m) % 2 = 0
    · by_cases hbulk1 : k1 < m * m
      · by_cases hadj : k2 = k1 - 1
        · have hres := hcore hkind1 hkind2 hbulk1 hadj
          simp only [decide_eq_false_iff_not.mpr hkind1, decide_eq_true_eq.mpr hkind2,
            decide_eq_true_eq.mpr hbulk1, decide_eq_true_eq.mpr hadj,
            decide_eq_true_eq.mpr hres]
          simp
        · simp only [decide_eq_false_iff_not.mpr hadj]; simp
      · simp only [decide_eq_false_iff_not.mpr hbulk1]; simp
    · simp only [decide_eq_false_iff_not.mpr hkind2]; simp

/-! ### Non-adjacency (for the non-overlap route)

The cell-form non-edge-adjacency `bbnaNonAdjTA2` is what `pairCommuteBulkBulkNonAdj`
consumes.  It follows from the failure of the four INDEX adjacency conditions plus
the cell decompositions `k = m·(k/m) + k%m`.  TWO leaves of the routing reach
non-overlap, so two facts:
* `dbbNonAdjAll`: all four `k2 = k1±1`, `k2 = k1±(d−1)` fail;
* `dbbNonAdjVu`:  `k2 = k1−(d−1)` holds but `cellR k1 = 0` (so `k2` is the row-0
  truncation `0`), and `k2 ≠ k1−1` (rules out the `cellC k1 = 1` adjacency). -/

/-- Pure-Nat core: two bulk cells whose four index-adjacencies all fail are NOT
edge-adjacent in cell coordinates. -/
private theorem dbbNonAdjAllCore {m r1 c1 r2 c2 : Nat} (hm : 2 ≤ m)
    (hc1 : c1 < m) (hc2 : c2 < m)
    (hp1 : m * r2 + c2 ≠ m * r1 + c1 + 1) (hpm : m * r2 + c2 ≠ m * r1 + c1 + m)
    (hm1 : m * r2 + c2 ≠ m * r1 + c1 - 1) (hmm : m * r2 + c2 ≠ m * r1 + c1 - m) :
    ¬((r1 = r2 ∧ (c1 = c2 + 1 ∨ c2 = c1 + 1)) ∨
      (c1 = c2 ∧ (r1 = r2 + 1 ∨ r2 = r1 + 1))) := by
  rintro (⟨hr, hc | hc⟩ | ⟨hc, hr | hr⟩) <;> subst hr <;> subst hc <;>
    (try simp only [Nat.mul_succ] at hp1 hpm hm1 hmm) <;> omega

/-- Non-overlap via all-four-fail.  The four index conditions are given as the
`.eqBool … (SC.b false)` produced directly by the routing `boolCases` false branches. -/
abbrev dbbNonAdjAllF (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true))
    (.imp (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true))
      (.imp (.eqBool (SC.closed (.eqNat k2P (.add k1P (.natLit 1)))) (SC.b false))
        (.imp (.eqBool (SC.closed (.eqNat k2P (.add k1P (dm1TA (dP2 D))))) (SC.b false))
          (.imp (.eqBool (SC.closed (.eqNat k2P (.sub k1P (.natLit 1)))) (SC.b false))
            (.imp (.eqBool (SC.closed (.eqNat k2P (.sub k1P (dm1TA (dP2 D))))) (SC.b false))
              (.eqBool (SC.closed (bbnaNonAdjTA2 D)) (SC.b true)))))))

def dbbNonAdjAll (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (dbbNonAdjAllF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [bbnaNonAdjTA2, bbnaEdgeAdjTA2,
    bulkGuardTA, bulkCountTA, dm1TA, dP2, k1P, k2P, SFormula.eval, SC.closed, SC.b,
    STerm.eval, Term.eval, Term.lift, bind, Option.bind]
  set k1 := rho ⟨1, by decide⟩ with hk1
  set k2 := rho ⟨0, by decide⟩ with hk2
  set d := D.distance with hdd
  have hdge : 3 ≤ d := by omega
  set m := d - 1 with hm
  have hm2 : 2 ≤ m := by omega
  have hcore : k1 < m * m → k2 < m * m → k2 ≠ k1 + 1 → k2 ≠ k1 + m →
      k2 ≠ k1 - 1 → k2 ≠ k1 - m →
      ¬((k1 / m = k2 / m ∧ (k1 % m = k2 % m + 1 ∨ k2 % m = k1 % m + 1)) ∨
        (k1 % m = k2 % m ∧ (k1 / m = k2 / m + 1 ∨ k2 / m = k1 / m + 1))) := by
    intro _ _ hp1 hpm hm1 hmm
    have e1 : k1 = m * (k1 / m) + k1 % m := (Nat.div_add_mod k1 m).symm
    have e2 : k2 = m * (k2 / m) + k2 % m := (Nat.div_add_mod k2 m).symm
    refine dbbNonAdjAllCore hm2 (Nat.mod_lt k1 (by omega)) (Nat.mod_lt k2 (by omega))
      ?_ ?_ ?_ ?_ <;> omega
  by_cases hbulk1 : k1 < m * m
  · by_cases hbulk2 : k2 < m * m
    · by_cases hp1 : k2 = k1 + 1
      · simp [decide_eq_true_eq.mpr hp1]
      · by_cases hpm : k2 = k1 + m
        · simp [decide_eq_true_eq.mpr hpm]
        · by_cases hm1 : k2 = k1 - 1
          · simp [decide_eq_true_eq.mpr hm1]
          · by_cases hmm : k2 = k1 - m
            · simp [decide_eq_true_eq.mpr hmm]
            · have hres := hcore hbulk1 hbulk2 hp1 hpm hm1 hmm
              have hl : ¬(k1 / m = k2 / m ∧ (k1 % m = k2 % m + 1 ∨ k2 % m = k1 % m + 1)) :=
                fun h => hres (Or.inl h)
              have hr : ¬(k1 % m = k2 % m ∧ (k1 / m = k2 / m + 1 ∨ k2 / m = k1 / m + 1)) :=
                fun h => hres (Or.inr h)
              simp only [decide_eq_false_iff_not.mpr hp1, decide_eq_false_iff_not.mpr hpm,
                decide_eq_false_iff_not.mpr hm1, decide_eq_false_iff_not.mpr hmm,
                decide_true, if_true]
              by_cases hrc : k1 / m = k2 / m
              · by_cases hcc : k1 % m = k2 % m + 1
                · exact absurd ⟨hrc, Or.inl hcc⟩ hl
                · by_cases hcc2 : k2 % m = k1 % m + 1
                  · exact absurd ⟨hrc, Or.inr hcc2⟩ hl
                  · simp [hrc, hcc, hcc2]
              · by_cases hcc : k1 % m = k2 % m
                · by_cases hrc2 : k1 / m = k2 / m + 1
                  · exact absurd ⟨hcc, Or.inl hrc2⟩ hr
                  · by_cases hrc3 : k2 / m = k1 / m + 1
                    · exact absurd ⟨hcc, Or.inr hrc3⟩ hr
                    · simp [hrc, hcc, hrc2, hrc3]
                · simp [hrc, hcc]
    · simp [decide_eq_false_iff_not.mpr hbulk2]
  · simp [decide_eq_false_iff_not.mpr hbulk1]

/-- Pure-Nat core for the VertU-fail non-overlap: `cellR k1 = 0` (so `k2 = k1−m`
truncates to `0`) and `k2 ≠ k1−1` (so `cellC k1 ≠ 1`) ⟹ not edge-adjacent. -/
private theorem dbbNonAdjVuCore {m k1 k2 : Nat} (hm : 2 ≤ m)
    (h1 : k1 = m * (k1 / m) + k1 % m) (hc1 : k1 % m < m)
    (h2 : k2 = m * (k2 / m) + k2 % m) (hc2 : k2 % m < m)
    (hr0 : ¬ 0 < k1 / m) (hmm : k2 = k1 - m) (hm1 : k2 ≠ k1 - 1) :
    ¬((k1 / m = k2 / m ∧ (k1 % m = k2 % m + 1 ∨ k2 % m = k1 % m + 1)) ∨
      (k1 % m = k2 % m ∧ (k1 / m = k2 / m + 1 ∨ k2 / m = k1 / m + 1))) := by
  -- r1 = 0 ⟹ k1 = c1 < m ⟹ k2 = k1 - m = 0 ⟹ r2 = c2 = 0; k2 ≠ k1−1 ⟹ c1 ≠ 1.
  have hr1z : k1 / m = 0 := Nat.le_zero.mp (Nat.not_lt.mp hr0)
  rw [hr1z, Nat.mul_zero, Nat.zero_add] at h1   -- h1 : k1 = k1 % m
  have hk1lt : k1 < m := by omega
  have hk2z : k2 = 0 := by omega
  have hr2z : k2 / m = 0 := by rw [hk2z]; exact Nat.zero_div m
  have hc2z : k2 % m = 0 := by rw [hk2z]; exact Nat.zero_mod m
  rw [hr1z, hr2z, hc2z]
  rintro (⟨hr, hc | hc⟩ | ⟨hc, hr | hr⟩) <;> omega

/-- Non-overlap via VertU-guard failure (`k2 = k1−(d−1)` but `cellR k1 = 0`). -/
abbrev dbbNonAdjVuF (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true))
    (.imp (.eqBool (SC.closed (.eqNat k2P (.sub k1P (.natLit 1)))) (SC.b false))
      (.imp (.eqBool (SC.closed (.eqNat k2P (.sub k1P (dm1TA (dP2 D))))) (SC.b true))
        (.imp (.eqBool (SC.closed (.ltNat (.natLit 0) (.div k1P (dm1TA (dP2 D))))) (SC.b false))
          (.eqBool (SC.closed (bbnaNonAdjTA2 D)) (SC.b true)))))

def dbbNonAdjVu (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (dbbNonAdjVuF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [bbnaNonAdjTA2, bbnaEdgeAdjTA2,
    bulkGuardTA, bulkCountTA, dm1TA, dP2, k1P, k2P, SFormula.eval, SC.closed, SC.b,
    STerm.eval, Term.eval, Term.lift, bind, Option.bind]
  set k1 := rho ⟨1, by decide⟩ with hk1
  set k2 := rho ⟨0, by decide⟩ with hk2
  set d := D.distance with hdd
  have hdge : 3 ≤ d := by omega
  set m := d - 1 with hm
  have hm2 : 2 ≤ m := by omega
  have hcore : k1 < m * m → k2 ≠ k1 - 1 → k2 = k1 - m → ¬ 0 < k1 / m →
      ¬((k1 / m = k2 / m ∧ (k1 % m = k2 % m + 1 ∨ k2 % m = k1 % m + 1)) ∨
        (k1 % m = k2 % m ∧ (k1 / m = k2 / m + 1 ∨ k2 / m = k1 / m + 1))) := by
    intro _ hm1 hmm hr0
    exact dbbNonAdjVuCore hm2 (Nat.div_add_mod k1 m).symm (Nat.mod_lt k1 (by omega))
      (Nat.div_add_mod k2 m).symm (Nat.mod_lt k2 (by omega)) hr0 hmm hm1
  by_cases hbulk1 : k1 < m * m
  · by_cases hm1 : k2 = k1 - 1
    · simp [decide_eq_true_eq.mpr hm1]
    · by_cases hmm : k2 = k1 - m
      · by_cases hr0 : 0 < k1 / m
        · simp [hbulk1, hm1, hmm, hr0]
        · have hres := hcore hbulk1 hm1 hmm hr0
          have hl : ¬(k1 / m = k2 / m ∧ (k1 % m = k2 % m + 1 ∨ k2 % m = k1 % m + 1)) :=
            fun h => hres (Or.inl h)
          have hr : ¬(k1 % m = k2 % m ∧ (k1 / m = k2 / m + 1 ∨ k2 / m = k1 / m + 1)) :=
            fun h => hres (Or.inr h)
          simp only [decide_eq_true_eq.mpr hbulk1, decide_eq_false_iff_not.mpr hm1,
            decide_eq_true_eq.mpr hmm, decide_eq_false_iff_not.mpr hr0,
            decide_true, if_true]
          by_cases hrc : k1 / m = k2 / m
          · by_cases hcc : k1 % m = k2 % m + 1
            · exact absurd ⟨hrc, Or.inl hcc⟩ hl
            · by_cases hcc2 : k2 % m = k1 % m + 1
              · exact absurd ⟨hrc, Or.inr hcc2⟩ hl
              · simp [hrc, hcc, hcc2]
          · by_cases hcc : k1 % m = k2 % m
            · by_cases hrc2 : k1 / m = k2 / m + 1
              · exact absurd ⟨hcc, Or.inl hrc2⟩ hr
              · by_cases hrc3 : k2 / m = k1 / m + 1
                · exact absurd ⟨hcc, Or.inr hrc3⟩ hr
                · simp [hrc, hcc, hrc2, hrc3]
            · simp [hrc, hcc]
      · simp [decide_eq_false_iff_not.mpr hmm]
  · simp [decide_eq_false_iff_not.mpr hbulk1]

/-! ### Purity witnesses + flat entries for the four overlap qubits

`entryAAtQ`/`entryBAtQ` need a `PureNatTerm` for the qubit term.  All eight overlap
qubits are built from `dP2 D` (`= natLit d` by `Term.lift` on a literal), `cellR`
(`div k1P (dm1TA (dP2 D))`), `cellC` (`mod …`), and `natLit`/`add`/`mul`. -/

/-- Purity of `dP2 D` (`= lift 0 (lift 0 (natLit d))`, defeq `natLit d`). -/
def dbbPureD (D : OddSurfaceDistance) : SFormula.PureNatTerm (dP2 D) :=
  SFormula.PureNatTerm.natLit (arity := 2) D.distance
/-- Purity of `dm1TA (dP2 D) = d − 1`. -/
def dbbPureDm1 (D : OddSurfaceDistance) : SFormula.PureNatTerm (dm1TA (dP2 D)) :=
  SFormula.PureNatTerm.sub (dbbPureD D) (SFormula.PureNatTerm.natLit 1)
/-- Purity of `cellR k1 = div k1P (d−1)`. -/
def dbbPureR1 (D : OddSurfaceDistance) :
    SFormula.PureNatTerm (.div k1P (dm1TA (dP2 D))) :=
  SFormula.PureNatTerm.div (SFormula.PureNatTerm.var ⟨1, by decide⟩) (dbbPureDm1 D)
/-- Purity of `cellC k1 = mod k1P (d−1)`. -/
def dbbPureC1 (D : OddSurfaceDistance) :
    SFormula.PureNatTerm (.mod k1P (dm1TA (dP2 D))) :=
  SFormula.PureNatTerm.mod (SFormula.PureNatTerm.var ⟨1, by decide⟩) (dbbPureDm1 D)

/-- The flat entries (row A and row B) at a pure qubit, as a conjoined pack. -/
def dbbEntryPair (D : OddSurfaceDistance) (qT : Term 2 .nat)
    (hq : SFormula.PureNatTerm qT) :
    PureFamilyDerivA Surface.code.body (D.distance + 2)
      (.and (entryAAtQF D qT) (entryBAtQF D qT)) :=
  pfdaAnd2 (entryAAtQ D qT hq) (entryBAtQ D qT hq)

/-- Purity of the eight overlap qubits (mechanical composition). -/
def dbbPureBhQ0 (D : OddSurfaceDistance) : SFormula.PureNatTerm (bhQ0 D) :=
  .add (.mul (dbbPureD D) (dbbPureR1 D)) (.add (dbbPureC1 D) (.natLit 1))
def dbbPureBhQ1 (D : OddSurfaceDistance) : SFormula.PureNatTerm (bhQ1 D) :=
  .add (.mul (dbbPureD D) (.add (dbbPureR1 D) (.natLit 1))) (.add (dbbPureC1 D) (.natLit 1))
def dbbPureBvQ0 (D : OddSurfaceDistance) : SFormula.PureNatTerm (bvQ0 D) :=
  .add (.mul (dbbPureD D) (.add (dbbPureR1 D) (.natLit 1))) (dbbPureC1 D)
def dbbPureBvQ1 (D : OddSurfaceDistance) : SFormula.PureNatTerm (bvQ1 D) :=
  .add (.mul (dbbPureD D) (.add (dbbPureR1 D) (.natLit 1))) (.add (dbbPureC1 D) (.natLit 1))
def dbbPureBhlQ0 (D : OddSurfaceDistance) : SFormula.PureNatTerm (bhlQ0 D) :=
  .add (.mul (dbbPureD D) (dbbPureR1 D)) (dbbPureC1 D)
def dbbPureBhlQ1 (D : OddSurfaceDistance) : SFormula.PureNatTerm (bhlQ1 D) :=
  .add (.mul (dbbPureD D) (.add (dbbPureR1 D) (.natLit 1))) (dbbPureC1 D)
def dbbPureBvuQ0 (D : OddSurfaceDistance) : SFormula.PureNatTerm (bvuQ0 D) :=
  .add (.mul (dbbPureD D) (dbbPureR1 D)) (dbbPureC1 D)
def dbbPureBvuQ1 (D : OddSurfaceDistance) : SFormula.PureNatTerm (bvuQ1 D) :=
  .add (.mul (dbbPureD D) (dbbPureR1 D)) (.add (dbbPureC1 D) (.natLit 1))

/-! ### Per-route pack bundles (`PureFamilyDerivA`, cut into the context)

Each overlap closer needs its Range/BandK1/BandK2/Pin packs plus four flat entries
(row A and row B at `q0`,`q1`).  We pack them per route as a 6-fold `and` so the
dispatcher extracts each closer's inputs by `andElim`.  Layout (left→right):
`Range ∧ BandK1 ∧ BandK2 ∧ Pin ∧ (EA0 ∧ EB0) ∧ (EA1 ∧ EB1)`. -/

abbrev dbbHorizBundleF (D : OddSurfaceDistance) : SFormula 2 :=
  .and (bhRangePackF D) (.and (bhBandK1PackF D) (.and (bhBandK2PackF D) (.and (bhPinF D)
    (.and (.and (entryAAtQF D (bhQ0 D)) (entryBAtQF D (bhQ0 D)))
      (.and (entryAAtQF D (bhQ1 D)) (entryBAtQF D (bhQ1 D)))))))
def dbbHorizBundle (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (dbbHorizBundleF D) :=
  pfdaAnd2 (bhRangePack D) (pfdaAnd2 (bhBandK1Pack D) (pfdaAnd2 (bhBandK2Pack D)
    (pfdaAnd2 (bhPinPack D) (pfdaAnd2 (dbbEntryPair D (bhQ0 D) (dbbPureBhQ0 D))
      (dbbEntryPair D (bhQ1 D) (dbbPureBhQ1 D))))))

abbrev dbbVertBundleF (D : OddSurfaceDistance) : SFormula 2 :=
  .and (bvRangePackF D) (.and (bvBandK1PackF D) (.and (bvBandK2PackF D) (.and (bvPinF D)
    (.and (.and (entryAAtQF D (bvQ0 D)) (entryBAtQF D (bvQ0 D)))
      (.and (entryAAtQF D (bvQ1 D)) (entryBAtQF D (bvQ1 D)))))))
def dbbVertBundle (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (dbbVertBundleF D) :=
  pfdaAnd2 (bvRangePack D) (pfdaAnd2 (bvBandK1Pack D) (pfdaAnd2 (bvBandK2Pack D)
    (pfdaAnd2 (bvPinPack D) (pfdaAnd2 (dbbEntryPair D (bvQ0 D) (dbbPureBvQ0 D))
      (dbbEntryPair D (bvQ1 D) (dbbPureBvQ1 D))))))

abbrev dbbHorizLBundleF (D : OddSurfaceDistance) : SFormula 2 :=
  .and (bhlRangePackF D) (.and (bhlBandK1PackF D) (.and (bhlBandK2PackF D) (.and (bhlPinF D)
    (.and (.and (entryAAtQF D (bhlQ0 D)) (entryBAtQF D (bhlQ0 D)))
      (.and (entryAAtQF D (bhlQ1 D)) (entryBAtQF D (bhlQ1 D)))))))
def dbbHorizLBundle (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (dbbHorizLBundleF D) :=
  pfdaAnd2 (bhlRangePack D) (pfdaAnd2 (bhlBandK1Pack D) (pfdaAnd2 (bhlBandK2Pack D)
    (pfdaAnd2 (bhlPinPack D) (pfdaAnd2 (dbbEntryPair D (bhlQ0 D) (dbbPureBhlQ0 D))
      (dbbEntryPair D (bhlQ1 D) (dbbPureBhlQ1 D))))))

abbrev dbbVertUBundleF (D : OddSurfaceDistance) : SFormula 2 :=
  .and (bvuRangePackF D) (.and (bvuBandK1PackF D) (.and (bvuBandK2PackF D) (.and (bvuPinF D)
    (.and (.and (entryAAtQF D (bvuQ0 D)) (entryBAtQF D (bvuQ0 D)))
      (.and (entryAAtQF D (bvuQ1 D)) (entryBAtQF D (bvuQ1 D)))))))
def dbbVertUBundle (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (dbbVertUBundleF D) :=
  pfdaAnd2 (bvuRangePack D) (pfdaAnd2 (bvuBandK1Pack D) (pfdaAnd2 (bvuBandK2Pack D)
    (pfdaAnd2 (bvuPinPack D) (pfdaAnd2 (dbbEntryPair D (bvuQ0 D) (dbbPureBvuQ0 D))
      (dbbEntryPair D (bvuQ1 D) (dbbPureBvuQ1 D))))))

/-- The complete bulk–bulk pack bundle: the four route packs, the non-overlap pin,
and the five validity / non-adjacency `arithBool` facts. -/
abbrev dbbPacksF (D : OddSurfaceDistance) : SFormula 2 :=
  .and (dbbHorizBundleF D) (.and (dbbVertBundleF D) (.and (dbbHorizLBundleF D)
    (.and (dbbVertUBundleF D) (.and (bbnaPinF D)
      (.and (dbbBhRowImpF D) (.and (dbbBvRowImpF D) (.and (dbbBhlColImpF D)
        (.and (dbbNonAdjAllF D) (dbbNonAdjVuF D)))))))))
def dbbPacks (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (dbbPacksF D) :=
  pfdaAnd2 (dbbHorizBundle D) (pfdaAnd2 (dbbVertBundle D) (pfdaAnd2 (dbbHorizLBundle D)
    (pfdaAnd2 (dbbVertUBundle D) (pfdaAnd2 (bbnaPinPack D)
      (pfdaAnd2 (dbbBhRowImp D) (pfdaAnd2 (dbbBvRowImp D) (pfdaAnd2 (dbbBhlColImp D)
        (pfdaAnd2 (dbbNonAdjAll D) (dbbNonAdjVu D)))))))))

/-- **Bulk–Bulk class-combo dispatcher.**  Both rows are bulk plaquettes (hence
different CSS type: `k1` X-kind, `k2` Z-kind).  Routes by the four relative-index
adjacencies `k2 = k1±1`, `k2 = k1±(d−1)` to the matching overlap closer, with the
non-overlap catch-all `pairCommuteBulkBulkNonAdj`.  The kind facts come from the
`typeExclF` packs (in `hbundle`); the validity guards and the non-adjacency come
from the `arithBool` facts in `hpacks`.  The band/pin packs and flat entries the
closers consume are extracted from `hpacks` (they live only as `PureFamilyDerivA`,
so they MUST be supplied via `hpacks`, not re-derived in `Γ`). -/
def dispatchBulkBulk {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hbundle : SFormula.Deriv Γ (pairBundleF D))
    (hpacks : SFormula.Deriv Γ (dbbPacksF D))
    (hkAX : SFormula.Deriv Γ (k1IsX D true))
    (hkBZ : SFormula.Deriv Γ (k2IsX D false))
    (hbulkA : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true)))
    (hbulkB : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true))) :
    SFormula.Deriv Γ (pairGoal D) := by
  -- Base facts from `hbundle`.
  have hEntryA : SFormula.Deriv Γ (entryAQuant D) := SFormula.Deriv.andElimLeft hbundle
  have hEntryB : SFormula.Deriv Γ (entryBQuant D) :=
    SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hbundle)
  have hExcl1 : SFormula.Deriv Γ (typeExclF D k1P) :=
    SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hbundle))
  have hExcl2 : SFormula.Deriv Γ (typeExclF D k2P) :=
    SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hbundle))
  -- Kind facts (free, from `typeExclF`).
  have hKindK1 : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k1P)) (SC.b false)) :=
    dbbKindK1OfIsX D hExcl1 hkAX hbulkA
  have hKindK2 : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k2P)) (SC.b true)) :=
    dbbKindK2OfNotIsX D hExcl2 hkBZ hbulkB
  -- Route bundles + validity / non-adjacency facts from `hpacks`.
  have hHoriz : SFormula.Deriv Γ (dbbHorizBundleF D) := SFormula.Deriv.andElimLeft hpacks
  have hVert : SFormula.Deriv Γ (dbbVertBundleF D) :=
    SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hpacks)
  have hHorizL : SFormula.Deriv Γ (dbbHorizLBundleF D) :=
    SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hpacks))
  have hVertU : SFormula.Deriv Γ (dbbVertUBundleF D) :=
    SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight hpacks)))
  have hBbna : SFormula.Deriv Γ (bbnaPinF D) :=
    SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hpacks))))
  have hImpRest := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hpacks))))
  have hBhRowImp : SFormula.Deriv Γ (dbbBhRowImpF D) := SFormula.Deriv.andElimLeft hImpRest
  have hBvRowImp : SFormula.Deriv Γ (dbbBvRowImpF D) :=
    SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hImpRest)
  have hBhlColImp : SFormula.Deriv Γ (dbbBhlColImpF D) :=
    SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hImpRest))
  have hNonAdjAll : SFormula.Deriv Γ (dbbNonAdjAllF D) :=
    SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight hImpRest)))
  have hNonAdjVu : SFormula.Deriv Γ (dbbNonAdjVuF D) :=
    SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight hImpRest)))
  -- Per-route closer inputs (Range/BandK1/BandK2/Pin/entries), extracted in `Γ`.
  have hHR := SFormula.Deriv.andElimLeft hHoriz
  have hHB1 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hHoriz)
  have hHB2 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hHoriz))
  have hHP := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight hHoriz)))
  have hHe := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight hHoriz)))
  have hHEA0 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimLeft hHe)
  have hHEB0 := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimLeft hHe)
  have hHEA1 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hHe)
  have hHEB1 := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hHe)
  have hVR := SFormula.Deriv.andElimLeft hVert
  have hVB1 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hVert)
  have hVB2 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hVert))
  have hVP := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight hVert)))
  have hVe := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight hVert)))
  have hVEA0 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimLeft hVe)
  have hVEB0 := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimLeft hVe)
  have hVEA1 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hVe)
  have hVEB1 := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hVe)
  have hLR := SFormula.Deriv.andElimLeft hHorizL
  have hLB1 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hHorizL)
  have hLB2 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hHorizL))
  have hLP := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight hHorizL)))
  have hLe := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight hHorizL)))
  have hLEA0 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimLeft hLe)
  have hLEB0 := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimLeft hLe)
  have hLEA1 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hLe)
  have hLEB1 := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hLe)
  have hUR := SFormula.Deriv.andElimLeft hVertU
  have hUB1 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hVertU)
  have hUB2 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hVertU))
  have hUP := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight hVertU)))
  have hUe := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight hVertU)))
  have hUEA0 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimLeft hUe)
  have hUEB0 := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimLeft hUe)
  have hUEA1 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hUe)
  have hUEB1 := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hUe)
  -- ROUTE 1: k2 = k1 + 1 (horizontal-right).
  refine SFormula.Deriv.boolCases (SC.closed (.eqNat k2P (.add k1P (.natLit 1)))) _ ?horiz ?rest1
  case horiz =>
    have hadj : SFormula.Deriv ((bhAdjF D) :: Γ) (bhAdjF D) := .hyp List.mem_cons_self
    have hrow : SFormula.Deriv _ (bhRowF D) :=
      SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp
        (cw1 hBhRowImp) (cw1 hKindK1)) (cw1 hKindK2)) (cw1 hbulkA)) hadj
    exact commBulkBulkHoriz D (cw1 hEntryA) (cw1 hEntryB) (cw1 hkAX) (cw1 hExcl1)
      (cw1 hbulkA) (cw1 hKindK1) (cw1 hbulkB) (cw1 hKindK2) hadj hrow
      (cw1 hHR) (cw1 hHB1) (cw1 hHB2) (cw1 hHP) (cw1 hHEA0) (cw1 hHEA1) (cw1 hHEB0) (cw1 hHEB1)
  case rest1 =>
    -- ROUTE 2: k2 = k1 + (d−1) (vertical-down).
    refine SFormula.Deriv.boolCases (SC.closed (.eqNat k2P (.add k1P (dm1TA (dP2 D))))) _ ?vert ?rest2
    case vert =>
      have hadj : SFormula.Deriv (bvAdjF D ::
          SFormula.eqBool (SC.closed (.eqNat k2P (.add k1P (.natLit 1)))) (SC.b false) :: Γ)
          (bvAdjF D) := .hyp List.mem_cons_self
      have hrow : SFormula.Deriv _ (bvRowF D) :=
        SFormula.Deriv.mp (SFormula.Deriv.mp (cw2 hBvRowImp) (cw2 hbulkB)) hadj
      exact commBulkBulkVert D (cw2 hEntryA) (cw2 hEntryB) (cw2 hkAX) (cw2 hExcl1)
        (cw2 hbulkA) (cw2 hKindK1) (cw2 hbulkB) (cw2 hKindK2) hadj hrow
        (cw2 hVR) (cw2 hVB1) (cw2 hVB2) (cw2 hVP) (cw2 hVEA0) (cw2 hVEA1) (cw2 hVEB0) (cw2 hVEB1)
    case rest2 =>
      -- ROUTE 3: k2 = k1 − 1 (horizontal-left).
      refine SFormula.Deriv.boolCases (SC.closed (.eqNat k2P (.sub k1P (.natLit 1)))) _ ?horizL ?rest3
      case horizL =>
        have hadj : SFormula.Deriv (bhlAdjF D ::
            SFormula.eqBool (SC.closed (.eqNat k2P (.add k1P (dm1TA (dP2 D))))) (SC.b false) ::
            SFormula.eqBool (SC.closed (.eqNat k2P (.add k1P (.natLit 1)))) (SC.b false) :: Γ)
            (bhlAdjF D) := .hyp List.mem_cons_self
        have hcol : SFormula.Deriv _ (bhlColF D) :=
          SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp
            (cw3 hBhlColImp) (cw3 hKindK1)) (cw3 hKindK2)) (cw3 hbulkA)) hadj
        exact commBulkBulkHorizL D (cw3 hEntryA) (cw3 hEntryB) (cw3 hkAX) (cw3 hExcl1)
          (cw3 hbulkA) (cw3 hKindK1) (cw3 hbulkB) (cw3 hKindK2) hadj hcol
          (cw3 hLR) (cw3 hLB1) (cw3 hLB2) (cw3 hLP) (cw3 hLEA0) (cw3 hLEA1) (cw3 hLEB0) (cw3 hLEB1)
      case rest3 =>
        -- ROUTE 4: k2 = k1 − (d−1) (vertical-up), guarded by `0 < cellR k1`.
        refine SFormula.Deriv.boolCases (SC.closed (.eqNat k2P (.sub k1P (dm1TA (dP2 D))))) _ ?vertU ?rest4
        case vertU =>
          -- Guard on `bvuRowF` (`0 < r1`): true → VertU; false → non-overlap (VertU-fail).
          refine SFormula.Deriv.boolCases (SC.closed (.ltNat (.natLit 0) (.div k1P (dm1TA (dP2 D))))) _ ?vu ?vuFail
          case vu =>
            exact commBulkBulkVertU D (cw5 hEntryA) (cw5 hEntryB) (cw5 hkAX) (cw5 hExcl1)
              (cw5 hbulkA) (cw5 hKindK1) (cw5 hbulkB) (cw5 hKindK2)
              (.hyp (by right; exact List.mem_cons_self)) (.hyp List.mem_cons_self)
              (cw5 hUR) (cw5 hUB1) (cw5 hUB2) (cw5 hUP) (cw5 hUEA0) (cw5 hUEA1) (cw5 hUEB0) (cw5 hUEB1)
          case vuFail =>
            -- k2 = k1−(d−1) but cellR k1 = 0: non-overlap via `dbbNonAdjVu`.
            refine pairCommuteBulkBulkNonAdj D (cw5 hEntryA) (cw5 hEntryB) (cw5 hkAX) (cw5 hExcl1)
              (cw5 hbulkA) (cw5 hKindK1) (cw5 hbulkB) (cw5 hKindK2) ?_ (cw5 hBbna)
            exact SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp
              (cw5 hNonAdjVu) (cw5 hbulkA)) (cw2 (.hyp List.mem_cons_self)))
              (.hyp (by right; exact List.mem_cons_self))) (.hyp List.mem_cons_self)
        case rest4 =>
          -- All four index conditions fail: non-overlap via `dbbNonAdjAll`.
          refine pairCommuteBulkBulkNonAdj D (cw4 hEntryA) (cw4 hEntryB) (cw4 hkAX) (cw4 hExcl1)
            (cw4 hbulkA) (cw4 hKindK1) (cw4 hbulkB) (cw4 hKindK2) ?_ (cw4 hBbna)
          exact SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp
            (SFormula.Deriv.mp (SFormula.Deriv.mp (cw4 hNonAdjAll) (cw4 hbulkA)) (cw4 hbulkB))
            (cw3 (.hyp List.mem_cons_self))) (cw2 (.hyp List.mem_cons_self)))
            (cw1 (.hyp List.mem_cons_self))) (.hyp List.mem_cons_self)

/-! ## Bulk–Boundary (Z) class-combo dispatchers (stage 1: right + left)

Two dispatchers route the BULK-X (`k1`) vs BOUNDARY-Z (`k2`) case to the matching
overlap closer or non-overlap handler.  Unlike the bulk–bulk dispatcher the boundary
row carries NO `baseKindGuardTA` fact — its CSS type is encoded by the boundary CLASS
guards (`¬top`, `right`/`¬right`, `left`), which the closer/handler consume directly.

* `dispatchBulkRight` : `k2` is a RIGHT-Z boundary; ADJACENT → `commRightBulk`
  (`brAdjF`), NON-ADJACENT → `pairCommuteBulkRightNonAdj` (`brnaNonAdjTA2`).
* `dispatchBulkLeft`  : `k2` is a LEFT-Z boundary;  ADJACENT → `commLeftBulk`
  (`blAdjF`),  NON-ADJACENT → `pairCommuteBulkLeftNonAdj` (`blnaNonAdjTA2`).

ROUTING is a SINGLE `boolCases` on the closer's `brAdjF`/`blAdjF` `eqNat` condition.
The KEY reconciliation (the "band-broad" form of the design notes): the non-overlap
handler's `brnaNonAdjTA2` (resp. `blnaNonAdjTA2`) is the negation of a band-broad
edge-adjacency that allows THREE bulk rows at the boundary column, whereas the
closer's `brAdjF`/`blAdjF` pins exactly ONE.  Under the X-kind parity of `k1`
(`baseKindGuardTA(k1)=false`, recovered free from `dbbKindK1OfIsX`) the band-broad
form COLLAPSES to the single pinned row (the boundary column has fixed parity, so
only the one row of matching parity can be X-kind), so the FALSE branch of the
single `brAdjF`/`blAdjF` `boolCases` already establishes `brnaNonAdjTA2`/`blnaNonAdjTA2`.
This collapse is the new `arithBool` implication fact `dbrNonAdjImp`/`dblNonAdjImp`. -/

/-- Pure-Nat core (bulk–right collapse): a bulk cell `(r1, c1)` X-kind
(`(r1+c1)` odd) whose pinned-row identity `m·r1+c1 = 2r·m + (m−1)` FAILS is NOT
band-broad edge-adjacent to a right boundary at rows `{2r, 2r+1}`, column `m−1`.  The
parity rules out the spurious rows `2r+1`, `2r−1`; the surviving row `2r` is exactly
the pinned identity. -/
private theorem dbrNonAdjCollapseCore {m r1 c1 r : Nat} (hm : 2 ≤ m) (hmeven : m % 2 = 0)
    (hkind : (r1 + c1) % 2 ≠ 0)
    (hne : m * r1 + c1 ≠ 2 * r * m + (m - 1)) :
    ¬ (c1 = m - 1 ∧ ((r1 = 2 * r ∨ r1 = 2 * r + 1) ∨ r1 + 1 = 2 * r)) := by
  rintro ⟨hc, hrow⟩
  rcases hrow with (h | h) | h
  · subst h; rw [hc, Nat.mul_comm m (2 * r)] at hne; exact hne rfl
  · subst h; omega
  · omega

/-- Pure-Nat core (bulk–left collapse): a bulk cell `(r1, c1)` X-kind
(`(r1+c1)` odd) whose pinned-row identity `m·r1+c1 = (2l+1)·m` FAILS is NOT
band-broad edge-adjacent to a left boundary at rows `{2l+1, 2l+2}`, column `0`.  The
parity rules out the spurious rows `2l`, `2l+2`; the surviving row `2l+1` is exactly
the pinned identity (`c1 = 0`). -/
private theorem dblNonAdjCollapseCore {m r1 c1 l : Nat} (hm : 2 ≤ m) (hmeven : m % 2 = 0)
    (hkind : (r1 + c1) % 2 ≠ 0)
    (hne : m * r1 + c1 ≠ (2 * l + 1) * m) :
    ¬ (c1 = 0 ∧ ((r1 = 2 * l + 1 ∨ r1 = 2 * l + 2) ∨ r1 + 1 = 2 * l + 1)) := by
  rintro ⟨hc, hrow⟩
  rcases hrow with (h | h) | h
  · subst h; rw [hc, Nat.add_zero, Nat.mul_comm m (2 * l + 1)] at hne; exact hne rfl
  · subst h; omega
  · omega

/-- Bulk–Right non-adjacency collapse (`arithBool`): under `k1` X-kind
(`baseKindGuardTA = false`) and the FAILURE of the pinned identity `brAdjF`
(`k1 = (2r)·(d−1) + ((d−1)−1)`), the band-broad non-adjacency `brnaNonAdjTA2` HOLDS.
`r = brR = baseBTA(k2) − half`.  Discharged by the parity core `dbrNonAdjCollapseCore`
(the X-kind parity forces the boundary column's lone same-parity row, i.e. the pinned
row, so the only edge-adjacency is exactly the failed identity). -/
abbrev dbrNonAdjImpF (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k1P)) (SC.b false))
    (.imp (.eqBool (SC.closed (.eqNat k1P
        (.add (.mul (.mul (.natLit 2) (brR D)) (dm1TA (dP2 D)))
          (.sub (dm1TA (dP2 D)) (.natLit 1))))) (SC.b false))
      (.eqBool (SC.closed (brnaNonAdjTA2 D)) (SC.b true)))

def dbrNonAdjImp (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (dbrNonAdjImpF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [brnaNonAdjTA2, brnaEdgeAdjTA2, brR, baseKindGuardTA, baseBTA, baseHalfTA,
    bulkCountTA, dm1TA, dP2, k1P, k2P, SFormula.eval, SC.closed, SC.b, STerm.eval,
    Term.eval, Term.lift, bind, Option.bind]
  set k1 := rho ⟨1, by decide⟩ with hk1
  set k2 := rho ⟨0, by decide⟩ with hk2
  set d := D.distance with hdd
  have hdge : 3 ≤ d := by omega
  set m := d - 1 with hm
  have hm2 : 2 ≤ m := by omega
  have hmeven : m % 2 = 0 := by omega
  set r := k2 - m * m - m / 2 with hr
  -- Core: X-kind + pinned-identity failure ⟹ not band-broad edge-adjacent.
  have hcore : (k1 / m + k1 % m) % 2 ≠ 0 → k1 ≠ 2 * r * m + (m - 1) →
      ¬ (k1 % m = m - 1 ∧
        ((k1 / m = 2 * r ∨ k1 / m = 2 * r + 1) ∨ k1 / m + 1 = 2 * r)) := by
    intro hkind hne
    have hc1lt : k1 % m < m := Nat.mod_lt k1 (by omega)
    have hkdec : k1 = m * (k1 / m) + k1 % m := (Nat.div_add_mod k1 m).symm
    refine dbrNonAdjCollapseCore hm2 hmeven hkind ?_
    omega
  by_cases hkind : (k1 / m + k1 % m) % 2 = 0
  · rw [hkind]; simp
  · by_cases hne : k1 = 2 * r * m + (m - 1)
    · simp only [decide_eq_true_eq.mpr hne]; simp
    · have hres := hcore hkind hne
      have hl : ¬ (k1 % m = m - 1 ∧
          ((k1 / m = 2 * r ∨ k1 / m = 2 * r + 1) ∨ k1 / m + 1 = 2 * r)) := hres
      simp only [decide_eq_false_iff_not.mpr hkind, decide_eq_false_iff_not.mpr hne]
      by_cases hcc : k1 % m = m - 1
      · by_cases hr0 : k1 / m = 2 * r
        · exact absurd ⟨hcc, Or.inl (Or.inl hr0)⟩ hl
        · by_cases hr1 : k1 / m = 2 * r + 1
          · exact absurd ⟨hcc, Or.inl (Or.inr hr1)⟩ hl
          · by_cases hr2 : k1 / m + 1 = 2 * r
            · exact absurd ⟨hcc, Or.inr hr2⟩ hl
            · simp [hcc, hr0, hr1, hr2]
      · simp [hcc]

/-- Bulk–Left non-adjacency collapse (`arithBool`): under `k1` X-kind and the FAILURE
of `blAdjF` (`k1 = (2l+1)·(d−1)`), the band-broad non-adjacency `blnaNonAdjTA2` HOLDS.
`l = blL = baseBTA(k2) − 2·half`.  Discharged by `dblNonAdjCollapseCore`. -/
abbrev dblNonAdjImpF (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k1P)) (SC.b false))
    (.imp (.eqBool (SC.closed (.eqNat k1P
        (.mul (.add (.mul (.natLit 2) (blL D)) (.natLit 1)) (dm1TA (dP2 D))))) (SC.b false))
      (.eqBool (SC.closed (blnaNonAdjTA2 D)) (SC.b true)))

def dblNonAdjImp (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (dblNonAdjImpF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [blnaNonAdjTA2, blnaEdgeAdjTA2, blL, baseKindGuardTA, baseBTA, baseHalfTA,
    bulkCountTA, dm1TA, dP2, k1P, k2P, SFormula.eval, SC.closed, SC.b, STerm.eval,
    Term.eval, Term.lift, bind, Option.bind]
  set k1 := rho ⟨1, by decide⟩ with hk1
  set k2 := rho ⟨0, by decide⟩ with hk2
  set d := D.distance with hdd
  have hdge : 3 ≤ d := by omega
  set m := d - 1 with hm
  have hm2 : 2 ≤ m := by omega
  have hmeven : m % 2 = 0 := by omega
  set l := k2 - m * m - 2 * (m / 2) with hl0
  have hcore : (k1 / m + k1 % m) % 2 ≠ 0 → k1 ≠ (2 * l + 1) * m →
      ¬ (k1 % m = 0 ∧
        ((k1 / m = 2 * l + 1 ∨ k1 / m = 2 * l + 2) ∨ k1 / m + 1 = 2 * l + 1)) := by
    intro hkind hne
    have hc1lt : k1 % m < m := Nat.mod_lt k1 (by omega)
    have hkdec : k1 = m * (k1 / m) + k1 % m := (Nat.div_add_mod k1 m).symm
    refine dblNonAdjCollapseCore hm2 hmeven hkind ?_
    omega
  by_cases hkind : (k1 / m + k1 % m) % 2 = 0
  · rw [hkind]; simp
  · by_cases hne : k1 = (2 * l + 1) * m
    · simp only [decide_eq_true_eq.mpr hne]; simp
    · have hres := hcore hkind hne
      have hl : ¬ (k1 % m = 0 ∧
          ((k1 / m = 2 * l + 1 ∨ k1 / m = 2 * l + 2) ∨ k1 / m + 1 = 2 * l + 1)) := hres
      simp only [decide_eq_false_iff_not.mpr hkind, decide_eq_false_iff_not.mpr hne]
      by_cases hcc : k1 % m = 0
      · by_cases hr0 : k1 / m = 2 * l + 1
        · exact absurd ⟨hcc, Or.inl (Or.inl hr0)⟩ hl
        · by_cases hr1 : k1 / m = 2 * l + 2
          · exact absurd ⟨hcc, Or.inl (Or.inr hr1)⟩ hl
          · by_cases hr2 : k1 / m = 2 * l
            · exact absurd ⟨hcc, Or.inr (by omega)⟩ hl
            · simp [hcc, hr0, hr1, hr2]
      · simp [hcc]

/-! ### Pure witnesses for the boundary overlap qubits -/

/-- Purity of `bulkCount = (d−1)·(d−1)`. -/
def dbrPureBulkCount (D : OddSurfaceDistance) :
    SFormula.PureNatTerm (bulkCountTA (dP2 D)) :=
  SFormula.PureNatTerm.mul (dbbPureDm1 D) (dbbPureDm1 D)
/-- Purity of `baseBTA(k2) = k2 − bulkCount`. -/
def dbrPureBaseB (D : OddSurfaceDistance) :
    SFormula.PureNatTerm (baseBTA (dP2 D) k2P) :=
  SFormula.PureNatTerm.sub (SFormula.PureNatTerm.var ⟨0, by decide⟩) (dbrPureBulkCount D)
/-- Purity of `baseHalfTA = (d−1)/2`. -/
def dbrPureHalf (D : OddSurfaceDistance) :
    SFormula.PureNatTerm (baseHalfTA (dP2 D)) :=
  SFormula.PureNatTerm.div (dbbPureDm1 D) (SFormula.PureNatTerm.natLit 2)
/-- Purity of `brR = baseBTA(k2) − half`. -/
def dbrPureR (D : OddSurfaceDistance) : SFormula.PureNatTerm (brR D) :=
  SFormula.PureNatTerm.sub (dbrPureBaseB D) (dbrPureHalf D)
/-- Purity of `brQ0 = d·(2r) + (d−1)`. -/
def dbrPureBrQ0 (D : OddSurfaceDistance) : SFormula.PureNatTerm (brQ0 D) :=
  .add (.mul (dbbPureD D) (.mul (.natLit 2) (dbrPureR D))) (dbbPureDm1 D)
/-- Purity of `brQ1 = d·(2r+1) + (d−1)`. -/
def dbrPureBrQ1 (D : OddSurfaceDistance) : SFormula.PureNatTerm (brQ1 D) :=
  .add (.mul (dbbPureD D) (.add (.mul (.natLit 2) (dbrPureR D)) (.natLit 1))) (dbbPureDm1 D)
/-- Purity of `blL = baseBTA(k2) − 2·half`. -/
def dblPureL (D : OddSurfaceDistance) : SFormula.PureNatTerm (blL D) :=
  SFormula.PureNatTerm.sub (dbrPureBaseB D)
    (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.natLit 2) (dbrPureHalf D))
/-- Purity of `blQ0 = d·(2l+1)`. -/
def dblPureBlQ0 (D : OddSurfaceDistance) : SFormula.PureNatTerm (blQ0 D) :=
  .mul (dbbPureD D) (.add (.mul (.natLit 2) (dblPureL D)) (.natLit 1))
/-- Purity of `blQ1 = d·(2l+2)`. -/
def dblPureBlQ1 (D : OddSurfaceDistance) : SFormula.PureNatTerm (blQ1 D) :=
  .mul (dbbPureD D) (.add (.mul (.natLit 2) (dblPureL D)) (.natLit 2))

/-! ### Per-dispatcher pack super-bundles (`PureFamilyDerivA`, cut into the context)

`dbrPacksF` gathers everything the bulk–right routing needs that lives ONLY as a
`PureFamilyDerivA`: the closer's Range / RightBand / BulkBand / Pin packs, the four
flat entries at `brQ0`,`brQ1`, the non-overlap handler's `brnaPinF`, and the
non-adjacency collapse fact `dbrNonAdjImpF`.  Layout (left→right):
`Range ∧ RightBand ∧ BulkBand ∧ Pin ∧ (EA0 ∧ EB0) ∧ (EA1 ∧ EB1) ∧ brnaPin ∧ NonAdjImp`. -/

abbrev dbrPacksF (D : OddSurfaceDistance) : SFormula 2 :=
  .and (brRangePackF D) (.and (brRightBandPackF D) (.and (brBulkBandPackF D) (.and (brPinF D)
    (.and (.and (entryAAtQF D (brQ0 D)) (entryBAtQF D (brQ0 D)))
      (.and (.and (entryAAtQF D (brQ1 D)) (entryBAtQF D (brQ1 D)))
        (.and (brnaPinF D) (dbrNonAdjImpF D)))))))
def dbrPacks (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (dbrPacksF D) :=
  pfdaAnd2 (brRangePack D) (pfdaAnd2 (brRightBandPack D) (pfdaAnd2 (brBulkBandPack D)
    (pfdaAnd2 (brPinPack D)
      (pfdaAnd2 (dbbEntryPair D (brQ0 D) (dbrPureBrQ0 D))
        (pfdaAnd2 (dbbEntryPair D (brQ1 D) (dbrPureBrQ1 D))
          (pfdaAnd2 (brnaPinPack D) (dbrNonAdjImp D)))))))

abbrev dblPacksF (D : OddSurfaceDistance) : SFormula 2 :=
  .and (blRangePackF D) (.and (blLeftBandPackF D) (.and (blBulkBandPackF D) (.and (blPinF D)
    (.and (.and (entryAAtQF D (blQ0 D)) (entryBAtQF D (blQ0 D)))
      (.and (.and (entryAAtQF D (blQ1 D)) (entryBAtQF D (blQ1 D)))
        (.and (blnaPinF D) (dblNonAdjImpF D)))))))
def dblPacks (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (dblPacksF D) :=
  pfdaAnd2 (blRangePack D) (pfdaAnd2 (blLeftBandPack D) (pfdaAnd2 (blBulkBandPack D)
    (pfdaAnd2 (blPinPack D)
      (pfdaAnd2 (dbbEntryPair D (blQ0 D) (dblPureBlQ0 D))
        (pfdaAnd2 (dbbEntryPair D (blQ1 D) (dblPureBlQ1 D))
          (pfdaAnd2 (blnaPinPack D) (dblNonAdjImp D)))))))

/-- **Bulk–Right class-combo dispatcher.**  Row A (`k1`) is an X-type BULK plaquette,
row B (`k2`) a Z-type RIGHT boundary.  Single `boolCases` on the pinned-row identity
`brAdjF`: TRUE → `commRightBulk`; FALSE → `pairCommuteBulkRightNonAdj`, where the
band-broad non-adjacency `brnaNonAdjTA2` is recovered from `dbrNonAdjImp` (the X-kind
parity collapse).  The kind fact `baseKindGuardTA(k1)=false` is free via
`dbbKindK1OfIsX`; all `PureFamilyDerivA` packs/entries come from `hpacks`. -/
def dispatchBulkRight {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hbundle : SFormula.Deriv Γ (pairBundleF D))
    (hpacks : SFormula.Deriv Γ (dbrPacksF D))
    (hkAX : SFormula.Deriv Γ (k1IsX D true))
    (hkBZ : SFormula.Deriv Γ (k2IsX D false))
    (hbulkA : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true)))
    (hnbulkB : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)))
    (hntopB : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false)))
    (hrightB : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b true))) :
    SFormula.Deriv Γ (pairGoal D) := by
  -- Base facts from `hbundle`.
  have hEntryA : SFormula.Deriv Γ (entryAQuant D) := SFormula.Deriv.andElimLeft hbundle
  have hEntryB : SFormula.Deriv Γ (entryBQuant D) :=
    SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hbundle)
  have hExcl1 : SFormula.Deriv Γ (typeExclF D k1P) :=
    SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hbundle))
  -- Kind fact for `k1` (free, X-kind).
  have hKindK1 : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k1P)) (SC.b false)) :=
    dbbKindK1OfIsX D hExcl1 hkAX hbulkA
  -- Packs / entries / facts from `hpacks`.
  have hRange : SFormula.Deriv Γ (brRangePackF D) := SFormula.Deriv.andElimLeft hpacks
  have hRest1 := SFormula.Deriv.andElimRight hpacks
  have hRightBand : SFormula.Deriv Γ (brRightBandPackF D) := SFormula.Deriv.andElimLeft hRest1
  have hRest2 := SFormula.Deriv.andElimRight hRest1
  have hBulkBand : SFormula.Deriv Γ (brBulkBandPackF D) := SFormula.Deriv.andElimLeft hRest2
  have hRest3 := SFormula.Deriv.andElimRight hRest2
  have hPin : SFormula.Deriv Γ (brPinF D) := SFormula.Deriv.andElimLeft hRest3
  have hRest4 := SFormula.Deriv.andElimRight hRest3
  have hE0 := SFormula.Deriv.andElimLeft hRest4
  have hEA0 := SFormula.Deriv.andElimLeft hE0
  have hEB0 := SFormula.Deriv.andElimRight hE0
  have hRest5 := SFormula.Deriv.andElimRight hRest4
  have hE1 := SFormula.Deriv.andElimLeft hRest5
  have hEA1 := SFormula.Deriv.andElimLeft hE1
  have hEB1 := SFormula.Deriv.andElimRight hE1
  have hRest6 := SFormula.Deriv.andElimRight hRest5
  have hBrnaPin : SFormula.Deriv Γ (brnaPinF D) := SFormula.Deriv.andElimLeft hRest6
  have hNonAdjImp : SFormula.Deriv Γ (dbrNonAdjImpF D) := SFormula.Deriv.andElimRight hRest6
  -- Single route: brAdjF (`k1 = (2r)·(d−1) + ((d−1)−1)`).
  refine SFormula.Deriv.boolCases (SC.closed (.eqNat k1P
    (.add (.mul (.mul (.natLit 2) (brR D)) (dm1TA (dP2 D)))
      (.sub (dm1TA (dP2 D)) (.natLit 1))))) _ ?adj ?nonAdj
  case adj =>
    have hadj : SFormula.Deriv (brAdjF D :: Γ) (brAdjF D) := .hyp List.mem_cons_self
    exact commRightBulk D (cw1 hEntryA) (cw1 hEntryB) (cw1 hkAX) (cw1 hExcl1)
      (cw1 hnbulkB) (cw1 hntopB) (cw1 hrightB) hadj
      (cw1 hRange) (cw1 hRightBand) (cw1 hBulkBand) (cw1 hPin)
      (cw1 hEA0) (cw1 hEA1) (cw1 hEB0) (cw1 hEB1)
  case nonAdj =>
    -- `¬brAdjF` ⟹ band-broad non-adjacency via the parity collapse `dbrNonAdjImp`.
    have hNonAdj : SFormula.Deriv _ (.eqBool (SC.closed (brnaNonAdjTA2 D)) (SC.b true)) :=
      SFormula.Deriv.mp (SFormula.Deriv.mp (cw1 hNonAdjImp) (cw1 hKindK1))
        (.hyp List.mem_cons_self)
    exact pairCommuteBulkRightNonAdj D (cw1 hEntryA) (cw1 hEntryB) (cw1 hkAX) (cw1 hExcl1)
      (cw1 hbulkA) (cw1 hKindK1) (cw1 hnbulkB) (cw1 hntopB) (cw1 hrightB) hNonAdj (cw1 hBrnaPin)

/-- **Bulk–Left class-combo dispatcher.**  Row A (`k1`) is an X-type BULK plaquette,
row B (`k2`) a Z-type LEFT boundary.  Single `boolCases` on the pinned-row identity
`blAdjF`: TRUE → `commLeftBulk`; FALSE → `pairCommuteBulkLeftNonAdj`, with the
band-broad non-adjacency `blnaNonAdjTA2` recovered from `dblNonAdjImp`. -/
def dispatchBulkLeft {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hbundle : SFormula.Deriv Γ (pairBundleF D))
    (hpacks : SFormula.Deriv Γ (dblPacksF D))
    (hkAX : SFormula.Deriv Γ (k1IsX D true))
    (hkBZ : SFormula.Deriv Γ (k2IsX D false))
    (hbulkA : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true)))
    (hnbulkB : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)))
    (hntopB : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false)))
    (hnrightB : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false)))
    (hleftB : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b true))) :
    SFormula.Deriv Γ (pairGoal D) := by
  have hEntryA : SFormula.Deriv Γ (entryAQuant D) := SFormula.Deriv.andElimLeft hbundle
  have hEntryB : SFormula.Deriv Γ (entryBQuant D) :=
    SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hbundle)
  have hExcl1 : SFormula.Deriv Γ (typeExclF D k1P) :=
    SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hbundle))
  have hKindK1 : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k1P)) (SC.b false)) :=
    dbbKindK1OfIsX D hExcl1 hkAX hbulkA
  have hRange : SFormula.Deriv Γ (blRangePackF D) := SFormula.Deriv.andElimLeft hpacks
  have hRest1 := SFormula.Deriv.andElimRight hpacks
  have hLeftBand : SFormula.Deriv Γ (blLeftBandPackF D) := SFormula.Deriv.andElimLeft hRest1
  have hRest2 := SFormula.Deriv.andElimRight hRest1
  have hBulkBand : SFormula.Deriv Γ (blBulkBandPackF D) := SFormula.Deriv.andElimLeft hRest2
  have hRest3 := SFormula.Deriv.andElimRight hRest2
  have hPin : SFormula.Deriv Γ (blPinF D) := SFormula.Deriv.andElimLeft hRest3
  have hRest4 := SFormula.Deriv.andElimRight hRest3
  have hE0 := SFormula.Deriv.andElimLeft hRest4
  have hEA0 := SFormula.Deriv.andElimLeft hE0
  have hEB0 := SFormula.Deriv.andElimRight hE0
  have hRest5 := SFormula.Deriv.andElimRight hRest4
  have hE1 := SFormula.Deriv.andElimLeft hRest5
  have hEA1 := SFormula.Deriv.andElimLeft hE1
  have hEB1 := SFormula.Deriv.andElimRight hE1
  have hRest6 := SFormula.Deriv.andElimRight hRest5
  have hBlnaPin : SFormula.Deriv Γ (blnaPinF D) := SFormula.Deriv.andElimLeft hRest6
  have hNonAdjImp : SFormula.Deriv Γ (dblNonAdjImpF D) := SFormula.Deriv.andElimRight hRest6
  refine SFormula.Deriv.boolCases (SC.closed (.eqNat k1P
    (.mul (.add (.mul (.natLit 2) (blL D)) (.natLit 1)) (dm1TA (dP2 D))))) _ ?adj ?nonAdj
  case adj =>
    have hadj : SFormula.Deriv (blAdjF D :: Γ) (blAdjF D) := .hyp List.mem_cons_self
    exact commLeftBulk D (cw1 hEntryA) (cw1 hEntryB) (cw1 hkAX) (cw1 hExcl1)
      (cw1 hnbulkB) (cw1 hntopB) (cw1 hnrightB) (cw1 hleftB) hadj
      (cw1 hRange) (cw1 hLeftBand) (cw1 hBulkBand) (cw1 hPin)
      (cw1 hEA0) (cw1 hEA1) (cw1 hEB0) (cw1 hEB1)
  case nonAdj =>
    have hNonAdj : SFormula.Deriv _ (.eqBool (SC.closed (blnaNonAdjTA2 D)) (SC.b true)) :=
      SFormula.Deriv.mp (SFormula.Deriv.mp (cw1 hNonAdjImp) (cw1 hKindK1))
        (.hyp List.mem_cons_self)
    exact pairCommuteBulkLeftNonAdj D (cw1 hEntryA) (cw1 hEntryB) (cw1 hkAX) (cw1 hExcl1)
      (cw1 hbulkA) (cw1 hKindK1) (cw1 hnbulkB) (cw1 hntopB) (cw1 hnrightB) (cw1 hleftB)
      hNonAdj (cw1 hBlnaPin)

#print axioms dispatchBulkRight
#print axioms dispatchBulkLeft
#print axioms dbrNonAdjImp
#print axioms dblNonAdjImp
#print axioms dbrPacks
#print axioms dblPacks

/-! ## Boundary (X) – Bulk (Z) class-combo dispatchers (stage 2: top + bottom)

Two dispatchers route the BOUNDARY-X (`k1`) vs BULK-Z (`k2`) case to the matching
overlap closer or non-overlap handler.  Here the BOUNDARY row is `k1` (its CSS type
is carried by the boundary CLASS guards — `top`/`bottom`, NO `baseKindGuardTA`); the
BULK row is `k2` (`kind(k2)=true`, Z-kind, free from `typeExclF` via `dbbKindK2OfNotIsX`).

* `dispatchTopBulk`    : `k1` is a TOP-X boundary;    ADJACENT → `commBulkTop`
  (`btAdjF`), NON-ADJACENT → `pairCommuteTopBulkNonAdj` (`tbnaNonAdjTA2`).
* `dispatchBottomBulk` : `k1` is a BOTTOM-X boundary; ADJACENT → `commBottomBulk`
  (`bbAdjF`),  NON-ADJACENT → `pairCommuteBottomBulkNonAdj` (`btbnaNonAdjTA2`).

ROUTING is a SINGLE `boolCases` on the closer's `btAdjF`/`bbAdjF` `eqNat` condition.
The KEY reconciliation mirrors stage-1's `dbrNonAdjImp`/`dblNonAdjImp`, but the
collapsing kind-parity is now `k2`'s Z-kind (the bulk row), NOT `k1`'s.  The
non-overlap handler's band-broad `tbnaNonAdjTA2` (resp. `btbnaNonAdjTA2`) admits
THREE bulk columns at the boundary strip, whereas the closer's `btAdjF`/`bbAdjF` pins
exactly ONE.  Under `kind(k2)=true` (`(cellR k2 + cellC k2)` even) the band-broad form
COLLAPSES to the single pinned column (the boundary row has fixed parity, so only the
one matching-parity bulk column can be Z-kind), so the FALSE branch of the single
`btAdjF`/`bbAdjF` `boolCases` already establishes `tbnaNonAdjTA2`/`btbnaNonAdjTA2`.
This collapse is the new `arithBool` implication fact `dtbNonAdjImp`/`dbtbNonAdjImp`.
For BOTTOM, one extra `arithBool` fact `dbtbStripImp` supplies the strip-validity
bound `bbStripF` that `commBottomBulk` consumes — it follows from `bulk(k2)` + `bbAdjF`
(`(d-2)·(d-1) + 2bb+1 < (d-1)²` forces `bb < half`, hence `baseBTA(k1) < 4·half`). -/

/-- Pure-Nat core (top–bulk collapse): a Z-kind bulk cell `(r2, c2)` (`(r2+c2)` even)
whose pinned-column identity `k2 = 2·t` FAILS (with `k2 = m·r2 + c2`, `c2 < m`) is NOT
band-broad edge-adjacent to a top boundary at row `0`, cols `{2t, 2t+1}`.  Edge-
adjacency forces `r2 = 0` (so `k2 = c2`); then the Z-kind parity makes `c2` even, and
the three column options `c2 ∈ {2t−1, 2t, 2t+1}` leave only `c2 = 2t` (the others
odd), which IS the failed identity `k2 = 2t`. -/
private theorem dtbNonAdjCollapseCore {m r2 c2 t : Nat} (hm : 2 ≤ m)
    (hc2lt : c2 < m) (hkind : (r2 + c2) % 2 = 0)
    (hne : m * r2 + c2 ≠ 2 * t) :
    ¬ (r2 = 0 ∧ ((c2 = 2 * t ∨ c2 = 2 * t + 1) ∨ c2 + 1 = 2 * t)) := by
  rintro ⟨hr, hcol⟩
  subst hr
  rcases hcol with (h | h) | h
  · subst h; simp at hne
  · omega
  · omega

/-- Top–Bulk non-adjacency collapse (`arithBool`): under `k2` Z-kind
(`baseKindGuardTA(k2) = true`) and the FAILURE of the pinned-column identity `btAdjF`
(`k2 = 2·baseBTA(k1)`), the band-broad non-adjacency `tbnaNonAdjTA2` HOLDS.  `t =
baseBTA(k1)`.  Discharged by the parity core `dtbNonAdjCollapseCore`. -/
abbrev dtbNonAdjImpF (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k2P)) (SC.b true))
    (.imp (.eqBool (SC.closed (.eqNat k2P (.mul (.natLit 2) (baseBTA (dP2 D) k1P)))) (SC.b false))
      (.eqBool (SC.closed (tbnaNonAdjTA2 D)) (SC.b true)))

def dtbNonAdjImp (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (dtbNonAdjImpF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [tbnaNonAdjTA2, tbnaEdgeAdjTA2, baseKindGuardTA, baseBTA, baseHalfTA,
    bulkCountTA, dm1TA, dP2, k1P, k2P, SFormula.eval, SC.closed, SC.b, STerm.eval,
    Term.eval, Term.lift, bind, Option.bind]
  set k1 := rho ⟨1, by decide⟩ with hk1
  set k2 := rho ⟨0, by decide⟩ with hk2
  set d := D.distance with hdd
  have hdge : 3 ≤ d := by omega
  set m := d - 1 with hm
  have hm2 : 2 ≤ m := by omega
  set t := k1 - m * m with ht
  -- Core: Z-kind + pinned-identity failure ⟹ not band-broad edge-adjacent.
  have hcore : (k2 / m + k2 % m) % 2 = 0 → k2 ≠ 2 * t →
      ¬ (k2 / m = 0 ∧
        ((k2 % m = 2 * t ∨ k2 % m = 2 * t + 1) ∨ k2 % m + 1 = 2 * t)) := by
    intro hkind hne
    have hc2lt : k2 % m < m := Nat.mod_lt k2 (by omega)
    have hkdec : k2 = m * (k2 / m) + k2 % m := (Nat.div_add_mod k2 m).symm
    refine dtbNonAdjCollapseCore (m := m) (r2 := k2 / m) (c2 := k2 % m) (t := t) hm2 hc2lt hkind ?_
    omega
  by_cases hkind : (k2 / m + k2 % m) % 2 = 0
  · by_cases hne : k2 = 2 * t
    · simp only [decide_eq_true_eq.mpr hne]; simp
    · have hl := hcore hkind hne
      simp only [decide_eq_true_eq.mpr hkind, decide_eq_false_iff_not.mpr hne]
      by_cases hr0 : k2 / m = 0
      · by_cases hc0 : k2 % m = 2 * t
        · exact absurd ⟨hr0, Or.inl (Or.inl hc0)⟩ hl
        · by_cases hc1 : k2 % m = 2 * t + 1
          · exact absurd ⟨hr0, Or.inl (Or.inr hc1)⟩ hl
          · by_cases hc2 : k2 % m + 1 = 2 * t
            · exact absurd ⟨hr0, Or.inr hc2⟩ hl
            · simp [hr0, hc0, hc1, hc2]
      · simp [hr0]
  · simp only [decide_eq_false_iff_not.mpr hkind, Bool.false_eq_true, if_false, reduceIte]
    simp

/-! ### Pure witnesses for the top/bottom boundary overlap qubits -/

/-- Purity of `baseBTA(k1) = k1 − bulkCount`. -/
def dtbPureBaseB1 (D : OddSurfaceDistance) :
    SFormula.PureNatTerm (baseBTA (dP2 D) k1P) :=
  SFormula.PureNatTerm.sub (SFormula.PureNatTerm.var ⟨1, by decide⟩) (dbrPureBulkCount D)
/-- Purity of `btQ0 = 2·baseBTA(k1)`. -/
def dtbPureBtQ0 (D : OddSurfaceDistance) : SFormula.PureNatTerm (btQ0 D) :=
  .mul (.natLit 2) (dtbPureBaseB1 D)
/-- Purity of `btQ1 = 2·baseBTA(k1) + 1`. -/
def dtbPureBtQ1 (D : OddSurfaceDistance) : SFormula.PureNatTerm (btQ1 D) :=
  .add (.mul (.natLit 2) (dtbPureBaseB1 D)) (.natLit 1)
/-- Purity of `bbB = baseBTA(k1) − 3·half`. -/
def dbtbPureBbB (D : OddSurfaceDistance) : SFormula.PureNatTerm (bbB D) :=
  SFormula.PureNatTerm.sub (dtbPureBaseB1 D)
    (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.natLit 3) (dbrPureHalf D))
/-- Purity of `bbQ0 = d·(d−1) + (2·bb + 1)`. -/
def dbtbPureBbQ0 (D : OddSurfaceDistance) : SFormula.PureNatTerm (bbQ0 D) :=
  .add (.mul (dbbPureD D) (dbbPureDm1 D)) (.add (.mul (.natLit 2) (dbtbPureBbB D)) (.natLit 1))
/-- Purity of `bbQ1 = d·(d−1) + (2·bb + 2)`. -/
def dbtbPureBbQ1 (D : OddSurfaceDistance) : SFormula.PureNatTerm (bbQ1 D) :=
  .add (.mul (dbbPureD D) (dbbPureDm1 D)) (.add (.mul (.natLit 2) (dbtbPureBbB D)) (.natLit 2))

/-! ### Top–Bulk pack super-bundle (`PureFamilyDerivA`, cut into the context)

`dtbPacksF` gathers everything the top–bulk routing needs that lives ONLY as a
`PureFamilyDerivA`: the closer's Range / TopBand / BulkBand / Pin packs, the four flat
entries at `btQ0`,`btQ1`, the non-overlap handler's `tbnaPinF`, and the non-adjacency
collapse fact `dtbNonAdjImpF`.  Layout (left→right):
`Range ∧ TopBand ∧ BulkBand ∧ Pin ∧ (EA0 ∧ EB0) ∧ (EA1 ∧ EB1) ∧ tbnaPin ∧ NonAdjImp`. -/

abbrev dtbPacksF (D : OddSurfaceDistance) : SFormula 2 :=
  .and (btRangePackF D) (.and (btTopBandPackF D) (.and (btBulkBandPackF D) (.and (btPinF D)
    (.and (.and (entryAAtQF D (btQ0 D)) (entryBAtQF D (btQ0 D)))
      (.and (.and (entryAAtQF D (btQ1 D)) (entryBAtQF D (btQ1 D)))
        (.and (tbnaPinF D) (dtbNonAdjImpF D)))))))
def dtbPacks (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (dtbPacksF D) :=
  pfdaAnd2 (btRangePack D) (pfdaAnd2 (btTopBandPack D) (pfdaAnd2 (btBulkBandPack D)
    (pfdaAnd2 (btPinPack D)
      (pfdaAnd2 (dbbEntryPair D (btQ0 D) (dtbPureBtQ0 D))
        (pfdaAnd2 (dbbEntryPair D (btQ1 D) (dtbPureBtQ1 D))
          (pfdaAnd2 (tbnaPinPack D) (dtbNonAdjImp D)))))))

/-- **Top–Bulk class-combo dispatcher.**  Row A (`k1`) is an X-type TOP boundary, row
B (`k2`) a Z-type BULK plaquette.  Single `boolCases` on the pinned-column identity
`btAdjF` (`k2 = 2·baseBTA(k1)`): TRUE → `commBulkTop`; FALSE →
`pairCommuteTopBulkNonAdj`, where the band-broad non-adjacency `tbnaNonAdjTA2` is
recovered from `dtbNonAdjImp` (the Z-kind parity collapse).  `k1`'s X-type is carried
by the boundary class guards (`¬bulk`, `topClass`); `k2`'s Z-kind fact comes free via
`dbbKindK2OfNotIsX`; all `PureFamilyDerivA` packs/entries come from `hpacks`. -/
def dispatchTopBulk {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hbundle : SFormula.Deriv Γ (pairBundleF D))
    (hpacks : SFormula.Deriv Γ (dtbPacksF D))
    (hkAX : SFormula.Deriv Γ (k1IsX D true))
    (hkBZ : SFormula.Deriv Γ (k2IsX D false))
    (hnbulkA : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false)))
    (htopA : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b true)))
    (hbulkB : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true))) :
    SFormula.Deriv Γ (pairGoal D) := by
  -- Base facts from `hbundle`.
  have hEntryA : SFormula.Deriv Γ (entryAQuant D) := SFormula.Deriv.andElimLeft hbundle
  have hEntryB : SFormula.Deriv Γ (entryBQuant D) :=
    SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hbundle)
  have hExcl1 : SFormula.Deriv Γ (typeExclF D k1P) :=
    SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hbundle))
  have hExcl2 : SFormula.Deriv Γ (typeExclF D k2P) :=
    SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hbundle))
  -- Kind fact for `k2` (free, Z-kind).
  have hKindK2 : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k2P)) (SC.b true)) :=
    dbbKindK2OfNotIsX D hExcl2 hkBZ hbulkB
  -- Packs / entries / facts from `hpacks`.
  have hRange : SFormula.Deriv Γ (btRangePackF D) := SFormula.Deriv.andElimLeft hpacks
  have hRest1 := SFormula.Deriv.andElimRight hpacks
  have hTopBand : SFormula.Deriv Γ (btTopBandPackF D) := SFormula.Deriv.andElimLeft hRest1
  have hRest2 := SFormula.Deriv.andElimRight hRest1
  have hBulkBand : SFormula.Deriv Γ (btBulkBandPackF D) := SFormula.Deriv.andElimLeft hRest2
  have hRest3 := SFormula.Deriv.andElimRight hRest2
  have hPin : SFormula.Deriv Γ (btPinF D) := SFormula.Deriv.andElimLeft hRest3
  have hRest4 := SFormula.Deriv.andElimRight hRest3
  have hE0 := SFormula.Deriv.andElimLeft hRest4
  have hEA0 := SFormula.Deriv.andElimLeft hE0
  have hEB0 := SFormula.Deriv.andElimRight hE0
  have hRest5 := SFormula.Deriv.andElimRight hRest4
  have hE1 := SFormula.Deriv.andElimLeft hRest5
  have hEA1 := SFormula.Deriv.andElimLeft hE1
  have hEB1 := SFormula.Deriv.andElimRight hE1
  have hRest6 := SFormula.Deriv.andElimRight hRest5
  have hTbnaPin : SFormula.Deriv Γ (tbnaPinF D) := SFormula.Deriv.andElimLeft hRest6
  have hNonAdjImp : SFormula.Deriv Γ (dtbNonAdjImpF D) := SFormula.Deriv.andElimRight hRest6
  -- Single route: btAdjF (`k2 = 2·baseBTA(k1)`).
  refine SFormula.Deriv.boolCases (SC.closed (.eqNat k2P (.mul (.natLit 2) (btB D)))) _ ?adj ?nonAdj
  case adj =>
    have hadj : SFormula.Deriv (btAdjF D :: Γ) (btAdjF D) := .hyp List.mem_cons_self
    exact commBulkTop D (cw1 hEntryA) (cw1 hEntryB) (cw1 hkAX) (cw1 hExcl1)
      (cw1 hnbulkA) (cw1 htopA) hadj
      (cw1 hRange) (cw1 hTopBand) (cw1 hBulkBand) (cw1 hPin)
      (cw1 hEA0) (cw1 hEA1) (cw1 hEB0) (cw1 hEB1)
  case nonAdj =>
    -- `¬btAdjF` ⟹ band-broad non-adjacency via the Z-kind parity collapse.
    have hNonAdj : SFormula.Deriv _ (.eqBool (SC.closed (tbnaNonAdjTA2 D)) (SC.b true)) :=
      SFormula.Deriv.mp (SFormula.Deriv.mp (cw1 hNonAdjImp) (cw1 hKindK2))
        (.hyp List.mem_cons_self)
    exact pairCommuteTopBulkNonAdj D (cw1 hEntryA) (cw1 hEntryB) (cw1 hkAX) (cw1 hExcl1)
      (cw1 hnbulkA) (cw1 htopA) (cw1 hbulkB) (cw1 hKindK2) hNonAdj (cw1 hTbnaPin)

#print axioms dtbNonAdjImp
#print axioms dtbPacks
#print axioms dispatchTopBulk

/-! ### Bottom–Bulk collapse + strip-validity `arithBool` facts -/

/-- Pure-Nat core (bottom–bulk collapse): a Z-kind bulk cell `(r2, c2)` (`(r2+c2)`
even) with `r2 < m` whose pinned-column identity `k2 = (m−1)·m + (2bb+1)` FAILS (with
`k2 = m·r2 + c2`, `c2 < m`) is NOT band-broad edge-adjacent to a bottom boundary at
row `m`, cols `{2bb+1, 2bb+2}`.  Edge-adjacency forces `r2 + 1 = m` (so `r2 = m−1`,
odd since `m` even); the Z-kind parity then makes `c2` odd, and the three column
options `c2 ∈ {2bb, 2bb+1, 2bb+2}` leave only `c2 = 2bb+1` (the others even), which IS
the failed identity. -/
private theorem dbtbNonAdjCollapseCore {m r2 c2 bb : Nat} (hm : 2 ≤ m) (hmeven : m % 2 = 0)
    (hc2lt : c2 < m) (hr2lt : r2 < m) (hkind : (r2 + c2) % 2 = 0)
    (hne : m * r2 + c2 ≠ (m - 1) * m + (2 * bb + 1)) :
    ¬ (r2 + 1 = m ∧ ((c2 = 2 * bb ∨ c2 = 2 * bb + 1) ∨ c2 = 2 * bb + 2)) := by
  rintro ⟨hr, hcol⟩
  have hr2 : r2 = m - 1 := by omega
  rcases hcol with (h | h) | h
  · omega
  · subst h; subst hr2
    apply hne
    rw [Nat.mul_comm]
  · omega

/-- Bottom–Bulk non-adjacency collapse (`arithBool`): under `k2` Z-kind
(`baseKindGuardTA(k2) = true`) and the FAILURE of the pinned-column identity `bbAdjF`
(`k2 = (d−2)·(d−1) + (2bb+1)`), the band-broad non-adjacency `btbnaNonAdjTA2` HOLDS.
`bb = baseBTA(k1) − 3·half`.  Discharged by `dbtbNonAdjCollapseCore`. -/
abbrev dbtbNonAdjImpF (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k2P)) (SC.b true))
    (.imp (.eqBool (SC.closed (.eqNat k2P
        (.add (.mul (.sub (dm1TA (dP2 D)) (.natLit 1)) (dm1TA (dP2 D)))
          (.add (.mul (.natLit 2) (bbB D)) (.natLit 1))))) (SC.b false))
      (.eqBool (SC.closed (btbnaNonAdjTA2 D)) (SC.b true)))

def dbtbNonAdjImp (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (dbtbNonAdjImpF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [btbnaNonAdjTA2, btbnaEdgeAdjTA2, bbB, baseKindGuardTA, baseBTA, baseHalfTA,
    bulkCountTA, dm1TA, dP2, k1P, k2P, SFormula.eval, SC.closed, SC.b, STerm.eval,
    Term.eval, Term.lift, bind, Option.bind]
  set k1 := rho ⟨1, by decide⟩ with hk1
  set k2 := rho ⟨0, by decide⟩ with hk2
  set d := D.distance with hdd
  have hdge : 3 ≤ d := by omega
  set m := d - 1 with hm
  have hm2 : 2 ≤ m := by omega
  have hmeven : m % 2 = 0 := by omega
  set bb := k1 - m * m - 3 * (m / 2) with hbb
  -- Core: Z-kind + pinned-identity failure ⟹ not band-broad edge-adjacent.
  have hcore : (k2 / m + k2 % m) % 2 = 0 → k2 ≠ (m - 1) * m + (2 * bb + 1) →
      ¬ (k2 / m + 1 = m ∧
        ((k2 % m = 2 * bb ∨ k2 % m = 2 * bb + 1) ∨ k2 % m = 2 * bb + 2)) := by
    intro hkind hne
    have hc2lt : k2 % m < m := Nat.mod_lt k2 (by omega)
    have hkdec : k2 = m * (k2 / m) + k2 % m := (Nat.div_add_mod k2 m).symm
    by_cases hr2lt : k2 / m < m
    · refine dbtbNonAdjCollapseCore (m := m) (r2 := k2 / m) (c2 := k2 % m) (bb := bb)
        hm2 hmeven hc2lt hr2lt hkind ?_
      omega
    · -- `cellR k2 ≥ m`: edge-adjacency needs `cellR k2 + 1 = m`, impossible.
      rintro ⟨hr, _⟩; omega
  by_cases hkind : (k2 / m + k2 % m) % 2 = 0
  · by_cases hne : k2 = (m - 1) * m + (2 * bb + 1)
    · simp only [decide_eq_true_eq.mpr hne]; simp
    · have hl := hcore hkind hne
      simp only [decide_eq_true_eq.mpr hkind, decide_eq_false_iff_not.mpr hne]
      by_cases hrr : k2 / m + 1 = m
      · by_cases hc0 : k2 % m = 2 * bb
        · exact absurd ⟨hrr, Or.inl (Or.inl hc0)⟩ hl
        · by_cases hc1 : k2 % m = 2 * bb + 1
          · exact absurd ⟨hrr, Or.inl (Or.inr hc1)⟩ hl
          · by_cases hc2 : k2 % m = 2 * bb + 2
            · exact absurd ⟨hrr, Or.inr hc2⟩ hl
            · simp [hrr, hc0, hc1, hc2]
      · simp [hrr]
  · simp only [decide_eq_false_iff_not.mpr hkind, Bool.false_eq_true, if_false, reduceIte]
    simp

/-- Pure-Nat core (bottom strip-validity): if `k2 = (m−1)·m + (2bb+1) < m·m` with
`bb = B − 3h` (`h = m/2`, `m` even, `m ≥ 2`), then `B < 4·h`.  From `k2 < m·m =
(m−1)·m + m` we get `2bb+1 < m`, so `bb < h`; `B = bb + 3h` (when `B ≥ 3h`) or
`B ≤ 3h < 4h` (when `B < 3h`) gives `B < 4h`. -/
private theorem dbtbStripCore {m B bb : Nat} (hm : 2 ≤ m) (hmeven : m % 2 = 0)
    (hbb : bb = B - 3 * (m / 2))
    (hlt : (m - 1) * m + (2 * bb + 1) < m * m) :
    B < 4 * (m / 2) := by
  have hmm : (m - 1) * m = m * m - m := by
    rw [Nat.sub_mul, Nat.one_mul]
  rw [hmm] at hlt
  have hmlem : m ≤ m * m := Nat.le_mul_of_pos_left m (by omega)
  have hhalf : 2 * (m / 2) = m := by omega
  omega

/-- Bottom strip-validity (`arithBool`): under `bulk(k2)=true` (`k2 < (d−1)²`) and the
pinned identity `bbAdjF` (`k2 = (d−2)·(d−1) + (2bb+1)`), the strip bound `bbStripF`
(`baseBTA(k1) < 4·half`) HOLDS.  This is the one extra range fact `commBottomBulk`
needs that the four boundary class guards do not give for free. -/
abbrev dbtbStripImpF (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true))
    (.imp (.eqBool (SC.closed (.eqNat k2P
        (.add (.mul (.sub (dm1TA (dP2 D)) (.natLit 1)) (dm1TA (dP2 D)))
          (.add (.mul (.natLit 2) (bbB D)) (.natLit 1))))) (SC.b true))
      (bbStripF D))

def dbtbStripImp (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (dbtbStripImpF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [bbStripF, bbB, bulkGuardTA, baseBTA, baseHalfTA, bulkCountTA, dm1TA, dP2,
    k1P, k2P, SFormula.eval, SC.closed, SC.b, STerm.eval, Term.eval, Term.lift, bind, Option.bind]
  set k1 := rho ⟨1, by decide⟩ with hk1
  set k2 := rho ⟨0, by decide⟩ with hk2
  set d := D.distance with hdd
  have hdge : 3 ≤ d := by omega
  set m := d - 1 with hm
  have hm2 : 2 ≤ m := by omega
  have hmeven : m % 2 = 0 := by omega
  set B := k1 - m * m with hB
  set bb := B - 3 * (m / 2) with hbb
  by_cases hbulk : k2 < m * m
  · have hbt : decide (decide (k2 < m * m) = true) = true := by
      rw [decide_eq_true_eq]; simp [hbulk]
    by_cases hadj : k2 = (m - 1) * m + (2 * bb + 1)
    · have hlt : (m - 1) * m + (2 * bb + 1) < m * m := by rw [← hadj]; exact hbulk
      have hres := dbtbStripCore (m := m) (B := B) (bb := bb) hm2 hmeven hbb hlt
      have hat : decide (decide (k2 = (m - 1) * m + (2 * bb + 1)) = true) = true := by
        rw [decide_eq_true_eq]; simp [hadj]
      have hrt : decide (decide (B < 4 * (m / 2)) = true) = true := by
        rw [decide_eq_true_eq]; simp [hres]
      simp only [hbt, hat, if_true, hrt]
    · have haf : decide (decide (k2 = (m - 1) * m + (2 * bb + 1)) = true) = false := by
        rw [decide_eq_false_iff_not]; simp [hadj]
      simp only [hbt, haf, if_true, Bool.false_eq_true, if_false, reduceIte]
  · have hbf : decide (decide (k2 < m * m) = true) = false := by
      rw [decide_eq_false_iff_not]; simp [hbulk]
    simp only [hbf, Bool.false_eq_true, if_false, reduceIte]

/-! ### Bottom–Bulk pack super-bundle (`PureFamilyDerivA`, cut into the context)

`dbtbPacksF` gathers everything the bottom–bulk routing needs that lives ONLY as a
`PureFamilyDerivA`: the closer's Range / BottomBand / BulkBand / Pin packs, the four
flat entries at `bbQ0`,`bbQ1`, the non-overlap handler's `btbnaPinF`, the non-adjacency
collapse fact `dbtbNonAdjImpF`, and the strip-validity fact `dbtbStripImpF`.  Layout:
`Range ∧ BotBand ∧ BulkBand ∧ Pin ∧ (EA0 ∧ EB0) ∧ (EA1 ∧ EB1) ∧ btbnaPin ∧ NonAdjImp ∧ StripImp`. -/

abbrev dbtbPacksF (D : OddSurfaceDistance) : SFormula 2 :=
  .and (bbRangePackF D) (.and (bbBottomBandPackF D) (.and (bbBulkBandPackF D) (.and (bbPinF D)
    (.and (.and (entryAAtQF D (bbQ0 D)) (entryBAtQF D (bbQ0 D)))
      (.and (.and (entryAAtQF D (bbQ1 D)) (entryBAtQF D (bbQ1 D)))
        (.and (btbnaPinF D) (.and (dbtbNonAdjImpF D) (dbtbStripImpF D))))))))
def dbtbPacks (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (dbtbPacksF D) :=
  pfdaAnd2 (bbRangePack D) (pfdaAnd2 (bbBottomBandPack D) (pfdaAnd2 (bbBulkBandPack D)
    (pfdaAnd2 (bbPinPack D)
      (pfdaAnd2 (dbbEntryPair D (bbQ0 D) (dbtbPureBbQ0 D))
        (pfdaAnd2 (dbbEntryPair D (bbQ1 D) (dbtbPureBbQ1 D))
          (pfdaAnd2 (btbnaPinPack D) (pfdaAnd2 (dbtbNonAdjImp D) (dbtbStripImp D))))))))

/-- **Bottom–Bulk class-combo dispatcher.**  Row A (`k1`) is an X-type BOTTOM boundary,
row B (`k2`) a Z-type BULK plaquette.  Single `boolCases` on the pinned-column identity
`bbAdjF` (`k2 = (d−2)·(d−1) + (2bb+1)`): TRUE → `commBottomBulk` (whose strip-validity
antecedent `bbStripF` is supplied by `dbtbStripImp` from `bulk(k2)` + `bbAdjF`); FALSE
→ `pairCommuteBottomBulkNonAdj`, where the band-broad non-adjacency `btbnaNonAdjTA2` is
recovered from `dbtbNonAdjImp` (the Z-kind parity collapse).  `k1`'s X-type is carried
by the four boundary class guards; `k2`'s Z-kind fact comes free via `dbbKindK2OfNotIsX`. -/
def dispatchBottomBulk {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hbundle : SFormula.Deriv Γ (pairBundleF D))
    (hpacks : SFormula.Deriv Γ (dbtbPacksF D))
    (hkAX : SFormula.Deriv Γ (k1IsX D true))
    (hkBZ : SFormula.Deriv Γ (k2IsX D false))
    (hnbulkA : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false)))
    (hntopA : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false)))
    (hnrightA : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k1P)) (SC.b false)))
    (hnleftA : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k1P)) (SC.b false)))
    (hbulkB : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true))) :
    SFormula.Deriv Γ (pairGoal D) := by
  -- Base facts from `hbundle`.
  have hEntryA : SFormula.Deriv Γ (entryAQuant D) := SFormula.Deriv.andElimLeft hbundle
  have hEntryB : SFormula.Deriv Γ (entryBQuant D) :=
    SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hbundle)
  have hExcl1 : SFormula.Deriv Γ (typeExclF D k1P) :=
    SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hbundle))
  have hExcl2 : SFormula.Deriv Γ (typeExclF D k2P) :=
    SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hbundle))
  -- Kind fact for `k2` (free, Z-kind).
  have hKindK2 : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k2P)) (SC.b true)) :=
    dbbKindK2OfNotIsX D hExcl2 hkBZ hbulkB
  -- Packs / entries / facts from `hpacks`.
  have hRange : SFormula.Deriv Γ (bbRangePackF D) := SFormula.Deriv.andElimLeft hpacks
  have hRest1 := SFormula.Deriv.andElimRight hpacks
  have hBotBand : SFormula.Deriv Γ (bbBottomBandPackF D) := SFormula.Deriv.andElimLeft hRest1
  have hRest2 := SFormula.Deriv.andElimRight hRest1
  have hBulkBand : SFormula.Deriv Γ (bbBulkBandPackF D) := SFormula.Deriv.andElimLeft hRest2
  have hRest3 := SFormula.Deriv.andElimRight hRest2
  have hPin : SFormula.Deriv Γ (bbPinF D) := SFormula.Deriv.andElimLeft hRest3
  have hRest4 := SFormula.Deriv.andElimRight hRest3
  have hE0 := SFormula.Deriv.andElimLeft hRest4
  have hEA0 := SFormula.Deriv.andElimLeft hE0
  have hEB0 := SFormula.Deriv.andElimRight hE0
  have hRest5 := SFormula.Deriv.andElimRight hRest4
  have hE1 := SFormula.Deriv.andElimLeft hRest5
  have hEA1 := SFormula.Deriv.andElimLeft hE1
  have hEB1 := SFormula.Deriv.andElimRight hE1
  have hRest6 := SFormula.Deriv.andElimRight hRest5
  have hBtbnaPin : SFormula.Deriv Γ (btbnaPinF D) := SFormula.Deriv.andElimLeft hRest6
  have hRest7 := SFormula.Deriv.andElimRight hRest6
  have hNonAdjImp : SFormula.Deriv Γ (dbtbNonAdjImpF D) := SFormula.Deriv.andElimLeft hRest7
  have hStripImp : SFormula.Deriv Γ (dbtbStripImpF D) := SFormula.Deriv.andElimRight hRest7
  -- Single route: bbAdjF (`k2 = (d−2)·(d−1) + (2bb+1)`).
  refine SFormula.Deriv.boolCases (SC.closed (.eqNat k2P
    (.add (.mul (.sub (dm1TA (dP2 D)) (.natLit 1)) (dm1TA (dP2 D)))
      (.add (.mul (.natLit 2) (bbB D)) (.natLit 1))))) _ ?adj ?nonAdj
  case adj =>
    have hadj : SFormula.Deriv (bbAdjF D :: Γ) (bbAdjF D) := .hyp List.mem_cons_self
    have hstrip : SFormula.Deriv _ (bbStripF D) :=
      SFormula.Deriv.mp (SFormula.Deriv.mp (cw1 hStripImp) (cw1 hbulkB)) hadj
    exact commBottomBulk D (cw1 hEntryA) (cw1 hEntryB) (cw1 hkAX) (cw1 hExcl1)
      (cw1 hnbulkA) (cw1 hntopA) (cw1 hnrightA) (cw1 hnleftA) hstrip hadj
      (cw1 hRange) (cw1 hBotBand) (cw1 hBulkBand) (cw1 hPin)
      (cw1 hEA0) (cw1 hEA1) (cw1 hEB0) (cw1 hEB1)
  case nonAdj =>
    -- `¬bbAdjF` ⟹ band-broad non-adjacency via the Z-kind parity collapse.
    have hNonAdj : SFormula.Deriv _ (.eqBool (SC.closed (btbnaNonAdjTA2 D)) (SC.b true)) :=
      SFormula.Deriv.mp (SFormula.Deriv.mp (cw1 hNonAdjImp) (cw1 hKindK2))
        (.hyp List.mem_cons_self)
    exact pairCommuteBottomBulkNonAdj D (cw1 hEntryA) (cw1 hEntryB) (cw1 hkAX) (cw1 hExcl1)
      (cw1 hnbulkA) (cw1 hntopA) (cw1 hnrightA) (cw1 hnleftA) (cw1 hbulkB) (cw1 hKindK2)
      hNonAdj (cw1 hBtbnaPin)

#print axioms dbtbNonAdjImp
#print axioms dbtbStripImp
#print axioms dbtbPacks
#print axioms dispatchBottomBulk

/-! ## Boundary–Boundary (X) ↔ (Z) class-combo dispatchers (stage 3)

Row A (`k1`) is an X-type BOUNDARY (top or bottom); row B (`k2`) is a Z-type BOUNDARY
(right or left).  Such a pair is ALWAYS non-adjacent: an X-boundary check and a
Z-boundary check never share a qubit (an X-type boundary lives on a top/bottom row, a
Z-type boundary on a left/right column; the disjointness cores `trnaCellContra`, etc.
discharge this UNCONDITIONALLY).  Hence there is NO adjacency `boolCases` and NO
overlap closer — each dispatcher simply assembles the boundary-class context for both
rows and calls the matching boundary–boundary non-overlap handler:

* `dispatchTopRight`    → `pairCommuteTopRightNonAdj`    (`trnaPinF`)
* `dispatchTopLeft`     → `pairCommuteTopLeftNonAdj`     (`tlnaPinF`)
* `dispatchBottomRight` → `pairCommuteBottomRightNonAdj` (`brbnaPinF`)
* `dispatchBottomLeft`  → `pairCommuteBottomLeftNonAdj`  (`blbnaPinF`)

The ONLY `PureFamilyDerivA` piece each consumes (it has no `arithBool`/`recUnfold` leaf
in `Γ`) is the handler's disjointness pin, so each dispatcher's `hpacks` super-bundle
is just that single pin pack.  `hEntryA`/`hEntryB`/`hExcl1` come from `hbundle`; the
boundary class guards for both rows are passed directly. -/

/-- Top–Right pack super-bundle: just the top–right disjointness pin (the lone
`PureFamilyDerivA` the non-overlap handler consumes). -/
abbrev dtrPacksF (D : OddSurfaceDistance) : SFormula 2 := trnaPinF D
def dtrPacks (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (dtrPacksF D) :=
  trnaPinPack D

/-- **Top–Right boundary–boundary class-combo dispatcher.**  Row A (`k1`) is an
X-type TOP boundary, row B (`k2`) a Z-type RIGHT boundary.  Always non-adjacent, so
NO routing: assemble the context and call `pairCommuteTopRightNonAdj`.  `k1`'s X-type
is carried by `hkAX`/`hExcl1` (the latter from `hbundle`); the boundary classes are
passed directly; the only pack (`trnaPinF`) comes from `hpacks`. -/
def dispatchTopRight {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hbundle : SFormula.Deriv Γ (pairBundleF D))
    (hpacks : SFormula.Deriv Γ (dtrPacksF D))
    (hkAX : SFormula.Deriv Γ (k1IsX D true))
    (hkBZ : SFormula.Deriv Γ (k2IsX D false))
    (hnbulkA : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false)))
    (htopA : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b true)))
    (hnbulkB : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)))
    (hntopB : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false)))
    (hrightB : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b true))) :
    SFormula.Deriv Γ (pairGoal D) := by
  have hEntryA : SFormula.Deriv Γ (entryAQuant D) := SFormula.Deriv.andElimLeft hbundle
  have hEntryB : SFormula.Deriv Γ (entryBQuant D) :=
    SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hbundle)
  have hExcl1 : SFormula.Deriv Γ (typeExclF D k1P) :=
    SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hbundle))
  exact pairCommuteTopRightNonAdj D hEntryA hEntryB hkAX hExcl1
    hnbulkA htopA hnbulkB hntopB hrightB hpacks

#print axioms dtrPacks
#print axioms dispatchTopRight

/-- Top–Left pack super-bundle: just the top–left disjointness pin. -/
abbrev dtlPacksF (D : OddSurfaceDistance) : SFormula 2 := tlnaPinF D
def dtlPacks (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (dtlPacksF D) :=
  tlnaPinPack D

/-- **Top–Left boundary–boundary class-combo dispatcher.**  Row A (`k1`) is an
X-type TOP boundary, row B (`k2`) a Z-type LEFT boundary.  Always non-adjacent, so
NO routing: assemble the context and call `pairCommuteTopLeftNonAdj`. -/
def dispatchTopLeft {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hbundle : SFormula.Deriv Γ (pairBundleF D))
    (hpacks : SFormula.Deriv Γ (dtlPacksF D))
    (hkAX : SFormula.Deriv Γ (k1IsX D true))
    (hkBZ : SFormula.Deriv Γ (k2IsX D false))
    (hnbulkA : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false)))
    (htopA : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b true)))
    (hnbulkB : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)))
    (hntopB : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false)))
    (hnrightB : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false)))
    (hleftB : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b true))) :
    SFormula.Deriv Γ (pairGoal D) := by
  have hEntryA : SFormula.Deriv Γ (entryAQuant D) := SFormula.Deriv.andElimLeft hbundle
  have hEntryB : SFormula.Deriv Γ (entryBQuant D) :=
    SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hbundle)
  have hExcl1 : SFormula.Deriv Γ (typeExclF D k1P) :=
    SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hbundle))
  exact pairCommuteTopLeftNonAdj D hEntryA hEntryB hkAX hExcl1
    hnbulkA htopA hnbulkB hntopB hnrightB hleftB hpacks

#print axioms dtlPacks
#print axioms dispatchTopLeft

/-- Bottom–Right pack super-bundle: just the bottom–right disjointness pin. -/
abbrev dbtrPacksF (D : OddSurfaceDistance) : SFormula 2 := brbnaPinF D
def dbtrPacks (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (dbtrPacksF D) :=
  brbnaPinPack D

/-- **Bottom–Right boundary–boundary class-combo dispatcher.**  Row A (`k1`) is an
X-type BOTTOM boundary (`¬top ∧ ¬right ∧ ¬left`), row B (`k2`) a Z-type RIGHT boundary.
Always non-adjacent, so NO routing: assemble the context and call
`pairCommuteBottomRightNonAdj`. -/
def dispatchBottomRight {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hbundle : SFormula.Deriv Γ (pairBundleF D))
    (hpacks : SFormula.Deriv Γ (dbtrPacksF D))
    (hkAX : SFormula.Deriv Γ (k1IsX D true))
    (hkBZ : SFormula.Deriv Γ (k2IsX D false))
    (hnbulkA : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false)))
    (hntopA : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false)))
    (hnrightA : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k1P)) (SC.b false)))
    (hnleftA : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k1P)) (SC.b false)))
    (hnbulkB : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)))
    (hntopB : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false)))
    (hrightB : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b true))) :
    SFormula.Deriv Γ (pairGoal D) := by
  have hEntryA : SFormula.Deriv Γ (entryAQuant D) := SFormula.Deriv.andElimLeft hbundle
  have hEntryB : SFormula.Deriv Γ (entryBQuant D) :=
    SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hbundle)
  have hExcl1 : SFormula.Deriv Γ (typeExclF D k1P) :=
    SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hbundle))
  exact pairCommuteBottomRightNonAdj D hEntryA hEntryB hkAX hExcl1
    hnbulkA hntopA hnrightA hnleftA hnbulkB hntopB hrightB hpacks

#print axioms dbtrPacks
#print axioms dispatchBottomRight

/-- Bottom–Left pack super-bundle: just the bottom–left disjointness pin. -/
abbrev dbtlPacksF (D : OddSurfaceDistance) : SFormula 2 := blbnaPinF D
def dbtlPacks (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (dbtlPacksF D) :=
  blbnaPinPack D

/-- **Bottom–Left boundary–boundary class-combo dispatcher.**  Row A (`k1`) is an
X-type BOTTOM boundary (`¬top ∧ ¬right ∧ ¬left`), row B (`k2`) a Z-type LEFT boundary.
Always non-adjacent, so NO routing: assemble the context and call
`pairCommuteBottomLeftNonAdj`. -/
def dispatchBottomLeft {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hbundle : SFormula.Deriv Γ (pairBundleF D))
    (hpacks : SFormula.Deriv Γ (dbtlPacksF D))
    (hkAX : SFormula.Deriv Γ (k1IsX D true))
    (hkBZ : SFormula.Deriv Γ (k2IsX D false))
    (hnbulkA : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false)))
    (hntopA : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false)))
    (hnrightA : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k1P)) (SC.b false)))
    (hnleftA : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k1P)) (SC.b false)))
    (hnbulkB : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)))
    (hntopB : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false)))
    (hnrightB : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false)))
    (hleftB : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b true))) :
    SFormula.Deriv Γ (pairGoal D) := by
  have hEntryA : SFormula.Deriv Γ (entryAQuant D) := SFormula.Deriv.andElimLeft hbundle
  have hEntryB : SFormula.Deriv Γ (entryBQuant D) :=
    SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hbundle)
  have hExcl1 : SFormula.Deriv Γ (typeExclF D k1P) :=
    SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hbundle))
  exact pairCommuteBottomLeftNonAdj D hEntryA hEntryB hkAX hExcl1
    hnbulkA hntopA hnrightA hnleftA hnbulkB hntopB hnrightB hleftB hpacks

#print axioms dbtlPacks
#print axioms dispatchBottomLeft

end QHL.CodeLang.Surface.Verify
