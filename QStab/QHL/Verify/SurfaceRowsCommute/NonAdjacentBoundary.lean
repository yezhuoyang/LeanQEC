import QStab.QHL.Verify.SurfaceRowsCommute.NonAdjacentBulk

/-!
# Rows-commute (pairwise generated-row commutation) — NonAdjacentBoundary

The top–bulk and bottom–bulk non-adjacent (non-overlap) pairs and their closers.
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface

set_option maxRecDepth 65536
set_option linter.unusedVariables false

/-! ## Top–Bulk NON-ADJACENT (non-overlap) different-type pair

MIRROR of `pairCommuteBulkTop` overlap, NON-overlap variant.  Row A (`k1`) is an
X-type TOP-boundary stabilizer, row B (`k2`) a Z-kind BULK plaquette, and the two are
NOT edge-adjacent.  A non-adjacent top boundary and bulk plaquette share NO qubit, so
the `(X,Z)`/`(Z,X)` leaf-pairs in the pointwise dispatcher never both fire — the
genuine `(X,Z)` branch is closed by a DISJOINTNESS PIN (the top band and the bulk band
can never both fire at one qubit), and the `(Z,X)` branch is vacuous via the X-type
exclusion.

The top boundary `k1` occupies row `0`, cols `{2·topIdx, 2·topIdx+1}`
(`topIdx = k1−bulkCount`).  The bulk plaquette `k2` shares a qubit with it ONLY when
`cellR k2 = 0` (its row band `{0,1}` meets row `0`) AND its col band
`{cellC k2, cellC k2+1}` meets `{2·topIdx, 2·topIdx+1}`, i.e.
`cellC k2 ∈ {2·topIdx−1, 2·topIdx, 2·topIdx+1}`.  NON-ADJACENCY is the negation of
exactly that condition. -/

/-- Edge-adjacency of a top-boundary row `k1` and a bulk cell `k2` (arity 3,
`k1 = var 2`, `k2 = var 1`): the bulk's row `cellR k2 = 0` meets the top strip's row
`0`, and the bulk col band meets the top strip's cols `{2·topIdx, 2·topIdx+1}`
(`topIdx = btB3`).  `r = k/(d−1) = cellR`, `c = k%(d−1) = cellC`. -/
abbrev tbnaEdgeAdjTA (D : OddSurfaceDistance) : Term 3 .bool :=
  .and (.eqNat (.div k2P3 (dm1TA (dP3 D))) (.natLit 0))
    (.or (.or (.eqNat (.mod k2P3 (dm1TA (dP3 D))) (.mul (.natLit 2) (btB3 D)))
        (.eqNat (.mod k2P3 (dm1TA (dP3 D))) (.add (.mul (.natLit 2) (btB3 D)) (.natLit 1))))
      (.eqNat (.add (.mod k2P3 (dm1TA (dP3 D))) (.natLit 1)) (.mul (.natLit 2) (btB3 D))))

/-- Non-adjacency Bool: the negation of `tbnaEdgeAdjTA`. -/
abbrev tbnaNonAdjTA (D : OddSurfaceDistance) : Term 3 .bool :=
  .not (tbnaEdgeAdjTA D)

/-- Arity-2 edge-adjacency Bool (`k1 = var 1`, `k2 = var 0`), the pair-goal-level
form of `tbnaEdgeAdjTA`.  `(tbnaEdgeAdjTA2 D).weaken = tbnaEdgeAdjTA D` by `rfl`. -/
abbrev tbnaEdgeAdjTA2 (D : OddSurfaceDistance) : Term 2 .bool :=
  .and (.eqNat (.div k2P (dm1TA (dP2 D))) (.natLit 0))
    (.or (.or (.eqNat (.mod k2P (dm1TA (dP2 D))) (.mul (.natLit 2) (baseBTA (dP2 D) k1P)))
        (.eqNat (.mod k2P (dm1TA (dP2 D))) (.add (.mul (.natLit 2) (baseBTA (dP2 D) k1P)) (.natLit 1))))
      (.eqNat (.add (.mod k2P (dm1TA (dP2 D))) (.natLit 1)) (.mul (.natLit 2) (baseBTA (dP2 D) k1P))))

/-- Arity-2 non-adjacency Bool (pair-goal level). -/
abbrev tbnaNonAdjTA2 (D : OddSurfaceDistance) : Term 2 .bool :=
  .not (tbnaEdgeAdjTA2 D)

/-- **Core geometric contradiction** (pure `Nat`) for top–bulk.  A top boundary at
row `0`, cols `{2·t, 2·t+1}`, and a bulk cell `(cellR2, cellC2)` sharing a slot
`(R, C)`: both bands hit `(R, C)`, so `R = 0` (top row) and `R ∈ {cellR2, cellR2+1}`,
forcing `cellR2 = 0`; and `C ∈ {2·t, 2·t+1} ∩ {cellC2, cellC2+1}`, forcing
`cellC2 ∈ {2·t−1, 2·t, 2·t+1}`.  NON-ADJACENCY (`hnadj`) rules out exactly that. -/
private theorem tbnaCellContra
    {R C cellR2 cellC2 t : Nat}
    (hRrow0 : R = 0)
    (hCcol : C = 2 * t ∨ C = 2 * t + 1) (hbR : R = cellR2 ∨ R = cellR2 + 1)
    (hbC : C = cellC2 ∨ C = cellC2 + 1)
    (hnadj : cellR2 = 0 →
      (cellC2 ≠ 2 * t ∧ cellC2 ≠ 2 * t + 1) ∧ cellC2 + 1 ≠ 2 * t) : False := by
  obtain ⟨⟨hne0, hne1⟩, hne2⟩ := hnadj (by omega)
  rcases hCcol with h | h <;> rcases hbC with h' | h' <;> omega

/-- The top–bulk disjointness-pin body (arity 3, `k1 = var 2`, `k2 = var 1`,
`q = var 0`): under the top class context for `k1` (`¬bulk ∧ topClass`), `bulk(k2)`,
`kind(k2)=true` (Z-kind), NON-adjacency, and both bands firing at `q`, derive `⊥` —
the top boundary and the bulk plaquette cannot share a qubit. -/
abbrev tbnaPinBody (D : OddSurfaceDistance) : SFormula 3 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b false))
    (.imp (.eqBool (SC.closed (topClassGuardTA (dP3 D) k1P3)) (SC.b true))
      (.imp (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b true))
        (.imp (.eqBool (SC.closed (baseKindGuardTA (dP3 D) k2P3)) (SC.b true))
          (.imp (.eqBool (SC.closed (topBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true))
            (.imp (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))
              (.imp (.eqBool (SC.closed (tbnaNonAdjTA D)) (SC.b true))
                .bot))))))

abbrev tbnaPinF (D : OddSurfaceDistance) : SFormula 2 :=
  .allNatLt (nP2 D) (tbnaPinBody D)

/-- Top–Bulk disjointness pin pack: a non-adjacent top boundary and bulk plaquette
share no qubit.  `arithBool`; the eval-cert unfolds the top band to
`suppMem_top_prop`'s `(row,col)` RHS and the bulk band to `suppMem_bulk_prop`'s, then
the geometric core lemma `tbnaCellContra` (non-adjacency) refutes a common qubit. -/
def tbnaPinPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (tbnaPinF D) := by
  refine PureFamilyDerivA.allNatLtIntro _ ?_
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd3 : D.distance = 2 * D.index + 3 := rfl
  simp only [tbnaNonAdjTA, tbnaEdgeAdjTA, btB3, bulkGuardTA, topClassGuardTA, baseKindGuardTA,
    topBandGuardTA, baseBulkBandGuardTA, baseBTA, baseHalfTA, bulkCountTA, dm1TA, band3, orEqSucc,
    dP3, dP2, k1P3, k2P3, qP3, SFormula.eval, SC.closed, SC.b, STerm.eval, Term.eval, Term.lift,
    bind, Option.bind]
  set q := rho ⟨0, by decide⟩ with hq'
  set k2 := rho ⟨1, by decide⟩ with hk2'
  set k1 := rho ⟨2, by decide⟩ with hk1'
  set d := D.distance with hdd
  have hdge : 3 ≤ d := by omega
  have hdpos : 0 < d := by omega
  by_cases hbulk1 : k1 < (d - 1) * (d - 1)
  · -- bulk(k1) true → antecedent `bulk(k1) = false` false → vacuous.
    have hb : decide (decide (k1 < (d - 1) * (d - 1)) = false) = false := by
      rw [decide_eq_false_iff_not]; simp [hbulk1]
    simp only [hb, Bool.false_eq_true, if_false, reduceIte]
  · by_cases htop1 : k1 - (d - 1) * (d - 1) < (d - 1) / 2
    · have hbf : decide (decide (k1 < (d - 1) * (d - 1)) = false) = true := by
        rw [decide_eq_true_eq]; simp [hbulk1]
      have htf : decide (decide (k1 - (d - 1) * (d - 1) < (d - 1) / 2) = true) = true := by
        rw [decide_eq_true_eq]; simp [htop1]
      by_cases hbulk2 : k2 < (d - 1) * (d - 1)
      · have hb2t : decide (decide (k2 < (d - 1) * (d - 1)) = true) = true := by
          rw [decide_eq_true_eq]; simp [hbulk2]
        by_cases hk2kind : (k2 / (d - 1) + k2 % (d - 1)) % 2 = 0
        · have hk2t : decide (decide ((k2 / (d - 1) + k2 % (d - 1)) % 2 = 0) = true) = true := by
            rw [decide_eq_true_eq]; simp [hk2kind]
          simp only [hbf, htf, hb2t, hk2t, if_true]
          set t := k1 - (d - 1) * (d - 1) with ht
          set r2 := k2 / (d - 1) with hr2
          set c2 := k2 % (d - 1) with hc2
          -- Collapse the `Option.bind` chain into a closed `Prop` over
          -- `q/d, q%d, t, r2, c2`.
          simp only [← apply_ite Option.some, Option.some.injEq, Bool.if_true_left,
            Bool.if_true_right, Bool.if_false_right,
            Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, Bool.not_eq_false,
            decide_eq_true_eq, decide_eq_false_iff_not]
          -- Refute the only `.bot`-reaching branch (both bands fire, not adjacent).
          by_contra hcon
          push_neg at hcon
          obtain ⟨⟨_, hb1r, hb1c⟩, ⟨hb2r, hb2c, _⟩, hnadj, _⟩ := hcon
          exact tbnaCellContra hb1r hb1c hb2r hb2c hnadj
        · have hk2f : decide (decide ((k2 / (d - 1) + k2 % (d - 1)) % 2 = 0) = true) = false := by
            rw [decide_eq_false_iff_not]; simp [hk2kind]
          simp only [hbf, htf, hb2t, hk2f, Bool.false_eq_true, if_false, reduceIte]
      · have hb2f : decide (decide (k2 < (d - 1) * (d - 1)) = true) = false := by
          rw [decide_eq_false_iff_not]; simp [hbulk2]
        simp only [hbf, htf, hb2f, Bool.false_eq_true, if_false, reduceIte]
    · have hbf : decide (decide (k1 < (d - 1) * (d - 1)) = false) = true := by
        rw [decide_eq_true_eq]; simp [hbulk1]
      have htf : decide (decide (k1 - (d - 1) * (d - 1) < (d - 1) / 2) = true) = false := by
        rw [decide_eq_false_iff_not]; simp [htop1]
      simp only [hbf, htf, Bool.false_eq_true, if_false, reduceIte]

/-- Extract the top–bulk disjointness-pin `⊥` at `boundNat`: under the class context
and NON-adjacency, the top band and bulk band cannot both fire. -/
def tbnaPinAt {Δ : List (SFormula 3)} (D : OddSurfaceDistance)
    (hW : SFormula.Deriv Δ (tbnaPinF D).weaken)
    (hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken))
    (hBulkF : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b false)))
    (hTopC : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA (dP3 D) k1P3)) (SC.b true)))
    (hBulkK2 : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b true)))
    (hKindK2 : SFormula.Deriv Δ (.eqBool (SC.closed (baseKindGuardTA (dP3 D) k2P3)) (SC.b true)))
    (hTopB : SFormula.Deriv Δ (.eqBool (SC.closed (topBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true)))
    (hBulkB : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true)))
    (hNonAdj : SFormula.Deriv Δ (.eqBool (SC.closed (tbnaNonAdjTA D)) (SC.b true))) :
    SFormula.Deriv Δ .bot := by
  have hElim := SFormula.Deriv.allNatLtElim (nP2 D).weaken
    ((tbnaPinBody D).lift 1) SFormula.boundNat hW hq
  have hBody := SFormula.Deriv.applyNatBoundNatBeta (tbnaPinBody D) hElim
  exact SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp
    (SFormula.Deriv.mp (SFormula.Deriv.mp hBody hBulkF) hTopC) hBulkK2) hKindK2)
      hTopB) hBulkB |>.mp hNonAdj

#print axioms tbnaCellContra
#print axioms tbnaPinPack
#print axioms tbnaPinAt

/-! ## Top–Bulk NON-ADJACENT closer (NON-OVERLAP routing path)

`pairCommuteTopBulkNonAdj` assembles the per-pair commutation goal for a NON-adjacent
top(X)–bulk(Z) pair via the non-overlap path `pairCommutePointwise`.  Row A (`k1`) is
X-type top boundary, row B (`k2`) is Z-kind bulk, and they are NOT edge-adjacent.
* `hAntiXZ` (both leaves genuinely fire): reverse-leaf the top band (`btTopBandFromX`)
  and the bulk band (`bbBulkBandFromZ`), then the disjointness pin `tbnaPinAt` yields
  `⊥` and `botElim` closes `lcGoalP D`;
* `hAntiZX` (k1-leaf = Z, impossible for an X-type row): vacuous via the type
  exclusion `typeExclF k1`, mirroring `twoAntiRestXZ`'s `(Z,X)` branch exactly. -/

/-- **Top–Bulk non-adjacent (non-overlap) closer.**  Row A is the X-type top-boundary
stabilizer, row B the Z-kind bulk plaquette, the two NOT edge-adjacent (`hNonAdj`).
They share no qubit, so the pair commutes.  Routed through the non-overlap path
`pairCommutePointwise`: the `(X,Z)` leaf-pair is closed by the disjointness pin
`tbnaPinAt` (→ `⊥`), the `(Z,X)` leaf-pair by the X-type exclusion `hExcl1`. -/
def pairCommuteTopBulkNonAdj {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hEntryA : SFormula.Deriv Γ (entryAQuant D)) (hEntryB : SFormula.Deriv Γ (entryBQuant D))
    (hk1X : SFormula.Deriv Γ (k1IsX D true))
    (hExcl1 : SFormula.Deriv Γ (typeExclF D k1P))
    (hbulkFk1 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false)))
    (htopCk1 : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b true)))
    (hBulkK2 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true)))
    (hKindK2 : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k2P)) (SC.b true)))
    (hNonAdj : SFormula.Deriv Γ (.eqBool (SC.closed (tbnaNonAdjTA2 D)) (SC.b true)))
    (hPin : SFormula.Deriv Γ (tbnaPinF D)) :
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
    have hBulkK2Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b true)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true)) hBulkK2))
    have hKindK2Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (baseKindGuardTA (dP3 D) k2P3)) (SC.b true)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (baseKindGuardTA (dP2 D) k2P)) (SC.b true)) hKindK2))
    have hNonAdjΔ : SFormula.Deriv Δ' (.eqBool (SC.closed (tbnaNonAdjTA D)) (SC.b true)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (tbnaNonAdjTA2 D)) (SC.b true)) hNonAdj))
    have hPinΔ : SFormula.Deriv Δ' (tbnaPinF D).weaken :=
      lift (cw1 (SFormula.Deriv.weakenFresh (A := tbnaPinF D) hPin))
    have hq : SFormula.Deriv Δ' (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken) :=
      lift (.hyp List.mem_cons_self)
    have hTopB := btTopBandFromX D hbulkFk1Δ htopCk1Δ hLeafA
    have hBulkB := bbBulkBandFromZ D hBulkK2Δ hLeafB
    have hBot := tbnaPinAt D hPinΔ hq hbulkFk1Δ htopCk1Δ hBulkK2Δ hKindK2Δ hTopB hBulkB hNonAdjΔ
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

#print axioms pairCommuteTopBulkNonAdj

/-! ## Bottom–Bulk NON-ADJACENT (non-overlap) different-type pair

MIRROR of `commBottomBulk` overlap, NON-overlap variant.  Row A (`k1`) is an X-type
BOTTOM-boundary stabilizer, row B (`k2`) a Z-kind BULK plaquette, and the two are NOT
edge-adjacent.  A non-adjacent bottom boundary and bulk plaquette share NO qubit, so
the `(X,Z)`/`(Z,X)` leaf-pairs in the pointwise dispatcher never both fire — the
genuine `(X,Z)` branch is closed by a DISJOINTNESS PIN (the bottom band and the bulk
band can never both fire at one qubit), and the `(Z,X)` branch is vacuous via the
X-type exclusion.

The bottom boundary `k1` occupies row `d−1`, cols `{2·botIdx+1, 2·botIdx+2}`
(`botIdx = (k1−bulkCount) − 3·half`, `half = (d−1)/2`).  The bulk plaquette `k2`
shares a qubit with it ONLY when its row band `{cellR k2, cellR k2+1}` meets row `d−1`
— and since a valid bulk cell has `cellR k2 ≤ d−2`, this forces `cellR k2 + 1 = d−1`
(i.e. `cellR k2 = d−2`) — AND its col band `{cellC k2, cellC k2+1}` meets
`{2·botIdx+1, 2·botIdx+2}`, i.e. `cellC k2 ∈ {2·botIdx, 2·botIdx+1, 2·botIdx+2}`.
NON-ADJACENCY is the negation of exactly that condition. -/

/-- Edge-adjacency of a bottom-boundary row `k1` and a bulk cell `k2` (arity 3,
`k1 = var 2`, `k2 = var 1`): the bulk's row band meets the bottom strip's row `d−1`
via `cellR k2 + 1 = d−1`, and the bulk col band meets the bottom strip's cols
`{2·botIdx+1, 2·botIdx+2}` (`botIdx = bbB3`), i.e.
`cellC k2 ∈ {2·botIdx, 2·botIdx+1, 2·botIdx+2}`.  `r = k/(d−1) = cellR`,
`c = k%(d−1) = cellC`. -/
abbrev btbnaEdgeAdjTA (D : OddSurfaceDistance) : Term 3 .bool :=
  .and (.eqNat (.add (.div k2P3 (dm1TA (dP3 D))) (.natLit 1)) (dm1TA (dP3 D)))
    (.or (.or (.eqNat (.mod k2P3 (dm1TA (dP3 D))) (.mul (.natLit 2) (bbB3 D)))
        (.eqNat (.mod k2P3 (dm1TA (dP3 D))) (.add (.mul (.natLit 2) (bbB3 D)) (.natLit 1))))
      (.eqNat (.mod k2P3 (dm1TA (dP3 D))) (.add (.mul (.natLit 2) (bbB3 D)) (.natLit 2))))

/-- Non-adjacency Bool: the negation of `btbnaEdgeAdjTA`. -/
abbrev btbnaNonAdjTA (D : OddSurfaceDistance) : Term 3 .bool :=
  .not (btbnaEdgeAdjTA D)

/-- Arity-2 edge-adjacency Bool (`k1 = var 1`, `k2 = var 0`), the pair-goal-level
form of `btbnaEdgeAdjTA`.  `(btbnaEdgeAdjTA2 D).weaken = btbnaEdgeAdjTA D` by `rfl`. -/
abbrev btbnaEdgeAdjTA2 (D : OddSurfaceDistance) : Term 2 .bool :=
  .and (.eqNat (.add (.div k2P (dm1TA (dP2 D))) (.natLit 1)) (dm1TA (dP2 D)))
    (.or (.or (.eqNat (.mod k2P (dm1TA (dP2 D))) (.mul (.natLit 2) (bbB D)))
        (.eqNat (.mod k2P (dm1TA (dP2 D))) (.add (.mul (.natLit 2) (bbB D)) (.natLit 1))))
      (.eqNat (.mod k2P (dm1TA (dP2 D))) (.add (.mul (.natLit 2) (bbB D)) (.natLit 2))))

/-- Arity-2 non-adjacency Bool (pair-goal level). -/
abbrev btbnaNonAdjTA2 (D : OddSurfaceDistance) : Term 2 .bool :=
  .not (btbnaEdgeAdjTA2 D)

/-- **Core geometric contradiction** (pure `Nat`) for bottom–bulk.  A bottom boundary
at row `d−1`, cols `{2·b+1, 2·b+2}`, and a bulk cell `(cellR2, cellC2)` with
`cellR2 < d−1` (valid bulk row), sharing a slot `(R, C)`: both bands hit `(R, C)`, so
`R = d−1` (bottom row) and `R ∈ {cellR2, cellR2+1}`; since `cellR2 < d−1`, this forces
`cellR2 + 1 = d−1`.  And `C ∈ {2·b+1, 2·b+2} ∩ {cellC2, cellC2+1}`, forcing
`cellC2 ∈ {2·b, 2·b+1, 2·b+2}`.  NON-ADJACENCY (`hnadj`) rules out exactly that. -/
private theorem btbnaCellContra
    {R C cellR2 cellC2 b d : Nat}
    (hr2lt : cellR2 < d - 1)
    (hRrow : R = d - 1)
    (hCcol : C = 2 * b + 1 ∨ C = 2 * b + 2) (hbR : R = cellR2 ∨ R = cellR2 + 1)
    (hbC : C = cellC2 ∨ C = cellC2 + 1)
    (hnadj : cellR2 + 1 = d - 1 →
      (cellC2 ≠ 2 * b ∧ cellC2 ≠ 2 * b + 1) ∧ cellC2 ≠ 2 * b + 2) : False := by
  obtain ⟨⟨hne0, hne1⟩, hne2⟩ := hnadj (by omega)
  rcases hCcol with h | h <;> rcases hbC with h' | h' <;> omega

/-- The bottom–bulk disjointness-pin body (arity 3, `k1 = var 2`, `k2 = var 1`,
`q = var 0`): under the bottom class context for `k1` (`¬bulk ∧ ¬top ∧ ¬right ∧
¬left`), `bulk(k2)`, `kind(k2)=true` (Z-kind), NON-adjacency, and both bands firing at
`q`, derive `⊥` — the bottom boundary and the bulk plaquette cannot share a qubit. -/
abbrev btbnaPinBody (D : OddSurfaceDistance) : SFormula 3 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b false))
    (.imp (.eqBool (SC.closed (topClassGuardTA (dP3 D) k1P3)) (SC.b false))
      (.imp (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k1P3)) (SC.b false))
        (.imp (.eqBool (SC.closed (leftClassGuardTA (dP3 D) k1P3)) (SC.b false))
          (.imp (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b true))
            (.imp (.eqBool (SC.closed (baseKindGuardTA (dP3 D) k2P3)) (SC.b true))
              (.imp (.eqBool (SC.closed (bottomBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true))
                (.imp (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))
                  (.imp (.eqBool (SC.closed (btbnaNonAdjTA D)) (SC.b true))
                    .bot))))))))

abbrev btbnaPinF (D : OddSurfaceDistance) : SFormula 2 :=
  .allNatLt (nP2 D) (btbnaPinBody D)

/-- Bottom–Bulk disjointness pin pack: a non-adjacent bottom boundary and bulk
plaquette share no qubit.  `arithBool`; the eval-cert unfolds the bottom band to
`suppMem_bottom_prop`'s `(row,col)` RHS and the bulk band to `suppMem_bulk_prop`'s,
then the geometric core lemma `btbnaCellContra` (non-adjacency) refutes a common
qubit. -/
def btbnaPinPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (btbnaPinF D) := by
  refine PureFamilyDerivA.allNatLtIntro _ ?_
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd3 : D.distance = 2 * D.index + 3 := rfl
  simp only [btbnaNonAdjTA, btbnaEdgeAdjTA, bbB3, bulkGuardTA, topClassGuardTA, rightClassGuardTA,
    leftClassGuardTA, baseKindGuardTA, bottomBandGuardTA, baseBulkBandGuardTA, baseBTA, baseHalfTA,
    bulkCountTA, dm1TA, band3, orEqSucc, orEqPair, dP3, dP2, k1P3, k2P3, qP3, SFormula.eval,
    SC.closed, SC.b, STerm.eval, Term.eval, Term.lift, bind, Option.bind]
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
      have htf : decide (decide (k1 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = false := by
        rw [decide_eq_false_iff_not]; simp [htop1]
      simp only [hbf, htf, Bool.false_eq_true, if_false, reduceIte]
    · by_cases hright1 : k1 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)
      · have hbf : decide (decide (k1 < (d - 1) * (d - 1)) = false) = true := by
          rw [decide_eq_true_eq]; simp [hbulk1]
        have htf : decide (decide (k1 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
          rw [decide_eq_true_eq]; simp [htop1]
        have hrf : decide (decide (k1 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = false := by
          rw [decide_eq_false_iff_not]; simp [hright1]
        simp only [hbf, htf, hrf, Bool.false_eq_true, if_false, reduceIte]
      · by_cases hleft1 : k1 - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)
        · have hbf : decide (decide (k1 < (d - 1) * (d - 1)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hbulk1]
          have htf : decide (decide (k1 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
            rw [decide_eq_true_eq]; simp [htop1]
          have hrf : decide (decide (k1 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hright1]
          have hlf : decide (decide (k1 - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)) = false) = false := by
            rw [decide_eq_false_iff_not]; simp [hleft1]
          simp only [hbf, htf, hrf, hlf, Bool.false_eq_true, if_false, reduceIte]
        · have hbf : decide (decide (k1 < (d - 1) * (d - 1)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hbulk1]
          have htf : decide (decide (k1 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
            rw [decide_eq_true_eq]; simp [htop1]
          have hrf : decide (decide (k1 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hright1]
          have hlf : decide (decide (k1 - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hleft1]
          by_cases hbulk2 : k2 < (d - 1) * (d - 1)
          · have hb2t : decide (decide (k2 < (d - 1) * (d - 1)) = true) = true := by
              rw [decide_eq_true_eq]; simp [hbulk2]
            by_cases hk2kind : (k2 / (d - 1) + k2 % (d - 1)) % 2 = 0
            · have hk2t : decide (decide ((k2 / (d - 1) + k2 % (d - 1)) % 2 = 0) = true) = true := by
                rw [decide_eq_true_eq]; simp [hk2kind]
              simp only [hbf, htf, hrf, hlf, hb2t, hk2t, if_true]
              set b := k1 - (d - 1) * (d - 1) - 3 * ((d - 1) / 2) with hb
              set r2 := k2 / (d - 1) with hr2
              set c2 := k2 % (d - 1) with hc2
              -- The bulk row is `< d-1` (from `k2 < (d-1)²`).
              have hr2lt : r2 < d - 1 := by
                rw [hr2]; exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm] at hbulk2; exact hbulk2)
              -- Collapse the `Option.bind` chain into a closed `Prop`.
              simp only [← apply_ite Option.some, Option.some.injEq, Bool.if_true_left,
                Bool.if_true_right, Bool.if_false_right,
                Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, Bool.not_eq_false,
                decide_eq_true_eq, decide_eq_false_iff_not]
              -- Refute the only `.bot`-reaching branch (both bands fire, not adjacent).
              by_contra hcon
              push_neg at hcon
              obtain ⟨⟨hb1r, hb1c⟩, ⟨hb2r, hb2c, _⟩, hnadj, _⟩ := hcon
              exact btbnaCellContra hr2lt hb1r hb1c hb2r hb2c hnadj
            · have hk2f : decide (decide ((k2 / (d - 1) + k2 % (d - 1)) % 2 = 0) = true) = false := by
                rw [decide_eq_false_iff_not]; simp [hk2kind]
              simp only [hbf, htf, hrf, hlf, hb2t, hk2f, Bool.false_eq_true, if_false, reduceIte]
          · have hb2f : decide (decide (k2 < (d - 1) * (d - 1)) = true) = false := by
              rw [decide_eq_false_iff_not]; simp [hbulk2]
            simp only [hbf, htf, hrf, hlf, hb2f, Bool.false_eq_true, if_false, reduceIte]

/-- Extract the bottom–bulk disjointness-pin `⊥` at `boundNat`: under the class context
and NON-adjacency, the bottom band and bulk band cannot both fire. -/
def btbnaPinAt {Δ : List (SFormula 3)} (D : OddSurfaceDistance)
    (hW : SFormula.Deriv Δ (btbnaPinF D).weaken)
    (hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken))
    (hBulkF : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b false)))
    (hTopF : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA (dP3 D) k1P3)) (SC.b false)))
    (hRightF : SFormula.Deriv Δ (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k1P3)) (SC.b false)))
    (hLeftF : SFormula.Deriv Δ (.eqBool (SC.closed (leftClassGuardTA (dP3 D) k1P3)) (SC.b false)))
    (hBulkK2 : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b true)))
    (hKindK2 : SFormula.Deriv Δ (.eqBool (SC.closed (baseKindGuardTA (dP3 D) k2P3)) (SC.b true)))
    (hBotB : SFormula.Deriv Δ (.eqBool (SC.closed (bottomBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true)))
    (hBulkB : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true)))
    (hNonAdj : SFormula.Deriv Δ (.eqBool (SC.closed (btbnaNonAdjTA D)) (SC.b true))) :
    SFormula.Deriv Δ .bot := by
  have hElim := SFormula.Deriv.allNatLtElim (nP2 D).weaken
    ((btbnaPinBody D).lift 1) SFormula.boundNat hW hq
  have hBody := SFormula.Deriv.applyNatBoundNatBeta (btbnaPinBody D) hElim
  exact SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp
    (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp hBody hBulkF)
      hTopF) hRightF) hLeftF) hBulkK2) hKindK2) hBotB) hBulkB |>.mp hNonAdj

#print axioms btbnaCellContra
#print axioms btbnaPinPack
#print axioms btbnaPinAt

/-! ## Bottom–Bulk NON-ADJACENT closer (NON-OVERLAP routing path)

`pairCommuteBottomBulkNonAdj` assembles the per-pair commutation goal for a
NON-adjacent bottom(X)–bulk(Z) pair via the non-overlap path `pairCommutePointwise`.
Row A (`k1`) is X-type bottom boundary, row B (`k2`) is Z-kind bulk, and they are NOT
edge-adjacent.
* `hAntiXZ` (both leaves genuinely fire): reverse-leaf the bottom band
  (`bbBottomBandFromX`) and the bulk band (`bbBulkBandFromZ`), then the disjointness
  pin `btbnaPinAt` yields `⊥` and `botElim` closes `lcGoalP D`;
* `hAntiZX` (k1-leaf = Z, impossible for an X-type row): vacuous via the type
  exclusion `typeExclF k1`, mirroring `twoAntiRestXZ`'s `(Z,X)` branch exactly. -/

/-- **Bottom–Bulk non-adjacent (non-overlap) closer.**  Row A is the X-type
bottom-boundary stabilizer, row B the Z-kind bulk plaquette, the two NOT edge-adjacent
(`hNonAdj`).  They share no qubit, so the pair commutes.  Routed through the
non-overlap path `pairCommutePointwise`: the `(X,Z)` leaf-pair is closed by the
disjointness pin `btbnaPinAt` (→ `⊥`), the `(Z,X)` leaf-pair by the X-type exclusion
`hExcl1`. -/
def pairCommuteBottomBulkNonAdj {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hEntryA : SFormula.Deriv Γ (entryAQuant D)) (hEntryB : SFormula.Deriv Γ (entryBQuant D))
    (hk1X : SFormula.Deriv Γ (k1IsX D true))
    (hExcl1 : SFormula.Deriv Γ (typeExclF D k1P))
    (hbulkFk1 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false)))
    (htopFk1 : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false)))
    (hrightFk1 : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k1P)) (SC.b false)))
    (hleftFk1 : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k1P)) (SC.b false)))
    (hBulkK2 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true)))
    (hKindK2 : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k2P)) (SC.b true)))
    (hNonAdj : SFormula.Deriv Γ (.eqBool (SC.closed (btbnaNonAdjTA2 D)) (SC.b true)))
    (hPin : SFormula.Deriv Γ (btbnaPinF D)) :
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
    have hBulkK2Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b true)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true)) hBulkK2))
    have hKindK2Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (baseKindGuardTA (dP3 D) k2P3)) (SC.b true)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (baseKindGuardTA (dP2 D) k2P)) (SC.b true)) hKindK2))
    have hNonAdjΔ : SFormula.Deriv Δ' (.eqBool (SC.closed (btbnaNonAdjTA D)) (SC.b true)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (btbnaNonAdjTA2 D)) (SC.b true)) hNonAdj))
    have hPinΔ : SFormula.Deriv Δ' (btbnaPinF D).weaken :=
      lift (cw1 (SFormula.Deriv.weakenFresh (A := btbnaPinF D) hPin))
    have hq : SFormula.Deriv Δ' (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken) :=
      lift (.hyp List.mem_cons_self)
    have hBotB := bbBottomBandFromX D hbulkFk1Δ htopFk1Δ hrightFk1Δ hleftFk1Δ hLeafA
    have hBulkB := bbBulkBandFromZ D hBulkK2Δ hLeafB
    have hBot := btbnaPinAt D hPinΔ hq hbulkFk1Δ htopFk1Δ hrightFk1Δ hleftFk1Δ hBulkK2Δ hKindK2Δ
      hBotB hBulkB hNonAdjΔ
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

#print axioms pairCommuteBottomBulkNonAdj

end QHL.CodeLang.Surface.Verify
