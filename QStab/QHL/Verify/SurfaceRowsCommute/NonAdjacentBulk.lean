import QStab.QHL.Verify.SurfaceRowsCommute.BulkBulkLU

/-!
# Rows-commute (pairwise generated-row commutation) — NonAdjacentBulk

The bulk–bulk non-adjacent (non-overlap) pair and closer, and the bulk–right / bulk–left
non-adjacent pairs and closers.
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface

set_option maxRecDepth 65536
set_option linter.unusedVariables false

/-! ## Bulk–Bulk NON-ADJACENT (non-overlap) different-kind pair

Validation spike for the NON-OVERLAP routing path.  Row A (`k1`) is an X-kind bulk
plaquette, row B (`k2`) a Z-kind bulk plaquette, and the two are NOT edge-adjacent.
Two non-adjacent bulk plaquettes of opposite kind share NO qubit, so the
`(X,Z)`/`(Z,X)` leaf-pairs in the pointwise dispatcher never both fire — the genuine
`(X,Z)` branch is closed by a DISJOINTNESS PIN (the two bulk bands can never both
fire at one qubit), and the `(Z,X)` branch is vacuous via the type-exclusion (an
X-type row never produces a `Z` leaf).

The non-adjacency is supplied as the Bool `bbnaNonAdjTA = ¬ edge-adjacent`, where
edge-adjacency is `(r1 = r2 ∧ |c1 − c2| = 1) ∨ (c1 = c2 ∧ |r1 − r2| = 1)` with
`r = k/(d−1) = cellR`, `c = k%(d−1) = cellC`.  Combined with the two band-fired
facts (each gives `q/d ∈ {r,r+1}` and `q%d ∈ {c,c+1}`, i.e. `suppMem_bulk_prop`'s
RHS) and the different-kind parity (`kind(k1)=false`, `kind(k2)=true`, i.e.
`(r1+c1)` and `(r2+c2)` opposite parity), `omega` refutes a shared qubit. -/

/-- Edge-adjacency of two bulk cells `k1`, `k2` (arity 3): same row & adjacent
column, or same column & adjacent row.  `r = k/(d−1)`, `c = k%(d−1)`. -/
abbrev bbnaEdgeAdjTA (D : OddSurfaceDistance) : Term 3 .bool :=
  .or
    (.and (.eqNat (.div k1P3 (dm1TA (dP3 D))) (.div k2P3 (dm1TA (dP3 D))))
      (.or (.eqNat (.mod k1P3 (dm1TA (dP3 D))) (.add (.mod k2P3 (dm1TA (dP3 D))) (.natLit 1)))
        (.eqNat (.mod k2P3 (dm1TA (dP3 D))) (.add (.mod k1P3 (dm1TA (dP3 D))) (.natLit 1)))))
    (.and (.eqNat (.mod k1P3 (dm1TA (dP3 D))) (.mod k2P3 (dm1TA (dP3 D))))
      (.or (.eqNat (.div k1P3 (dm1TA (dP3 D))) (.add (.div k2P3 (dm1TA (dP3 D))) (.natLit 1)))
        (.eqNat (.div k2P3 (dm1TA (dP3 D))) (.add (.div k1P3 (dm1TA (dP3 D))) (.natLit 1)))))

/-- Non-adjacency Bool: the negation of `bbnaEdgeAdjTA`. -/
abbrev bbnaNonAdjTA (D : OddSurfaceDistance) : Term 3 .bool :=
  .not (bbnaEdgeAdjTA D)

/-- Arity-2 edge-adjacency Bool (`k1 = var 1`, `k2 = var 0`), the pair-goal-level
form of `bbnaEdgeAdjTA`.  `(bbnaEdgeAdjTA2 D).weaken = bbnaEdgeAdjTA D` by `rfl`. -/
abbrev bbnaEdgeAdjTA2 (D : OddSurfaceDistance) : Term 2 .bool :=
  .or
    (.and (.eqNat (.div k1P (dm1TA (dP2 D))) (.div k2P (dm1TA (dP2 D))))
      (.or (.eqNat (.mod k1P (dm1TA (dP2 D))) (.add (.mod k2P (dm1TA (dP2 D))) (.natLit 1)))
        (.eqNat (.mod k2P (dm1TA (dP2 D))) (.add (.mod k1P (dm1TA (dP2 D))) (.natLit 1)))))
    (.and (.eqNat (.mod k1P (dm1TA (dP2 D))) (.mod k2P (dm1TA (dP2 D))))
      (.or (.eqNat (.div k1P (dm1TA (dP2 D))) (.add (.div k2P (dm1TA (dP2 D))) (.natLit 1)))
        (.eqNat (.div k2P (dm1TA (dP2 D))) (.add (.div k1P (dm1TA (dP2 D))) (.natLit 1)))))

/-- Arity-2 non-adjacency Bool (pair-goal level). -/
abbrev bbnaNonAdjTA2 (D : OddSurfaceDistance) : Term 2 .bool :=
  .not (bbnaEdgeAdjTA2 D)

/-- The disjointness-pin body (arity 3, `k1 = var 2`, `k2 = var 1`, `q = var 0`):
under `bulk(k1)`, `bulk(k2)`, `kind(k1)=false` (X-kind), `kind(k2)=true` (Z-kind),
NON-adjacency, and both bulk bands firing at `q`, derive `⊥` — the two plaquettes
cannot share a qubit. -/
abbrev bbnaPinBody (D : OddSurfaceDistance) : SFormula 3 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b true))
    (.imp (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b true))
      (.imp (.eqBool (SC.closed (baseKindGuardTA (dP3 D) k1P3)) (SC.b false))
        (.imp (.eqBool (SC.closed (baseKindGuardTA (dP3 D) k2P3)) (SC.b true))
          (.imp (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true))
            (.imp (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))
              (.imp (.eqBool (SC.closed (bbnaNonAdjTA D)) (SC.b true))
                .bot))))))

abbrev bbnaPinF (D : OddSurfaceDistance) : SFormula 2 :=
  .allNatLt (nP2 D) (bbnaPinBody D)

/-- **Core geometric contradiction** (pure `Nat`).  Two bulk cells `(r1,c1)`,
`(r2,c2)` of OPPOSITE kind (`hsame` rules out the same cell, `hdiag` the diagonal —
both encode the parity difference) that are NOT edge-adjacent (`hedgeRow`,
`hedgeCol`) cannot have a shared qubit: a common plaquette-band hit forces row/col
membership `R ∈ {r1,r1+1}∩{r2,r2+1}`, `C ∈ {c1,c1+1}∩{c2,c2+1}`, hence row/col
distance ≤ 1 — i.e. same cell, edge-adjacent, or diagonal, all excluded. -/
private theorem bbnaCellContra
    {r1 c1 r2 c2 R C : Nat}
    (hedgeRow : r1 = r2 → c1 ≠ c2 + 1 ∧ c2 ≠ c1 + 1)
    (hedgeCol : c1 = c2 → r1 ≠ r2 + 1 ∧ r2 ≠ r1 + 1)
    (hsame : ¬(r1 = r2 ∧ c1 = c2))
    (hdiag : ¬((r1 = r2 + 1 ∨ r2 = r1 + 1) ∧ (c1 = c2 + 1 ∨ c2 = c1 + 1)))
    (hb1r : R = r1 ∨ R = r1 + 1) (hb1c : C = c1 ∨ C = c1 + 1)
    (hb2r : R = r2 ∨ R = r2 + 1) (hb2c : C = c2 ∨ C = c2 + 1) : False := by
  rcases hb1r with hb1r | hb1r <;> rcases hb1c with hb1c | hb1c <;>
    rcases hb2r with hb2r | hb2r <;> rcases hb2c with hb2c | hb2c <;> omega

/-- Disjointness pin pack: two non-adjacent opposite-kind bulk plaquettes share no
qubit.  `arithBool`; the eval-cert unfolds both bulk bands to `suppMem_bulk_prop`'s
`(row,col)` RHS, then the geometric core lemma `bbnaCellContra` (different-kind
parity + non-adjacency) refutes a common qubit. -/
def bbnaPinPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (bbnaPinF D) := by
  refine PureFamilyDerivA.allNatLtIntro _ ?_
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd3 : D.distance = 2 * D.index + 3 := rfl
  simp only [bbnaPinBody, bbnaNonAdjTA, bbnaEdgeAdjTA, bulkGuardTA, baseKindGuardTA,
    baseBulkBandGuardTA, bulkCountTA, dm1TA, band3, orEqSucc, dP3, dP2, k1P3, k2P3, qP3,
    SFormula.eval, SFormula.boundNat, SC.closed, SC.b, STerm.eval, Term.eval, Term.lift,
    bind, Option.bind]
  set q := rho ⟨0, by decide⟩ with hq'
  set k2 := rho ⟨1, by decide⟩ with hk2'
  set k1 := rho ⟨2, by decide⟩ with hk1'
  set d := D.distance with hdd
  have hdge : 3 ≤ d := by omega
  have hdpos : 0 < d := by omega
  by_cases hbulk1 : k1 < (d - 1) * (d - 1)
  · have hb1t : decide (decide (k1 < (d - 1) * (d - 1)) = true) = true := by
      rw [decide_eq_true_eq]; simp [hbulk1]
    by_cases hbulk2 : k2 < (d - 1) * (d - 1)
    · have hb2t : decide (decide (k2 < (d - 1) * (d - 1)) = true) = true := by
        rw [decide_eq_true_eq]; simp [hbulk2]
      simp only [hb1t, hb2t, if_true]
      set r1 := k1 / (d - 1) with hr1
      set c1 := k1 % (d - 1) with hc1
      set r2 := k2 / (d - 1) with hr2
      set c2 := k2 % (d - 1) with hc2
      -- Different-kind: case on the two kind guards.
      by_cases hk1kind : (r1 + c1) % 2 = 0
      · -- kind(k1)=true ⟹ antecedent `kind(k1)=false` is false ⟹ vacuous.
        have hk1f : decide (decide ((r1 + c1) % 2 = 0) = false) = false := by
          rw [decide_eq_false_iff_not]; simp [hk1kind]
        simp only [hk1f, Bool.false_eq_true, if_false, reduceIte]
      · have hk1f : decide (decide ((r1 + c1) % 2 = 0) = false) = true := by
          rw [decide_eq_true_eq]; simp [hk1kind]
        by_cases hk2kind : (r2 + c2) % 2 = 0
        · have hk2t : decide (decide ((r2 + c2) % 2 = 0) = true) = true := by
            rw [decide_eq_true_eq]; simp [hk2kind]
          simp only [hk1f, hk2t, if_true]
          -- Collapse the `Option.bind` chain (every leaf is `some _`) into one closed
          -- Boolean expression over `r1,c1,r2,c2,q/d,q%d`.  After decoding each `decide`
          -- to a `Prop`, the goal is `¬band1 ∨ ¬band2 ∨ ¬(edge = false)`; `omega` refutes
          -- the only `.bot`-reaching branch (both bands fire AND not edge-adjacent):
          -- opposite-kind bulk cells (parity `hk1kind`/`hk2kind`) sharing a qubit must
          -- be edge-adjacent.
          simp only [← apply_ite Option.some, Option.some.injEq, Bool.if_true_left,
            Bool.if_false_left, Bool.if_true_right, Bool.if_false_right, Bool.and_true,
            Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, Bool.not_eq_false,
            decide_eq_true_eq, decide_eq_false_iff_not]
          -- The goal is now a closed `Prop`: `¬band1 ∨ ¬band2 ∨ edge-adjacent ∨ ⊥`.
          -- Free the `let`-bound cell coordinates and drop the `decide`-form / div
          -- defining noise, then refute the only `.bot`-reaching branch (both bands
          -- fire, not edge-adjacent).  We expose the four band disjunctions as concrete
          -- equalities so each of the 16 leaves is a contradiction by `omega`: two
          -- opposite-kind bulk cells (parity `hk1kind`/`hk2kind`) at row/col distance
          -- ≤ 1 are necessarily edge-adjacent (same cell / diagonal both have equal
          -- parity, which is excluded).
          -- The goal is now a closed `Prop`: `¬band1 ∨ ¬band2 ∨ edge-adjacent ∨ ⊥`.
          -- Refute the only `.bot`-reaching branch (both bands fire, not edge-adjacent).
          by_contra hcon
          push_neg at hcon
          obtain ⟨⟨hb1r, hb1c, _⟩, ⟨hb2r, hb2c, _⟩, hedge, _⟩ := hcon
          obtain ⟨hedgeRow, hedgeCol⟩ := hedge
          -- Opposite parity (`hk1kind` X-kind, `hk2kind` Z-kind) digested into the two
          -- non-edge sharing exclusions: SAME cell and DIAGONAL.
          have hsame : ¬(r1 = r2 ∧ c1 = c2) := by rintro ⟨hr, hc⟩; omega
          have hdiag : ¬((r1 = r2 + 1 ∨ r2 = r1 + 1) ∧ (c1 = c2 + 1 ∨ c2 = c1 + 1)) := by
            rintro ⟨hr, hc⟩; omega
          -- The band memberships pin `q/d ∈ {r1,r1+1}∩{r2,r2+1}`, `q%d ∈ {c1,c1+1}∩
          -- {c2,c2+1}`; the pure geometric core derives the contradiction.
          exact bbnaCellContra hedgeRow hedgeCol hsame hdiag hb1r hb1c hb2r hb2c
        · have hk2f : decide (decide ((r2 + c2) % 2 = 0) = true) = false := by
            rw [decide_eq_false_iff_not]; simp [hk2kind]
          simp only [hk1f, hk2f, Bool.false_eq_true, if_false, reduceIte]
    · have hb2f : decide (decide (k2 < (d - 1) * (d - 1)) = true) = false := by
        rw [decide_eq_false_iff_not]; simp [hbulk2]
      simp only [hb1t, hb2f, Bool.false_eq_true, if_false, reduceIte]
  · have hb1f : decide (decide (k1 < (d - 1) * (d - 1)) = true) = false := by
      rw [decide_eq_false_iff_not]; simp [hbulk1]
    simp only [hb1f, Bool.false_eq_true, if_false, reduceIte]

/-- Extract the disjointness-pin `⊥` at `boundNat`: under the class context, the two
non-adjacent opposite-kind bulk bands cannot both fire. -/
def bbnaPinAt {Δ : List (SFormula 3)} (D : OddSurfaceDistance)
    (hW : SFormula.Deriv Δ (bbnaPinF D).weaken)
    (hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken))
    (hBulkK1 : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b true)))
    (hBulkK2 : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b true)))
    (hKindK1 : SFormula.Deriv Δ (.eqBool (SC.closed (baseKindGuardTA (dP3 D) k1P3)) (SC.b false)))
    (hKindK2 : SFormula.Deriv Δ (.eqBool (SC.closed (baseKindGuardTA (dP3 D) k2P3)) (SC.b true)))
    (hNonAdj : SFormula.Deriv Δ (.eqBool (SC.closed (bbnaNonAdjTA D)) (SC.b true)))
    (hBandK1 : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true)))
    (hBandK2 : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))) :
    SFormula.Deriv Δ .bot := by
  have hElim := SFormula.Deriv.allNatLtElim (nP2 D).weaken
    ((bbnaPinBody D).lift 1) SFormula.boundNat hW hq
  have hBody := SFormula.Deriv.applyNatBoundNatBeta (bbnaPinBody D) hElim
  exact SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp
    (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp hBody hBulkK1) hBulkK2)
      hKindK1) hKindK2) hBandK1) hBandK2) hNonAdj

/-! ## Bulk–Bulk NON-ADJACENT closer (NON-OVERLAP routing path)

`pairCommuteBulkBulkNonAdj` assembles the per-pair commutation goal for a NON-adjacent
different-kind bulk pair via the non-overlap path `pairCommutePointwise`.  Row A
(`k1`) is X-kind bulk, row B (`k2`) is Z-kind bulk, and they are NOT edge-adjacent.
The two anti-handlers:
* `hAntiXZ` (both leaves genuinely fire): reverse-leaf BOTH bands (`bhBandK1FromX`,
  `bhBandK2FromZ`), then the disjointness pin `bbnaPinAt` yields `⊥` — the two
  non-adjacent opposite-kind bands cannot both fire at one qubit — and `botElim`
  closes `lcGoalP D`;
* `hAntiZX` (k1-leaf = Z, impossible for an X-type row): vacuous via the type
  exclusion `typeExclF k1`, mirroring `twoAntiRestXZ`'s `(Z,X)` branch exactly. -/

/-- **Bulk–Bulk non-adjacent (non-overlap) closer.**  Row A is the X-kind bulk
plaquette, row B the Z-kind bulk plaquette, the two NOT edge-adjacent (`hNonAdj`).
They share no qubit, so the pair commutes.  Routed through the non-overlap path
`pairCommutePointwise`: the `(X,Z)` leaf-pair is closed by the disjointness pin
`bbnaPinAt` (→ `⊥`), the `(Z,X)` leaf-pair by the X-type exclusion `hExcl1`. -/
def pairCommuteBulkBulkNonAdj {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hEntryA : SFormula.Deriv Γ (entryAQuant D)) (hEntryB : SFormula.Deriv Γ (entryBQuant D))
    (hk1X : SFormula.Deriv Γ (k1IsX D true))
    (hExcl1 : SFormula.Deriv Γ (typeExclF D k1P))
    (hBulkK1 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true)))
    (hKindK1 : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k1P)) (SC.b false)))
    (hBulkK2 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true)))
    (hKindK2 : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k2P)) (SC.b true)))
    (hNonAdj : SFormula.Deriv Γ (.eqBool (SC.closed (bbnaNonAdjTA2 D)) (SC.b true)))
    (hPin : SFormula.Deriv Γ (bbnaPinF D)) :
    SFormula.Deriv Γ (pairGoal D) := by
  refine pairCommutePointwise D hEntryA hEntryB ?hXZ ?hZX
  · -- (X, Z): both leaves genuinely fire; the disjointness pin forces ⊥.
    intro Δ' lift hLeafA hLeafB
    -- Lift the class facts and the pin into Δ'.
    have hBulkK1Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b true)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true)) hBulkK1))
    have hBulkK2Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b true)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true)) hBulkK2))
    have hKindK1Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (baseKindGuardTA (dP3 D) k1P3)) (SC.b false)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (baseKindGuardTA (dP2 D) k1P)) (SC.b false)) hKindK1))
    have hKindK2Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (baseKindGuardTA (dP3 D) k2P3)) (SC.b true)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (baseKindGuardTA (dP2 D) k2P)) (SC.b true)) hKindK2))
    have hNonAdjΔ : SFormula.Deriv Δ' (.eqBool (SC.closed (bbnaNonAdjTA D)) (SC.b true)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (bbnaNonAdjTA2 D)) (SC.b true)) hNonAdj))
    have hPinΔ : SFormula.Deriv Δ' (bbnaPinF D).weaken :=
      lift (cw1 (SFormula.Deriv.weakenFresh (A := bbnaPinF D) hPin))
    have hq : SFormula.Deriv Δ' (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken) :=
      lift (.hyp List.mem_cons_self)
    -- Reverse-leaf both bands, then the pin yields ⊥.
    have hBandK1 := bhBandK1FromX D hBulkK1Δ hLeafA
    have hBandK2 := bhBandK2FromZ D hBulkK2Δ hLeafB
    have hBot := bbnaPinAt D hPinΔ hq hBulkK1Δ hBulkK2Δ hKindK1Δ hKindK2Δ hNonAdjΔ hBandK1 hBandK2
    exact SFormula.Deriv.botElim hBot
  · -- (Z, X): A leaf = Z impossible since A is X-type → type-exclusion contradiction.
    --   Mirrors `twoAntiRestXZ`'s `(Z,X)` branch exactly (driven by `hk1X`/`hExcl1`).
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

#print axioms bbnaCellContra
#print axioms bbnaPinPack
#print axioms bbnaPinAt
#print axioms pairCommuteBulkBulkNonAdj

/-! ## Bulk–Right NON-ADJACENT (non-overlap) different-type pair

Row A (`k1`) is an X-kind bulk plaquette, row B (`k2`) a Z-type RIGHT-boundary
stabilizer, and the two are NOT edge-adjacent.  A non-adjacent bulk plaquette and a
right boundary share NO qubit, so the `(X,Z)`/`(Z,X)` leaf-pairs in the pointwise
dispatcher never both fire — the genuine `(X,Z)` branch is closed by a DISJOINTNESS
PIN (the bulk band and the right band can never both fire at one qubit), and the
`(Z,X)` branch is vacuous via the X-type exclusion.

The right boundary `k2` occupies column `d-1`, rows `{2·rightIdx, 2·rightIdx+1}`
(`rightIdx = (k2−bulkCount) − half`, `half = (d−1)/2`).  The bulk plaquette `k1`
shares a qubit with it ONLY when `cellC k1 = (d−1)−1` (its right column is `d−2`,
neighbouring column `d−1`) AND its row band `{cellR k1, cellR k1+1}` meets
`{2·rightIdx, 2·rightIdx+1}`, i.e. `cellR k1 ∈ {2·rightIdx−1, 2·rightIdx,
2·rightIdx+1}`.  NON-ADJACENCY is the negation of exactly that condition. -/

/-- Edge-adjacency of a bulk cell `k1` and a right-boundary row `k2` (arity 3,
`k1 = var 2`, `k2 = var 1`): the bulk's right column `cellC k1 = (d−1)−1` neighbours
column `d−1`, and the bulk row band meets the right strip's rows
`{2·rightIdx, 2·rightIdx+1}` (`rightIdx = brR3`).  `r = k/(d−1) = cellR`,
`c = k%(d−1) = cellC`. -/
abbrev brnaEdgeAdjTA (D : OddSurfaceDistance) : Term 3 .bool :=
  .and (.eqNat (.mod k1P3 (dm1TA (dP3 D))) (.sub (dm1TA (dP3 D)) (.natLit 1)))
    (.or (.or (.eqNat (.div k1P3 (dm1TA (dP3 D))) (.mul (.natLit 2) (brR3 D)))
        (.eqNat (.div k1P3 (dm1TA (dP3 D))) (.add (.mul (.natLit 2) (brR3 D)) (.natLit 1))))
      (.eqNat (.add (.div k1P3 (dm1TA (dP3 D))) (.natLit 1)) (.mul (.natLit 2) (brR3 D))))

/-- Non-adjacency Bool: the negation of `brnaEdgeAdjTA`. -/
abbrev brnaNonAdjTA (D : OddSurfaceDistance) : Term 3 .bool :=
  .not (brnaEdgeAdjTA D)

/-- Arity-2 edge-adjacency Bool (`k1 = var 1`, `k2 = var 0`), the pair-goal-level
form of `brnaEdgeAdjTA`.  `(brnaEdgeAdjTA2 D).weaken = brnaEdgeAdjTA D` by `rfl`. -/
abbrev brnaEdgeAdjTA2 (D : OddSurfaceDistance) : Term 2 .bool :=
  .and (.eqNat (.mod k1P (dm1TA (dP2 D))) (.sub (dm1TA (dP2 D)) (.natLit 1)))
    (.or (.or (.eqNat (.div k1P (dm1TA (dP2 D))) (.mul (.natLit 2) (brR D)))
        (.eqNat (.div k1P (dm1TA (dP2 D))) (.add (.mul (.natLit 2) (brR D)) (.natLit 1))))
      (.eqNat (.add (.div k1P (dm1TA (dP2 D))) (.natLit 1)) (.mul (.natLit 2) (brR D))))

/-- Arity-2 non-adjacency Bool (pair-goal level). -/
abbrev brnaNonAdjTA2 (D : OddSurfaceDistance) : Term 2 .bool :=
  .not (brnaEdgeAdjTA2 D)

/-- **Core geometric contradiction** (pure `Nat`) for bulk–right.  A bulk cell
`(cellR1, cellC1)` (`cellC1 < dm1`) and a right boundary at column `dm1`, rows
`{2·r, 2·r+1}`, sharing a slot `(R, C)`: both bands hit `(R, C)`, so `C = dm1`
(right col) and `C ∈ {cellC1, cellC1+1}`, forcing `cellC1 = dm1−1`; and
`R ∈ {2·r, 2·r+1} ∩ {cellR1, cellR1+1}`, forcing `cellR1 ∈ {2·r−1, 2·r, 2·r+1}`.
NON-ADJACENCY (`hnadj`) rules out exactly that. -/
private theorem brnaCellContra
    {dm1 R C cellR1 cellC1 r : Nat}
    (hc1lt : cellC1 < dm1) (hCcol : C = dm1)
    (hRrow : R = 2 * r ∨ R = 2 * r + 1) (hbR : R = cellR1 ∨ R = cellR1 + 1)
    (hbC : C = cellC1 ∨ C = cellC1 + 1)
    (hnadj : cellC1 = dm1 - 1 →
      (cellR1 ≠ 2 * r ∧ cellR1 ≠ 2 * r + 1) ∧ cellR1 + 1 ≠ 2 * r) : False := by
  obtain ⟨⟨hne0, hne1⟩, hne2⟩ := hnadj (by omega)
  rcases hRrow with h | h <;> rcases hbR with h' | h' <;> omega

/-- The bulk–right disjointness-pin body (arity 3, `k1 = var 2`, `k2 = var 1`,
`q = var 0`): under `bulk(k1)`, `kind(k1)=false` (X-kind), the right class context
for `k2` (`¬bulk ∧ ¬top ∧ right`), NON-adjacency, and both bands firing at `q`,
derive `⊥` — the bulk plaquette and the right boundary cannot share a qubit. -/
abbrev brnaPinBody (D : OddSurfaceDistance) : SFormula 3 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b true))
    (.imp (.eqBool (SC.closed (baseKindGuardTA (dP3 D) k1P3)) (SC.b false))
      (.imp (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b false))
        (.imp (.eqBool (SC.closed (topClassGuardTA (dP3 D) k2P3)) (SC.b false))
          (.imp (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k2P3)) (SC.b true))
            (.imp (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true))
              (.imp (.eqBool (SC.closed (rightBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))
                (.imp (.eqBool (SC.closed (brnaNonAdjTA D)) (SC.b true))
                  .bot)))))))

abbrev brnaPinF (D : OddSurfaceDistance) : SFormula 2 :=
  .allNatLt (nP2 D) (brnaPinBody D)

/-- Bulk–Right disjointness pin pack: a non-adjacent bulk plaquette and right
boundary share no qubit.  `arithBool`; the eval-cert unfolds the bulk band to
`suppMem_bulk_prop`'s `(row,col)` RHS and the right band to `suppMem_right_prop`'s,
then the geometric core lemma `brnaCellContra` (non-adjacency) refutes a common
qubit. -/
def brnaPinPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (brnaPinF D) := by
  refine PureFamilyDerivA.allNatLtIntro _ ?_
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd3 : D.distance = 2 * D.index + 3 := rfl
  simp only [brnaNonAdjTA, brnaEdgeAdjTA, brR3, bulkGuardTA, baseKindGuardTA,
    topClassGuardTA, rightClassGuardTA, baseBulkBandGuardTA, rightBandGuardTA, baseBTA,
    baseHalfTA, bulkCountTA, dm1TA, band3, orEqSucc, dP3, dP2, k1P3, k2P3, qP3,
    SFormula.eval, SC.closed, SC.b, STerm.eval, Term.eval, Term.lift,
    bind, Option.bind]
  set q := rho ⟨0, by decide⟩ with hq'
  set k2 := rho ⟨1, by decide⟩ with hk2'
  set k1 := rho ⟨2, by decide⟩ with hk1'
  set d := D.distance with hdd
  have hdge : 3 ≤ d := by omega
  have hdpos : 0 < d := by omega
  by_cases hbulk1 : k1 < (d - 1) * (d - 1)
  · have hb1t : decide (decide (k1 < (d - 1) * (d - 1)) = true) = true := by
      rw [decide_eq_true_eq]; simp [hbulk1]
    -- kind(k1): case on the X/Z parity guard.
    by_cases hk1kind : (k1 / (d - 1) + k1 % (d - 1)) % 2 = 0
    · -- kind(k1)=true ⟹ antecedent `kind(k1)=false` is false ⟹ vacuous.
      have hk1f : decide (decide ((k1 / (d - 1) + k1 % (d - 1)) % 2 = 0) = false) = false := by
        rw [decide_eq_false_iff_not]; simp [hk1kind]
      simp only [hb1t, hk1f, Bool.false_eq_true, if_false, reduceIte]
    · have hk1f : decide (decide ((k1 / (d - 1) + k1 % (d - 1)) % 2 = 0) = false) = true := by
        rw [decide_eq_true_eq]; simp [hk1kind]
      by_cases hbulk2 : k2 < (d - 1) * (d - 1)
      · have hb2f : decide (decide (k2 < (d - 1) * (d - 1)) = false) = false := by
          rw [decide_eq_false_iff_not]; simp [hbulk2]
        simp only [hb1t, hk1f, hb2f, Bool.false_eq_true, if_false, reduceIte]
      · by_cases htop : k2 - (d - 1) * (d - 1) < (d - 1) / 2
        · have hbf : decide (decide (k2 < (d - 1) * (d - 1)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hbulk2]
          have htf : decide (decide (k2 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = false := by
            rw [decide_eq_false_iff_not]; simp [htop]
          simp only [hb1t, hk1f, hbf, htf, Bool.false_eq_true, if_false, reduceIte]
        · by_cases hright : k2 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)
          · have hbf : decide (decide (k2 < (d - 1) * (d - 1)) = false) = true := by
              rw [decide_eq_true_eq]; simp [hbulk2]
            have htf : decide (decide (k2 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
              rw [decide_eq_true_eq]; simp [htop]
            have hrf : decide (decide (k2 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = true) = true := by
              rw [decide_eq_true_eq]; simp [hright]
            simp only [hb1t, hk1f, hbf, htf, hrf, if_true]
            set r := k2 - (d - 1) * (d - 1) - (d - 1) / 2 with hr
            -- Collapse the `Option.bind` chain into a closed `Prop` over
            -- `q/d, q%d, k1/(d-1), k1%(d-1), r`.
            simp only [← apply_ite Option.some, Option.some.injEq, Bool.if_true_left,
              Bool.if_true_right, Bool.if_false_right,
              Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, Bool.not_eq_false,
              decide_eq_true_eq, decide_eq_false_iff_not]
            -- Refute the only `.bot`-reaching branch (both bands fire, not adjacent).
            by_contra hcon
            push_neg at hcon
            obtain ⟨⟨hb1r, hb1c, _⟩, ⟨hcol, hb2r⟩, hnadj, _⟩ := hcon
            have hc1lt : k1 % (d - 1) < d - 1 := Nat.mod_lt _ (by omega)
            exact brnaCellContra hc1lt hcol hb2r hb1r hb1c hnadj
          · have hbf : decide (decide (k2 < (d - 1) * (d - 1)) = false) = true := by
              rw [decide_eq_true_eq]; simp [hbulk2]
            have htf : decide (decide (k2 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
              rw [decide_eq_true_eq]; simp [htop]
            have hrf : decide (decide (k2 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = true) = false := by
              rw [decide_eq_false_iff_not]; simp [hright]
            simp only [hb1t, hk1f, hbf, htf, hrf, Bool.false_eq_true, if_false, reduceIte]
  · have hb1f : decide (decide (k1 < (d - 1) * (d - 1)) = true) = false := by
      rw [decide_eq_false_iff_not]; simp [hbulk1]
    simp only [hb1f, Bool.false_eq_true, if_false]

/-- Extract the bulk–right disjointness-pin `⊥` at `boundNat`: under the class
context and NON-adjacency, the bulk band and right band cannot both fire. -/
def brnaPinAt {Δ : List (SFormula 3)} (D : OddSurfaceDistance)
    (hW : SFormula.Deriv Δ (brnaPinF D).weaken)
    (hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken))
    (hBulkK1 : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b true)))
    (hKindK1 : SFormula.Deriv Δ (.eqBool (SC.closed (baseKindGuardTA (dP3 D) k1P3)) (SC.b false)))
    (hBulkF : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b false)))
    (hTopF : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA (dP3 D) k2P3)) (SC.b false)))
    (hRightC : SFormula.Deriv Δ (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k2P3)) (SC.b true)))
    (hBandK1 : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true)))
    (hRightB : SFormula.Deriv Δ (.eqBool (SC.closed (rightBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true)))
    (hNonAdj : SFormula.Deriv Δ (.eqBool (SC.closed (brnaNonAdjTA D)) (SC.b true))) :
    SFormula.Deriv Δ .bot := by
  have hElim := SFormula.Deriv.allNatLtElim (nP2 D).weaken
    ((brnaPinBody D).lift 1) SFormula.boundNat hW hq
  have hBody := SFormula.Deriv.applyNatBoundNatBeta (brnaPinBody D) hElim
  exact SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp
    (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp hBody hBulkK1) hKindK1)
      hBulkF) hTopF) hRightC) hBandK1) hRightB |>.mp hNonAdj

#print axioms brnaCellContra
#print axioms brnaPinPack
#print axioms brnaPinAt

/-! ## Bulk–Right NON-ADJACENT closer (NON-OVERLAP routing path)

`pairCommuteBulkRightNonAdj` assembles the per-pair commutation goal for a NON-adjacent
bulk(X)–right(Z) pair via the non-overlap path `pairCommutePointwise`.  Row A (`k1`)
is X-kind bulk, row B (`k2`) is Z-type right boundary, and they are NOT edge-adjacent.
* `hAntiXZ` (both leaves genuinely fire): reverse-leaf the bulk band (`bhBandK1FromX`)
  and the right band (`brRightBandFromZ`), then the disjointness pin `brnaPinAt` yields
  `⊥` and `botElim` closes `lcGoalP D`;
* `hAntiZX` (k1-leaf = Z, impossible for an X-type row): vacuous via the type
  exclusion `typeExclF k1`, mirroring `twoAntiRestXZ`'s `(Z,X)` branch exactly. -/

/-- **Bulk–Right non-adjacent (non-overlap) closer.**  Row A is the X-kind bulk
plaquette, row B the Z-type right-boundary stabilizer, the two NOT edge-adjacent
(`hNonAdj`).  They share no qubit, so the pair commutes.  Routed through the
non-overlap path `pairCommutePointwise`: the `(X,Z)` leaf-pair is closed by the
disjointness pin `brnaPinAt` (→ `⊥`), the `(Z,X)` leaf-pair by the X-type exclusion
`hExcl1`. -/
def pairCommuteBulkRightNonAdj {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hEntryA : SFormula.Deriv Γ (entryAQuant D)) (hEntryB : SFormula.Deriv Γ (entryBQuant D))
    (hk1X : SFormula.Deriv Γ (k1IsX D true))
    (hExcl1 : SFormula.Deriv Γ (typeExclF D k1P))
    (hBulkK1 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true)))
    (hKindK1 : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k1P)) (SC.b false)))
    (hbulkFk2 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)))
    (htopFk2 : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false)))
    (hrightCk2 : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b true)))
    (hNonAdj : SFormula.Deriv Γ (.eqBool (SC.closed (brnaNonAdjTA2 D)) (SC.b true)))
    (hPin : SFormula.Deriv Γ (brnaPinF D)) :
    SFormula.Deriv Γ (pairGoal D) := by
  refine pairCommutePointwise D hEntryA hEntryB ?hXZ ?hZX
  · -- (X, Z): both leaves genuinely fire; the disjointness pin forces ⊥.
    intro Δ' lift hLeafA hLeafB
    have hBulkK1Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b true)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true)) hBulkK1))
    have hKindK1Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (baseKindGuardTA (dP3 D) k1P3)) (SC.b false)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (baseKindGuardTA (dP2 D) k1P)) (SC.b false)) hKindK1))
    have hbulkFk2Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b false)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)) hbulkFk2))
    have htopFk2Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (topClassGuardTA (dP3 D) k2P3)) (SC.b false)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false)) htopFk2))
    have hrightCk2Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k2P3)) (SC.b true)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b true)) hrightCk2))
    have hNonAdjΔ : SFormula.Deriv Δ' (.eqBool (SC.closed (brnaNonAdjTA D)) (SC.b true)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (brnaNonAdjTA2 D)) (SC.b true)) hNonAdj))
    have hPinΔ : SFormula.Deriv Δ' (brnaPinF D).weaken :=
      lift (cw1 (SFormula.Deriv.weakenFresh (A := brnaPinF D) hPin))
    have hq : SFormula.Deriv Δ' (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken) :=
      lift (.hyp List.mem_cons_self)
    have hBandK1 := bhBandK1FromX D hBulkK1Δ hLeafA
    have hRightB := brRightBandFromZ D hbulkFk2Δ htopFk2Δ hrightCk2Δ hLeafB
    have hBot := brnaPinAt D hPinΔ hq hBulkK1Δ hKindK1Δ hbulkFk2Δ htopFk2Δ hrightCk2Δ
      hBandK1 hRightB hNonAdjΔ
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

#print axioms pairCommuteBulkRightNonAdj

/-! ## Bulk–Left NON-ADJACENT (non-overlap) different-type pair

Row A (`k1`) is an X-kind bulk plaquette, row B (`k2`) a Z-type LEFT-boundary
stabilizer, and the two are NOT edge-adjacent.  A non-adjacent bulk plaquette and a
left boundary share NO qubit, so the `(X,Z)`/`(Z,X)` leaf-pairs never both fire — the
genuine `(X,Z)` branch is closed by a DISJOINTNESS PIN, and the `(Z,X)` branch is
vacuous via the X-type exclusion.

The left boundary `k2` occupies column `0`, rows `{2·leftIdx+1, 2·leftIdx+2}`
(`leftIdx = (k2−bulkCount) − 2·half`, `half = (d−1)/2`).  The bulk plaquette `k1`
shares a qubit with it ONLY when `cellC k1 = 0` (column `0`) AND its row band
`{cellR k1, cellR k1+1}` meets `{2·leftIdx+1, 2·leftIdx+2}`, i.e. `cellR k1 ∈
{2·leftIdx, 2·leftIdx+1, 2·leftIdx+2}`.  NON-ADJACENCY is the negation of that. -/

/-- Edge-adjacency of a bulk cell `k1` and a left-boundary row `k2` (arity 3,
`k1 = var 2`, `k2 = var 1`): the bulk's column `cellC k1 = 0` neighbours column `0`,
and the bulk row band meets the left strip's rows `{2·leftIdx+1, 2·leftIdx+2}`
(`leftIdx = blL3`).  `r = k/(d−1) = cellR`, `c = k%(d−1) = cellC`. -/
abbrev blnaEdgeAdjTA (D : OddSurfaceDistance) : Term 3 .bool :=
  .and (.eqNat (.mod k1P3 (dm1TA (dP3 D))) (.natLit 0))
    (.or (.or (.eqNat (.div k1P3 (dm1TA (dP3 D))) (.add (.mul (.natLit 2) (blL3 D)) (.natLit 1)))
        (.eqNat (.div k1P3 (dm1TA (dP3 D))) (.add (.mul (.natLit 2) (blL3 D)) (.natLit 2))))
      (.eqNat (.add (.div k1P3 (dm1TA (dP3 D))) (.natLit 1))
        (.add (.mul (.natLit 2) (blL3 D)) (.natLit 1))))

/-- Non-adjacency Bool: the negation of `blnaEdgeAdjTA`. -/
abbrev blnaNonAdjTA (D : OddSurfaceDistance) : Term 3 .bool :=
  .not (blnaEdgeAdjTA D)

/-- Arity-2 edge-adjacency Bool (`k1 = var 1`, `k2 = var 0`), the pair-goal-level
form of `blnaEdgeAdjTA`.  `(blnaEdgeAdjTA2 D).weaken = blnaEdgeAdjTA D` by `rfl`. -/
abbrev blnaEdgeAdjTA2 (D : OddSurfaceDistance) : Term 2 .bool :=
  .and (.eqNat (.mod k1P (dm1TA (dP2 D))) (.natLit 0))
    (.or (.or (.eqNat (.div k1P (dm1TA (dP2 D))) (.add (.mul (.natLit 2) (blL D)) (.natLit 1)))
        (.eqNat (.div k1P (dm1TA (dP2 D))) (.add (.mul (.natLit 2) (blL D)) (.natLit 2))))
      (.eqNat (.add (.div k1P (dm1TA (dP2 D))) (.natLit 1))
        (.add (.mul (.natLit 2) (blL D)) (.natLit 1))))

/-- Arity-2 non-adjacency Bool (pair-goal level). -/
abbrev blnaNonAdjTA2 (D : OddSurfaceDistance) : Term 2 .bool :=
  .not (blnaEdgeAdjTA2 D)

/-- **Core geometric contradiction** (pure `Nat`) for bulk–left.  A bulk cell
`(cellR1, cellC1)` and a left boundary at column `0`, rows `{2·l+1, 2·l+2}`, sharing
a slot `(R, C)`: both bands hit `(R, C)`, so `C = 0` (left col) and
`C ∈ {cellC1, cellC1+1}`, forcing `cellC1 = 0`; and `R ∈ {2·l+1, 2·l+2} ∩
{cellR1, cellR1+1}`, forcing `cellR1 ∈ {2·l, 2·l+1, 2·l+2}`.  NON-ADJACENCY
(`hnadj`) rules out exactly that. -/
private theorem blnaCellContra
    {R C cellR1 cellC1 l : Nat}
    (hCcol : C = 0)
    (hRrow : R = 2 * l + 1 ∨ R = 2 * l + 2) (hbR : R = cellR1 ∨ R = cellR1 + 1)
    (hbC : C = cellC1 ∨ C = cellC1 + 1)
    (hnadj : cellC1 = 0 →
      (cellR1 ≠ 2 * l + 1 ∧ cellR1 ≠ 2 * l + 2) ∧ cellR1 + 1 ≠ 2 * l + 1) : False := by
  obtain ⟨⟨hne0, hne1⟩, hne2⟩ := hnadj (by omega)
  rcases hRrow with h | h <;> rcases hbR with h' | h' <;> omega

/-- The bulk–left disjointness-pin body (arity 3, `k1 = var 2`, `k2 = var 1`,
`q = var 0`): under `bulk(k1)`, `kind(k1)=false` (X-kind), the left class context for
`k2` (`¬bulk ∧ ¬top ∧ ¬right ∧ left`), NON-adjacency, and both bands firing at `q`,
derive `⊥` — the bulk plaquette and the left boundary cannot share a qubit. -/
abbrev blnaPinBody (D : OddSurfaceDistance) : SFormula 3 :=
  .imp (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b true))
    (.imp (.eqBool (SC.closed (baseKindGuardTA (dP3 D) k1P3)) (SC.b false))
      (.imp (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b false))
        (.imp (.eqBool (SC.closed (topClassGuardTA (dP3 D) k2P3)) (SC.b false))
          (.imp (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k2P3)) (SC.b false))
            (.imp (.eqBool (SC.closed (leftClassGuardTA (dP3 D) k2P3)) (SC.b true))
              (.imp (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true))
                (.imp (.eqBool (SC.closed (leftBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true))
                  (.imp (.eqBool (SC.closed (blnaNonAdjTA D)) (SC.b true))
                    .bot))))))))

abbrev blnaPinF (D : OddSurfaceDistance) : SFormula 2 :=
  .allNatLt (nP2 D) (blnaPinBody D)

/-- Bulk–Left disjointness pin pack: a non-adjacent bulk plaquette and left boundary
share no qubit.  `arithBool`; the eval-cert unfolds the bulk band to
`suppMem_bulk_prop`'s `(row,col)` RHS and the left band to `suppMem_left_prop`'s, then
the geometric core lemma `blnaCellContra` (non-adjacency) refutes a common qubit. -/
def blnaPinPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (blnaPinF D) := by
  refine PureFamilyDerivA.allNatLtIntro _ ?_
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd3 : D.distance = 2 * D.index + 3 := rfl
  simp only [blnaNonAdjTA, blnaEdgeAdjTA, blL3, bulkGuardTA, baseKindGuardTA,
    topClassGuardTA, rightClassGuardTA, leftClassGuardTA, baseBulkBandGuardTA, leftBandGuardTA,
    baseBTA, baseHalfTA, bulkCountTA, dm1TA, band3, orEqSucc, orEqPair, dP3, dP2, k1P3, k2P3, qP3,
    SFormula.eval, SC.closed, SC.b, STerm.eval, Term.eval, Term.lift, bind, Option.bind]
  set q := rho ⟨0, by decide⟩ with hq'
  set k2 := rho ⟨1, by decide⟩ with hk2'
  set k1 := rho ⟨2, by decide⟩ with hk1'
  set d := D.distance with hdd
  have hdge : 3 ≤ d := by omega
  have hdpos : 0 < d := by omega
  by_cases hbulk1 : k1 < (d - 1) * (d - 1)
  · have hb1t : decide (decide (k1 < (d - 1) * (d - 1)) = true) = true := by
      rw [decide_eq_true_eq]; simp [hbulk1]
    by_cases hk1kind : (k1 / (d - 1) + k1 % (d - 1)) % 2 = 0
    · have hk1f : decide (decide ((k1 / (d - 1) + k1 % (d - 1)) % 2 = 0) = false) = false := by
        rw [decide_eq_false_iff_not]; simp [hk1kind]
      simp only [hb1t, hk1f, Bool.false_eq_true, if_false, reduceIte]
    · have hk1f : decide (decide ((k1 / (d - 1) + k1 % (d - 1)) % 2 = 0) = false) = true := by
        rw [decide_eq_true_eq]; simp [hk1kind]
      by_cases hbulk2 : k2 < (d - 1) * (d - 1)
      · have hb2f : decide (decide (k2 < (d - 1) * (d - 1)) = false) = false := by
          rw [decide_eq_false_iff_not]; simp [hbulk2]
        simp only [hb1t, hk1f, hb2f, Bool.false_eq_true, if_false, reduceIte]
      · by_cases htop : k2 - (d - 1) * (d - 1) < (d - 1) / 2
        · have hbf : decide (decide (k2 < (d - 1) * (d - 1)) = false) = true := by
            rw [decide_eq_true_eq]; simp [hbulk2]
          have htf : decide (decide (k2 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = false := by
            rw [decide_eq_false_iff_not]; simp [htop]
          simp only [hb1t, hk1f, hbf, htf, Bool.false_eq_true, if_false, reduceIte]
        · by_cases hright : k2 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)
          · have hbf : decide (decide (k2 < (d - 1) * (d - 1)) = false) = true := by
              rw [decide_eq_true_eq]; simp [hbulk2]
            have htf : decide (decide (k2 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
              rw [decide_eq_true_eq]; simp [htop]
            have hrf : decide (decide (k2 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = false := by
              rw [decide_eq_false_iff_not]; simp [hright]
            simp only [hb1t, hk1f, hbf, htf, hrf, Bool.false_eq_true, if_false, reduceIte]
          · by_cases hleft : k2 - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)
            · have hbf : decide (decide (k2 < (d - 1) * (d - 1)) = false) = true := by
                rw [decide_eq_true_eq]; simp [hbulk2]
              have htf : decide (decide (k2 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
                rw [decide_eq_true_eq]; simp [htop]
              have hrf : decide (decide (k2 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = true := by
                rw [decide_eq_true_eq]; simp [hright]
              have hlf : decide (decide (k2 - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)) = true) = true := by
                rw [decide_eq_true_eq]; simp [hleft]
              simp only [hb1t, hk1f, hbf, htf, hrf, hlf, if_true]
              set l := k2 - (d - 1) * (d - 1) - 2 * ((d - 1) / 2) with hl
              -- Collapse the `Option.bind` chain into a closed `Prop`.
              simp only [← apply_ite Option.some, Option.some.injEq, Bool.if_true_left,
                Bool.if_true_right, Bool.if_false_right,
                Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, Bool.not_eq_false,
                decide_eq_true_eq, decide_eq_false_iff_not]
              -- Refute the only `.bot`-reaching branch (both bands fire, not adjacent).
              by_contra hcon
              push_neg at hcon
              obtain ⟨⟨hb1r, hb1c, _⟩, ⟨hcol, hb2r⟩, hnadj, _⟩ := hcon
              exact blnaCellContra hcol hb2r hb1r hb1c hnadj
            · have hbf : decide (decide (k2 < (d - 1) * (d - 1)) = false) = true := by
                rw [decide_eq_true_eq]; simp [hbulk2]
              have htf : decide (decide (k2 - (d - 1) * (d - 1) < (d - 1) / 2) = false) = true := by
                rw [decide_eq_true_eq]; simp [htop]
              have hrf : decide (decide (k2 - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = true := by
                rw [decide_eq_true_eq]; simp [hright]
              have hlf : decide (decide (k2 - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)) = true) = false := by
                rw [decide_eq_false_iff_not]; simp [hleft]
              simp only [hb1t, hk1f, hbf, htf, hrf, hlf, Bool.false_eq_true, if_false, reduceIte]
  · have hb1f : decide (decide (k1 < (d - 1) * (d - 1)) = true) = false := by
      rw [decide_eq_false_iff_not]; simp [hbulk1]
    simp only [hb1f, Bool.false_eq_true, if_false]

/-- Extract the bulk–left disjointness-pin `⊥` at `boundNat`: under the class context
and NON-adjacency, the bulk band and left band cannot both fire. -/
def blnaPinAt {Δ : List (SFormula 3)} (D : OddSurfaceDistance)
    (hW : SFormula.Deriv Δ (blnaPinF D).weaken)
    (hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken))
    (hBulkK1 : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b true)))
    (hKindK1 : SFormula.Deriv Δ (.eqBool (SC.closed (baseKindGuardTA (dP3 D) k1P3)) (SC.b false)))
    (hBulkF : SFormula.Deriv Δ (.eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b false)))
    (hTopF : SFormula.Deriv Δ (.eqBool (SC.closed (topClassGuardTA (dP3 D) k2P3)) (SC.b false)))
    (hRightF : SFormula.Deriv Δ (.eqBool (SC.closed (rightClassGuardTA (dP3 D) k2P3)) (SC.b false)))
    (hLeftC : SFormula.Deriv Δ (.eqBool (SC.closed (leftClassGuardTA (dP3 D) k2P3)) (SC.b true)))
    (hBandK1 : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k1P3 qP3)) (SC.b true)))
    (hLeftB : SFormula.Deriv Δ (.eqBool (SC.closed (leftBandGuardTA (dP3 D) k2P3 qP3)) (SC.b true)))
    (hNonAdj : SFormula.Deriv Δ (.eqBool (SC.closed (blnaNonAdjTA D)) (SC.b true))) :
    SFormula.Deriv Δ .bot := by
  have hElim := SFormula.Deriv.allNatLtElim (nP2 D).weaken
    ((blnaPinBody D).lift 1) SFormula.boundNat hW hq
  have hBody := SFormula.Deriv.applyNatBoundNatBeta (blnaPinBody D) hElim
  exact SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp
    (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp hBody hBulkK1)
      hKindK1) hBulkF) hTopF) hRightF) hLeftC) hBandK1) hLeftB |>.mp hNonAdj

#print axioms blnaCellContra
#print axioms blnaPinPack
#print axioms blnaPinAt

/-! ## Bulk–Left NON-ADJACENT closer (NON-OVERLAP routing path)

`pairCommuteBulkLeftNonAdj` assembles the per-pair commutation goal for a NON-adjacent
bulk(X)–left(Z) pair via the non-overlap path `pairCommutePointwise`.  Row A (`k1`) is
X-kind bulk, row B (`k2`) is Z-type left boundary, and they are NOT edge-adjacent.
* `hAntiXZ` (both leaves genuinely fire): reverse-leaf the bulk band (`bhBandK1FromX`)
  and the left band (`blLeftBandFromZ`), then the disjointness pin `blnaPinAt` yields
  `⊥` and `botElim` closes `lcGoalP D`;
* `hAntiZX` (k1-leaf = Z, impossible for an X-type row): vacuous via the type
  exclusion `typeExclF k1`, mirroring `twoAntiRestXZ`'s `(Z,X)` branch exactly. -/

/-- **Bulk–Left non-adjacent (non-overlap) closer.**  Row A is the X-kind bulk
plaquette, row B the Z-type left-boundary stabilizer, the two NOT edge-adjacent
(`hNonAdj`).  They share no qubit, so the pair commutes.  Routed through the
non-overlap path `pairCommutePointwise`: the `(X,Z)` leaf-pair is closed by the
disjointness pin `blnaPinAt` (→ `⊥`), the `(Z,X)` leaf-pair by the X-type exclusion
`hExcl1`. -/
def pairCommuteBulkLeftNonAdj {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hEntryA : SFormula.Deriv Γ (entryAQuant D)) (hEntryB : SFormula.Deriv Γ (entryBQuant D))
    (hk1X : SFormula.Deriv Γ (k1IsX D true))
    (hExcl1 : SFormula.Deriv Γ (typeExclF D k1P))
    (hBulkK1 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true)))
    (hKindK1 : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dP2 D) k1P)) (SC.b false)))
    (hbulkFk2 : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)))
    (htopFk2 : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false)))
    (hrightFk2 : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false)))
    (hleftCk2 : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b true)))
    (hNonAdj : SFormula.Deriv Γ (.eqBool (SC.closed (blnaNonAdjTA2 D)) (SC.b true)))
    (hPin : SFormula.Deriv Γ (blnaPinF D)) :
    SFormula.Deriv Γ (pairGoal D) := by
  refine pairCommutePointwise D hEntryA hEntryB ?hXZ ?hZX
  · -- (X, Z): both leaves genuinely fire; the disjointness pin forces ⊥.
    intro Δ' lift hLeafA hLeafB
    have hBulkK1Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b true)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true)) hBulkK1))
    have hKindK1Δ : SFormula.Deriv Δ' (.eqBool (SC.closed (baseKindGuardTA (dP3 D) k1P3)) (SC.b false)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (baseKindGuardTA (dP2 D) k1P)) (SC.b false)) hKindK1))
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
    have hNonAdjΔ : SFormula.Deriv Δ' (.eqBool (SC.closed (blnaNonAdjTA D)) (SC.b true)) :=
      lift (cw1 (SFormula.Deriv.weakenFresh
        (A := .eqBool (SC.closed (blnaNonAdjTA2 D)) (SC.b true)) hNonAdj))
    have hPinΔ : SFormula.Deriv Δ' (blnaPinF D).weaken :=
      lift (cw1 (SFormula.Deriv.weakenFresh (A := blnaPinF D) hPin))
    have hq : SFormula.Deriv Δ' (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken) :=
      lift (.hyp List.mem_cons_self)
    have hBandK1 := bhBandK1FromX D hBulkK1Δ hLeafA
    have hLeftB := blLeftBandFromZ D hbulkFk2Δ htopFk2Δ hrightFk2Δ hleftCk2Δ hLeafB
    have hBot := blnaPinAt D hPinΔ hq hBulkK1Δ hKindK1Δ hbulkFk2Δ htopFk2Δ hrightFk2Δ
      hleftCk2Δ hBandK1 hLeftB hNonAdjΔ
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

#print axioms pairCommuteBulkLeftNonAdj

end QHL.CodeLang.Surface.Verify
