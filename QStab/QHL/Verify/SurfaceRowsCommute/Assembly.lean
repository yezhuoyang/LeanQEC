import QStab.QHL.Verify.SurfaceRowsCommute.Resolvers

/-!
# Rows-commute (pairwise generated-row commutation) — Assembly

Pointwise assembly of the per-pair goal, the CSS type guards and same-type vacuity packs
(type-exclusion arithmetic + literal leaf-value contradictions), and the headline assembly.
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface

set_option maxRecDepth 65536
set_option linter.unusedVariables false

/-! ## Pointwise assembly of the per-pair goal

`commutesOfPointwise` reduces `pairGoal` to local commutation at every qubit.  The
flat-entry facts for both rows are cut into the qubit-binder context and the leaves
resolved by `localDispatch`.  The caller supplies the two anti-handlers — for a
NON-overlapping or SAME-type pair these are vacuous (the `(X,Z)`/`(Z,X)` leaf-pairs
never both fire), and the caller closes them by a guard contradiction; this lemma
performs the structural plumbing once. -/

/-- The flat-entry facts, quantified over the qubit `q < nQubits`, at arity 2, so
they can be eliminated at `boundNat` inside the qubit binder. -/
abbrev entryAQuant (D : OddSurfaceDistance) : SFormula 2 :=
  .allNatLt (nP2 D) (entryAF D)
abbrev entryBQuant (D : OddSurfaceDistance) : SFormula 2 :=
  .allNatLt (nP2 D) (entryBF D)

def entryAQuantPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (entryAQuant D) :=
  PureFamilyDerivA.allNatLtIntro _ (entryAFlat D)
def entryBQuantPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (entryBQuant D) :=
  PureFamilyDerivA.allNatLtIntro _ (entryBFlat D)

/-- Extract the row-A flat-entry fact at `boundNat` from the weakened quantified pack. -/
def entryAAtBound {Δ : List (SFormula 3)} (D : OddSurfaceDistance)
    (hW : SFormula.Deriv Δ (entryAQuant D).weaken)
    (hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken)) :
    SFormula.Deriv Δ (entryAF D) := by
  have hElim := SFormula.Deriv.allNatLtElim (nP2 D).weaken
    ((entryAF D).lift 1) SFormula.boundNat hW hq
  exact SFormula.Deriv.applyNatBoundNatBeta (entryAF D) hElim
def entryBAtBound {Δ : List (SFormula 3)} (D : OddSurfaceDistance)
    (hW : SFormula.Deriv Δ (entryBQuant D).weaken)
    (hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken)) :
    SFormula.Deriv Δ (entryBF D) := by
  have hElim := SFormula.Deriv.allNatLtElim (nP2 D).weaken
    ((entryBF D).lift 1) SFormula.boundNat hW hq
  exact SFormula.Deriv.applyNatBoundNatBeta (entryBF D) hElim

/-- The qubit-binder context produced by `commutesOfPointwise` + `allNatLtIntroBounded`
over a context `Γ`: `boundNatLt (nP2 D) :: Γ.map weaken`. -/
abbrev pwCtx (D : OddSurfaceDistance) (Γ : List (SFormula 2)) : List (SFormula 3) :=
  SFormula.boundNatLt (nP2 D) :: List.map (fun G => G.weaken) Γ

/-- **Pointwise assembly.**  Given the quantified flat-entry facts in `Γ` and the
two anti-handlers (closing the `(X,Z)` / `(Z,X)` leaf-pairs in the deepened
qubit-binder context), the two rows commute.  Off the overlap / for same-type pairs
the anti-handlers are vacuous (closed by the caller via a guard contradiction). -/
def pairCommutePointwise {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hEntryAF : SFormula.Deriv Γ (entryAQuant D))
    (hEntryBF : SFormula.Deriv Γ (entryBQuant D))
    (hAntiXZ : ∀ (Δ' : List (SFormula 3)),
      (∀ {A : SFormula 3}, SFormula.Deriv (pwCtx D Γ) A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3)) (SC.p Pauli.X)) →
      SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p Pauli.Z)) →
        SFormula.Deriv Δ' (lcGoalP D))
    (hAntiZX : ∀ (Δ' : List (SFormula 3)),
      (∀ {A : SFormula 3}, SFormula.Deriv (pwCtx D Γ) A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3)) (SC.p Pauli.Z)) →
      SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p Pauli.X)) →
        SFormula.Deriv Δ' (lcGoalP D)) :
    SFormula.Deriv Γ (pairGoal D) := by
  refine SFormula.Deriv.commutesOfPointwise _ _ _ ?_
  unfold SFormula.pointwiseCommutesUpTo
  refine SFormula.Deriv.allNatLtIntroBounded _ _ ?_
  -- context now: pwCtx D Γ
  have hq : SFormula.Deriv (pwCtx D Γ)
      (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken) :=
    SFormula.Deriv.hyp List.mem_cons_self
  have hEntryAW : SFormula.Deriv (pwCtx D Γ) (entryAQuant D).weaken :=
    cw1 (SFormula.Deriv.weakenFresh (A := entryAQuant D) hEntryAF)
  have hEntryBW : SFormula.Deriv (pwCtx D Γ) (entryBQuant D).weaken :=
    cw1 (SFormula.Deriv.weakenFresh (A := entryBQuant D) hEntryBF)
  have hEntryA := entryAAtBound D hEntryAW hq
  have hEntryB := entryBAtBound D hEntryBW hq
  exact localDispatch D hEntryA hEntryB hAntiXZ hAntiZX

/-! ## CSS type guards and the same-type vacuity packs

`arithBool` rejects `anticommutes`/`eqPauli`, so "leaves never anticommute" cannot
be proved arithmetically.  Instead we contradict the leaf VALUES against per-row
k-only TYPE facts: an X-type row never produces a `Z` leaf, and a Z-type row never
produces an `X` leaf.  The row's CSS type is a pure function of `k`:
`X-type ⟺ (bulk ∧ ¬kind) ∨ top ∨ bottom`, `Z-type ⟺ (bulk ∧ kind) ∨ right ∨ left`
(verified exhaustively, d = 3,5,7).

The genuinely arithmetic facts (no Pauli, so `arithBool`-provable):
* `xTypeExclZ`: if a row is X-type, then NONE of the `Z`-producing leaf class-guard
  conjunctions can hold — i.e. `¬(bulk∧kind) ∧ ¬(¬bulk∧¬top∧right) ∧
  ¬(¬bulk∧¬top∧¬right∧left)`;
* `zTypeExclX`: symmetric, with the `X`-producing classes.

We capture each as a k-only implication and use it, after re-resolving the
offending row's leaf with guards exposed, to contradict the `Z`/`X` leaf. -/

/-- X-type classifier, `k`-only.  bulk → ¬kind; top → true; right/left → false;
bottom (the else) → true. -/
def isXTypeTA {arity : Nat} (dT kT : Term arity .nat) : Term arity .bool :=
  .ite (bulkGuardTA dT kT) (.not (baseKindGuardTA dT kT))
    (.ite (topClassGuardTA dT kT) (.boolLit true)
      (.ite (rightClassGuardTA dT kT) (.boolLit false)
        (.ite (leftClassGuardTA dT kT) (.boolLit false) (.boolLit true))))

/-! NOTE.  The pair goal binds `k1 = var 1` (`k1P`), `k2 = var 0` (`k2P`), with
distance `dP2 D`.  The type guards are taken directly on those. -/

/-- X-type classifier on the pair's first index `k1 = var 1` (arity 2). -/
abbrev k1IsX (D : OddSurfaceDistance) (v : Bool) : SFormula 2 :=
  .eqBool (SC.closed (isXTypeTA (dP2 D) k1P)) (SC.b v)
/-- X-type classifier on the pair's second index `k2 = var 0` (arity 2). -/
abbrev k2IsX (D : OddSurfaceDistance) (v : Bool) : SFormula 2 :=
  .eqBool (SC.closed (isXTypeTA (dP2 D) k2P)) (SC.b v)

/-! ### Type-exclusion arithmetic packs (`k`-only, `arithBool`-provable)

An X-type row produces no `Z` leaf.  The three `Z`-producing leaf branches are
bulk-`Z` (`bulk ∧ kind`), right-`Z` (`¬bulk ∧ ¬top ∧ right`), left-`Z`
(`¬bulk ∧ ¬top ∧ ¬right ∧ left`).  Each is excluded by `isXType = true`, captured
as a `k`-only implication chain.  Symmetric `zTypeExcl*` for Z-type vs `X`. -/

/-- Generic-index bulk-Z exclusion: `isXType → bulk → ¬kind`. -/
abbrev xtNotBulkZF (D : OddSurfaceDistance) (kT : Term 2 .nat) : SFormula 2 :=
  .imp (.eqBool (SC.closed (isXTypeTA (dP2 D) kT)) (SC.b true))
    (.imp (.eqBool (SC.closed (bulkGuardTA (dP2 D) kT)) (SC.b true))
      (.eqBool (SC.closed (baseKindGuardTA (dP2 D) kT)) (SC.b false)))
/-- Generic-index right-Z exclusion: `isXType → ¬bulk → ¬top → ¬right`. -/
abbrev xtNotRightZF (D : OddSurfaceDistance) (kT : Term 2 .nat) : SFormula 2 :=
  .imp (.eqBool (SC.closed (isXTypeTA (dP2 D) kT)) (SC.b true))
    (.imp (.eqBool (SC.closed (bulkGuardTA (dP2 D) kT)) (SC.b false))
      (.imp (.eqBool (SC.closed (topClassGuardTA (dP2 D) kT)) (SC.b false))
        (.eqBool (SC.closed (rightClassGuardTA (dP2 D) kT)) (SC.b false))))
/-- Generic-index left-Z exclusion: `isXType → ¬bulk → ¬top → ¬right → ¬left`. -/
abbrev xtNotLeftZF (D : OddSurfaceDistance) (kT : Term 2 .nat) : SFormula 2 :=
  .imp (.eqBool (SC.closed (isXTypeTA (dP2 D) kT)) (SC.b true))
    (.imp (.eqBool (SC.closed (bulkGuardTA (dP2 D) kT)) (SC.b false))
      (.imp (.eqBool (SC.closed (topClassGuardTA (dP2 D) kT)) (SC.b false))
        (.imp (.eqBool (SC.closed (rightClassGuardTA (dP2 D) kT)) (SC.b false))
          (.eqBool (SC.closed (leftClassGuardTA (dP2 D) kT)) (SC.b false)))))

/-- Generic-index bulk-X exclusion: `¬isXType → bulk → kind` (Z-type has kind). -/
abbrev ztNotBulkXF (D : OddSurfaceDistance) (kT : Term 2 .nat) : SFormula 2 :=
  .imp (.eqBool (SC.closed (isXTypeTA (dP2 D) kT)) (SC.b false))
    (.imp (.eqBool (SC.closed (bulkGuardTA (dP2 D) kT)) (SC.b true))
      (.eqBool (SC.closed (baseKindGuardTA (dP2 D) kT)) (SC.b true)))
/-- Generic-index top-X exclusion: `¬isXType → ¬bulk → ¬top`. -/
abbrev ztNotTopXF (D : OddSurfaceDistance) (kT : Term 2 .nat) : SFormula 2 :=
  .imp (.eqBool (SC.closed (isXTypeTA (dP2 D) kT)) (SC.b false))
    (.imp (.eqBool (SC.closed (bulkGuardTA (dP2 D) kT)) (SC.b false))
      (.eqBool (SC.closed (topClassGuardTA (dP2 D) kT)) (SC.b false)))
/-- Generic-index bottom-X exclusion: `¬isXType → ¬bulk → ¬top → (right ∨ left)`,
expressed as `→ leftClass = true` (bottom is the else of `leftClass`, so under
`¬isXType` with `¬bulk ¬top`, we must be in right/left, hence `leftClass = true`). -/
abbrev ztNotBottomXF (D : OddSurfaceDistance) (kT : Term 2 .nat) : SFormula 2 :=
  .imp (.eqBool (SC.closed (isXTypeTA (dP2 D) kT)) (SC.b false))
    (.imp (.eqBool (SC.closed (bulkGuardTA (dP2 D) kT)) (SC.b false))
      (.imp (.eqBool (SC.closed (topClassGuardTA (dP2 D) kT)) (SC.b false))
        (.eqBool (SC.closed (leftClassGuardTA (dP2 D) kT)) (SC.b true))))

/-- All six type-exclusion facts for a single index, packed. -/
abbrev typeExclF (D : OddSurfaceDistance) (kT : Term 2 .nat) : SFormula 2 :=
  .and (xtNotBulkZF D kT) (.and (xtNotRightZF D kT) (.and (xtNotLeftZF D kT)
    (.and (ztNotBulkXF D kT) (.and (ztNotTopXF D kT) (ztNotBottomXF D kT)))))

/-- The type-exclusion pack for the second index `k2 = var 0`. -/
def typeExclPackK2 (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (typeExclF D k2P) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [isXTypeTA, bulkGuardTA, baseKindGuardTA, topClassGuardTA, rightClassGuardTA,
    leftClassGuardTA, baseBTA, baseHalfTA, bulkCountTA, dP2, k2P, dm1TA, SFormula.eval, SC.closed,
    SC.b, STerm.eval, Term.eval, Term.lift, bind, Option.bind]
  set k := rho ⟨0, by decide⟩ with hk
  set d := D.distance with hdd
  have hdpos : 0 < d := by omega
  by_cases hbulk : k < (d - 1) * (d - 1)
  · by_cases hkind : (k / (d - 1) + k % (d - 1)) % 2 = 0
    · simp [hbulk, hkind]
    · simp [hbulk, hkind]
  · by_cases htop : k - (d - 1) * (d - 1) < (d - 1) / 2
    · simp [hbulk, htop]
    · by_cases hright : k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)
      · have h3 : k - (d - 1) * (d - 1) < 3 * ((d - 1) / 2) := by omega
        simp [hbulk, htop, hright, h3]
      · by_cases hleft : k - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)
        · simp [hbulk, htop, hright, hleft]
        · simp [hbulk, htop, hright, hleft]

/-- The type-exclusion pack for the first index `k1 = var 1`. -/
def typeExclPackK1 (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (typeExclF D k1P) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [isXTypeTA, bulkGuardTA, baseKindGuardTA, topClassGuardTA, rightClassGuardTA,
    leftClassGuardTA, baseBTA, baseHalfTA, bulkCountTA, dP2, k1P, dm1TA, SFormula.eval, SC.closed,
    SC.b, STerm.eval, Term.eval, Term.lift, bind, Option.bind]
  set k := rho ⟨1, by decide⟩ with hk
  set d := D.distance with hdd
  have hdpos : 0 < d := by omega
  by_cases hbulk : k < (d - 1) * (d - 1)
  · by_cases hkind : (k / (d - 1) + k % (d - 1)) % 2 = 0
    · simp [hbulk, hkind]
    · simp [hbulk, hkind]
  · by_cases htop : k - (d - 1) * (d - 1) < (d - 1) / 2
    · simp [hbulk, htop]
    · by_cases hright : k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)
      · have h3 : k - (d - 1) * (d - 1) < 3 * ((d - 1) / 2) := by omega
        simp [hbulk, htop, hright, h3]
      · by_cases hleft : k - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)
        · simp [hbulk, htop, hright, hleft]
        · simp [hbulk, htop, hright, hleft]

/-! ### Literal leaf-value contradictions

When a row's leaf is asserted to be both `p1` and `p2` for distinct literals, we
derive a contradiction by transporting `anticommutes` against a reference Pauli on
which `p1` and `p2` disagree.  We use reference `X`: `anticommutes I X = false`,
`anticommutes X X = false`, `anticommutes Z X = true`. -/

/-- Leaf both `p` (with `anticommutes p X = false`) and `Z` ⟹ contradiction. -/
def leafNotPandZ {Δ : List (SFormula 3)} {C : SFormula 3} (D : OddSurfaceDistance)
    (kT : Term 3 .nat) (p : Pauli) (hpX : ErrorVec.Pauli.anticommutes p Pauli.X = false)
    (hP : SFormula.Deriv Δ (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) kT qP3)) (SC.p p)))
    (hZ : SFormula.Deriv Δ (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) kT qP3)) (SC.p Pauli.Z))) :
    SFormula.Deriv Δ C := by
  -- anticommutes leaf X = false (via p) and = true (via Z).
  have hFalse : SFormula.Deriv Δ
      (.eqBool (.anticommutes (SC.closed (baseLeafTreeTA (dP3 D) kT qP3)) (SC.p Pauli.X)) (SC.b false)) :=
    SFormula.Deriv.anticommutesTransport _ (SC.p p) _ (SC.p Pauli.X) (SC.b false)
      hP (SFormula.Deriv.pauliEqLit Pauli.X) (antiP p Pauli.X hpX)
  have hTrue : SFormula.Deriv Δ
      (.eqBool (.anticommutes (SC.closed (baseLeafTreeTA (dP3 D) kT qP3)) (SC.p Pauli.X)) (SC.b true)) :=
    SFormula.Deriv.anticommutesTransport _ (SC.p Pauli.Z) _ (SC.p Pauli.X) (SC.b true)
      hZ (SFormula.Deriv.pauliEqLit Pauli.X) (SFormula.Deriv.pauliAnticommutesLit Pauli.Z Pauli.X)
  exact eqBoolContra _ hTrue hFalse

/-- Leaf both `p` (with `anticommutes p Z = false`, i.e. `p ∈ {I, Z}`) and `X`
⟹ contradiction.  Reference `Z`: `anticommutes I Z = false`,
`anticommutes Z Z = false`, `anticommutes X Z = true`. -/
def leafNotPandX {Δ : List (SFormula 3)} {C : SFormula 3} (D : OddSurfaceDistance)
    (kT : Term 3 .nat) (p : Pauli) (hpZ : ErrorVec.Pauli.anticommutes p Pauli.Z = false)
    (hP : SFormula.Deriv Δ (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) kT qP3)) (SC.p p)))
    (hX : SFormula.Deriv Δ (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) kT qP3)) (SC.p Pauli.X))) :
    SFormula.Deriv Δ C := by
  have hFalse : SFormula.Deriv Δ
      (.eqBool (.anticommutes (SC.closed (baseLeafTreeTA (dP3 D) kT qP3)) (SC.p Pauli.Z)) (SC.b false)) :=
    SFormula.Deriv.anticommutesTransport _ (SC.p p) _ (SC.p Pauli.Z) (SC.b false)
      hP (SFormula.Deriv.pauliEqLit Pauli.Z) (antiP p Pauli.Z hpZ)
  have hTrue : SFormula.Deriv Δ
      (.eqBool (.anticommutes (SC.closed (baseLeafTreeTA (dP3 D) kT qP3)) (SC.p Pauli.Z)) (SC.b true)) :=
    SFormula.Deriv.anticommutesTransport _ (SC.p Pauli.X) _ (SC.p Pauli.Z) (SC.b true)
      hX (SFormula.Deriv.pauliEqLit Pauli.Z) (SFormula.Deriv.pauliAnticommutesLit Pauli.X Pauli.Z)
  exact eqBoolContra _ hTrue hFalse

/-! ## Headline assembly

The per-pair goal `pairGoal D` is assembled by classifying the pair `(k1, k2)` by
the CSS type of each row and applying:
* SAME type (both X-type or both Z-type) → `pairCommutePointwise` with vacuous
  anti-handlers (a same-type pair never produces an `(X,Z)`/`(Z,X)` leaf-pair, so
  those handlers are closed by a guard contradiction);
* DIFFERENT type → either non-overlapping (`pairCommutePointwise`, vacuous
  handlers) or overlapping at exactly two qubits `q0`,`q1`
  (`commutesOfTwoAnti (nP2 D) (rowA D) (rowB D) q0 q1`).

The verified overlap geometry (`#eval` on `surfaceCellPauli`, d = 3,5,7,
exhaustive — scratch deleted):

* every row is uniformly X-type or Z-type;
* two SAME-type rows never anticommute at any qubit;
* two DIFFERENT-type rows anticommute exactly on `support(k1) ∩ support(k2)`,
  always of size 0 or 2 — the two shared corner qubits of two adjacent
  surface-code plaquettes, and every such overlap is either a VERTICAL edge
  (same column `c·? `, rows `r, r+1`) or a HORIZONTAL edge (same row, cols
  `c, c+1`).  Every overlapping pair involves at least one bulk plaquette (there
  are NO boundary-vs-boundary overlaps).  Closed forms (grid coordinates of the
  two anti qubits `q0 = d·row0 + col0`, `q1 = d·row1 + col1`):
  - bulk(r1,c1)–bulk vertical neighbour below:  `(r1+1, c1+1)` and `(r1+2, c1+1)` etc.
    (the two qubits in the shared edge of the two `2×2` plaquette stencils);
  - bulk–top/right/left/bottom boundary: the single shared boundary edge of the
    bulk plaquette and the weight-2 boundary stabilizer.

`pairCommutePointwise` (proved above, sorry-free) is the complete pointwise spine;
`commutesOfTwoAnti` is the kernel rule for the overlapping case.  What remains to
mechanize is, per class-pair, the arithmetic `q0`/`q1` witnesses together with the
band-fires-at-`q0`/`q1` packs and the all-others pin (`arithBool`) — the direct
analogue of `classAPack`/`classABulkZPin` in `SurfaceNormalizers.lean`, now for two
generated rows instead of one row vs. a fixed logical operator. -/

end QHL.CodeLang.Surface.Verify
