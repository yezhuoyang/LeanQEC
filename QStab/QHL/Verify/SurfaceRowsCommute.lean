import QStab.QHL.Verify.SurfaceNormalizers
import QStab.QHL.Verify.SurfaceFlatBridge
import QStab.QHL.Verify.SurfaceRowOverlapNat

/-!
# Pairwise row commutation for the recursive Surface code (`∀ D`)

`rowsCommuteSym D : PureFamilyDerivA Surface.code.body (D.distance + 2)
  (closedSF (rowsCommuteOddF D))` — every pair of generated stabilizer rows
`codeRow d k1`, `codeRow d k2` commutes, for all `OddSurfaceDistance D`.

This is the third input (`rows`) to `codeLevelPureFromGeneratedRows`, alongside
the two normalizers `xNormCommuteSym` / `zNormCommuteSym`.

## Strategy (CSS, verified by `#eval` on `surfaceCellPauli`/`baseLeafTreeTA`)

The surface code is CSS: every generated row is uniformly X-type or Z-type.
Verified geometry (d = 3,5,7, exhaustive):
* each row is uniformly X or Z (0 mixed);
* two rows of the SAME type never anticommute at any qubit;
* two rows of DIFFERENT type anticommute exactly on `support(k1) ∩ support(k2)`,
  whose size is always 0 or 2 (the two shared corner qubits of two adjacent
  surface-code plaquettes).

The proof reuses the normalizer machinery (`SurfaceNormalizers.lean`):
`rowEntryFlatSym` resolves BOTH row entries to the flat `baseLeafTreeTA`
classifier, `commutesOfPointwise` discharges the same-type / non-overlapping
classes, and `commutesOfTwoAnti` with arithmetic `q0`/`q1` discharges the
overlapping X-vs-Z classes.

Prover-side only: no `native_decide` / `Formula.check` / `Formula.eval`-as-proof
/ `deriveTrue?` / `admit` / new `axiom` / `@[implemented_by]` / `unsafe` /
`checkedBoundFree`.
-/

namespace QHL.CodeLang.Surface.Verify

open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface

set_option maxRecDepth 65536

set_option linter.unusedVariables false

/-! ## Arity-2 abbreviations for the pair-of-rows goal

After the two `allNatLtIntro`s, both stabilizer indices are bound:
`k1 = var 1`, `k2 = var 0`, distance `dP2 = lift0 (lift0 (natLit d))`, qubit
count `lift0 (lift0 (natLit nQubits))`.  Both rows are `recCall dP2 k`. -/

/-- Distance term at arity 2 (twice-lifted literal). -/
abbrev dP2 (D : OddSurfaceDistance) : Term 2 .nat :=
  Term.lift 0 (Term.lift 0 (Term.natLit D.distance))
/-- First row index `k1 = var 1` at arity 2. -/
abbrev k1P : Term 2 .nat := Term.var ⟨1, by decide⟩
/-- Second row index `k2 = var 0` at arity 2. -/
abbrev k2P : Term 2 .nat := Term.var ⟨0, by decide⟩
/-- Qubit count term at arity 2. -/
abbrev nP2 (D : OddSurfaceDistance) : STerm 2 .nat :=
  SC.closed (Term.lift 0 (Term.lift 0 (Term.natLit (nQubits D.distance))))
/-- First row stabilizer (closed `recCall` at `k1`). -/
abbrev rowA (D : OddSurfaceDistance) : STerm 2 .stab :=
  SC.closed (.recCall (dP2 D) k1P)
/-- Second row stabilizer (closed `recCall` at `k2`). -/
abbrev rowB (D : OddSurfaceDistance) : STerm 2 .stab :=
  SC.closed (.recCall (dP2 D) k2P)

/-- The per-pair commutation goal at arity 2. -/
abbrev pairGoal (D : OddSurfaceDistance) : SFormula 2 :=
  SFormula.commutesUpTo (nP2 D) (rowA D) (rowB D)

/-- The reduction of `rowsCommuteSym` to the per-pair goal: two `allNatLtIntro`s. -/
def rowsCommuteFromPair (D : OddSurfaceDistance)
    (h : PureFamilyDerivA Surface.code.body (D.distance + 2) (pairGoal D)) :
    PureFamilyDerivA Surface.code.body (D.distance + 2)
      (closedSF (rowsCommuteOddF D)) := by
  unfold closedSF rowsCommuteOddF rowsCommuteF Formula.codeRowsCommuteUpTo
  simp only [closedSF, Formula.codeRow, Term.weaken]
  exact PureFamilyDerivA.allNatLtIntro _ (PureFamilyDerivA.allNatLtIntro _ h)

/-! ## Flat entries for both rows (arity 2, symbolic qubit binder)

`rowEntryFlatSym` resolves each row entry at the symbolic qubit `var 0` (arity 3,
after the qubit binder is added) to the flat `baseLeafTreeTA`.  We need this for
BOTH `k1 = var 1` and `k2 = var 0`.  The distance witness `distAtBoundIdx2 D`
has `dT = dP2 D` already. -/

/-- Distance term at arity 3 (after qubit binder). -/
abbrev dP3 (D : OddSurfaceDistance) : Term 3 .nat :=
  Term.lift 0 (dP2 D)
/-- `k1 = var 2` at arity 3. -/
abbrev k1P3 : Term 3 .nat := Term.var ⟨2, by decide⟩
/-- `k2 = var 1` at arity 3. -/
abbrev k2P3 : Term 3 .nat := Term.var ⟨1, by decide⟩
/-- qubit `q = var 0` at arity 3. -/
abbrev qP3 : Term 3 .nat := Term.var ⟨0, by decide⟩

/-- Distance witness at arity 2 (reuse of the normalizer's). -/
abbrev distP2 (D : OddSurfaceDistance) : DistAtA 2 D.index := distAtBoundIdx2 D

/-- Distance witness at arity 3 with `dT = dP3 D = lift0 (lift0 (lift0 (natLit d)))`. -/
def distP3 (D : OddSurfaceDistance) : DistAtA 3 D.index where
  dT := dP3 D
  pure := SFormula.PureNatTerm.natLit (arity := 3) D.distance
  evalsTo := by
    intro fuel rho
    simp only [dP3, dP2, Term.lift, Term.eval, OddSurfaceDistance.distance]

/-- **Flat entry of row A (`k1 = var 1`) at the symbolic qubit binder.**  At arity
2, probed at `boundNat = var 0`, the (weakened) row-A entry equals the flat
classifier `baseLeafTreeTA (dP3 D) (var 2) (var 0)`. -/
def entryAFlat (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2)
      (.eqPauli (.stabAt (SC.closed (.recCall (dP3 D) k1P3)) SFormula.boundNat)
        (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3))) :=
  rowEntryFlatSym (fuel := D.distance + 2) D.index (distP3 D) k1P3 qP3
    (SFormula.PureNatTerm.var ⟨2, by decide⟩)
    (SFormula.PureNatTerm.var ⟨0, by decide⟩)

/-- **Flat entry of row B (`k2 = var 0`) at the symbolic qubit binder.** -/
def entryBFlat (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2)
      (.eqPauli (.stabAt (SC.closed (.recCall (dP3 D) k2P3)) SFormula.boundNat)
        (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3))) :=
  rowEntryFlatSym (fuel := D.distance + 2) D.index (distP3 D) k2P3 qP3
    (SFormula.PureNatTerm.var ⟨1, by decide⟩)
    (SFormula.PureNatTerm.var ⟨0, by decide⟩)

/-- The weakened row-A stabilizer equals the arity-3 `recCall` at `k1 = var 2`. -/
theorem rowA_weaken (D : OddSurfaceDistance) :
    (rowA D).weaken = SC.closed (.recCall (dP3 D) k1P3) := rfl
/-- The weakened row-B stabilizer equals the arity-3 `recCall` at `k2 = var 1`. -/
theorem rowB_weaken (D : OddSurfaceDistance) :
    (rowB D).weaken = SC.closed (.recCall (dP3 D) k2P3) := rfl

/-! ## The local-commutation goal and entry-equality abbreviations (arity 3) -/

/-- The local-commutation goal at the symbolic qubit binder. -/
abbrev lcGoalP (D : OddSurfaceDistance) : SFormula 3 :=
  SFormula.localCommutesAt (rowA D).weaken (rowB D).weaken SFormula.boundNat

/-- Row-A flat-entry equality as a formula (cut into context). -/
abbrev entryAF (D : OddSurfaceDistance) : SFormula 3 :=
  .eqPauli (.stabAt (SC.closed (.recCall (dP3 D) k1P3)) SFormula.boundNat)
    (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3))
/-- Row-B flat-entry equality as a formula (cut into context). -/
abbrev entryBF (D : OddSurfaceDistance) : SFormula 3 :=
  .eqPauli (.stabAt (SC.closed (.recCall (dP3 D) k2P3)) SFormula.boundNat)
    (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3))

/-- **Local commutation from two resolved leaves.**  Given both row entries resolve
to literal Paulis `pa`/`pb` (via leaf peels) that do not anticommute, the two rows
commute locally at `boundNat`. -/
def lcFromTwoLeaves {Δ : List (SFormula 3)} (D : OddSurfaceDistance) (pa pb : Pauli)
    (hEntryA : SFormula.Deriv Δ (entryAF D))
    (hLeafA : SFormula.Deriv Δ
      (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3)) (SC.p pa)))
    (hEntryB : SFormula.Deriv Δ (entryBF D))
    (hLeafB : SFormula.Deriv Δ
      (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p pb)))
    (hAnti : SFormula.Deriv Δ
      (.eqBool (.anticommutes (SC.p pb) (SC.p pa)) (SC.b false))) :
    SFormula.Deriv Δ (lcGoalP D) := by
  have hA : SFormula.Deriv Δ
      (.eqPauli (.stabAt (rowA D).weaken SFormula.boundNat) (SC.p pa)) := by
    rw [rowA_weaken]; exact SFormula.Deriv.eqPauliTrans _ _ _ hEntryA hLeafA
  have hB : SFormula.Deriv Δ
      (.eqPauli (.stabAt (rowB D).weaken SFormula.boundNat) (SC.p pb)) := by
    rw [rowB_weaken]; exact SFormula.Deriv.eqPauliTrans _ _ _ hEntryB hLeafB
  refine SFormula.Deriv.localCommutesOfLeftEqNoAntiRight _ _ _ (SC.p pa) hA ?_
  have hLitFalse : SFormula.Deriv Δ
      (.eqBool (.anticommutes (.stabAt (rowB D).weaken SFormula.boundNat) (SC.p pa)) (SC.b false)) :=
    SFormula.Deriv.anticommutesTransport _ (SC.p pb) _ (SC.p pa) (SC.b false)
      hB (SFormula.Deriv.pauliEqLit pa) hAnti
  exact SFormula.Deriv.eqBoolFalseNotTrue _ hLitFalse

/-! ## Per-row guard abbreviations at arity 3 (`k1 = var 2`, `k2 = var 1`, `q = var 0`)

The cell-classification guards for each row, instantiated at the arity-3 indices.
Both rows are classified independently; the qubit guards reference `q = var 0`. -/

-- Row A (k1 = var 2) guards
abbrev aBulk (D : OddSurfaceDistance) (v : Bool) : SFormula 3 :=
  .eqBool (SC.closed (bulkGuardTA (dP3 D) k1P3)) (SC.b v)
abbrev aBand (D : OddSurfaceDistance) (v : Bool) : SFormula 3 :=
  .eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k1P3 qP3)) (SC.b v)
abbrev aKind (D : OddSurfaceDistance) (v : Bool) : SFormula 3 :=
  .eqBool (SC.closed (baseKindGuardTA (dP3 D) k1P3)) (SC.b v)
abbrev aTopC (D : OddSurfaceDistance) (v : Bool) : SFormula 3 :=
  .eqBool (SC.closed (topClassGuardTA (dP3 D) k1P3)) (SC.b v)
abbrev aTopB (D : OddSurfaceDistance) (v : Bool) : SFormula 3 :=
  .eqBool (SC.closed (topBandGuardTA (dP3 D) k1P3 qP3)) (SC.b v)
abbrev aRightC (D : OddSurfaceDistance) (v : Bool) : SFormula 3 :=
  .eqBool (SC.closed (rightClassGuardTA (dP3 D) k1P3)) (SC.b v)
abbrev aRightB (D : OddSurfaceDistance) (v : Bool) : SFormula 3 :=
  .eqBool (SC.closed (rightBandGuardTA (dP3 D) k1P3 qP3)) (SC.b v)
abbrev aLeftC (D : OddSurfaceDistance) (v : Bool) : SFormula 3 :=
  .eqBool (SC.closed (leftClassGuardTA (dP3 D) k1P3)) (SC.b v)
abbrev aLeftB (D : OddSurfaceDistance) (v : Bool) : SFormula 3 :=
  .eqBool (SC.closed (leftBandGuardTA (dP3 D) k1P3 qP3)) (SC.b v)
abbrev aBotB (D : OddSurfaceDistance) (v : Bool) : SFormula 3 :=
  .eqBool (SC.closed (bottomBandGuardTA (dP3 D) k1P3 qP3)) (SC.b v)

-- Row B (k2 = var 1) guards
abbrev bBulk (D : OddSurfaceDistance) (v : Bool) : SFormula 3 :=
  .eqBool (SC.closed (bulkGuardTA (dP3 D) k2P3)) (SC.b v)
abbrev bBand (D : OddSurfaceDistance) (v : Bool) : SFormula 3 :=
  .eqBool (SC.closed (baseBulkBandGuardTA (dP3 D) k2P3 qP3)) (SC.b v)
abbrev bKind (D : OddSurfaceDistance) (v : Bool) : SFormula 3 :=
  .eqBool (SC.closed (baseKindGuardTA (dP3 D) k2P3)) (SC.b v)
abbrev bTopC (D : OddSurfaceDistance) (v : Bool) : SFormula 3 :=
  .eqBool (SC.closed (topClassGuardTA (dP3 D) k2P3)) (SC.b v)
abbrev bTopB (D : OddSurfaceDistance) (v : Bool) : SFormula 3 :=
  .eqBool (SC.closed (topBandGuardTA (dP3 D) k2P3 qP3)) (SC.b v)
abbrev bRightC (D : OddSurfaceDistance) (v : Bool) : SFormula 3 :=
  .eqBool (SC.closed (rightClassGuardTA (dP3 D) k2P3)) (SC.b v)
abbrev bRightB (D : OddSurfaceDistance) (v : Bool) : SFormula 3 :=
  .eqBool (SC.closed (rightBandGuardTA (dP3 D) k2P3 qP3)) (SC.b v)
abbrev bLeftC (D : OddSurfaceDistance) (v : Bool) : SFormula 3 :=
  .eqBool (SC.closed (leftClassGuardTA (dP3 D) k2P3)) (SC.b v)
abbrev bLeftB (D : OddSurfaceDistance) (v : Bool) : SFormula 3 :=
  .eqBool (SC.closed (leftBandGuardTA (dP3 D) k2P3 qP3)) (SC.b v)
abbrev bBotB (D : OddSurfaceDistance) (v : Bool) : SFormula 3 :=
  .eqBool (SC.closed (bottomBandGuardTA (dP3 D) k2P3 qP3)) (SC.b v)

/-! ## Anti-commutation literal facts (Pauli pairs) -/

def antiP {Δ : List (SFormula 3)} (p1 p2 : Pauli)
    (h : ErrorVec.Pauli.anticommutes p1 p2 = false) :
    SFormula.Deriv Δ (.eqBool (.anticommutes (SC.p p1) (SC.p p2)) (SC.b false)) := by
  have := SFormula.Deriv.pauliAnticommutesLit (Γ := Δ) p1 p2
  simpa [h] using this

/-! ## Identity-entry local commutation (sorry-free, complete)

When EITHER row's entry resolves to `I` at the bound qubit, the two rows commute
locally there — independently of the other entry.  This is the workhorse for the
qubits outside one of the supports (the overwhelming majority of qubits for any
pair).  Built from `localCommutesOfLeftI` / `localCommutesOfRightI` and the flat
entry. -/

/-- Local commutation when row A's leaf resolves to `I`. -/
def lcFromLeftI {Δ : List (SFormula 3)} (D : OddSurfaceDistance)
    (hEntryA : SFormula.Deriv Δ (entryAF D))
    (hLeafA : SFormula.Deriv Δ
      (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3)) (SC.p Pauli.I))) :
    SFormula.Deriv Δ (lcGoalP D) := by
  refine SFormula.Deriv.localCommutesOfLeftI _ _ _ ?_
  rw [rowA_weaken]; exact SFormula.Deriv.eqPauliTrans _ _ _ hEntryA hLeafA

/-- Local commutation when row B's leaf resolves to `I`. -/
def lcFromRightI {Δ : List (SFormula 3)} (D : OddSurfaceDistance)
    (hEntryB : SFormula.Deriv Δ (entryBF D))
    (hLeafB : SFormula.Deriv Δ
      (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p Pauli.I))) :
    SFormula.Deriv Δ (lcGoalP D) := by
  refine SFormula.Deriv.localCommutesOfRightI _ _ _ ?_
  rw [rowB_weaken]; exact SFormula.Deriv.eqPauliTrans _ _ _ hEntryB hLeafB

/-! ## Single-row leaf resolver (continuation-passing `boolCases` cascade)

`withLeafA D goal handler` performs the full `boolCases` cascade over row A's
cell-classification guards (`bulkGuardTA`, `baseBulkBandGuardTA`, `baseKindGuardTA`,
the four boundary class guards, and their band guards), resolving
`baseLeafTreeTA (dP3 D) k1P3 qP3` to a literal Pauli in every branch.  In each
branch it calls `handler` with:
* the deepened context `Δ'`;
* a weakening `lift : Δ → Δ'`;
* the resolved leaf Pauli `p`;
* a derivation that `baseLeafTreeTA (dP3 D) k1P3 qP3 = p` in `Δ'`.

The handler closes the goal `C`.  This factors the 11-leaf cascade once for row A;
the row-B version `withLeafB` is identical with `k2P3`.  No two-anti content here —
purely the leaf resolution. -/

/-- A per-row leaf-handler triple: continuations for the `I`, `X`, and `Z` leaf
outcomes (the only Paulis `baseLeafTreeTA` produces), each receiving the deepened
context, the weakening, and the resolved leaf equality. -/
structure LeafHandlers (Δ : List (SFormula 3)) (D : OddSurfaceDistance)
    (kT : Term 3 .nat) (C : SFormula 3) where
  hI : ∀ (Δ' : List (SFormula 3)),
    (∀ {A : SFormula 3}, SFormula.Deriv Δ A → SFormula.Deriv Δ' A) →
    SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) kT qP3)) (SC.p Pauli.I)) →
      SFormula.Deriv Δ' C
  hX : ∀ (Δ' : List (SFormula 3)),
    (∀ {A : SFormula 3}, SFormula.Deriv Δ A → SFormula.Deriv Δ' A) →
    SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) kT qP3)) (SC.p Pauli.X)) →
      SFormula.Deriv Δ' C
  hZ : ∀ (Δ' : List (SFormula 3)),
    (∀ {A : SFormula 3}, SFormula.Deriv Δ A → SFormula.Deriv Δ' A) →
    SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) kT qP3)) (SC.p Pauli.Z)) →
      SFormula.Deriv Δ' C

/-- Row-A leaf resolver (dispatches into the three-way handler triple). -/
def withLeafA {Δ : List (SFormula 3)} (D : OddSurfaceDistance) (C : SFormula 3)
    (H : LeafHandlers Δ D k1P3 C) :
    SFormula.Deriv Δ C := by
  refine SFormula.Deriv.boolCases (SC.closed (bulkGuardTA (dP3 D) k1P3)) _ ?_ ?_
  · -- bulk TRUE
    refine SFormula.Deriv.boolCases (SC.closed (baseBulkBandGuardTA (dP3 D) k1P3 qP3)) _ ?_ ?_
    · -- band TRUE
      refine SFormula.Deriv.boolCases (SC.closed (baseKindGuardTA (dP3 D) k1P3)) _ ?_ ?_
      · exact H.hZ _ (fun h => cw3 h)
          (baseLeafZ _ _ _ (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption)
      · exact H.hX _ (fun h => cw3 h)
          (baseLeafBulkX _ _ _ (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption)
    · exact H.hI _ (fun h => cw2 h)
        (baseLeafBulkI _ _ _ (.hyp (by right; left)) .assumption)
  · -- bulk FALSE
    refine SFormula.Deriv.boolCases (SC.closed (topClassGuardTA (dP3 D) k1P3)) _ ?_ ?_
    · refine SFormula.Deriv.boolCases (SC.closed (topBandGuardTA (dP3 D) k1P3 qP3)) _ ?_ ?_
      · exact H.hX _ (fun h => cw3 h)
          (baseLeafTopX _ _ _ (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption)
      · exact H.hI _ (fun h => cw3 h)
          (baseLeafTopI _ _ _ (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption)
    · refine SFormula.Deriv.boolCases (SC.closed (rightClassGuardTA (dP3 D) k1P3)) _ ?_ ?_
      · refine SFormula.Deriv.boolCases (SC.closed (rightBandGuardTA (dP3 D) k1P3 qP3)) _ ?_ ?_
        · exact H.hZ _ (fun h => cw4 h)
            (baseLeafRightZ _ _ _ (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
              (.hyp (by right; left)) .assumption)
        · exact H.hI _ (fun h => cw4 h)
            (baseLeafRightI _ _ _ (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
              (.hyp (by right; left)) .assumption)
      · refine SFormula.Deriv.boolCases (SC.closed (leftClassGuardTA (dP3 D) k1P3)) _ ?_ ?_
        · refine SFormula.Deriv.boolCases (SC.closed (leftBandGuardTA (dP3 D) k1P3 qP3)) _ ?_ ?_
          · exact H.hZ _ (fun h => cw5 h)
              (baseLeafLeftZ _ _ _ (.hyp (by right; right; right; right; left))
                (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
                (.hyp (by right; left)) .assumption)
          · exact H.hI _ (fun h => cw5 h)
              (baseLeafLeftI _ _ _ (.hyp (by right; right; right; right; left))
                (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
                (.hyp (by right; left)) .assumption)
        · refine SFormula.Deriv.boolCases (SC.closed (bottomBandGuardTA (dP3 D) k1P3 qP3)) _ ?_ ?_
          · exact H.hX _ (fun h => cw5 h)
              (baseLeafBottomX _ _ _ (.hyp (by right; right; right; right; left))
                (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
                (.hyp (by right; left)) .assumption)
          · exact H.hI _ (fun h => cw5 h)
              (baseLeafBottomI _ _ _ (.hyp (by right; right; right; right; left))
                (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
                (.hyp (by right; left)) .assumption)

/-- Row-B leaf resolver (identical cascade with `k2P3`). -/
def withLeafB {Δ : List (SFormula 3)} (D : OddSurfaceDistance) (C : SFormula 3)
    (H : LeafHandlers Δ D k2P3 C) :
    SFormula.Deriv Δ C := by
  refine SFormula.Deriv.boolCases (SC.closed (bulkGuardTA (dP3 D) k2P3)) _ ?_ ?_
  · refine SFormula.Deriv.boolCases (SC.closed (baseBulkBandGuardTA (dP3 D) k2P3 qP3)) _ ?_ ?_
    · refine SFormula.Deriv.boolCases (SC.closed (baseKindGuardTA (dP3 D) k2P3)) _ ?_ ?_
      · exact H.hZ _ (fun h => cw3 h)
          (baseLeafZ _ _ _ (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption)
      · exact H.hX _ (fun h => cw3 h)
          (baseLeafBulkX _ _ _ (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption)
    · exact H.hI _ (fun h => cw2 h)
        (baseLeafBulkI _ _ _ (.hyp (by right; left)) .assumption)
  · refine SFormula.Deriv.boolCases (SC.closed (topClassGuardTA (dP3 D) k2P3)) _ ?_ ?_
    · refine SFormula.Deriv.boolCases (SC.closed (topBandGuardTA (dP3 D) k2P3 qP3)) _ ?_ ?_
      · exact H.hX _ (fun h => cw3 h)
          (baseLeafTopX _ _ _ (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption)
      · exact H.hI _ (fun h => cw3 h)
          (baseLeafTopI _ _ _ (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption)
    · refine SFormula.Deriv.boolCases (SC.closed (rightClassGuardTA (dP3 D) k2P3)) _ ?_ ?_
      · refine SFormula.Deriv.boolCases (SC.closed (rightBandGuardTA (dP3 D) k2P3 qP3)) _ ?_ ?_
        · exact H.hZ _ (fun h => cw4 h)
            (baseLeafRightZ _ _ _ (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
              (.hyp (by right; left)) .assumption)
        · exact H.hI _ (fun h => cw4 h)
            (baseLeafRightI _ _ _ (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
              (.hyp (by right; left)) .assumption)
      · refine SFormula.Deriv.boolCases (SC.closed (leftClassGuardTA (dP3 D) k2P3)) _ ?_ ?_
        · refine SFormula.Deriv.boolCases (SC.closed (leftBandGuardTA (dP3 D) k2P3 qP3)) _ ?_ ?_
          · exact H.hZ _ (fun h => cw5 h)
              (baseLeafLeftZ _ _ _ (.hyp (by right; right; right; right; left))
                (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
                (.hyp (by right; left)) .assumption)
          · exact H.hI _ (fun h => cw5 h)
              (baseLeafLeftI _ _ _ (.hyp (by right; right; right; right; left))
                (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
                (.hyp (by right; left)) .assumption)
        · refine SFormula.Deriv.boolCases (SC.closed (bottomBandGuardTA (dP3 D) k2P3 qP3)) _ ?_ ?_
          · exact H.hX _ (fun h => cw5 h)
              (baseLeafBottomX _ _ _ (.hyp (by right; right; right; right; left))
                (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
                (.hyp (by right; left)) .assumption)
          · exact H.hI _ (fun h => cw5 h)
              (baseLeafBottomI _ _ _ (.hyp (by right; right; right; right; left))
                (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
                (.hyp (by right; left)) .assumption)

/-! ## Guard-exposing leaf resolvers

`withLeafA`/`withLeafB` discard the cell-classification guards that produced each
leaf.  For the SAME-type vacuity contradictions we need those guards (an X-type row
that produced a `Z` leaf must be in a `Z`-producing class — `bulk∧kind`, `right`,
or `left` — contradicting `isXType`).  `withLeafAG`/`withLeafBG` re-run the same
cascade but call PER-BRANCH handlers that receive the branch's class guards. -/

/-- Per-branch guard-exposing handler set for one row (index `kT`). -/
structure LeafHandlersG (Δ : List (SFormula 3)) (D : OddSurfaceDistance)
    (kT : Term 3 .nat) (C : SFormula 3) where
  /-- `I` leaf (any branch). -/
  hI : ∀ (Δ' : List (SFormula 3)),
    (∀ {A : SFormula 3}, SFormula.Deriv Δ A → SFormula.Deriv Δ' A) →
    SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) kT qP3)) (SC.p Pauli.I)) →
      SFormula.Deriv Δ' C
  /-- bulk-`Z`: `bulk = true`, `kind = true`. -/
  hBulkZ : ∀ (Δ' : List (SFormula 3)),
    (∀ {A : SFormula 3}, SFormula.Deriv Δ A → SFormula.Deriv Δ' A) →
    SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) kT qP3)) (SC.p Pauli.Z)) →
    SFormula.Deriv Δ' (.eqBool (SC.closed (bulkGuardTA (dP3 D) kT)) (SC.b true)) →
    SFormula.Deriv Δ' (.eqBool (SC.closed (baseKindGuardTA (dP3 D) kT)) (SC.b true)) →
      SFormula.Deriv Δ' C
  /-- bulk-`X`: `bulk = true`, `kind = false`. -/
  hBulkX : ∀ (Δ' : List (SFormula 3)),
    (∀ {A : SFormula 3}, SFormula.Deriv Δ A → SFormula.Deriv Δ' A) →
    SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) kT qP3)) (SC.p Pauli.X)) →
    SFormula.Deriv Δ' (.eqBool (SC.closed (bulkGuardTA (dP3 D) kT)) (SC.b true)) →
    SFormula.Deriv Δ' (.eqBool (SC.closed (baseKindGuardTA (dP3 D) kT)) (SC.b false)) →
      SFormula.Deriv Δ' C
  /-- top-`X`: `bulk = false`, `topClass = true`. -/
  hTopX : ∀ (Δ' : List (SFormula 3)),
    (∀ {A : SFormula 3}, SFormula.Deriv Δ A → SFormula.Deriv Δ' A) →
    SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) kT qP3)) (SC.p Pauli.X)) →
    SFormula.Deriv Δ' (.eqBool (SC.closed (bulkGuardTA (dP3 D) kT)) (SC.b false)) →
    SFormula.Deriv Δ' (.eqBool (SC.closed (topClassGuardTA (dP3 D) kT)) (SC.b true)) →
      SFormula.Deriv Δ' C
  /-- right-`Z`: `bulk = false`, `topClass = false`, `rightClass = true`. -/
  hRightZ : ∀ (Δ' : List (SFormula 3)),
    (∀ {A : SFormula 3}, SFormula.Deriv Δ A → SFormula.Deriv Δ' A) →
    SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) kT qP3)) (SC.p Pauli.Z)) →
    SFormula.Deriv Δ' (.eqBool (SC.closed (bulkGuardTA (dP3 D) kT)) (SC.b false)) →
    SFormula.Deriv Δ' (.eqBool (SC.closed (topClassGuardTA (dP3 D) kT)) (SC.b false)) →
    SFormula.Deriv Δ' (.eqBool (SC.closed (rightClassGuardTA (dP3 D) kT)) (SC.b true)) →
      SFormula.Deriv Δ' C
  /-- left-`Z`: `bulk = false`, `topClass = false`, `rightClass = false`, `leftClass = true`. -/
  hLeftZ : ∀ (Δ' : List (SFormula 3)),
    (∀ {A : SFormula 3}, SFormula.Deriv Δ A → SFormula.Deriv Δ' A) →
    SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) kT qP3)) (SC.p Pauli.Z)) →
    SFormula.Deriv Δ' (.eqBool (SC.closed (bulkGuardTA (dP3 D) kT)) (SC.b false)) →
    SFormula.Deriv Δ' (.eqBool (SC.closed (topClassGuardTA (dP3 D) kT)) (SC.b false)) →
    SFormula.Deriv Δ' (.eqBool (SC.closed (rightClassGuardTA (dP3 D) kT)) (SC.b false)) →
    SFormula.Deriv Δ' (.eqBool (SC.closed (leftClassGuardTA (dP3 D) kT)) (SC.b true)) →
      SFormula.Deriv Δ' C
  /-- bottom-`X`: `bulk = false`, `topClass = false`, `rightClass = false`, `leftClass = false`. -/
  hBottomX : ∀ (Δ' : List (SFormula 3)),
    (∀ {A : SFormula 3}, SFormula.Deriv Δ A → SFormula.Deriv Δ' A) →
    SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) kT qP3)) (SC.p Pauli.X)) →
    SFormula.Deriv Δ' (.eqBool (SC.closed (bulkGuardTA (dP3 D) kT)) (SC.b false)) →
    SFormula.Deriv Δ' (.eqBool (SC.closed (topClassGuardTA (dP3 D) kT)) (SC.b false)) →
    SFormula.Deriv Δ' (.eqBool (SC.closed (rightClassGuardTA (dP3 D) kT)) (SC.b false)) →
    SFormula.Deriv Δ' (.eqBool (SC.closed (leftClassGuardTA (dP3 D) kT)) (SC.b false)) →
      SFormula.Deriv Δ' C

/-- Guard-exposing row resolver (generic index `kT`).  Identical cascade to
`withLeafA`/`withLeafB`, dispatching into the per-branch handler set. -/
def withLeafG {Δ : List (SFormula 3)} (D : OddSurfaceDistance) (kT : Term 3 .nat)
    (C : SFormula 3) (H : LeafHandlersG Δ D kT C) :
    SFormula.Deriv Δ C := by
  refine SFormula.Deriv.boolCases (SC.closed (bulkGuardTA (dP3 D) kT)) _ ?_ ?_
  · refine SFormula.Deriv.boolCases (SC.closed (baseBulkBandGuardTA (dP3 D) kT qP3)) _ ?_ ?_
    · refine SFormula.Deriv.boolCases (SC.closed (baseKindGuardTA (dP3 D) kT)) _ ?_ ?_
      · exact H.hBulkZ _ (fun h => cw3 h)
          (baseLeafZ _ _ _ (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption)
          (.hyp (by right; right; left)) .assumption
      · exact H.hBulkX _ (fun h => cw3 h)
          (baseLeafBulkX _ _ _ (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption)
          (.hyp (by right; right; left)) .assumption
    · exact H.hI _ (fun h => cw2 h)
        (baseLeafBulkI _ _ _ (.hyp (by right; left)) .assumption)
  · refine SFormula.Deriv.boolCases (SC.closed (topClassGuardTA (dP3 D) kT)) _ ?_ ?_
    · refine SFormula.Deriv.boolCases (SC.closed (topBandGuardTA (dP3 D) kT qP3)) _ ?_ ?_
      · exact H.hTopX _ (fun h => cw3 h)
          (baseLeafTopX _ _ _ (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption)
          (.hyp (by right; right; left)) (.hyp (by right; left))
      · exact H.hI _ (fun h => cw3 h)
          (baseLeafTopI _ _ _ (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption)
    · refine SFormula.Deriv.boolCases (SC.closed (rightClassGuardTA (dP3 D) kT)) _ ?_ ?_
      · refine SFormula.Deriv.boolCases (SC.closed (rightBandGuardTA (dP3 D) kT qP3)) _ ?_ ?_
        · exact H.hRightZ _ (fun h => cw4 h)
            (baseLeafRightZ _ _ _ (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
              (.hyp (by right; left)) .assumption)
            (.hyp (by right; right; right; left)) (.hyp (by right; right; left)) (.hyp (by right; left))
        · exact H.hI _ (fun h => cw4 h)
            (baseLeafRightI _ _ _ (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
              (.hyp (by right; left)) .assumption)
      · refine SFormula.Deriv.boolCases (SC.closed (leftClassGuardTA (dP3 D) kT)) _ ?_ ?_
        · refine SFormula.Deriv.boolCases (SC.closed (leftBandGuardTA (dP3 D) kT qP3)) _ ?_ ?_
          · exact H.hLeftZ _ (fun h => cw5 h)
              (baseLeafLeftZ _ _ _ (.hyp (by right; right; right; right; left))
                (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
                (.hyp (by right; left)) .assumption)
              (.hyp (by right; right; right; right; left)) (.hyp (by right; right; right; left))
              (.hyp (by right; right; left)) (.hyp (by right; left))
          · exact H.hI _ (fun h => cw5 h)
              (baseLeafLeftI _ _ _ (.hyp (by right; right; right; right; left))
                (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
                (.hyp (by right; left)) .assumption)
        · refine SFormula.Deriv.boolCases (SC.closed (bottomBandGuardTA (dP3 D) kT qP3)) _ ?_ ?_
          · exact H.hBottomX _ (fun h => cw5 h)
              (baseLeafBottomX _ _ _ (.hyp (by right; right; right; right; left))
                (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
                (.hyp (by right; left)) .assumption)
              (.hyp (by right; right; right; right; left)) (.hyp (by right; right; right; left))
              (.hyp (by right; right; left)) (.hyp (by right; left))
          · exact H.hI _ (fun h => cw5 h)
              (baseLeafBottomI _ _ _ (.hyp (by right; right; right; right; left))
                (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
                (.hyp (by right; left)) .assumption)

/-! ## The full local-commutation dispatcher

Resolve BOTH row leaves and dispatch on the (pa, pb) Pauli pair:
* either is `I`, or both equal → commute via `lcFromLeftI`/`lcFromRightI`/`lcFromTwoLeaves`;
* the two genuinely-anticommuting pairs `(X, Z)` and `(Z, X)` are delegated to the
  handlers `hAntiXZ` / `hAntiZX` (they receive the deepened context with both leaf
  equalities; in the pointwise branch they are vacuous, in the two-anti branch they
  use the qubit exclusions). -/

/-- For commuting Pauli pairs, `anticommutes pb pa = false` is decidable to `false`. -/
private def antiFalseOfCommute (pa pb : Pauli)
    (h : ErrorVec.Pauli.anticommutes pb pa = false) {Δ : List (SFormula 3)} :
    SFormula.Deriv Δ (.eqBool (.anticommutes (SC.p pb) (SC.p pa)) (SC.b false)) :=
  antiP pb pa h

/-- The full local-commutation dispatcher.  Resolves BOTH row leaves into one of
`{I, X, Z}` and dispatches on the (pa, pb) pair.  The genuinely-anticommuting
`(X, Z)` / `(Z, X)` leaf-pairs are delegated to the handlers; all other pairs
commute and are closed here via `lcFromLeftI` / `lcFromRightI` / `lcFromTwoLeaves`. -/
def localDispatch {Δ : List (SFormula 3)} (D : OddSurfaceDistance)
    (hEntryA : SFormula.Deriv Δ (entryAF D))
    (hEntryB : SFormula.Deriv Δ (entryBF D))
    (hAntiXZ : ∀ (Δ' : List (SFormula 3)),
      (∀ {A : SFormula 3}, SFormula.Deriv Δ A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3)) (SC.p Pauli.X)) →
      SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p Pauli.Z)) →
        SFormula.Deriv Δ' (lcGoalP D))
    (hAntiZX : ∀ (Δ' : List (SFormula 3)),
      (∀ {A : SFormula 3}, SFormula.Deriv Δ A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3)) (SC.p Pauli.Z)) →
      SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p Pauli.X)) →
        SFormula.Deriv Δ' (lcGoalP D)) :
    SFormula.Deriv Δ (lcGoalP D) := by
  refine withLeafA D _ ⟨?_, ?_, ?_⟩
  · -- A leaf I → left I (commute regardless of B)
    intro Δ1 lift1 hLeafA
    exact lcFromLeftI D (lift1 hEntryA) hLeafA
  · -- A leaf X
    intro Δ1 lift1 hLeafA
    refine withLeafB D _ ⟨?_, ?_, ?_⟩
    · -- B leaf I → right I
      intro Δ2 lift2 hLeafB
      exact lcFromRightI D (lift2 (lift1 hEntryB)) hLeafB
    · -- (X, X) → commute
      intro Δ2 lift2 hLeafB
      exact lcFromTwoLeaves D Pauli.X Pauli.X (lift2 (lift1 hEntryA)) (lift2 hLeafA)
        (lift2 (lift1 hEntryB)) hLeafB (antiP Pauli.X Pauli.X rfl)
    · -- (X, Z) → anti handler
      intro Δ2 lift2 hLeafB
      exact hAntiXZ Δ2 (fun h => lift2 (lift1 h)) (lift2 hLeafA) hLeafB
  · -- A leaf Z
    intro Δ1 lift1 hLeafA
    refine withLeafB D _ ⟨?_, ?_, ?_⟩
    · -- B leaf I → right I
      intro Δ2 lift2 hLeafB
      exact lcFromRightI D (lift2 (lift1 hEntryB)) hLeafB
    · -- (Z, X) → anti handler
      intro Δ2 lift2 hLeafB
      exact hAntiZX Δ2 (fun h => lift2 (lift1 h)) (lift2 hLeafA) hLeafB
    · -- (Z, Z) → commute
      intro Δ2 lift2 hLeafB
      exact lcFromTwoLeaves D Pauli.Z Pauli.Z (lift2 (lift1 hEntryA)) (lift2 hLeafA)
        (lift2 (lift1 hEntryB)) hLeafB (antiP Pauli.Z Pauli.Z rfl)

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

/-! ### Same-type pair commutation (both X-type, or both Z-type)

A same-type pair never overlaps, so both `localDispatch` anti-handlers are vacuous.
We discharge them by RE-RESOLVING the offending row's leaf with guards exposed
(`withLeafG`) and contradicting:
* an `I`/`X` re-resolution against the `Z` leaf value (`leafNotPandZ`);
* a `Z` re-resolution (bulk-`Z`/right-`Z`/left-`Z` class guards) against the row's
  X-type fact via the `typeExcl` arithmetic pack. -/

/-- Both rows X-type ⟹ pair commutes. -/
def pairCommuteSameTypeX {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hEntryAF : SFormula.Deriv Γ (entryAQuant D))
    (hEntryBF : SFormula.Deriv Γ (entryBQuant D))
    (hk1X : SFormula.Deriv Γ (k1IsX D true))
    (hk2X : SFormula.Deriv Γ (k2IsX D true))
    (hExcl1 : SFormula.Deriv Γ (typeExclF D k1P))
    (hExcl2 : SFormula.Deriv Γ (typeExclF D k2P)) :
    SFormula.Deriv Γ (pairGoal D) := by
  refine pairCommutePointwise D hEntryAF hEntryBF ?_ ?_
  · -- (X, Z): A leaf = X, B leaf = Z.  B is X-type → re-resolve B, contradict.
    intro Δ' lift hLeafA hLeafB
    -- type fact + exclusion pack for k2 in Δ'.
    have hk2Xd : SFormula.Deriv Δ' (k2IsX D true).weaken :=
      lift (cw1 (SFormula.Deriv.weakenFresh (A := k2IsX D true) hk2X))
    have hExcl2d : SFormula.Deriv Δ' (typeExclF D k2P).weaken :=
      lift (cw1 (SFormula.Deriv.weakenFresh (A := typeExclF D k2P) hExcl2))
    have hxnbz := SFormula.Deriv.andElimLeft hExcl2d
    have hxnrz := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hExcl2d)
    have hxnlz := SFormula.Deriv.andElimLeft
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hExcl2d))
    refine withLeafG D k2P3 _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- I vs Z
      intro Δ'' lift2 hI
      exact leafNotPandZ D k2P3 Pauli.I rfl hI (lift2 hLeafB)
    · -- bulkZ: bulk=true, kind=true; exclusion gives kind=false.
      intro Δ'' lift2 _ hbulk hkind
      have hkindF := SFormula.Deriv.mp (SFormula.Deriv.mp (lift2 hxnbz) (lift2 hk2Xd)) hbulk
      exact eqBoolContra _ hkind hkindF
    · -- bulkX vs Z
      intro Δ'' lift2 hX _ _
      exact leafNotPandZ D k2P3 Pauli.X rfl hX (lift2 hLeafB)
    · -- topX vs Z
      intro Δ'' lift2 hX _ _
      exact leafNotPandZ D k2P3 Pauli.X rfl hX (lift2 hLeafB)
    · -- rightZ: bulk=false, top=false, right=true; exclusion gives right=false.
      intro Δ'' lift2 _ hbulk htop hright
      have hrightF := SFormula.Deriv.mp (SFormula.Deriv.mp
        (SFormula.Deriv.mp (lift2 hxnrz) (lift2 hk2Xd)) hbulk) htop
      exact eqBoolContra _ hright hrightF
    · -- leftZ: exclusion gives left=false.
      intro Δ'' lift2 _ hbulk htop hright hleft
      have hleftF := SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp
        (SFormula.Deriv.mp (lift2 hxnlz) (lift2 hk2Xd)) hbulk) htop) hright
      exact eqBoolContra _ hleft hleftF
    · -- bottomX vs Z
      intro Δ'' lift2 hX _ _ _ _
      exact leafNotPandZ D k2P3 Pauli.X rfl hX (lift2 hLeafB)
  · -- (Z, X): A leaf = Z, B leaf = X.  A is X-type → re-resolve A, contradict.
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

/-- Both rows Z-type ⟹ pair commutes.  Dual of `pairCommuteSameTypeX`: a Z-type row
never produces an `X` leaf, so the offending `X` leaf is re-resolved and contradicted
via the `ztNotBulkXF`/`ztNotTopXF`/`ztNotBottomXF` arithmetic exclusions, while the
`Z` re-resolutions contradict the `X` leaf value. -/
def pairCommuteSameTypeZ {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hEntryAF : SFormula.Deriv Γ (entryAQuant D))
    (hEntryBF : SFormula.Deriv Γ (entryBQuant D))
    (hk1X : SFormula.Deriv Γ (k1IsX D false))
    (hk2X : SFormula.Deriv Γ (k2IsX D false))
    (hExcl1 : SFormula.Deriv Γ (typeExclF D k1P))
    (hExcl2 : SFormula.Deriv Γ (typeExclF D k2P)) :
    SFormula.Deriv Γ (pairGoal D) := by
  refine pairCommutePointwise D hEntryAF hEntryBF ?_ ?_
  · -- (X, Z): A leaf = X, B leaf = Z.  A is Z-type → re-resolve A, contradict.
    intro Δ' lift hLeafA hLeafB
    have hk1Xd : SFormula.Deriv Δ' (k1IsX D false).weaken :=
      lift (cw1 (SFormula.Deriv.weakenFresh (A := k1IsX D false) hk1X))
    have hExcl1d : SFormula.Deriv Δ' (typeExclF D k1P).weaken :=
      lift (cw1 (SFormula.Deriv.weakenFresh (A := typeExclF D k1P) hExcl1))
    have hznbx := SFormula.Deriv.andElimLeft
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hExcl1d)))
    have hzntx := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hExcl1d))))
    have hznbtx := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hExcl1d))))
    refine withLeafG D k1P3 _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- I vs X
      intro Δ'' lift2 hI
      exact leafNotPandX D k1P3 Pauli.I rfl hI (lift2 hLeafA)
    · -- bulkZ vs X
      intro Δ'' lift2 hZ _ _
      exact leafNotPandX D k1P3 Pauli.Z rfl hZ (lift2 hLeafA)
    · -- bulkX: bulk=true, kind=false; exclusion gives kind=true.
      intro Δ'' lift2 _ hbulk hkind
      have hkindT := SFormula.Deriv.mp (SFormula.Deriv.mp (lift2 hznbx) (lift2 hk1Xd)) hbulk
      exact eqBoolContra _ hkindT hkind
    · -- topX: bulk=false, top=true; exclusion gives top=false.
      intro Δ'' lift2 _ hbulk htop
      have htopF := SFormula.Deriv.mp (SFormula.Deriv.mp (lift2 hzntx) (lift2 hk1Xd)) hbulk
      exact eqBoolContra _ htop htopF
    · -- rightZ vs X
      intro Δ'' lift2 hZ _ _ _
      exact leafNotPandX D k1P3 Pauli.Z rfl hZ (lift2 hLeafA)
    · -- leftZ vs X
      intro Δ'' lift2 hZ _ _ _ _
      exact leafNotPandX D k1P3 Pauli.Z rfl hZ (lift2 hLeafA)
    · -- bottomX: bulk=false, top=false, right=false, left=false; exclusion gives left=true.
      intro Δ'' lift2 _ hbulk htop _ hleft
      have hleftT := SFormula.Deriv.mp (SFormula.Deriv.mp
        (SFormula.Deriv.mp (lift2 hznbtx) (lift2 hk1Xd)) hbulk) htop
      exact eqBoolContra _ hleftT hleft
  · -- (Z, X): A leaf = Z, B leaf = X.  B is Z-type → re-resolve B, contradict.
    intro Δ' lift hLeafA hLeafB
    have hk2Xd : SFormula.Deriv Δ' (k2IsX D false).weaken :=
      lift (cw1 (SFormula.Deriv.weakenFresh (A := k2IsX D false) hk2X))
    have hExcl2d : SFormula.Deriv Δ' (typeExclF D k2P).weaken :=
      lift (cw1 (SFormula.Deriv.weakenFresh (A := typeExclF D k2P) hExcl2))
    have hznbx := SFormula.Deriv.andElimLeft
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hExcl2d)))
    have hzntx := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hExcl2d))))
    have hznbtx := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hExcl2d))))
    refine withLeafG D k2P3 _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro Δ'' lift2 hI
      exact leafNotPandX D k2P3 Pauli.I rfl hI (lift2 hLeafB)
    · intro Δ'' lift2 hZ _ _
      exact leafNotPandX D k2P3 Pauli.Z rfl hZ (lift2 hLeafB)
    · intro Δ'' lift2 _ hbulk hkind
      have hkindT := SFormula.Deriv.mp (SFormula.Deriv.mp (lift2 hznbx) (lift2 hk2Xd)) hbulk
      exact eqBoolContra _ hkindT hkind
    · intro Δ'' lift2 _ hbulk htop
      have htopF := SFormula.Deriv.mp (SFormula.Deriv.mp (lift2 hzntx) (lift2 hk2Xd)) hbulk
      exact eqBoolContra _ htop htopF
    · intro Δ'' lift2 hZ _ _ _
      exact leafNotPandX D k2P3 Pauli.Z rfl hZ (lift2 hLeafB)
    · intro Δ'' lift2 hZ _ _ _ _
      exact leafNotPandX D k2P3 Pauli.Z rfl hZ (lift2 hLeafB)
    · intro Δ'' lift2 _ hbulk htop _ hleft
      have hleftT := SFormula.Deriv.mp (SFormula.Deriv.mp
        (SFormula.Deriv.mp (lift2 hznbtx) (lift2 hk2Xd)) hbulk) htop
      exact eqBoolContra _ hleftT hleft

/-- Conjoin two arity-2 family-derivations. -/
def pfdaAnd2 {D : OddSurfaceDistance} {A B : SFormula 2}
    (hA : PureFamilyDerivA Surface.code.body (D.distance + 2) A)
    (hB : PureFamilyDerivA Surface.code.body (D.distance + 2) B) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (.and A B) :=
  PureFamilyDerivA.cut2 (SFormula.Deriv.andIntro .assumption
    (.hyp (by right; exact List.mem_cons_self))) hA hB

/-! ## Generic two-anti closer for the DIFFERENT-type (X-vs-Z) overlapping case

The reusable spine for an overlapping `(X-type, Z-type)` pair, the two-generated-row
analogue of `commTwoAntiA`/`commTwoAntiB` in `SurfaceNormalizers.lean` (there one
operand was a fixed `logicalX`; here both are generated rows resolved via
`rowEntryFlatSym`).  Given:
* the two anti qubits `q0`, `q1` (closed arithmetic terms) with purity witnesses;
* that they are `< nQubits`, distinct;
* that row A resolves to `X` and row B to `Z` at both `q0` and `q1` (the verified
  overlap geometry — `#eval`-confirmed, d = 3,5,7);
* an all-others handler closing local commutation at every qubit `q ∉ {q0, q1}`
  (where the only obstruction is the `(X,Z)` leaf-pair, dispatched via `localDispatch`),

the rows commute by the even-parity rule `commutesOfTwoAnti`.  Each overlap
class-pair supplies `q0`/`q1` and the band-fires / joint-pin packs and plugs in. -/

/-- Row-A entry at a concrete pure qubit term `qT` (arity 2): the flat classifier. -/
def entryAAtQ (D : OddSurfaceDistance) (qT : Term 2 .nat) (hq : SFormula.PureNatTerm qT) :
    PureFamilyDerivA Surface.code.body (D.distance + 2)
      (.eqPauli (.stabAt (SC.closed (.recCall (dP2 D) k1P)) (SC.closed qT))
        (SC.closed (baseLeafTreeTA (dP2 D) k1P qT))) :=
  rowEntryFlatSym (fuel := D.distance + 2) D.index (distP2 D) k1P qT
    (SFormula.PureNatTerm.var ⟨1, by decide⟩) hq

/-- Row-B entry at a concrete pure qubit term `qT` (arity 2): the flat classifier. -/
def entryBAtQ (D : OddSurfaceDistance) (qT : Term 2 .nat) (hq : SFormula.PureNatTerm qT) :
    PureFamilyDerivA Surface.code.body (D.distance + 2)
      (.eqPauli (.stabAt (SC.closed (.recCall (dP2 D) k2P)) (SC.closed qT))
        (SC.closed (baseLeafTreeTA (dP2 D) k2P qT))) :=
  rowEntryFlatSym (fuel := D.distance + 2) D.index (distP2 D) k2P qT
    (SFormula.PureNatTerm.var ⟨0, by decide⟩) hq

/-- The `commutesOfTwoAnti` all-others premise, as a goal abbreviation: local
commutation at `boundNat` for every `q < nQubits` away from `q0`, `q1`. -/
abbrev twoAntiRest (D : OddSurfaceDistance) (q0 q1 : Term 2 .nat) : SFormula 2 :=
  .allNatLt (nP2 D)
    (.imp (.not (.eqNat SFormula.boundNat (SC.closed q0).weaken))
      (.imp (.not (.eqNat SFormula.boundNat (SC.closed q1).weaken))
        (SFormula.localCommutesAt (rowA D).weaken (rowB D).weaken SFormula.boundNat)))

/-- **Generic X-vs-Z two-anti closer.**  Mirrors `commTwoAntiA`: assemble
`commutesOfTwoAnti` from the in-range / distinctness witnesses, the `X`/`Z`
resolutions at `q0`/`q1` (so they anticommute there), and the all-others premise. -/
def commTwoAntiXZ {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (q0 q1 : Term 2 .nat)
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
    (hRest : SFormula.Deriv Γ (twoAntiRest D q0 q1)) :
    SFormula.Deriv Γ (pairGoal D) := by
  refine SFormula.Deriv.commutesOfTwoAnti (nP2 D) (rowA D) (rowB D)
    (SC.closed q0) (SC.closed q1) hLt0 hLt1 ?wne ?wanti0 ?wanti1 hRest
  case wne =>
    refine SFormula.Deriv.notIntro ?_
    refine SFormula.Deriv.notElim
      (SFormula.Deriv.eqNatBoolTrue (Γ := _) q0 q1 .assumption) ?_
    exact SFormula.Deriv.eqBoolFalseNotTrue _ (cw1 hNe)
  case wanti0 =>
    -- A = X, B = Z at q0 ⟹ anticommute (true).
    exact SFormula.Deriv.anticommutesTransport _ (SC.p Pauli.X) _ (SC.p Pauli.Z) (SC.b true)
      hAX0 hBZ0 (SFormula.Deriv.pauliAnticommutesLit Pauli.X Pauli.Z)
  case wanti1 =>
    exact SFormula.Deriv.anticommutesTransport _ (SC.p Pauli.X) _ (SC.p Pauli.Z) (SC.b true)
      hAX1 hBZ1 (SFormula.Deriv.pauliAnticommutesLit Pauli.X Pauli.Z)

/-- **All-others discharger for the X-vs-Z overlapping case.**  Discharges the
`commutesOfTwoAnti` all-others premise `twoAntiRest D q0 q1`.

Row A is X-type (`hk1X`), row B is Z-type (`hk2X`).  After introducing the qubit
binder and the two `≠ q0`/`≠ q1` exclusions, `localDispatch` reduces the obstruction
to the two genuinely-anticommuting leaf-pairs:
* `(Z, X)` (A leaf `Z`) — impossible: A is X-type, contradicted via the type-
  exclusion pack (exactly as in `pairCommuteSameTypeX`'s `(Z,X)` branch);
* `(X, Z)` (A leaf `X`, B leaf `Z`) — the genuine overlap, delegated to `hXZpin`,
  which (per overlap class) re-resolves the two leaves' band guards and pins
  `boundNat ∈ {q0, q1}`, contradicting the two `≠` exclusions.

The `hXZpin` handler receives the deepened qubit-binder context (with both `≠`
exclusions and `boundNat < nQubits` available as the first hyps), plus the `X`/`Z`
leaf facts; it must close `lcGoalP D` (typically `botElim` after the pin). -/
def twoAntiRestXZ {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (q0 q1 : Term 2 .nat)
    (hEntryAF : SFormula.Deriv Γ (entryAQuant D))
    (hEntryBF : SFormula.Deriv Γ (entryBQuant D))
    (hk1X : SFormula.Deriv Γ (k1IsX D true))
    (hExcl1 : SFormula.Deriv Γ (typeExclF D k1P))
    (hXZpin : ∀ (Δ' : List (SFormula 3)),
      (∀ {A : SFormula 3}, SFormula.Deriv
        (.not (.eqNat SFormula.boundNat (SC.closed q1).weaken)
          :: .not (.eqNat SFormula.boundNat (SC.closed q0).weaken)
          :: SFormula.boundNatLt (nP2 D) :: List.map (fun G => G.weaken) Γ) A →
        SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k1P3 qP3)) (SC.p Pauli.X)) →
      SFormula.Deriv Δ' (.eqPauli (SC.closed (baseLeafTreeTA (dP3 D) k2P3 qP3)) (SC.p Pauli.Z)) →
        SFormula.Deriv Δ' (lcGoalP D)) :
    SFormula.Deriv Γ (twoAntiRest D q0 q1) := by
  unfold twoAntiRest
  refine SFormula.Deriv.allNatLtIntroBounded _ _ ?_
  refine SFormula.Deriv.impIntro (SFormula.Deriv.impIntro ?_)
  -- context Δ0 := [¬q=q1, ¬q=q0, boundNatLt (nP2 D), Γ.map weaken]
  set Δ0 : List (SFormula 3) :=
    .not (.eqNat SFormula.boundNat (SC.closed q1).weaken)
      :: .not (.eqNat SFormula.boundNat (SC.closed q0).weaken)
      :: SFormula.boundNatLt (nP2 D) :: List.map (fun G => G.weaken) Γ with hΔ0
  -- the local-commutation goal is exactly `lcGoalP D`.
  have hgoalEq : SFormula.localCommutesAt (rowA D).weaken (rowB D).weaken SFormula.boundNat
      = lcGoalP D := rfl
  rw [hgoalEq]
  -- qubit-in-range, entries at the qubit binder.
  have hq : SFormula.Deriv Δ0 (SFormula.witnessLt SFormula.boundNat (nP2 D).weaken) :=
    SFormula.Deriv.hyp (by rw [hΔ0]; right; right; exact List.mem_cons_self)
  have hEntryAW : SFormula.Deriv Δ0 (entryAQuant D).weaken :=
    cw3 (SFormula.Deriv.weakenFresh (A := entryAQuant D) hEntryAF)
  have hEntryBW : SFormula.Deriv Δ0 (entryBQuant D).weaken :=
    cw3 (SFormula.Deriv.weakenFresh (A := entryBQuant D) hEntryBF)
  have hEntryA := entryAAtBound D hEntryAW hq
  have hEntryB := entryBAtBound D hEntryBW hq
  refine localDispatch D hEntryA hEntryB ?hXZ ?hZX
  · -- (X, Z): the genuine overlap → delegate to the pin handler.
    intro Δ' lift hLeafA hLeafB
    exact hXZpin Δ' (fun h => lift h) hLeafA hLeafB
  · -- (Z, X): A leaf = Z impossible since A is X-type → type-exclusion contradiction.
    intro Δ' lift hLeafA hLeafB
    have hk1Xd : SFormula.Deriv Δ' (k1IsX D true).weaken :=
      lift (cw3 (SFormula.Deriv.weakenFresh (A := k1IsX D true) hk1X))
    have hExcl1d : SFormula.Deriv Δ' (typeExclF D k1P).weaken :=
      lift (cw3 (SFormula.Deriv.weakenFresh (A := typeExclF D k1P) hExcl1))
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

/-! ## Mega-pack bundle and top-level (X,Z) router

`megaPacksF` is the `.and`-conjunction of all nine per-combo `PacksF` super-bundles,
in the fixed RIGHT-NESTED association (combo order: bulk–bulk, bulk–right, bulk–left,
top–bulk, bottom–bulk, top–right, top–left, bottom–right, bottom–left):

  dbbPacksF ∧ (dbrPacksF ∧ (dblPacksF ∧ (dtbPacksF ∧ (dbtbPacksF ∧
    (dtrPacksF ∧ (dtlPacksF ∧ (dbtrPacksF ∧ dbtlPacksF)))))))

`megaPacks` is the matching right-nested `pfdaAnd2` chain of the nine `Packs`. -/
abbrev megaPacksF (D : OddSurfaceDistance) : SFormula 2 :=
  .and (dbbPacksF D) (.and (dbrPacksF D) (.and (dblPacksF D) (.and (dtbPacksF D)
    (.and (dbtbPacksF D) (.and (dtrPacksF D) (.and (dtlPacksF D)
      (.and (dbtrPacksF D) (dbtlPacksF D))))))))

def megaPacks (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (megaPacksF D) :=
  pfdaAnd2 (dbbPacks D) (pfdaAnd2 (dbrPacks D) (pfdaAnd2 (dblPacks D) (pfdaAnd2 (dtbPacks D)
    (pfdaAnd2 (dbtbPacks D) (pfdaAnd2 (dtrPacks D) (pfdaAnd2 (dtlPacks D)
      (pfdaAnd2 (dbtrPacks D) (dbtlPacks D))))))))

#print axioms megaPacks

/-- **Top-level (X,Z) class-combo router.**

`k1` is X-type (`hkAX`), `k2` is Z-type (`hkBZ`).  A `boolCases` TREE on the bulk /
top / right / left class guards of both rows establishes each of the nine concrete
class contexts and dispatches to the matching combo dispatcher, extracting the
combo's `PacksF` super-bundle from `hmega` (the right-nested mega-bundle) by
`andElim`.  The impossible boundary classes (`k2` = bottom under Z-type;
`k1` = right/left under X-type) are ruled out via the `typeExclF` exclusion
implications already carried in `pairBundleF` (`ztNotTopXF`/`ztNotBottomXF` for the
Z-type `k2`, `xtNotRightZF`/`xtNotLeftZF` for the X-type `k1`). -/
def dispatchRouter {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hbundle : SFormula.Deriv Γ (pairBundleF D))
    (hmega : SFormula.Deriv Γ (megaPacksF D))
    (hkAX : SFormula.Deriv Γ (k1IsX D true))
    (hkBZ : SFormula.Deriv Γ (k2IsX D false)) :
    SFormula.Deriv Γ (pairGoal D) := by
  -- Extract the type-exclusion packs (the isX bridges) from `hbundle`.
  have hExcl1 : SFormula.Deriv Γ (typeExclF D k1P) :=
    SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hbundle))
  have hExcl2 : SFormula.Deriv Γ (typeExclF D k2P) :=
    SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hbundle))
  -- Extract each combo's PacksF from the right-nested `hmega`.
  have hMdbb : SFormula.Deriv Γ (dbbPacksF D) := SFormula.Deriv.andElimLeft hmega
  have hMr1 := SFormula.Deriv.andElimRight hmega
  have hMdbr : SFormula.Deriv Γ (dbrPacksF D) := SFormula.Deriv.andElimLeft hMr1
  have hMr2 := SFormula.Deriv.andElimRight hMr1
  have hMdbl : SFormula.Deriv Γ (dblPacksF D) := SFormula.Deriv.andElimLeft hMr2
  have hMr3 := SFormula.Deriv.andElimRight hMr2
  have hMdtb : SFormula.Deriv Γ (dtbPacksF D) := SFormula.Deriv.andElimLeft hMr3
  have hMr4 := SFormula.Deriv.andElimRight hMr3
  have hMdbtb : SFormula.Deriv Γ (dbtbPacksF D) := SFormula.Deriv.andElimLeft hMr4
  have hMr5 := SFormula.Deriv.andElimRight hMr4
  have hMdtr : SFormula.Deriv Γ (dtrPacksF D) := SFormula.Deriv.andElimLeft hMr5
  have hMr6 := SFormula.Deriv.andElimRight hMr5
  have hMdtl : SFormula.Deriv Γ (dtlPacksF D) := SFormula.Deriv.andElimLeft hMr6
  have hMr7 := SFormula.Deriv.andElimRight hMr6
  have hMdbtr : SFormula.Deriv Γ (dbtrPacksF D) := SFormula.Deriv.andElimLeft hMr7
  have hMdbtl : SFormula.Deriv Γ (dbtlPacksF D) := SFormula.Deriv.andElimRight hMr7
  -- The isX exclusion implications for `k1` (X-type) and `k2` (Z-type).
  -- k1: xtNotRightZF / xtNotLeftZF (rule out right/left under X-type boundary).
  have hXtNotRightZ : SFormula.Deriv Γ (xtNotRightZF D k1P) :=
    SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hExcl1)
  have hXtNotLeftZ : SFormula.Deriv Γ (xtNotLeftZF D k1P) :=
    SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hExcl1))
  -- k2: ztNotTopXF / ztNotBottomXF (rule out top, and bottom-vacuity under Z-type).
  have hZtNotTopX : SFormula.Deriv Γ (ztNotTopXF D k2P) :=
    SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hExcl2))))
  have hZtNotBottomX : SFormula.Deriv Γ (ztNotBottomXF D k2P) :=
    SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hExcl2))))
  -- ROOT: case on bulk(k1).
  refine SFormula.Deriv.boolCases (SC.closed (bulkGuardTA (dP2 D) k1P)) _ ?k1bulk ?k1nbulk
  case k1bulk =>
    -- ctx0: bulk(k1)=true :: Γ
    have hbulkA : SFormula.Deriv
        (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true) :: Γ)
        (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true)) :=
      .hyp List.mem_cons_self
    refine SFormula.Deriv.boolCases (SC.closed (bulkGuardTA (dP2 D) k2P)) _ ?k1b_k2bulk ?k1b_k2nbulk
    case k1b_k2bulk =>
      -- ctx1: bulk(k2)=true :: bulk(k1)=true :: Γ
      have hbulkB : SFormula.Deriv
          (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true)
            :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true) :: Γ)
          (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true)) :=
        .hyp List.mem_cons_self
      exact dispatchBulkBulk D (cw2 hbundle) (cw2 hMdbb) (cw2 hkAX) (cw2 hkBZ)
        (cw1 hbulkA) hbulkB
    case k1b_k2nbulk =>
      -- ctx1: bulk(k2)=false :: bulk(k1)=true :: Γ
      have hnbulkB : SFormula.Deriv
          (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
            :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true) :: Γ)
          (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)) :=
        .hyp List.mem_cons_self
      -- hntopB := ztNotTopXF(k2) hkBZ hnbulkB
      have hntopB : SFormula.Deriv
          (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
            :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true) :: Γ)
          (.eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false)) :=
        SFormula.Deriv.mp (SFormula.Deriv.mp (cw2 hZtNotTopX) (cw2 hkBZ)) hnbulkB
      refine SFormula.Deriv.boolCases (SC.closed (rightClassGuardTA (dP2 D) k2P)) _ ?rT ?rF
      case rT =>
        have hrightB : SFormula.Deriv
            (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b true)
              :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
              :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true) :: Γ)
            (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b true)) :=
          .hyp List.mem_cons_self
        exact dispatchBulkRight D (cw3 hbundle) (cw3 hMdbr) (cw3 hkAX) (cw3 hkBZ)
          (cw2 hbulkA) (cw1 hnbulkB) (cw1 hntopB) hrightB
      case rF =>
        have hnrightB : SFormula.Deriv
            (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false)
              :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
              :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true) :: Γ)
            (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false)) :=
          .hyp List.mem_cons_self
        refine SFormula.Deriv.boolCases (SC.closed (leftClassGuardTA (dP2 D) k2P)) _ ?lT ?lF
        case lT =>
          have hleftB : SFormula.Deriv
              (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b true)
                :: .eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false)
                :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
                :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true) :: Γ)
              (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b true)) :=
            .hyp List.mem_cons_self
          exact dispatchBulkLeft D (cw4 hbundle) (cw4 hMdbl) (cw4 hkAX) (cw4 hkBZ)
            (cw3 hbulkA) (cw2 hnbulkB) (cw2 hntopB) (cw1 hnrightB) hleftB
        case lF =>
          -- vacuous: k2 has ¬bulk ¬top ¬right ¬left → bottom = X-type, contradicting Z-type.
          have hnleftB : SFormula.Deriv
              (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b false)
                :: .eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false)
                :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
                :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true) :: Γ)
              (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b false)) :=
            .hyp List.mem_cons_self
          have hleftBtrue : SFormula.Deriv
              (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b false)
                :: .eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false)
                :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
                :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b true) :: Γ)
              (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b true)) :=
            SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (cw4 hZtNotBottomX) (cw4 hkBZ))
              (cw2 hnbulkB)) (cw2 hntopB)
          exact SFormula.Deriv.botElim
            (SFormula.Deriv.notElim hleftBtrue (SFormula.Deriv.eqBoolFalseNotTrue _ hnleftB))
  case k1nbulk =>
    -- ctx0: bulk(k1)=false :: Γ
    have hnbulkA : SFormula.Deriv
        (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
        (.eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false)) :=
      .hyp List.mem_cons_self
    refine SFormula.Deriv.boolCases (SC.closed (bulkGuardTA (dP2 D) k2P)) _ ?k1nb_k2bulk ?k1nb_k2nbulk
    case k1nb_k2bulk =>
      -- ctx1: bulk(k2)=true :: bulk(k1)=false :: Γ
      have hbulkB : SFormula.Deriv
          (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true)
            :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
          (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true)) :=
        .hyp List.mem_cons_self
      refine SFormula.Deriv.boolCases (SC.closed (topClassGuardTA (dP2 D) k1P)) _ ?tbT ?tbF
      case tbT =>
        have htopA : SFormula.Deriv
            (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b true)
              :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true)
              :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
            (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b true)) :=
          .hyp List.mem_cons_self
        exact dispatchTopBulk D (cw3 hbundle) (cw3 hMdtb) (cw3 hkAX) (cw3 hkBZ)
          (cw2 hnbulkA) htopA (cw1 hbulkB)
      case tbF =>
        have hntopA : SFormula.Deriv
            (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false)
              :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true)
              :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
            (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false)) :=
          .hyp List.mem_cons_self
        -- hnrightA := xtNotRightZF(k1) hkAX hnbulkA hntopA ; hnleftA := xtNotLeftZF(k1) ... hnrightA
        have hnrightA : SFormula.Deriv
            (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false)
              :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true)
              :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
            (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k1P)) (SC.b false)) :=
          SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (cw3 hXtNotRightZ) (cw3 hkAX))
            (cw2 hnbulkA)) hntopA
        have hnleftA : SFormula.Deriv
            (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false)
              :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b true)
              :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
            (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k1P)) (SC.b false)) :=
          SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp
            (cw3 hXtNotLeftZ) (cw3 hkAX)) (cw2 hnbulkA)) hntopA) hnrightA
        exact dispatchBottomBulk D (cw3 hbundle) (cw3 hMdbtb) (cw3 hkAX) (cw3 hkBZ)
          (cw2 hnbulkA) hntopA hnrightA hnleftA (cw1 hbulkB)
    case k1nb_k2nbulk =>
      -- ctx1: bulk(k2)=false :: bulk(k1)=false :: Γ
      have hnbulkB : SFormula.Deriv
          (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
            :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
          (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)) :=
        .hyp List.mem_cons_self
      have hntopB : SFormula.Deriv
          (.eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
            :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
          (.eqBool (SC.closed (topClassGuardTA (dP2 D) k2P)) (SC.b false)) :=
        SFormula.Deriv.mp (SFormula.Deriv.mp (cw2 hZtNotTopX) (cw2 hkBZ)) hnbulkB
      refine SFormula.Deriv.boolCases (SC.closed (topClassGuardTA (dP2 D) k1P)) _ ?topT ?topF
      case topT =>
        have htopA : SFormula.Deriv
            (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b true)
              :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
              :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
            (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b true)) :=
          .hyp List.mem_cons_self
        refine SFormula.Deriv.boolCases (SC.closed (rightClassGuardTA (dP2 D) k2P)) _ ?trT ?trF
        case trT =>
          have hrightB : SFormula.Deriv
              (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b true)
                :: .eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b true)
                :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
                :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
              (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b true)) :=
            .hyp List.mem_cons_self
          exact dispatchTopRight D (cw4 hbundle) (cw4 hMdtr) (cw4 hkAX) (cw4 hkBZ)
            (cw3 hnbulkA) (cw1 htopA) (cw2 hnbulkB) (cw2 hntopB) hrightB
        case trF =>
          have hnrightB : SFormula.Deriv
              (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false)
                :: .eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b true)
                :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
                :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
              (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false)) :=
            .hyp List.mem_cons_self
          refine SFormula.Deriv.boolCases (SC.closed (leftClassGuardTA (dP2 D) k2P)) _ ?tlT ?tlF
          case tlT =>
            have hleftB : SFormula.Deriv
                (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b true)
                  :: .eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false)
                  :: .eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b true)
                  :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
                  :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
                (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b true)) :=
              .hyp List.mem_cons_self
            exact dispatchTopLeft D (cw5 hbundle) (cw5 hMdtl) (cw5 hkAX) (cw5 hkBZ)
              (cw4 hnbulkA) (cw2 htopA) (cw3 hnbulkB) (cw3 hntopB) (cw1 hnrightB) hleftB
          case tlF =>
            have hnleftB : SFormula.Deriv
                (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b false)
                  :: .eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false)
                  :: .eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b true)
                  :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
                  :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
                (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b false)) :=
              .hyp List.mem_cons_self
            have hleftBtrue : SFormula.Deriv
                (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b false)
                  :: .eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false)
                  :: .eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b true)
                  :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
                  :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
                (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b true)) :=
              SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (cw5 hZtNotBottomX) (cw5 hkBZ))
                (cw3 hnbulkB)) (cw3 hntopB)
            exact SFormula.Deriv.botElim
              (SFormula.Deriv.notElim hleftBtrue (SFormula.Deriv.eqBoolFalseNotTrue _ hnleftB))
      case topF =>
        have hntopA : SFormula.Deriv
            (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false)
              :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
              :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
            (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false)) :=
          .hyp List.mem_cons_self
        have hnrightA : SFormula.Deriv
            (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false)
              :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
              :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
            (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k1P)) (SC.b false)) :=
          SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (cw3 hXtNotRightZ) (cw3 hkAX))
            (cw2 hnbulkA)) hntopA
        have hnleftA : SFormula.Deriv
            (.eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false)
              :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
              :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
            (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k1P)) (SC.b false)) :=
          SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp
            (cw3 hXtNotLeftZ) (cw3 hkAX)) (cw2 hnbulkA)) hntopA) hnrightA
        refine SFormula.Deriv.boolCases (SC.closed (rightClassGuardTA (dP2 D) k2P)) _ ?brT ?brF
        case brT =>
          have hrightB : SFormula.Deriv
              (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b true)
                :: .eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false)
                :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
                :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
              (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b true)) :=
            .hyp List.mem_cons_self
          exact dispatchBottomRight D (cw4 hbundle) (cw4 hMdbtr) (cw4 hkAX) (cw4 hkBZ)
            (cw3 hnbulkA) (cw1 hntopA) (cw1 hnrightA) (cw1 hnleftA) (cw2 hnbulkB) (cw2 hntopB) hrightB
        case brF =>
          have hnrightB : SFormula.Deriv
              (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false)
                :: .eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false)
                :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
                :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
              (.eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false)) :=
            .hyp List.mem_cons_self
          refine SFormula.Deriv.boolCases (SC.closed (leftClassGuardTA (dP2 D) k2P)) _ ?blT ?blF
          case blT =>
            have hleftB : SFormula.Deriv
                (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b true)
                  :: .eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false)
                  :: .eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false)
                  :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
                  :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
                (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b true)) :=
              .hyp List.mem_cons_self
            exact dispatchBottomLeft D (cw5 hbundle) (cw5 hMdbtl) (cw5 hkAX) (cw5 hkBZ)
              (cw4 hnbulkA) (cw2 hntopA) (cw2 hnrightA) (cw2 hnleftA) (cw3 hnbulkB) (cw3 hntopB)
              (cw1 hnrightB) hleftB
          case blF =>
            have hnleftB : SFormula.Deriv
                (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b false)
                  :: .eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false)
                  :: .eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false)
                  :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
                  :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
                (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b false)) :=
              .hyp List.mem_cons_self
            have hleftBtrue : SFormula.Deriv
                (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b false)
                  :: .eqBool (SC.closed (rightClassGuardTA (dP2 D) k2P)) (SC.b false)
                  :: .eqBool (SC.closed (topClassGuardTA (dP2 D) k1P)) (SC.b false)
                  :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k2P)) (SC.b false)
                  :: .eqBool (SC.closed (bulkGuardTA (dP2 D) k1P)) (SC.b false) :: Γ)
                (.eqBool (SC.closed (leftClassGuardTA (dP2 D) k2P)) (SC.b true)) :=
              SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp (cw5 hZtNotBottomX) (cw5 hkBZ))
                (cw3 hnbulkB)) (cw3 hntopB)
            exact SFormula.Deriv.botElim
              (SFormula.Deriv.notElim hleftBtrue (SFormula.Deriv.eqBoolFalseNotTrue _ hnleftB))

#print axioms dispatchRouter

/-! ## The ∀∀-quantified DIFFERENT-type dispatch (`dispatchDiffType`)

`dispatchRouter` is fixed to `k1 = var 1` X-type, `k2 = var 0` Z-type and concludes
the canonical-orientation `pairGoal D = commutesUpTo (nP2 D) (recCall k1) (recCall k2)`.
The `(Z,X)` leaf of `rowsCommuteSym` has the X/Z roles in the OPPOSITE De Bruijn
slots, so `dispatchRouter` does not apply directly.  We therefore prove a
`∀ kA, ∀ kB`-quantified bounded fact over BOTH stabilizer indices,

  `∀ kA < numStab, ∀ kB < numStab,
     isX kA = true → isX kB = false → commutesUpTo N (recCall kA) (recCall kB)`,

at arity 0 (the two binders re-introduce `kA = var 1`, `kB = var 0` at arity 2,
where `dispatchRouter` applies verbatim).  In the `(Z,X)` leaf we instantiate it at
the SWAPPED witnesses `kA := k2`, `kB := k1`, obtaining
`commutesUpTo N (recCall k2) (recCall k1)` — exactly the post-`commutesSymm` goal —
for free, with no row-swapped re-derivation of the dispatcher. -/

/-- The body of `DDF`, at arity 2 (after the two stabilizer binders, `kA = k1 = var 1`,
`kB = k2 = var 0`): the X→Z implication chain guarding the canonical pair goal. -/
abbrev diffTypeBody (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (k1IsX D true) (.imp (k2IsX D false) (pairGoal D))

/-- The ∀∀-quantified DIFFERENT-type dispatch formula (arity 0).  The two bounds
match `rowsCommuteOddF`/`codeRowsCommuteUpTo` EXACTLY (`numStab` then its weakening),
so an `allNatLtElim` lines up with the `boundNatLt` hypotheses the bounded binders
expose in `rowsCommuteSym`. -/
abbrev DDF (D : OddSurfaceDistance) : SFormula 0 :=
  .allNatLt (SC.closed (Term.natLit (numStab D.distance)))
    (.allNatLt (SC.closed (Term.lift 0 (Term.natLit (numStab D.distance))))
      (diffTypeBody D))

/-- **The ∀∀-quantified DIFFERENT-type dispatch.**  Built by two UNBOUNDED
`PureFamilyDerivA.allNatLtIntro`s (the dispatcher does not consume the `k < numStab`
side conditions) down to arity 2, where the canonical `dispatchRouter` discharges the
guarded `pairGoal` from the split combined bundle. -/
def dispatchDiffType (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (DDF D) :=
  PureFamilyDerivA.allNatLtIntro _
    (PureFamilyDerivA.allNatLtIntro _
      (PureFamilyDerivA.cut1
        (by
          -- Context: [.and (pairBundleF D) (megaPacksF D)].  Goal: diffTypeBody D.
          refine SFormula.Deriv.impIntro (SFormula.Deriv.impIntro ?_)
          -- Context now:
          --   [k2IsX D false, k1IsX D true, .and (pairBundleF D) (megaPacksF D)]
          have hbundleD : SFormula.Deriv
              [k2IsX D false, k1IsX D true, .and (pairBundleF D) (megaPacksF D)]
              (pairBundleF D) :=
            SFormula.Deriv.andElimLeft (.hyp (by right; right; exact List.mem_cons_self))
          have hmegaD : SFormula.Deriv
              [k2IsX D false, k1IsX D true, .and (pairBundleF D) (megaPacksF D)]
              (megaPacksF D) :=
            SFormula.Deriv.andElimRight (.hyp (by right; right; exact List.mem_cons_self))
          have hk1X : SFormula.Deriv
              [k2IsX D false, k1IsX D true, .and (pairBundleF D) (megaPacksF D)]
              (k1IsX D true) :=
            .hyp (by right; exact List.mem_cons_self)
          have hk2notX : SFormula.Deriv
              [k2IsX D false, k1IsX D true, .and (pairBundleF D) (megaPacksF D)]
              (k2IsX D false) :=
            .assumption
          exact dispatchRouter D hbundleD hmegaD hk1X hk2notX)
        (pfdaAnd2 (pairBundle D) (megaPacks D))))

#print axioms dispatchDiffType

/-! ## The ∀∀-quantified SAME-type dispatches (`sameTypeXFamily` / `sameTypeZFamily`)

The same-type closers `pairCommuteSameTypeX` / `pairCommuteSameTypeZ` also need the
pair bundle.  To assemble the entire pair goal from a SINGLE arity-0 cut (so the
`(Z,X)` leaf can elim `DDF` at swapped indices in the SAME bounded-binder context as
the other leaves), we quantify the two same-type closers identically to `DDF`. -/

/-- The body of `sameTypeXFamily` (both rows X-type ⇒ commute). -/
abbrev sameTypeXBody (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (k1IsX D true) (.imp (k2IsX D true) (pairGoal D))

/-- The body of `sameTypeZFamily` (both rows Z-type ⇒ commute). -/
abbrev sameTypeZBody (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (k1IsX D false) (.imp (k2IsX D false) (pairGoal D))

/-- ∀∀-quantified SAME-type-X dispatch (arity 0), bounds matching `rowsCommuteOddF`. -/
abbrev SDFX (D : OddSurfaceDistance) : SFormula 0 :=
  .allNatLt (SC.closed (Term.natLit (numStab D.distance)))
    (.allNatLt (SC.closed (Term.lift 0 (Term.natLit (numStab D.distance))))
      (sameTypeXBody D))

/-- ∀∀-quantified SAME-type-Z dispatch (arity 0), bounds matching `rowsCommuteOddF`. -/
abbrev SDFZ (D : OddSurfaceDistance) : SFormula 0 :=
  .allNatLt (SC.closed (Term.natLit (numStab D.distance)))
    (.allNatLt (SC.closed (Term.lift 0 (Term.natLit (numStab D.distance))))
      (sameTypeZBody D))

/-- The combined four-fact bundle used as the single arity-0 cut for `rowsCommuteSym`. -/
abbrev allDispatchF (D : OddSurfaceDistance) : SFormula 0 :=
  .and (DDF D) (.and (SDFX D) (SDFZ D))

/-- Extract the four pair packs of `pairBundleF` from a derivation of it. -/
private def bundlePieces (D : OddSurfaceDistance)
    (Γ : List (SFormula 2)) (hb : SFormula.Deriv Γ (pairBundleF D)) :
    SFormula.Deriv Γ (entryAQuant D) × SFormula.Deriv Γ (entryBQuant D) ×
      SFormula.Deriv Γ (typeExclF D k1P) × SFormula.Deriv Γ (typeExclF D k2P) :=
  ⟨SFormula.Deriv.andElimLeft hb,
   SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hb),
   SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hb)),
   SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hb))⟩

/-- The ∀∀-quantified SAME-type-X dispatch. -/
def sameTypeXFamily (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (SDFX D) :=
  PureFamilyDerivA.allNatLtIntro _
    (PureFamilyDerivA.allNatLtIntro _
      (PureFamilyDerivA.cut1
        (by
          refine SFormula.Deriv.impIntro (SFormula.Deriv.impIntro ?_)
          set Γ : List (SFormula 2) :=
            [k2IsX D true, k1IsX D true, pairBundleF D] with hΓ
          have hbundleD : SFormula.Deriv Γ (pairBundleF D) :=
            .hyp (by right; right; exact List.mem_cons_self)
          obtain ⟨hEntryA, hEntryB, hExcl1, hExcl2⟩ := bundlePieces D Γ hbundleD
          have hk1X : SFormula.Deriv Γ (k1IsX D true) :=
            .hyp (by right; exact List.mem_cons_self)
          have hk2X : SFormula.Deriv Γ (k2IsX D true) := .assumption
          exact pairCommuteSameTypeX D hEntryA hEntryB hk1X hk2X hExcl1 hExcl2)
        (pairBundle D)))

/-- The ∀∀-quantified SAME-type-Z dispatch. -/
def sameTypeZFamily (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (SDFZ D) :=
  PureFamilyDerivA.allNatLtIntro _
    (PureFamilyDerivA.allNatLtIntro _
      (PureFamilyDerivA.cut1
        (by
          refine SFormula.Deriv.impIntro (SFormula.Deriv.impIntro ?_)
          set Γ : List (SFormula 2) :=
            [k2IsX D false, k1IsX D false, pairBundleF D] with hΓ
          have hbundleD : SFormula.Deriv Γ (pairBundleF D) :=
            .hyp (by right; right; exact List.mem_cons_self)
          obtain ⟨hEntryA, hEntryB, hExcl1, hExcl2⟩ := bundlePieces D Γ hbundleD
          have hk1X : SFormula.Deriv Γ (k1IsX D false) :=
            .hyp (by right; exact List.mem_cons_self)
          have hk2X : SFormula.Deriv Γ (k2IsX D false) := .assumption
          exact pairCommuteSameTypeZ D hEntryA hEntryB hk1X hk2X hExcl1 hExcl2)
        (pairBundle D)))

/-- Arity-generic conjunction introduction for `PureFamilyDerivA`. -/
def pfdaAndG {D : OddSurfaceDistance} {arity : Nat} {A B : SFormula arity}
    (hA : PureFamilyDerivA Surface.code.body (D.distance + 2) A)
    (hB : PureFamilyDerivA Surface.code.body (D.distance + 2) B) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (.and A B) :=
  PureFamilyDerivA.cut2 (SFormula.Deriv.andIntro .assumption
    (.hyp (by right; exact List.mem_cons_self))) hA hB

/-- The combined four-fact dispatch family. -/
def allDispatch (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (allDispatchF D) :=
  pfdaAndG (dispatchDiffType D) (pfdaAndG (sameTypeXFamily D) (sameTypeZFamily D))

#print axioms allDispatch

/-! ## Instantiating the ∀∀ families at the pair indices

Each family `F = allNatLt numStab (allNatLt numStab.weaken B)` (with `B` an arity-2
body referencing `k1 = var 1`, `k2 = var 0`), once weakened into the per-pair
context, is eliminated at two pure witnesses.  Eliminating at `(k1, k2)` returns `B`
verbatim (identity substitution on the matching De Bruijn slots); eliminating at the
SWAPPED `(k2, k1)` returns `B` with `k1`/`k2` exchanged.  The reductions below are
purely the capture-avoiding lift/instantiate book-keeping (Fin-index arithmetic), so
they go through by structural `simp` on the closed numeral bound and the concrete
body — no `arithBool`-fragment reasoning, no `decide` on Pauli content. -/

/-- The closed outer bound `numStab` (arity 2) shared by every `∀∀` family. -/
abbrev famN0 (D : OddSurfaceDistance) : STerm 2 .nat :=
  SC.closed (Term.lift 0 (Term.lift 0 (Term.natLit (numStab D.distance))))

/-- The DIFFERENT-type family, weakened into a per-pair context, instantiated at the
SWAPPED indices `(k2, k1)` — yielding the row-swapped pair goal `commutesUpTo (nP2 D)
(rowB D) (rowA D)` guarded by `k2 X-type → k1 Z-type`.  This is the `(Z,X)` workhorse.
The full structural `simp` set reduces only the lift/instantiate book-keeping. -/
private def instDDFswap {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hF : SFormula.Deriv Γ
      ((SFormula.allNatLt (SC.closed (Term.natLit (numStab D.distance)))
        (SFormula.allNatLt (SC.closed (Term.lift 0 (Term.natLit (numStab D.distance))))
          (diffTypeBody D))).weaken.weaken))
    (hk1Lt : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed k1P) (famN0 D)))
    (hk2Lt : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed k2P) (famN0 D))) :
    SFormula.Deriv Γ
      (.imp (k2IsX D true) (.imp (k1IsX D false)
        (SFormula.commutesUpTo (nP2 D) (rowB D) (rowA D)))) := by
  have hStep1 := SFormula.Deriv.allNatLtElim (famN0 D) _ (SC.closed k2P) hF hk2Lt
  have hStep1b := SFormula.Deriv.applyNatSubstitutionBetaElim k2P _
    (SFormula.PureNatTerm.var ⟨0, by decide⟩) hStep1
  simp only [SFormula.instantiateTopNat, SFormula.instantiateNatAt, SFormula.lift,
    STerm.instantiateNatAt, STerm.lift, Term.instantiateNatAt, Term.lift,
    STerm.weaken, SFormula.weaken, Term.weaken, Term.weakenVar, SC.n, SC.closed] at hStep1b
  have hStep2 := SFormula.Deriv.allNatLtElim (famN0 D) _ (SC.closed k1P) hStep1b hk1Lt
  have hStep2b := SFormula.Deriv.applyNatSubstitutionBetaElim k1P _
    (SFormula.PureNatTerm.var ⟨1, by decide⟩) hStep2
  simpa [diffTypeBody, k1IsX, k2IsX, pairGoal, nP2, rowA, rowB, dP2, k1P, k2P,
    isXTypeTA, bulkGuardTA, baseKindGuardTA, topClassGuardTA, rightClassGuardTA, leftClassGuardTA,
    bulkCountTA, dm1TA, baseBTA, baseHalfTA,
    SFormula.instantiateTopNat, SFormula.instantiateNatAt, SFormula.lift, SFormula.weaken,
    STerm.instantiateNatAt, STerm.lift, STerm.weaken, Term.instantiateNatAt, Term.lift,
    Term.weaken, Term.weakenVar, SC.n, SC.closed, SC.b] using hStep2b

/-- The DIFFERENT-type family, instantiated at the NATURAL order `(k1, k2)` (identity
substitution), yielding `k1 X-type → k2 Z-type → pairGoal D`.  The `(X,Z)` workhorse. -/
private def instDDFid {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hF : SFormula.Deriv Γ
      ((SFormula.allNatLt (SC.closed (Term.natLit (numStab D.distance)))
        (SFormula.allNatLt (SC.closed (Term.lift 0 (Term.natLit (numStab D.distance))))
          (diffTypeBody D))).weaken.weaken))
    (hk1Lt : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed k1P) (famN0 D)))
    (hk2Lt : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed k2P) (famN0 D))) :
    SFormula.Deriv Γ (.imp (k1IsX D true) (.imp (k2IsX D false) (pairGoal D))) := by
  have hStep1 := SFormula.Deriv.allNatLtElim (famN0 D) _ (SC.closed k1P) hF hk1Lt
  have hStep1b := SFormula.Deriv.applyNatSubstitutionBetaElim k1P _
    (SFormula.PureNatTerm.var ⟨1, by decide⟩) hStep1
  simp only [SFormula.instantiateTopNat, SFormula.instantiateNatAt, SFormula.lift,
    STerm.instantiateNatAt, STerm.lift, Term.instantiateNatAt, Term.lift,
    STerm.weaken, SFormula.weaken, Term.weaken, Term.weakenVar, SC.n, SC.closed] at hStep1b
  have hStep2 := SFormula.Deriv.allNatLtElim (famN0 D) _ (SC.closed k2P) hStep1b hk2Lt
  have hStep2b := SFormula.Deriv.applyNatSubstitutionBetaElim k2P _
    (SFormula.PureNatTerm.var ⟨0, by decide⟩) hStep2
  simpa [diffTypeBody, k1IsX, k2IsX, pairGoal, nP2, rowA, rowB, dP2, k1P, k2P,
    isXTypeTA, bulkGuardTA, baseKindGuardTA, topClassGuardTA, rightClassGuardTA, leftClassGuardTA,
    bulkCountTA, dm1TA, baseBTA, baseHalfTA,
    SFormula.instantiateTopNat, SFormula.instantiateNatAt, SFormula.lift, SFormula.weaken,
    STerm.instantiateNatAt, STerm.lift, STerm.weaken, Term.instantiateNatAt, Term.lift,
    Term.weaken, Term.weakenVar, SC.n, SC.closed, SC.b] using hStep2b

/-- The SAME-type-X family, instantiated at `(k1, k2)`: `k1 X-type → k2 X-type →
pairGoal D`. -/
private def instSDFXid {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hF : SFormula.Deriv Γ
      ((SFormula.allNatLt (SC.closed (Term.natLit (numStab D.distance)))
        (SFormula.allNatLt (SC.closed (Term.lift 0 (Term.natLit (numStab D.distance))))
          (sameTypeXBody D))).weaken.weaken))
    (hk1Lt : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed k1P) (famN0 D)))
    (hk2Lt : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed k2P) (famN0 D))) :
    SFormula.Deriv Γ (.imp (k1IsX D true) (.imp (k2IsX D true) (pairGoal D))) := by
  have hStep1 := SFormula.Deriv.allNatLtElim (famN0 D) _ (SC.closed k1P) hF hk1Lt
  have hStep1b := SFormula.Deriv.applyNatSubstitutionBetaElim k1P _
    (SFormula.PureNatTerm.var ⟨1, by decide⟩) hStep1
  simp only [SFormula.instantiateTopNat, SFormula.instantiateNatAt, SFormula.lift,
    STerm.instantiateNatAt, STerm.lift, Term.instantiateNatAt, Term.lift,
    STerm.weaken, SFormula.weaken, Term.weaken, Term.weakenVar, SC.n, SC.closed] at hStep1b
  have hStep2 := SFormula.Deriv.allNatLtElim (famN0 D) _ (SC.closed k2P) hStep1b hk2Lt
  have hStep2b := SFormula.Deriv.applyNatSubstitutionBetaElim k2P _
    (SFormula.PureNatTerm.var ⟨0, by decide⟩) hStep2
  simpa [sameTypeXBody, k1IsX, k2IsX, pairGoal, nP2, rowA, rowB, dP2, k1P, k2P,
    isXTypeTA, bulkGuardTA, baseKindGuardTA, topClassGuardTA, rightClassGuardTA, leftClassGuardTA,
    bulkCountTA, dm1TA, baseBTA, baseHalfTA,
    SFormula.instantiateTopNat, SFormula.instantiateNatAt, SFormula.lift, SFormula.weaken,
    STerm.instantiateNatAt, STerm.lift, STerm.weaken, Term.instantiateNatAt, Term.lift,
    Term.weaken, Term.weakenVar, SC.n, SC.closed, SC.b] using hStep2b

/-- The SAME-type-Z family, instantiated at `(k1, k2)`: `k1 Z-type → k2 Z-type →
pairGoal D`. -/
private def instSDFZid {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hF : SFormula.Deriv Γ
      ((SFormula.allNatLt (SC.closed (Term.natLit (numStab D.distance)))
        (SFormula.allNatLt (SC.closed (Term.lift 0 (Term.natLit (numStab D.distance))))
          (sameTypeZBody D))).weaken.weaken))
    (hk1Lt : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed k1P) (famN0 D)))
    (hk2Lt : SFormula.Deriv Γ (SFormula.witnessLt (SC.closed k2P) (famN0 D))) :
    SFormula.Deriv Γ (.imp (k1IsX D false) (.imp (k2IsX D false) (pairGoal D))) := by
  have hStep1 := SFormula.Deriv.allNatLtElim (famN0 D) _ (SC.closed k1P) hF hk1Lt
  have hStep1b := SFormula.Deriv.applyNatSubstitutionBetaElim k1P _
    (SFormula.PureNatTerm.var ⟨1, by decide⟩) hStep1
  simp only [SFormula.instantiateTopNat, SFormula.instantiateNatAt, SFormula.lift,
    STerm.instantiateNatAt, STerm.lift, Term.instantiateNatAt, Term.lift,
    STerm.weaken, SFormula.weaken, Term.weaken, Term.weakenVar, SC.n, SC.closed] at hStep1b
  have hStep2 := SFormula.Deriv.allNatLtElim (famN0 D) _ (SC.closed k2P) hStep1b hk2Lt
  have hStep2b := SFormula.Deriv.applyNatSubstitutionBetaElim k2P _
    (SFormula.PureNatTerm.var ⟨0, by decide⟩) hStep2
  simpa [sameTypeZBody, k1IsX, k2IsX, pairGoal, nP2, rowA, rowB, dP2, k1P, k2P,
    isXTypeTA, bulkGuardTA, baseKindGuardTA, topClassGuardTA, rightClassGuardTA, leftClassGuardTA,
    bulkCountTA, dm1TA, baseBTA, baseHalfTA,
    SFormula.instantiateTopNat, SFormula.instantiateNatAt, SFormula.lift, SFormula.weaken,
    STerm.instantiateNatAt, STerm.lift, STerm.weaken, Term.instantiateNatAt, Term.lift,
    Term.weaken, Term.weakenVar, SC.n, SC.closed, SC.b] using hStep2b

/-- **Pairwise row commutation, all `D`.**

FULLY sorry-free and axiom-clean.  A single arity-0 cut introduces the four
∀∀-quantified dispatch families (`allDispatch` = `dispatchDiffType` ∧
`sameTypeXFamily` ∧ `sameTypeZFamily`); the two stabilizer binders are introduced with
their `k < numStab` side conditions exposed (`allNatLtIntroBounded`); both rows are
classified by CSS type (`isXTypeTA`, a `k`-only function); and each of the four combos
is closed by instantiating the matching family at the per-leaf indices:
* `(X,X)` / `(Z,Z)`: the SAME-type closers (`instSDFXid` / `instSDFZid`, internalising
  `pairCommuteSameTypeX` / `pairCommuteSameTypeZ`) at the natural order `(k1, k2)`;
* `(X,Z)`: the DIFFERENT-type dispatcher (`instDDFid`, internalising `dispatchRouter`)
  at `(k1, k2)`;
* `(Z,X)`: the SAME DIFFERENT-type family instantiated at the SWAPPED indices
  `(k2, k1)` (`instDDFswap`), composed with `commutesSymm` to recover the canonical
  orientation — so the `(Z,X)` leaf reuses the `(X,Z)` dispatcher verbatim, with the
  X/Z roles exchanged purely by the ∀∀ instantiation (no row-swapped re-derivation). -/
def rowsCommuteSym (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2)
      (closedSF (rowsCommuteOddF D)) :=
  PureFamilyDerivA.cut1
    (by
      -- Context: [allDispatchF D] (a single arity-0 cut of the four ∀∀ dispatch
      -- families).  Goal: closedSF (rowsCommuteOddF D), i.e. after unfolding,
      -- `allNatLt numStab (allNatLt numStab.weaken (pairGoal D))`.
      unfold closedSF rowsCommuteOddF rowsCommuteF Formula.codeRowsCommuteUpTo
      simp only [closedSF, Formula.codeRow, Term.weaken]
      -- Introduce both stabilizer binders with their `k < numStab` side conditions
      -- exposed (needed to ELIM the ∀∀ dispatch families at `k1`/`k2`).
      refine SFormula.Deriv.allNatLtIntroBounded _ _ ?_
      refine SFormula.Deriv.allNatLtIntroBounded _ _ ?_
      -- The arity-2 context (innermost first):
      --   [ boundNatLt N₁ , (boundNatLt N₀).weaken , (allDispatchF D).weaken.weaken ]
      -- with N₀ = numStab, N₁ = numStab.weaken.  `hk1Lt`/`hk2Lt` are the two
      -- exposed side conditions; `hAll` is the cut.
      have hAll : SFormula.Deriv
          [SFormula.boundNatLt (SC.closed (Term.lift 0 (Term.natLit (numStab D.distance)))),
            (SFormula.boundNatLt (SC.closed (Term.natLit (numStab D.distance)))).weaken,
            (allDispatchF D).weaken.weaken]
          ((allDispatchF D).weaken.weaken) :=
        .hyp (by right; right; exact List.mem_cons_self)
      have hDDF := SFormula.Deriv.andElimLeft hAll
      have hSDFX := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hAll)
      have hSDFZ := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hAll)
      have hk2Lt : SFormula.Deriv
          [SFormula.boundNatLt (SC.closed (Term.lift 0 (Term.natLit (numStab D.distance)))),
            (SFormula.boundNatLt (SC.closed (Term.natLit (numStab D.distance)))).weaken,
            (allDispatchF D).weaken.weaken]
          (SFormula.boundNatLt (SC.closed (Term.lift 0 (Term.natLit (numStab D.distance))))) :=
        .assumption
      have hk1Lt : SFormula.Deriv
          [SFormula.boundNatLt (SC.closed (Term.lift 0 (Term.natLit (numStab D.distance)))),
            (SFormula.boundNatLt (SC.closed (Term.natLit (numStab D.distance)))).weaken,
            (allDispatchF D).weaken.weaken]
          ((SFormula.boundNatLt (SC.closed (Term.natLit (numStab D.distance)))).weaken) :=
        .hyp (by right; exact List.mem_cons_self)
      -- Classify both rows by CSS type, routing each combo through the matching
      -- ∀∀-dispatch family instantiated at the appropriate (possibly swapped) indices.
      refine SFormula.Deriv.boolCases (SC.closed (isXTypeTA (dP2 D) k1P)) _ ?k1T ?k1F
      case k1T =>
        refine SFormula.Deriv.boolCases (SC.closed (isXTypeTA (dP2 D) k2P)) _ ?k1Tk2T ?k1Tk2F
        case k1Tk2T =>
          -- (X, X): SAME-type-X family at (k1, k2).
          exact ((instSDFXid D (cw2 hSDFX) (cw2 hk1Lt) (cw2 hk2Lt)).mp
            (.hyp (by right; exact List.mem_cons_self))).mp .assumption
        case k1Tk2F =>
          -- (X, Z): DIFFERENT-type family at (k1, k2).
          exact ((instDDFid D (cw2 hDDF) (cw2 hk1Lt) (cw2 hk2Lt)).mp
            (.hyp (by right; exact List.mem_cons_self))).mp .assumption
      case k1F =>
        refine SFormula.Deriv.boolCases (SC.closed (isXTypeTA (dP2 D) k2P)) _ ?k1Fk2T ?k1Fk2F
        case k1Fk2T =>
          -- (Z, X): DIFFERENT-type family at the SWAPPED indices (k2, k1), then
          -- `commutesSymm` to recover the canonical orientation.
          refine SFormula.Deriv.commutesSymm (nP2 D) (rowB D) (rowA D) ?_
          exact ((instDDFswap D (cw2 hDDF) (cw2 hk1Lt) (cw2 hk2Lt)).mp .assumption).mp
            (.hyp (by right; exact List.mem_cons_self))
        case k1Fk2F =>
          -- (Z, Z): SAME-type-Z family at (k1, k2).
          exact ((instSDFZid D (cw2 hSDFZ) (cw2 hk1Lt) (cw2 hk2Lt)).mp
            (.hyp (by right; exact List.mem_cons_self))).mp .assumption)
    (allDispatch D)

-- The bulk–bulk class-combo dispatcher (validation spike): routing + kind-bridge +
-- validity/non-adjacency derivations, sorry-free and axiom-clean.
#print axioms dispatchBulkBulk
#print axioms dbbKindK1OfIsX
#print axioms dbbBhRowImp
#print axioms dbbBvRowImp
#print axioms dbbBhlColImp
#print axioms dbbNonAdjAll
#print axioms dbbNonAdjVu
#print axioms dbbPacks

-- Axiom hygiene of the proven (sorry-free) infrastructure spine and the two
-- SAME-type closers.  `rowsCommuteSym` is now FULLY sorry-free and axiom-clean: all
-- four CSS-type combos are dispatched through the ∀∀-quantified `dispatchDiffType` /
-- `sameTypeXFamily` / `sameTypeZFamily` families (cut once at arity 0, instantiated
-- per leaf):
--   * `(X,Z)`: `instDDFid` (canonical orientation, dispatchRouter verbatim);
--   * `(Z,X)`: `instDDFswap` (DIFFERENT-type family at the SWAPPED indices `(k2,k1)`)
--      composed with the `commutesSymm` step — no row-swapped re-derivation needed;
--   * `(X,X)` / `(Z,Z)`: the two SAME-type closers via `instSDFXid` / `instSDFZid`.
-- The reusable two-anti spine they plug into (`commTwoAntiXZ` / `twoAntiRestXZ`)
-- and the entire pointwise / leaf / type-exclusion infrastructure are sorry-free
-- and axiom-clean (verified below).
#print axioms localDispatch
#print axioms pairCommutePointwise
#print axioms withLeafG
#print axioms typeExclPackK1
#print axioms typeExclPackK2
#print axioms pairCommuteSameTypeX
#print axioms pairCommuteSameTypeZ
-- The new reusable DIFFERENT-type (X-vs-Z) two-anti spines (sorry-free, axiom-clean).
#print axioms entryAAtQ
#print axioms entryBAtQ
#print axioms commTwoAntiXZ
#print axioms twoAntiRestXZ
-- The bulk–top overlap-class closer (sorry-free, axiom-clean).
#print axioms commBulkTopXZ
-- The bulk–top joint pin pack and the full bulk–top class closer (sorry-free, axiom-clean).
#print axioms btPinPack
#print axioms btPinAt
#print axioms btTopBandFromX
#print axioms btBulkBandFromZ
#print axioms commBulkTop
-- The bulk–bottom overlap-class closer + its arithmetic packs (sorry-free, axiom-clean).
#print axioms bbRangePack
#print axioms bbBottomBandPack
#print axioms bbBulkBandPack
#print axioms bbPinPack
#print axioms bbPinAt
#print axioms bbBottomBandFromX
#print axioms bbBulkBandFromZ
#print axioms commBottomBulk
-- The bulk–right overlap-class closer + its arithmetic packs (sorry-free, axiom-clean).
#print axioms brRangePack
#print axioms brRightBandPack
#print axioms brBulkBandPack
#print axioms brPinPack
#print axioms brPinAt
#print axioms brBulkBandFromX
#print axioms brRightBandFromZ
#print axioms commRightBulk
-- The bulk–left overlap-class closer + its arithmetic packs (sorry-free, axiom-clean).
#print axioms blRangePack
#print axioms blLeftBandPack
#print axioms blBulkBandPack
#print axioms blPinPack
#print axioms blPinAt
#print axioms blBulkBandFromX
#print axioms blLeftBandFromZ
#print axioms commLeftBulk
#print axioms rowsCommuteSym

end QHL.CodeLang.Surface.Verify
