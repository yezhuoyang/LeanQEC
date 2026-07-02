import QStab.QHL.Verify.SurfaceNormalizers
import QStab.QHL.Verify.SurfaceFlatBridge
import QStab.QHL.Verify.SurfaceRowOverlapNat

/-!
# Rows-commute (pairwise generated-row commutation) — Setup

Arity-2/3 abbreviations for the pair-of-rows goal, flat row entries, the local-commutation
goal and entry-equality abbreviations, per-row guard abbreviations, anti-commutation literal facts,
and identity-entry local commutation.
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

end QHL.CodeLang.Surface.Verify
