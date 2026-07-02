import QStab.QHL.Verify.SurfaceNormalizers.XTop

/-!
# Logical-normalizer consumers — ZSetup

Z normaliser setup (row/column transpose of `XSetup`): the symbolic (∀ D) logicalZ
normaliser, lifted `logicalZ` on/off-row entries, the local-commutation goal, the row-0 arithmetic
fact, the pointwise wrapper, and the `r = 0` guard.
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface

set_option maxRecDepth 65536

/-! ## Symbolic (forall D) logicalZ normalizer (geometric classification)

The transpose of the `logicalX` machinery above.  `logicalZ` is the single-ROW
operator (`Z` on `q / d = 0`, `I` elsewhere), so the on-line guard is the ROW
guard `q / d = 0` and the off-line half is `logicalZOffRowLocalCommutes`.  The
two anti classes (verified by `#eval` on the evaluator, NOT used in any proof)
are:

* class (a): top-row odd-`c` bulk `X`-plaquettes (`k < (d-1)²`, `r = k/(d-1) = 0`,
  `c = k%(d-1)` odd → kind FALSE → bulk-`X`) anticommuting with `logicalZ` at the
  two ROW-0 qubits `q0 = c`, `q1 = c+1`;
* class (b): top-`X` boundary stabilizers (`¬bulk`, `topClass` true, `b < half`,
  `b = k-(d-1)²`, `half = (d-1)/2`) anticommuting at `q0 = 2b`, `q1 = 2b+1`.

The row entry at an anti qubit is `X` (`baseLeafBulkX` for (a), `baseLeafTopX` for
(b)); the `logicalZ` entry is `Z`; `anticommutes X Z = true`.  All other `k`
commute pointwise on row 0 (their row-0 entries are `I` or `Z`, both commuting
with `Z`).  The row-structure helpers (`entryFlat*`, `rowK*`, `baseLeaf*`, all
`g*` guards, the `arithBool` packs) are X/Z-agnostic and reused verbatim. -/

/-! ### Lifted `logicalZ` and its on/off-row entries (∀ D) -/

/-- The lifted `logicalZ` operator at arity 2 (`(lift logicalZOdd D).weaken`). -/
abbrev liftedLZ2 (D : OddSurfaceDistance) : STerm 2 .stab :=
  (SC.closed (Term.lift 0 (logicalZOdd D))).weaken

/-- The lifted `logicalZ` operator at arity 1 (`lift logicalZOdd D`). -/
abbrev liftedLZ1 (D : OddSurfaceDistance) : STerm 1 .stab :=
  SC.closed (Term.lift 0 (logicalZOdd D))

/-- On a row-0 qubit (row guard `q / d = 0` TRUE), the `logicalZ` entry at the
bound qubit is `Z`.  ∀-D mirror of `lxOnColEntryX`. -/
def lzOnRowEntryZ {Δ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hTrue : SFormula.Deriv Δ (.eqBool (logicalZRowGuardAt2 D) (SC.b true))) :
    SFormula.Deriv Δ (.eqPauli (.stabAt (liftedLZ2 D) SFormula.boundNat) (SC.p Pauli.Z)) := by
  have h := SFormula.Deriv.stabAtClosedIteLamEqThen (Γ := Δ)
    (.eqNat (.div Formula.qVar (.natLit D.distance)) (.natLit 0))
    (.pauliLit Pauli.Z) (.pauliLit Pauli.I)
    (Term.var ⟨0, by decide⟩)
    (SFormula.PureNatTerm.var ⟨0, by decide⟩)
    (by simpa [logicalZRowGuardAt2] using hTrue)
  simpa [liftedLZ2, logicalZOdd, logicalZ, Formula.qVar, SFormula.boundNat, SC.closed, SC.p,
    OddSurfaceDistance.distance, oddDistance,
    STerm.weaken, STerm.lift, Term.instantiateTopNat, Term.instantiateNatAt, Term.lift,
    Term.weaken, Term.weakenVar] using h

/-- The closed `logicalZ` row guard `q / d = 0` at a PURE qubit term `qT`, true
form, at arity 1. -/
abbrev rowGuardPure1 (D : OddSurfaceDistance) (qT : Term 1 .nat) : SFormula 1 :=
  .eqBool (SC.closed (.eqNat (.div qT (.natLit D.distance)) (.natLit 0))) (SC.b true)

/-- At a PURE row-0 qubit `qT`, given the closed row guard `qT / d = 0`, the
`logicalZ` entry is `Z`.  Arity-1 ∀-D mirror of `lxPureEntryX`. -/
def lzPureEntryZ {Γ : List (SFormula 1)} (D : OddSurfaceDistance)
    (qT : Term 1 .nat) (hq : SFormula.PureNatTerm qT)
    (hguardq : SFormula.Deriv Γ (rowGuardPure1 D qT)) :
    SFormula.Deriv Γ (.eqPauli (.stabAt (liftedLZ1 D) (SC.closed qT)) (SC.p Pauli.Z)) := by
  have hguard : SFormula.Deriv Γ
      (.eqBool (SC.closed (Term.instantiateTopNat qT
        (.eqNat (.div Formula.qVar (.natLit D.distance)) (.natLit 0)))) (SC.b true)) := by
    simpa [rowGuardPure1, Formula.qVar,
      Term.instantiateTopNat, Term.instantiateNatAt] using hguardq
  have h := SFormula.Deriv.stabAtClosedIteLamEqThen (Γ := Γ)
    (.eqNat (.div Formula.qVar (.natLit D.distance)) (.natLit 0))
    (.pauliLit Pauli.Z) (.pauliLit Pauli.I)
    qT hq hguard
  simpa [liftedLZ1, logicalZOdd, logicalZ, Formula.qVar, SC.closed, SC.p,
    Term.instantiateTopNat, Term.instantiateNatAt, Term.lift] using h

/-! ### Local-commutation goal against `logicalZ`, and the row-guard raw form -/

/-- Local-commutation goal at the symbolic qubit, against `logicalZ`. -/
abbrev lcGoalZ (D : OddSurfaceDistance) : SFormula 2 :=
  SFormula.localCommutesAt (rowK2 D) (liftedLZ2 D) SFormula.boundNat

/-- The closed row guard at `boundNat`, raw `var0 / d = 0` form, as it appears
after unfolding `logicalZRowGuardAt2`. -/
abbrev rowGuardRaw2 (D : OddSurfaceDistance) : SFormula 2 :=
  .eqBool (SC.closed (.eqNat (.div (Term.var ⟨0, by decide⟩) (Term.natLit D.distance)) (Term.natLit 0)))
    (SC.b true)

/-- `logicalZRowGuardAt2 D = rowGuardRaw2 D` after the instantiation reduces. -/
theorem rowGuard2_eq (D : OddSurfaceDistance) :
    (SFormula.eqBool (logicalZRowGuardAt2 D) (SC.b true)) = rowGuardRaw2 D := by
  simp [logicalZRowGuardAt2, rowGuardRaw2, Formula.qVar, OddSurfaceDistance.distance,
    Term.instantiateTopNat, Term.instantiateNatAt]

/-- Row-0 local commutation from a non-`X` row entry.  Given the row guard true at
`boundNat` (so `logicalZ` entry is `Z`) and the row entry at `boundNat` equal to a
Pauli `p` with `anticommutes Z p = false`, the row locally commutes with `logicalZ`
at `boundNat`.  Mirror of `colCommFromEntry`. -/
def rowCommFromEntry {Δ : List (SFormula 2)} (D : OddSurfaceDistance) (p : Pauli)
    (hEntry : SFormula.Deriv Δ (.eqPauli (.stabAt (rowK2 D) SFormula.boundNat) (SC.p p)))
    (hAnti : SFormula.Deriv Δ (.eqBool (.anticommutes (SC.p Pauli.Z) (SC.p p)) (SC.b false)))
    (hrow : SFormula.Deriv Δ (.eqBool (logicalZRowGuardAt2 D) (SC.b true))) :
    SFormula.Deriv Δ (SFormula.localCommutesAt (rowK2 D) (liftedLZ2 D) SFormula.boundNat) := by
  refine SFormula.Deriv.localCommutesOfLeftEqNoAntiRight _ _ _ (SC.p p) hEntry ?_
  have hZ := lzOnRowEntryZ (Δ := Δ) D hrow
  have hLitFalse : SFormula.Deriv Δ
      (.eqBool (.anticommutes (.stabAt (liftedLZ2 D) SFormula.boundNat) (SC.p p)) (SC.b false)) :=
    SFormula.Deriv.anticommutesTransport _ (SC.p Pauli.Z) _ (SC.p p) (SC.b false)
      hZ (SFormula.Deriv.pauliEqLit p) hAnti
  exact SFormula.Deriv.eqBoolFalseNotTrue _ hLitFalse

/-- Local commutation from a leaf-peel entry equality (`baseLeafTreeTA` resolves to
a Pauli `p` commuting with `Z`), given the flat-entry fact in context.  Mirror of
`lcFromLeaf`. -/
def lcFromLeafZ {Δ : List (SFormula 2)} (D : OddSurfaceDistance) (p : Pauli)
    (hEntry : SFormula.Deriv Δ (entryFlat2F D))
    (hLeaf : SFormula.Deriv Δ (.eqPauli (SC.closed (baseLeafTreeTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.p p)))
    (hAnti : SFormula.Deriv Δ (.eqBool (.anticommutes (SC.p Pauli.Z) (SC.p p)) (SC.b false)))
    (hrow : SFormula.Deriv Δ (.eqBool (logicalZRowGuardAt2 D) (SC.b true))) :
    SFormula.Deriv Δ (lcGoalZ D) :=
  rowCommFromEntry D p
    (SFormula.Deriv.eqPauliTrans _ _ _ hEntry hLeaf) hAnti hrow

/-- `anticommutes Z I = false` and `anticommutes Z Z = false`, lit form. -/
def antiZI {Δ : List (SFormula 2)} : SFormula.Deriv Δ (.eqBool (.anticommutes (SC.p Pauli.Z) (SC.p Pauli.I)) (SC.b false)) :=
  SFormula.Deriv.pauliAnticommutesLit Pauli.Z Pauli.I
def antiZZ {Δ : List (SFormula 2)} : SFormula.Deriv Δ (.eqBool (.anticommutes (SC.p Pauli.Z) (SC.p Pauli.Z)) (SC.b false)) :=
  SFormula.Deriv.pauliAnticommutesLit Pauli.Z Pauli.Z

/-! ### Row-0 quantified arithmetic fact: bottom band is false on row 0

The transpose of `rightBandFalsePack`.  On row 0 (`q / d = 0`), the bottom-`X`
band guard is `false` (bottom-`X` lives in row `d-1 ≠ 0`). -/

abbrev bottomBandFalseBody (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (rowGuardRaw2 D)
    (.eqBool (SC.closed (bottomBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.b false))

abbrev bottomBandFalseF (D : OddSurfaceDistance) : SFormula 1 :=
  .allNatLt (nQ1 D) (bottomBandFalseBody D)

def bottomBandFalsePack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (bottomBandFalseF D) := by
  refine PureFamilyDerivA.allNatLtIntro _ ?_
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  have hd0 : (0 : Nat) ≠ D.distance - 1 := by omega
  simp only [bottomBandGuardTA, rowGuardRaw2, dX2, distAtBoundIdx2, kX2, dm1TA, orEqPair,
    SFormula.eval, SC.closed, SC.b, STerm.eval, Term.eval, Term.lift, bind, Option.bind]
  by_cases hq : rho ⟨0, by decide⟩ / D.distance = 0
  · -- row 0: inner `if q/d = d-1` is false (0 ≠ d-1 since d ≥ 3).
    rw [hq]
    simp only [hd0, decide_true, decide_false, Bool.false_eq_true, if_false, if_true, reduceIte]
  · simp only [hq, decide_false, Bool.false_eq_true, if_false, reduceIte]

/-- Extract the bottom-band-false fact at `boundNat` (under the row guard) from the
weakened quantified `bottomBandFalseF`.  Mirror of `rbfAtBound`. -/
def bbfAtBound {Δ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hW : SFormula.Deriv Δ (bottomBandFalseF D).weaken)
    (hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nQ1 D).weaken))
    (hrow : SFormula.Deriv Δ (rowGuardRaw2 D)) :
    SFormula.Deriv Δ (.eqBool (SC.closed (bottomBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.b false)) := by
  have hElim := SFormula.Deriv.allNatLtElim (nQ1 D).weaken
    ((bottomBandFalseBody D).lift 1) SFormula.boundNat hW hq
  have hBody := SFormula.Deriv.applyNatBoundNatBeta (bottomBandFalseBody D) hElim
  exact SFormula.Deriv.mp hBody hrow

/-- **Row-0 entry dispatcher.**  On the row-0 branch (row guard true at `boundNat`),
resolve the flat row entry by `boolCases` over the `baseLeafTreeTA` guards.  Every
`I`/`Z` leaf commutes with `Z` directly; the bottom-`X` leaf is excluded on row 0
(`bottomBandFalse`); the bulk-`X` and top-`X` leaves are delegated to per-class
handlers `hXbulk` / `hXtop`.  Transpose of `colDispatchOnTrue`. -/
def rowDispatchOnTrue {Δ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hEntry : SFormula.Deriv Δ (entryFlat2F D))
    (hrow : SFormula.Deriv Δ (.eqBool (logicalZRowGuardAt2 D) (SC.b true)))
    (hBBF : SFormula.Deriv Δ (.eqBool (SC.closed (bottomBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.b false)))
    (hXbulk : ∀ (Δ' : List (SFormula 2)),
      (∀ {A : SFormula 2}, SFormula.Deriv Δ A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (entryFlat2F D) →
      SFormula.Deriv Δ' (.eqBool (logicalZRowGuardAt2 D) (SC.b true)) →
      SFormula.Deriv Δ' (gBulk D true) → SFormula.Deriv Δ' (gBand D true) →
      SFormula.Deriv Δ' (gKind D false) → SFormula.Deriv Δ' (lcGoalZ D))
    (hXtop : ∀ (Δ' : List (SFormula 2)),
      (∀ {A : SFormula 2}, SFormula.Deriv Δ A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (entryFlat2F D) →
      SFormula.Deriv Δ' (.eqBool (logicalZRowGuardAt2 D) (SC.b true)) →
      SFormula.Deriv Δ' (gBulk D false) → SFormula.Deriv Δ' (gTopC D true) →
      SFormula.Deriv Δ' (gTopB D true) → SFormula.Deriv Δ' (lcGoalZ D)) :
    SFormula.Deriv Δ (lcGoalZ D) := by
  refine SFormula.Deriv.boolCases (SC.closed (bulkGuardTA (dX2 D) kX2)) _ ?_ ?_
  · -- bulk TRUE
    refine SFormula.Deriv.boolCases (SC.closed (baseBulkBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) _ ?_ ?_
    · -- band TRUE
      refine SFormula.Deriv.boolCases (SC.closed (baseKindGuardTA (dX2 D) kX2)) _ ?_ ?_
      · -- kind TRUE → bulk Z (commutes with Z)
        exact lcFromLeafZ D Pauli.Z (cw3 hEntry)
          (baseLeafZ _ _ _ (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption)
          antiZZ (cw3 hrow)
      · -- kind FALSE → bulk X (class (a) anti) → delegate
        exact hXbulk _ (fun h => cw3 h)
          (cw3 hEntry) (cw3 hrow) (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption
    · -- band FALSE → bulk I
      exact lcFromLeafZ D Pauli.I (cw2 hEntry)
        (baseLeafBulkI _ _ _ (.hyp (by right; left)) .assumption)
        antiZI (cw2 hrow)
  · -- bulk FALSE
    refine SFormula.Deriv.boolCases (SC.closed (topClassGuardTA (dX2 D) kX2)) _ ?_ ?_
    · -- topC TRUE
      refine SFormula.Deriv.boolCases (SC.closed (topBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) _ ?_ ?_
      · -- topB TRUE → top X (class (b) anti) → delegate
        exact hXtop _ (fun h => cw3 h)
          (cw3 hEntry) (cw3 hrow) (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption
      · -- topB FALSE → top I
        exact lcFromLeafZ D Pauli.I (cw3 hEntry)
          (baseLeafTopI _ _ _ (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption)
          antiZI (cw3 hrow)
    · -- topC FALSE
      refine SFormula.Deriv.boolCases (SC.closed (rightClassGuardTA (dX2 D) kX2)) _ ?_ ?_
      · -- rightC TRUE
        refine SFormula.Deriv.boolCases (SC.closed (rightBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) _ ?_ ?_
        · -- rightB TRUE → right Z (commutes with Z)
          exact lcFromLeafZ D Pauli.Z (cw4 hEntry)
            (baseLeafRightZ _ _ _ (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
              (.hyp (by right; left)) .assumption)
            antiZZ (cw4 hrow)
        · -- rightB FALSE → right I
          exact lcFromLeafZ D Pauli.I (cw4 hEntry)
            (baseLeafRightI _ _ _ (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
              (.hyp (by right; left)) .assumption)
            antiZI (cw4 hrow)
      · -- rightC FALSE
        refine SFormula.Deriv.boolCases (SC.closed (leftClassGuardTA (dX2 D) kX2)) _ ?_ ?_
        · -- leftC TRUE
          refine SFormula.Deriv.boolCases (SC.closed (leftBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) _ ?_ ?_
          · -- leftB TRUE → left Z (commutes with Z)
            exact lcFromLeafZ D Pauli.Z (cw5 hEntry)
              (baseLeafLeftZ _ _ _ (.hyp (by right; right; right; right; left))
                (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
                (.hyp (by right; left)) .assumption)
              antiZZ (cw5 hrow)
          · -- leftB FALSE → left I
            exact lcFromLeafZ D Pauli.I (cw5 hEntry)
              (baseLeafLeftI _ _ _ (.hyp (by right; right; right; right; left))
                (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
                (.hyp (by right; left)) .assumption)
              antiZI (cw5 hrow)
        · -- leftC FALSE
          refine SFormula.Deriv.boolCases (SC.closed (bottomBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) _ ?_ ?_
          · -- botB TRUE → contradiction with bottomBandFalse on row 0
            exact SFormula.Deriv.botElim
              (SFormula.Deriv.notElim .assumption
                (SFormula.Deriv.eqBoolFalseNotTrue _ (cw5 hBBF)))
          · -- botB FALSE → bottom I
            exact lcFromLeafZ D Pauli.I (cw5 hEntry)
              (baseLeafBottomI _ _ _ (.hyp (by right; right; right; right; left))
                (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
                (.hyp (by right; left)) .assumption)
              antiZI (cw5 hrow)

/-! ### Pointwise per-`k` commutation wrapper (against `logicalZ`) -/

/-- The per-`k` commutation goal at arity 1, against `logicalZ`. -/
abbrev commGoalZ1 (D : OddSurfaceDistance) : SFormula 1 :=
  SFormula.commutesUpTo (SC.closed (Term.lift 0 (Term.natLit (nQubits D.distance))))
    (SC.closed ((Term.lift 0 (Term.natLit D.distance)).recCall (Term.var ⟨0, Formula.normalizesCodeUpTo._proof_1⟩)))
    (SC.closed (Term.lift 0 (logicalZOdd D)))

/-- **Pointwise per-`k` commutation against `logicalZ`.**  Given the flat-entry and
bottom-band-false quantified facts (in `Γ`), and the two `X`-leaf handlers, the row
commutes with `logicalZ` pointwise.  Off row 0 → `logicalZOffRowLocalCommutes`; on
row 0 → `rowDispatchOnTrue`.  Transpose of `commPointwiseSym`. -/
def commPointwiseZSym {Γ : List (SFormula 1)} (D : OddSurfaceDistance)
    (hEntryF : SFormula.Deriv Γ (entryFlatF1 D))
    (hBBFF : SFormula.Deriv Γ (bottomBandFalseF D))
    (hXbulk : ∀ (Δ' : List (SFormula 2)),
      (∀ {A : SFormula 2}, SFormula.Deriv (.eqBool (logicalZRowGuardAt2 D) (SC.b true)
          :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (entryFlat2F D) →
      SFormula.Deriv Δ' (.eqBool (logicalZRowGuardAt2 D) (SC.b true)) →
      SFormula.Deriv Δ' (gBulk D true) → SFormula.Deriv Δ' (gBand D true) →
      SFormula.Deriv Δ' (gKind D false) → SFormula.Deriv Δ' (lcGoalZ D))
    (hXtop : ∀ (Δ' : List (SFormula 2)),
      (∀ {A : SFormula 2}, SFormula.Deriv (.eqBool (logicalZRowGuardAt2 D) (SC.b true)
          :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (entryFlat2F D) →
      SFormula.Deriv Δ' (.eqBool (logicalZRowGuardAt2 D) (SC.b true)) →
      SFormula.Deriv Δ' (gBulk D false) → SFormula.Deriv Δ' (gTopC D true) →
      SFormula.Deriv Δ' (gTopB D true) → SFormula.Deriv Δ' (lcGoalZ D)) :
    SFormula.Deriv Γ (commGoalZ1 D) := by
  refine SFormula.Deriv.commutesOfPointwise _ _ _ ?_
  unfold SFormula.pointwiseCommutesUpTo
  refine SFormula.Deriv.allNatLtIntroBounded _ _ ?_
  refine SFormula.Deriv.boolCases (logicalZRowGuardAt2 D) _ ?_ ?_
  · -- row TRUE.  Context: rowGuard(true) :: boundNatLt :: Γ.map weaken.
    have hEntryW :
        SFormula.Deriv (.eqBool (logicalZRowGuardAt2 D) (SC.b true)
          :: SFormula.boundNatLt (nQ1 D)
          :: List.map (fun G => G.weaken) Γ) (entryFlatF1 D).weaken :=
      cw2 (SFormula.Deriv.weakenFresh (A := entryFlatF1 D) hEntryF)
    have hBBFW :
        SFormula.Deriv (.eqBool (logicalZRowGuardAt2 D) (SC.b true)
          :: SFormula.boundNatLt (nQ1 D)
          :: List.map (fun G => G.weaken) Γ) (bottomBandFalseF D).weaken :=
      cw2 (SFormula.Deriv.weakenFresh (A := bottomBandFalseF D) hBBFF)
    have hq :
        SFormula.Deriv (.eqBool (logicalZRowGuardAt2 D) (SC.b true)
          :: SFormula.boundNatLt (nQ1 D)
          :: List.map (fun G => G.weaken) Γ)
          (SFormula.witnessLt SFormula.boundNat (nQ1 D).weaken) :=
      SFormula.Deriv.hyp (List.mem_cons_of_mem _ List.mem_cons_self)
    have hrowT :
        SFormula.Deriv (.eqBool (logicalZRowGuardAt2 D) (SC.b true)
          :: SFormula.boundNatLt (nQ1 D)
          :: List.map (fun G => G.weaken) Γ)
          (.eqBool (logicalZRowGuardAt2 D) (SC.b true)) := .assumption
    have hrowRaw :
        SFormula.Deriv (.eqBool (logicalZRowGuardAt2 D) (SC.b true)
          :: SFormula.boundNatLt (nQ1 D)
          :: List.map (fun G => G.weaken) Γ) (rowGuardRaw2 D) := by
      rw [← rowGuard2_eq]; exact hrowT
    have hEntry := entryAtBound D hEntryW hq
    have hBBF := bbfAtBound D hBBFW hq hrowRaw
    exact rowDispatchOnTrue D hEntry hrowT hBBF hXbulk hXtop
  · -- row FALSE → off-row
    exact logicalZOffRowLocalCommutes D (rowK2 D) .assumption

/-! ### k-only `r = 0` guard (the row-0 selector for class (a)) -/

abbrev gRZero1 (D : OddSurfaceDistance) (v : Bool) : SFormula 1 :=
  .eqBool (SC.closed (.eqNat (.div kX1 (dm1TA (dX1 D))) (.natLit 0))) (SC.b v)
abbrev gRZero2 (D : OddSurfaceDistance) (v : Bool) : SFormula 2 :=
  .eqBool (SC.closed (.eqNat (.div kX2 (dm1TA (dX2 D))) (.natLit 0))) (SC.b v)
theorem gRZero1_weaken (D : OddSurfaceDistance) (v : Bool) : (gRZero1 D v).weaken = gRZero2 D v := rfl

end QHL.CodeLang.Surface.Verify
