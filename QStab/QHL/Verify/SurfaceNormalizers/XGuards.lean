import QStab.QHL.Verify.SurfaceNormalizers.XLogicalXEntries

/-!
# Logical-normalizer consumers — XGuards

Arity-2 guard-fact abbreviations, the pointwise per-`k` commutation wrapper, and the k-only
guard facts (arity 1) with their bridge into the qubit binder.
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface

set_option maxRecDepth 65536

/-! ## Guard-fact abbreviations at arity 2 (`k = var 1`, qubit binder `var 0`) -/

abbrev gBulk (D : OddSurfaceDistance) (v : Bool) : SFormula 2 :=
  .eqBool (SC.closed (bulkGuardTA (dX2 D) kX2)) (SC.b v)
abbrev gBand (D : OddSurfaceDistance) (v : Bool) : SFormula 2 :=
  .eqBool (SC.closed (baseBulkBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.b v)
abbrev gKind (D : OddSurfaceDistance) (v : Bool) : SFormula 2 :=
  .eqBool (SC.closed (baseKindGuardTA (dX2 D) kX2)) (SC.b v)
abbrev gTopC (D : OddSurfaceDistance) (v : Bool) : SFormula 2 :=
  .eqBool (SC.closed (topClassGuardTA (dX2 D) kX2)) (SC.b v)
abbrev gTopB (D : OddSurfaceDistance) (v : Bool) : SFormula 2 :=
  .eqBool (SC.closed (topBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.b v)
abbrev gRightC (D : OddSurfaceDistance) (v : Bool) : SFormula 2 :=
  .eqBool (SC.closed (rightClassGuardTA (dX2 D) kX2)) (SC.b v)
abbrev gRightB (D : OddSurfaceDistance) (v : Bool) : SFormula 2 :=
  .eqBool (SC.closed (rightBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.b v)
abbrev gLeftC (D : OddSurfaceDistance) (v : Bool) : SFormula 2 :=
  .eqBool (SC.closed (leftClassGuardTA (dX2 D) kX2)) (SC.b v)
abbrev gLeftB (D : OddSurfaceDistance) (v : Bool) : SFormula 2 :=
  .eqBool (SC.closed (leftBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.b v)
abbrev gBotB (D : OddSurfaceDistance) (v : Bool) : SFormula 2 :=
  .eqBool (SC.closed (bottomBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.b v)

/-- Local-commutation goal at the symbolic qubit. -/
abbrev lcGoal (D : OddSurfaceDistance) : SFormula 2 :=
  SFormula.localCommutesAt (rowK2 D) (liftedLX2 D) SFormula.boundNat

/-- The flat-entry equality at the symbolic qubit, as a formula (cut into context). -/
abbrev entryFlat2F (D : OddSurfaceDistance) : SFormula 2 :=
  .eqPauli (.stabAt (rowK2 D) SFormula.boundNat)
    (SC.closed (baseLeafTreeTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩)))

/-- Local commutation from a leaf-peel entry equality (`baseLeafTreeTA` resolves to
a Pauli `p` commuting with `X`), given the flat-entry fact in context. -/
def lcFromLeaf {Δ : List (SFormula 2)} (D : OddSurfaceDistance) (p : Pauli)
    (hEntry : SFormula.Deriv Δ (entryFlat2F D))
    (hLeaf : SFormula.Deriv Δ (.eqPauli (SC.closed (baseLeafTreeTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.p p)))
    (hAnti : SFormula.Deriv Δ (.eqBool (.anticommutes (SC.p Pauli.X) (SC.p p)) (SC.b false)))
    (hcol : SFormula.Deriv Δ (.eqBool (logicalXColGuardAt2 D) (SC.b true))) :
    SFormula.Deriv Δ (lcGoal D) :=
  colCommFromEntry D p
    (SFormula.Deriv.eqPauliTrans _ _ _ hEntry hLeaf) hAnti hcol

/-- Contradiction from a guard asserted both `true` and `false`. -/
def eqBoolContra {arity : Nat} {Δ : List (SFormula arity)} {C : SFormula arity} (b : STerm arity .bool)
    (hT : SFormula.Deriv Δ (.eqBool b (SC.b true)))
    (hF : SFormula.Deriv Δ (.eqBool b (SC.b false))) :
    SFormula.Deriv Δ C :=
  SFormula.Deriv.botElim (SFormula.Deriv.notElim hT (SFormula.Deriv.eqBoolFalseNotTrue _ hF))

/-- `anticommutes X I = false` and `anticommutes X X = false`, lit form. -/
def antiXI {Δ : List (SFormula 2)} : SFormula.Deriv Δ (.eqBool (.anticommutes (SC.p Pauli.X) (SC.p Pauli.I)) (SC.b false)) :=
  SFormula.Deriv.pauliAnticommutesLit Pauli.X Pauli.I
def antiXX {Δ : List (SFormula 2)} : SFormula.Deriv Δ (.eqBool (.anticommutes (SC.p Pauli.X) (SC.p Pauli.X)) (SC.b false)) :=
  SFormula.Deriv.pauliAnticommutesLit Pauli.X Pauli.X

/-- Context weakening by `n` fresh leading hypotheses (used to lift a Δ-derivation
into the deeper context produced by nested `boolCases`). -/
def cw1 {arity : Nat} {Δ : List (SFormula arity)} {A B : SFormula arity}
    (h : SFormula.Deriv Δ A) : SFormula.Deriv (B :: Δ) A :=
  SFormula.Deriv.contextWeakening (fun _C hC => List.mem_cons_of_mem _ hC) h
def cw2 {arity : Nat} {Δ : List (SFormula arity)} {A B C : SFormula arity}
    (h : SFormula.Deriv Δ A) : SFormula.Deriv (B :: C :: Δ) A := cw1 (cw1 h)
def cw3 {arity : Nat} {Δ : List (SFormula arity)} {A B C E : SFormula arity}
    (h : SFormula.Deriv Δ A) : SFormula.Deriv (B :: C :: E :: Δ) A := cw1 (cw2 h)
def cw4 {arity : Nat} {Δ : List (SFormula arity)} {A B C E F : SFormula arity}
    (h : SFormula.Deriv Δ A) : SFormula.Deriv (B :: C :: E :: F :: Δ) A := cw1 (cw3 h)
def cw5 {arity : Nat} {Δ : List (SFormula arity)} {A B C E F G : SFormula arity}
    (h : SFormula.Deriv Δ A) : SFormula.Deriv (B :: C :: E :: F :: G :: Δ) A := cw1 (cw4 h)

/-- **Column-0 entry dispatcher.**  On the column-0 branch (column guard true at
`boundNat`), resolve the flat row entry by `boolCases` over the `baseLeafTreeTA`
guards.  Every `I`/`X` leaf commutes with `X` directly; the right-`Z` leaf is
excluded on column 0 (`rightBandFalse`); the bulk-`Z` and left-`Z` leaves are
delegated to per-class handlers `hZbulk` / `hZleft` (which see the cascade guards in
context). -/
def colDispatchOnTrue {Δ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hEntry : SFormula.Deriv Δ (entryFlat2F D))
    (hcol : SFormula.Deriv Δ (.eqBool (logicalXColGuardAt2 D) (SC.b true)))
    (hRBF : SFormula.Deriv Δ (.eqBool (SC.closed (rightBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.b false)))
    (hZbulk : ∀ (Δ' : List (SFormula 2)),
      (∀ {A : SFormula 2}, SFormula.Deriv Δ A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (entryFlat2F D) →
      SFormula.Deriv Δ' (.eqBool (logicalXColGuardAt2 D) (SC.b true)) →
      SFormula.Deriv Δ' (gBulk D true) → SFormula.Deriv Δ' (gBand D true) →
      SFormula.Deriv Δ' (gKind D true) → SFormula.Deriv Δ' (lcGoal D))
    (hZleft : ∀ (Δ' : List (SFormula 2)),
      (∀ {A : SFormula 2}, SFormula.Deriv Δ A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (entryFlat2F D) →
      SFormula.Deriv Δ' (.eqBool (logicalXColGuardAt2 D) (SC.b true)) →
      SFormula.Deriv Δ' (gBulk D false) → SFormula.Deriv Δ' (gTopC D false) →
      SFormula.Deriv Δ' (gRightC D false) → SFormula.Deriv Δ' (gLeftC D true) →
      SFormula.Deriv Δ' (gLeftB D true) → SFormula.Deriv Δ' (lcGoal D)) :
    SFormula.Deriv Δ (lcGoal D) := by
  -- helper to weaken an existing Δ-derivation under one fresh hypothesis
  refine SFormula.Deriv.boolCases (SC.closed (bulkGuardTA (dX2 D) kX2)) _ ?_ ?_
  · -- bulk TRUE
    refine SFormula.Deriv.boolCases (SC.closed (baseBulkBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) _ ?_ ?_
    · -- band TRUE
      refine SFormula.Deriv.boolCases (SC.closed (baseKindGuardTA (dX2 D) kX2)) _ ?_ ?_
      · -- kind TRUE → bulk Z
        exact hZbulk _ (fun h => cw3 h)
          (cw3 hEntry) (cw3 hcol) (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption
      · -- kind FALSE → bulk X
        exact lcFromLeaf D Pauli.X (cw3 hEntry)
          (baseLeafBulkX _ _ _ (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption)
          antiXX (cw3 hcol)
    · -- band FALSE → bulk I
      exact lcFromLeaf D Pauli.I (cw2 hEntry)
        (baseLeafBulkI _ _ _ (.hyp (by right; left)) .assumption)
        antiXI (cw2 hcol)
  · -- bulk FALSE
    refine SFormula.Deriv.boolCases (SC.closed (topClassGuardTA (dX2 D) kX2)) _ ?_ ?_
    · -- topC TRUE
      refine SFormula.Deriv.boolCases (SC.closed (topBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) _ ?_ ?_
      · -- topB TRUE → top X
        exact lcFromLeaf D Pauli.X (cw3 hEntry)
          (baseLeafTopX _ _ _ (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption)
          antiXX (cw3 hcol)
      · -- topB FALSE → top I
        exact lcFromLeaf D Pauli.I (cw3 hEntry)
          (baseLeafTopI _ _ _ (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption)
          antiXI (cw3 hcol)
    · -- topC FALSE
      refine SFormula.Deriv.boolCases (SC.closed (rightClassGuardTA (dX2 D) kX2)) _ ?_ ?_
      · -- rightC TRUE
        refine SFormula.Deriv.boolCases (SC.closed (rightBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) _ ?_ ?_
        · -- rightB TRUE → contradiction with rightBandFalse on column 0
          exact SFormula.Deriv.botElim
            (SFormula.Deriv.notElim .assumption
              (SFormula.Deriv.eqBoolFalseNotTrue _ (cw4 hRBF)))
        · -- rightB FALSE → right I
          exact lcFromLeaf D Pauli.I (cw4 hEntry)
            (baseLeafRightI _ _ _ (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
              (.hyp (by right; left)) .assumption)
            antiXI (cw4 hcol)
      · -- rightC FALSE
        refine SFormula.Deriv.boolCases (SC.closed (leftClassGuardTA (dX2 D) kX2)) _ ?_ ?_
        · -- leftC TRUE
          refine SFormula.Deriv.boolCases (SC.closed (leftBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) _ ?_ ?_
          · -- leftB TRUE → left Z
            exact hZleft _ (fun h => cw5 h) (cw5 hEntry) (cw5 hcol)
              (.hyp (by right; right; right; right; left)) (.hyp (by right; right; right; left))
              (.hyp (by right; right; left)) (.hyp (by right; left)) .assumption
          · -- leftB FALSE → left I
            exact lcFromLeaf D Pauli.I (cw5 hEntry)
              (baseLeafLeftI _ _ _ (.hyp (by right; right; right; right; left))
                (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
                (.hyp (by right; left)) .assumption)
              antiXI (cw5 hcol)
        · -- leftC FALSE
          refine SFormula.Deriv.boolCases (SC.closed (bottomBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) _ ?_ ?_
          · -- botB TRUE → bottom X
            exact lcFromLeaf D Pauli.X (cw5 hEntry)
              (baseLeafBottomX _ _ _ (.hyp (by right; right; right; right; left))
                (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
                (.hyp (by right; left)) .assumption)
              antiXX (cw5 hcol)
          · -- botB FALSE → bottom I
            exact lcFromLeaf D Pauli.I (cw5 hEntry)
              (baseLeafBottomI _ _ _ (.hyp (by right; right; right; right; left))
                (.hyp (by right; right; right; left)) (.hyp (by right; right; left))
                (.hyp (by right; left)) .assumption)
              antiXI (cw5 hcol)

/-! ## Pointwise per-`k` commutation wrapper

`commutesOfPointwise` reduces the per-`k` goal to local commutation at every qubit.
Off column 0 the `logicalX` entry is `I` (`logicalXOffColumnLocalCommutes`); on
column 0 we resolve via `colDispatchOnTrue`.  The flat-entry fact and the
right-band-false fact are cut into the qubit-binder context; the two `Z`-leaf
handlers are supplied per class. -/

/-- The per-`k` commutation goal at arity 1. -/
abbrev commGoal1 (D : OddSurfaceDistance) : SFormula 1 :=
  SFormula.commutesUpTo (SC.closed (Term.lift 0 (Term.natLit (nQubits D.distance))))
    (SC.closed ((Term.lift 0 (Term.natLit D.distance)).recCall (Term.var ⟨0, Formula.normalizesCodeUpTo._proof_1⟩)))
    (SC.closed (Term.lift 0 (logicalXOdd D)))

/-- The flat-entry fact, quantified over the qubit `q < nQubits`, at arity 1, so it
can be eliminated at `boundNat` inside the qubit binder.  Its body is exactly
`entryFlat2F D` (with `k = var 1`, `q = var 0`). -/
abbrev entryFlatF1 (D : OddSurfaceDistance) : SFormula 1 :=
  .allNatLt (nQ1 D) (entryFlat2F D)

def entryFlatPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (entryFlatF1 D) :=
  PureFamilyDerivA.allNatLtIntro _ (xEntryFlat2BoundW D)

/-! ## k-only guard facts at arity 1, and their bridge into the qubit binder

The bulk / kind / class guards depend only on `k` (here `var 0` at arity 1).  We
`boolCases` on them at arity 1 to classify `k`, then weaken each fact into the qubit
binder, where it becomes the matching arity-2 `g*` guard fact (`k = var 1`). -/

abbrev gBulk1 (D : OddSurfaceDistance) (v : Bool) : SFormula 1 :=
  .eqBool (SC.closed (bulkGuardTA (dX1 D) kX1)) (SC.b v)
abbrev gKind1 (D : OddSurfaceDistance) (v : Bool) : SFormula 1 :=
  .eqBool (SC.closed (baseKindGuardTA (dX1 D) kX1)) (SC.b v)
abbrev gTopC1 (D : OddSurfaceDistance) (v : Bool) : SFormula 1 :=
  .eqBool (SC.closed (topClassGuardTA (dX1 D) kX1)) (SC.b v)
abbrev gRightC1 (D : OddSurfaceDistance) (v : Bool) : SFormula 1 :=
  .eqBool (SC.closed (rightClassGuardTA (dX1 D) kX1)) (SC.b v)
abbrev gLeftC1 (D : OddSurfaceDistance) (v : Bool) : SFormula 1 :=
  .eqBool (SC.closed (leftClassGuardTA (dX1 D) kX1)) (SC.b v)

theorem gBulk1_weaken (D : OddSurfaceDistance) (v : Bool) : (gBulk1 D v).weaken = gBulk D v := rfl
theorem gKind1_weaken (D : OddSurfaceDistance) (v : Bool) : (gKind1 D v).weaken = gKind D v := rfl
theorem gTopC1_weaken (D : OddSurfaceDistance) (v : Bool) : (gTopC1 D v).weaken = gTopC D v := rfl
theorem gRightC1_weaken (D : OddSurfaceDistance) (v : Bool) : (gRightC1 D v).weaken = gRightC D v := rfl
theorem gLeftC1_weaken (D : OddSurfaceDistance) (v : Bool) : (gLeftC1 D v).weaken = gLeftC D v := rfl

theorem cZero1_weaken (D : OddSurfaceDistance) (v : Bool) : (cZero1 D v).weaken = cZero2 D v := rfl

/-- Extract the flat-entry fact at the symbolic qubit `boundNat` from the weakened
quantified `entryFlatF1`. -/
def entryAtBound {Δ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hW : SFormula.Deriv Δ (entryFlatF1 D).weaken)
    (hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nQ1 D).weaken)) :
    SFormula.Deriv Δ (entryFlat2F D) := by
  have hElim := SFormula.Deriv.allNatLtElim (nQ1 D).weaken
    ((entryFlat2F D).lift 1) SFormula.boundNat hW hq
  exact SFormula.Deriv.applyNatBoundNatBeta (entryFlat2F D) hElim

/-- Extract the right-band-false fact at `boundNat` (under the column guard) from
the weakened quantified `rightBandFalseF`. -/
def rbfAtBound {Δ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hW : SFormula.Deriv Δ (rightBandFalseF D).weaken)
    (hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nQ1 D).weaken))
    (hcol : SFormula.Deriv Δ (colGuardRaw2 D)) :
    SFormula.Deriv Δ (.eqBool (SC.closed (rightBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.b false)) := by
  have hElim := SFormula.Deriv.allNatLtElim (nQ1 D).weaken
    ((rightBandFalseBody D).lift 1) SFormula.boundNat hW hq
  have hBody := SFormula.Deriv.applyNatBoundNatBeta (rightBandFalseBody D) hElim
  exact SFormula.Deriv.mp hBody hcol

/-- **Pointwise per-`k` commutation.**  Given the flat-entry and right-band-false
quantified facts (in `Γ`), and the two `Z`-leaf handlers, the row commutes with
`logicalX` pointwise.  Off column 0 → `logicalXOffColumnLocalCommutes`; on column 0
→ `colDispatchOnTrue`.  Each `Z`-leaf handler is given the qubit-binder context as a
black box `Δ'` (it must close `lcGoal D`). -/
def commPointwiseSym {Γ : List (SFormula 1)} (D : OddSurfaceDistance)
    (hEntryF : SFormula.Deriv Γ (entryFlatF1 D))
    (hRBFF : SFormula.Deriv Γ (rightBandFalseF D))
    (hZbulk : ∀ (Δ' : List (SFormula 2)),
      (∀ {A : SFormula 2}, SFormula.Deriv (.eqBool (logicalXColGuardAt2 D) (SC.b true)
          :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (entryFlat2F D) →
      SFormula.Deriv Δ' (.eqBool (logicalXColGuardAt2 D) (SC.b true)) →
      SFormula.Deriv Δ' (gBulk D true) → SFormula.Deriv Δ' (gBand D true) →
      SFormula.Deriv Δ' (gKind D true) → SFormula.Deriv Δ' (lcGoal D))
    (hZleft : ∀ (Δ' : List (SFormula 2)),
      (∀ {A : SFormula 2}, SFormula.Deriv (.eqBool (logicalXColGuardAt2 D) (SC.b true)
          :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (entryFlat2F D) →
      SFormula.Deriv Δ' (.eqBool (logicalXColGuardAt2 D) (SC.b true)) →
      SFormula.Deriv Δ' (gBulk D false) → SFormula.Deriv Δ' (gTopC D false) →
      SFormula.Deriv Δ' (gRightC D false) → SFormula.Deriv Δ' (gLeftC D true) →
      SFormula.Deriv Δ' (gLeftB D true) → SFormula.Deriv Δ' (lcGoal D)) :
    SFormula.Deriv Γ (commGoal1 D) := by
  refine SFormula.Deriv.commutesOfPointwise _ _ _ ?_
  unfold SFormula.pointwiseCommutesUpTo
  refine SFormula.Deriv.allNatLtIntroBounded _ _ ?_
  -- Context now: boundNatLt nQubits :: Γ.map weaken.
  refine SFormula.Deriv.boolCases (logicalXColGuardAt2 D) _ ?_ ?_
  · -- column TRUE.  Context: colGuard(true) :: boundNatLt :: Γ.map weaken.
    have hEntryW :
        SFormula.Deriv (.eqBool (logicalXColGuardAt2 D) (SC.b true)
          :: SFormula.boundNatLt (nQ1 D)
          :: List.map (fun G => G.weaken) Γ) (entryFlatF1 D).weaken :=
      cw2 (SFormula.Deriv.weakenFresh (A := entryFlatF1 D) hEntryF)
    have hRBFW :
        SFormula.Deriv (.eqBool (logicalXColGuardAt2 D) (SC.b true)
          :: SFormula.boundNatLt (nQ1 D)
          :: List.map (fun G => G.weaken) Γ) (rightBandFalseF D).weaken :=
      cw2 (SFormula.Deriv.weakenFresh (A := rightBandFalseF D) hRBFF)
    have hq :
        SFormula.Deriv (.eqBool (logicalXColGuardAt2 D) (SC.b true)
          :: SFormula.boundNatLt (nQ1 D)
          :: List.map (fun G => G.weaken) Γ)
          (SFormula.witnessLt SFormula.boundNat (nQ1 D).weaken) :=
      SFormula.Deriv.hyp (List.mem_cons_of_mem _ List.mem_cons_self)
    have hcolT :
        SFormula.Deriv (.eqBool (logicalXColGuardAt2 D) (SC.b true)
          :: SFormula.boundNatLt (nQ1 D)
          :: List.map (fun G => G.weaken) Γ)
          (.eqBool (logicalXColGuardAt2 D) (SC.b true)) := .assumption
    have hcolRaw :
        SFormula.Deriv (.eqBool (logicalXColGuardAt2 D) (SC.b true)
          :: SFormula.boundNatLt (nQ1 D)
          :: List.map (fun G => G.weaken) Γ) (colGuardRaw2 D) := by
      rw [← colGuard2_eq]; exact hcolT
    have hEntry := entryAtBound D hEntryW hq
    have hRBF := rbfAtBound D hRBFW hq hcolRaw
    exact colDispatchOnTrue D hEntry hcolT hRBF hZbulk hZleft
  · -- column FALSE → off-column
    exact logicalXOffColumnLocalCommutes D (rowK2 D) .assumption

end QHL.CodeLang.Surface.Verify
