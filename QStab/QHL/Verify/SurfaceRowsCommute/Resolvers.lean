import QStab.QHL.Verify.SurfaceRowsCommute.Setup

/-!
# Rows-commute (pairwise generated-row commutation) — Resolvers

The single-row leaf resolver (continuation-passing `boolCases` cascade), the guard-exposing
leaf resolvers, and the full local-commutation dispatcher.
-/

namespace QHL.CodeLang.Surface.Verify
open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface

set_option maxRecDepth 65536
set_option linter.unusedVariables false

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

end QHL.CodeLang.Surface.Verify
