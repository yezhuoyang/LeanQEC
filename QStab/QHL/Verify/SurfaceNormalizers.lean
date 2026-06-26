import QStab.QHL.Verify.SurfaceRowCharacterizationSymbolic
import QStab.QHL.Verify.SurfaceCodeLevelPure
import QStab.QHL.Verify.SurfaceFlatBridge

/-!
# Logical-normalizer consumers (TASK B)

`xNorm` / `zNorm` : the two logical operators `logicalX` / `logicalZ` commute with
every generated stabilizer row of the recursive Surface code.  These are two of
the three inputs to `codeLevelPureFromGeneratedRows`.

Prover-side only: no new logic rules, no `native_decide` / `Formula.check` /
`deriveTrue?` / `admit` / axioms / oracles.

## State of TASK B (honest)

The CSS overlap structure (confirmed by `#eval` on the evaluator, NOT used in any
proof) is: a generated row anticommutes with `logicalX` at **exactly 0 or 2**
column-0 qubits — never odd — so commutation always holds.  Concretely for `d=3`
stabilizers 0,6 overlap at 2; for `d=5` stabilizers 0,8,20,21 overlap at 2; all
other rows overlap at 0.

The faithful, sorry-free row-entry characterization `surfaceRowEntryCharSymbolicA`
(TASK A) resolves the symbolic row entry to the guarded leaf tree `rowSymTreeA`.

### Progress in this file (axiom-clean `[propext, Quot.sound]`)

The `recCall` obstacle is fully discharged:

* `boundRowEntryPure` / `boundRowsResolved` — for *every* qubit `q < nQubits`,
  the bound-index generated row entry `stabAt (recCall (lift d) k) q` equals the
  recursion-free leaf tree `rowSymTreeA D.index (lift d) (lift k) q`.  Built
  directly from `surfaceRowEntryCharSymbolicA`, no new rule.

* `xNormScaffold` then `cut1`s `boundRowsResolved` in, so the remaining goal is a
  pure `SFormula.Deriv` derivation of
  `commutesUpTo n (recCall (lift d) (var 0)) (lift logicalX)` **with the
  resolved-row equality available as an `SFormula.Deriv` hypothesis** — i.e. with
  the `recCall` already eliminated to a literal `rowSymTreeA` tree (via
  `allNatLtElim` of the hypothesis at any qubit).  This is the precise frontier:
  a recursion-free parity statement on the resolved tree, where `boolCases` on the
  (purely arithmetic) cell guards is now legal.

### Partial progress landed (axiom-clean `[propext, Quot.sound]`, sorry-free)

The **off-support** half of each normalizer is now factored out into two
reusable, sorry-free lemmas:

* `logicalXOffColumnLocalCommutes` — at every qubit where the `logicalX` column
  guard `q mod d = 0` is `false`, the `logicalX` entry is `I`, so it locally
  commutes with *any* row entry there (via `localCommutesOfRightI` + the
  `else`-branch entry peel).  No parity content, no `recCall`, no oracle.
* `logicalZOffRowLocalCommutes` — the row/column transpose for `logicalZ`
  (`q / d = 0`).

These discharge the entire all-others premise *off* the relevant logical line,
for every recursion depth.

### Both normalizers fully closed (axiom-clean, sorry-free)

The **column-0 (resp. top-row) even-parity argument** is now fully mechanized for
every `D`: classify the bound stabilizer index `k = var 0` by its (purely
arithmetic) cell guards and supply, via `commutesOfTwoAnti`, the two
anticommuting qubits as functions of `k` (`commutesOfPointwise` for the
commuting classes).  `xNormCommuteSym` (`logicalX`, column 0) and its row/column
transpose `zNormCommuteSym` (`logicalZ`, row 0) discharge the per-`k` commutation
goal completely; `xNormScaffold := xNormCommuteSym` and
`zNormScaffold := zNormCommuteSym`.  Axiom-clean
`[propext, Classical.choice, Quot.sound]`, sorry-free.
-/

namespace QHL.CodeLang.Surface.Verify

open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface

set_option maxRecDepth 65536

/-! ## The distance witness at the consumer arity

The consumers introduce the stabilizer index via `allNatLt`, exposing the body at
arity 1 with `kT = boundIdx = .var 0`.  The distance literal `(d).weaken` at that
arity is `DistAtA.lit 1 D.index` once we know `nQubits`/`oddDistance` line up. -/

/-- The distance witness for the weakened distance literal `(natLit d).lift 0`,
keyed to `D.index`, at arity 1.  `oddDistance D.index = D.distance` by definition,
so the literal `.natLit D.distance` evaluates to `oddDistance D.index`. -/
def distAtBoundIdx (D : OddSurfaceDistance) :
    DistAtA 1 D.index where
  dT := Term.lift 0 (.natLit D.distance)
  pure := SFormula.PureNatTerm.natLit (arity := 1) D.distance
  evalsTo := by
    intro fuel rho
    simp only [Term.lift, Term.eval, OddSurfaceDistance.distance]

#print axioms distAtBoundIdx

/-! ## Discharging the `recCall` obstacle: universally-quantified resolved rows

The generated code row entry `stabAt (recCall (lift d) (var 0)) q` (the body row
at the object-logic bound stabilizer index `k = var 0`) resolves — for *every*
pure qubit term `q` — to the fully-resolved leaf tree
`rowSymTreeA D.index (lift d) (lift k) q` (TASK A, `surfaceRowEntryCharSymbolicA`).

`boundRowsResolved` packages this as a single object-logic formula
`∀ q < n, stabAt rowK q = rowSymTreeA … q`, built by `allNatLtIntro` over the
per-entry characterization.  Cutting this in (`cut1`/`cut2`) turns the symbolic
row entry into the recursion-free literal tree *as an `SFormula.Deriv`
hypothesis*, so the downstream parity argument can `boolCases` on the (purely
arithmetic) cell guards of `rowSymTreeA` — the architectural move the
`PureFamilyDerivA` layer cannot perform directly (no `boolCases`), now legal
because the residual is `recCall`-free. -/

/-- Distance witness at arity 2 with the *syntactic* twice-lifted literal
`lift 0 (lift 0 (natLit d))`, keyed to `D.index`.  (Inside the
`allNatLt n` body, with the qubit binder added, the lifted stabilizer index `k`
is `var 1` and the distance literal carries two lifts.) -/
def distAtBoundIdx2 (D : OddSurfaceDistance) :
    DistAtA 2 D.index where
  dT := Term.lift 0 (Term.lift 0 (Term.natLit D.distance))
  pure := SFormula.PureNatTerm.natLit (arity := 2) D.distance
  evalsTo := by
    intro fuel rho
    simp only [Term.lift, Term.eval, OddSurfaceDistance.distance]

/-- The lifted stabilizer index inside the `allNatLt n` body of
`normalizesCodeUpTo`: `var 1` (= the once-weakened bound index `k`). -/
def liftedBoundIdx : Term 2 .nat := Term.lift 0 (boundIdx (arity := 0))

/-- The per-qubit entry equality at the bound stabilizer index and bound qubit:
`stabAt (recCall (lift0 (lift0 d)) (var 1)) (var 0) = rowSymTreeA … (var 0)`.
Direct specialization of `surfaceRowEntryCharSymbolicA` to the consumer indices.
This fully resolves the `recCall` row entry to a recursion-free leaf tree. -/
def boundRowEntryPure (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2)
      (.eqPauli
        (.stabAt (SC.closed (.recCall (distAtBoundIdx2 D).dT liftedBoundIdx))
          (SC.closed Formula.qVar))
        (SC.closed (rowSymTreeA D.index (distAtBoundIdx2 D).dT liftedBoundIdx Formula.qVar))) :=
  surfaceRowEntryCharSymbolicA D.index (distAtBoundIdx2 D)
    liftedBoundIdx Formula.qVar
    (SFormula.PureNatTerm.var ⟨1, by decide⟩)
    (SFormula.PureNatTerm.var ⟨0, by decide⟩)

/-- **Resolved rows, quantified.**  For every qubit `q < nQubits`, the bound-index
generated row entry equals the recursion-free leaf tree.  This is the cut premise
that converts the `recCall` row into a literal tree as an `SFormula.Deriv`
hypothesis — discharging the `recCall` obstacle for the downstream parity argument. -/
def boundRowsResolved (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2)
      (.allNatLt (SC.n (nQubits D.distance))
        (.eqPauli
          (.stabAt (SC.closed (.recCall (distAtBoundIdx2 D).dT liftedBoundIdx))
            (SC.closed Formula.qVar))
          (SC.closed (rowSymTreeA D.index (distAtBoundIdx2 D).dT liftedBoundIdx Formula.qVar)))) :=
  PureFamilyDerivA.allNatLtIntro _ (boundRowEntryPure D)

/-! ## Reusable off-support local-commutation lemmas (axiom-clean, sorry-free)

The logical operators are *single-column* (`logicalX`: `X` exactly on column-0
qubits, `I` elsewhere) and *single-row* (`logicalZ`: `Z` exactly on top-row
qubits, `I` elsewhere).  Hence at every qubit OFF the relevant line the logical
entry is the identity, so it commutes with *any* row entry there — independently
of the row's CSS type or the recursion depth.  These two lemmas package exactly
that fact at the consumer arity (under the stabilizer-index binder, with the
qubit binder `boundNat`): given the closed column/row guard is `false` at the
bound qubit, `localCommutesAt A logicalX/logicalZ boundNat` holds via
`localCommutesOfRightI`.  They contain no parity content and are the
`all-others-commute` workhorse for the eventual `commutesOfTwoAnti` /
`commutesOfPointwise` assembly.  No `recCall`, no oracle, no fixed-entry
hypothesis on `A`. -/

/-- The `logicalX` column guard at the bound qubit, as a closed boolean STerm at
arity 2 (stabilizer-index binder · qubit binder).  This is the instantiation of
the `logicalX` lambda condition `q mod d = 0` at the bound qubit `var 0`. -/
def logicalXColGuardAt2 (D : OddSurfaceDistance) : STerm 2 .bool :=
  SC.closed (Term.instantiateTopNat (Term.var ⟨0, by decide⟩)
    (.eqNat (.mod Formula.qVar (.natLit D.distance)) (.natLit 0)))

/-- The `logicalZ` row guard at the bound qubit, as a closed boolean STerm at
arity 2.  Instantiation of the `logicalZ` lambda condition `q / d = 0` at the
bound qubit. -/
def logicalZRowGuardAt2 (D : OddSurfaceDistance) : STerm 2 .bool :=
  SC.closed (Term.instantiateTopNat (Term.var ⟨0, by decide⟩)
    (.eqNat (.div Formula.qVar (.natLit D.distance)) (.natLit 0)))

/-- **Off-column local commutation (X).**  For any left stabilizer `A`, in any
context `Γ`, if the `logicalX` column guard is `false` at the bound qubit then
`A` locally commutes with the lifted `logicalX` there, because the `logicalX`
entry is `I`.  Sorry-free; only `localCommutesOfRightI` + the `else`-branch entry
peel. -/
def logicalXOffColumnLocalCommutes {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (A : STerm 2 .stab) :
    SFormula.Deriv Γ (.eqBool (logicalXColGuardAt2 D) (SC.b false)) ->
      SFormula.Deriv Γ
        (SFormula.localCommutesAt A (SC.closed (Term.lift 0 (logicalXOdd D))).weaken
          SFormula.boundNat) := by
  intro hFalse
  refine SFormula.Deriv.localCommutesOfRightI _ _ _ ?_
  have h := SFormula.Deriv.stabAtClosedIteLamEqElse (Γ := Γ)
    (.eqNat (.mod Formula.qVar (.natLit D.distance)) (.natLit 0))
    (.pauliLit Pauli.X) (.pauliLit Pauli.I)
    (Term.var ⟨0, by decide⟩)
    (SFormula.PureNatTerm.var ⟨0, by decide⟩)
    (by simpa [logicalXColGuardAt2] using hFalse)
  simpa [logicalXOdd, logicalX, Formula.qVar, SFormula.boundNat, SC.closed, SC.p,
    STerm.weaken, STerm.lift, Term.instantiateTopNat, Term.instantiateNatAt, Term.lift,
    Term.weaken, Term.weakenVar] using h

/-- **Off-row local commutation (Z).**  Mirror of `logicalXOffColumnLocalCommutes`:
if the `logicalZ` row guard is `false` at the bound qubit then `A` locally
commutes with the lifted `logicalZ` there (its entry is `I`).  Sorry-free. -/
def logicalZOffRowLocalCommutes {Γ : List (SFormula 2)} (D : OddSurfaceDistance)
    (A : STerm 2 .stab) :
    SFormula.Deriv Γ (.eqBool (logicalZRowGuardAt2 D) (SC.b false)) ->
      SFormula.Deriv Γ
        (SFormula.localCommutesAt A (SC.closed (Term.lift 0 (logicalZOdd D))).weaken
          SFormula.boundNat) := by
  intro hFalse
  refine SFormula.Deriv.localCommutesOfRightI _ _ _ ?_
  have h := SFormula.Deriv.stabAtClosedIteLamEqElse (Γ := Γ)
    (.eqNat (.div Formula.qVar (.natLit D.distance)) (.natLit 0))
    (.pauliLit Pauli.Z) (.pauliLit Pauli.I)
    (Term.var ⟨0, by decide⟩)
    (SFormula.PureNatTerm.var ⟨0, by decide⟩)
    (by simpa [logicalZRowGuardAt2] using hFalse)
  simpa [logicalZOdd, logicalZ, Formula.qVar, SFormula.boundNat, SC.closed, SC.p,
    STerm.weaken, STerm.lift, Term.instantiateTopNat, Term.instantiateNatAt, Term.lift,
    Term.weaken, Term.weakenVar] using h

/-! ## Symbolic (forall D) logicalX normalizer (geometric classification)

The definitions below implement the geometric classification of the bound
stabilizer index that closes the `sorry` in `xNormScaffold`.  They were developed
incrementally and are prover-side only (no `native_decide` / `Formula.check` /
`Formula.eval`-as-proof / `deriveTrue?` / `admit` / new `axiom` / `unsafe`). -/

/-! ## The arity-1 distance witness and flat row-entry resolver

`distAtBoundIdx D : DistAtA 1 D.index` has `dT = Term.lift 0 (.natLit D.distance)`,
exactly the distance term appearing in the per-`k` commutation goal of
`xNormScaffold` (after `allNatLtIntro`).  `rowEntryFlatSym` keyed to it resolves
the generated row entry at the symbolic stabilizer index `k = var 0` and any pure
qubit term `qT` directly to the flat classifier `baseLeafTreeTA`. -/

/-- The distance term shared by the goal and by `distAtBoundIdx`. -/
abbrev dX1 (D : OddSurfaceDistance) : Term 1 .nat := Term.lift 0 (Term.natLit D.distance)

/-- The bound stabilizer index `k = var 0` at arity 1. -/
abbrev kX1 : Term 1 .nat := Term.var ⟨0, by decide⟩

/-- **Flat row entry at a pure qubit term.**  For any pure qubit term `qT`, the
generated row entry of the bound stabilizer `k = var 0` at `qT` equals the flat
recursion-free classifier `baseLeafTreeTA (lift d) (var 0) qT`. -/
def xEntryFlat1 (D : OddSurfaceDistance) (qT : Term 1 .nat) (hq : SFormula.PureNatTerm qT) :
    PureFamilyDerivA Surface.code.body (D.distance + 2)
      (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed qT))
        (SC.closed (baseLeafTreeTA (dX1 D) kX1 qT))) :=
  rowEntryFlatSym (fuel := D.distance + 2) D.index (distAtBoundIdx D) kX1 qT
    (SFormula.PureNatTerm.var ⟨0, by decide⟩) hq

/-! ## Arity-general `baseLeafTreeTA` leaf peels (public, re-derived locally)

Mirrors of the `private baseLeaf*S` reducers in `SurfaceFlatBridge.lean`, reducing
`baseLeafTreeTA dT kT qT` to its selected leaf Pauli given the cell-class / band
guards as `SFormula.Deriv` premises.  Each is a transparent `eqPauliTrans` chain of
`pauliIteSelectThen/Else` over the `ite`-tree of `baseLeafTreeTA`.  Arity-general so
they apply at both arity 1 (literal qubit) and arity 2 (symbolic qubit binder). -/

def baseLeafZ {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hBand : SFormula.Deriv Γ (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)))
    (hKind : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b true))) :
    SFormula.Deriv Γ (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.p Pauli.Z)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hBand)
      (SFormula.Deriv.pauliIteSelectThen _ _ _ hKind))

def baseLeafBulkX {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hBand : SFormula.Deriv Γ (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b true)))
    (hKind : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA dT kT)) (SC.b false))) :
    SFormula.Deriv Γ (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.p Pauli.X)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hBand)
      (SFormula.Deriv.pauliIteSelectElse _ _ _ hKind))

def baseLeafBulkI {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b true)))
    (hBand : SFormula.Deriv Γ (.eqBool (SC.closed (baseBulkBandGuardTA dT kT qT)) (SC.b false))) :
    SFormula.Deriv Γ (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.p Pauli.I)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hBulk)
    (SFormula.Deriv.pauliIteSelectElse _ _ _ hBand)

def baseLeafTopX {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b true)))
    (hTopBand : SFormula.Deriv Γ (.eqBool (SC.closed (topBandGuardTA dT kT qT)) (SC.b true))) :
    SFormula.Deriv Γ (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.p Pauli.X)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hTopClass)
      (SFormula.Deriv.pauliIteSelectThen _ _ _ hTopBand))

def baseLeafTopI {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b true)))
    (hTopBand : SFormula.Deriv Γ (.eqBool (SC.closed (topBandGuardTA dT kT qT)) (SC.b false))) :
    SFormula.Deriv Γ (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.p Pauli.I)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hTopClass)
      (SFormula.Deriv.pauliIteSelectElse _ _ _ hTopBand))

def baseLeafRightZ {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false)))
    (hRightClass : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b true)))
    (hRightBand : SFormula.Deriv Γ (.eqBool (SC.closed (rightBandGuardTA dT kT qT)) (SC.b true))) :
    SFormula.Deriv Γ (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.p Pauli.Z)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hTopClass)
      (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hRightClass)
        (SFormula.Deriv.pauliIteSelectThen _ _ _ hRightBand)))

def baseLeafRightI {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false)))
    (hRightClass : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b true)))
    (hRightBand : SFormula.Deriv Γ (.eqBool (SC.closed (rightBandGuardTA dT kT qT)) (SC.b false))) :
    SFormula.Deriv Γ (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.p Pauli.I)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hTopClass)
      (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hRightClass)
        (SFormula.Deriv.pauliIteSelectElse _ _ _ hRightBand)))

def baseLeafLeftZ {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false)))
    (hRightClass : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b false)))
    (hLeftClass : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA dT kT)) (SC.b true)))
    (hLeftBand : SFormula.Deriv Γ (.eqBool (SC.closed (leftBandGuardTA dT kT qT)) (SC.b true))) :
    SFormula.Deriv Γ (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.p Pauli.Z)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hTopClass)
      (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hRightClass)
        (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hLeftClass)
          (SFormula.Deriv.pauliIteSelectThen _ _ _ hLeftBand))))

def baseLeafLeftI {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false)))
    (hRightClass : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b false)))
    (hLeftClass : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA dT kT)) (SC.b true)))
    (hLeftBand : SFormula.Deriv Γ (.eqBool (SC.closed (leftBandGuardTA dT kT qT)) (SC.b false))) :
    SFormula.Deriv Γ (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.p Pauli.I)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hTopClass)
      (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hRightClass)
        (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectThen _ _ _ hLeftClass)
          (SFormula.Deriv.pauliIteSelectElse _ _ _ hLeftBand))))

def baseLeafBottomX {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false)))
    (hRightClass : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b false)))
    (hLeftClass : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA dT kT)) (SC.b false)))
    (hBottomBand : SFormula.Deriv Γ (.eqBool (SC.closed (bottomBandGuardTA dT kT qT)) (SC.b true))) :
    SFormula.Deriv Γ (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.p Pauli.X)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hTopClass)
      (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hRightClass)
        (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hLeftClass)
          (SFormula.Deriv.pauliIteSelectThen _ _ _ hBottomBand))))

def baseLeafBottomI {arity : Nat} {Γ : List (SFormula arity)} (dT kT qT : Term arity .nat)
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA dT kT)) (SC.b false)))
    (hTopClass : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA dT kT)) (SC.b false)))
    (hRightClass : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA dT kT)) (SC.b false)))
    (hLeftClass : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA dT kT)) (SC.b false)))
    (hBottomBand : SFormula.Deriv Γ (.eqBool (SC.closed (bottomBandGuardTA dT kT qT)) (SC.b false))) :
    SFormula.Deriv Γ (.eqPauli (SC.closed (baseLeafTreeTA dT kT qT)) (SC.p Pauli.I)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hBulk)
    (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hTopClass)
      (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hRightClass)
        (SFormula.Deriv.eqPauliTrans _ _ _ (SFormula.Deriv.pauliIteSelectElse _ _ _ hLeftClass)
          (SFormula.Deriv.pauliIteSelectElse _ _ _ hBottomBand))))

/-! ## `logicalX` entry lemmas (∀ D)

The lifted `logicalX` operator and its column-0 / off-column entries, generalized
from the d=3 mirrors `logicalXOnColumnEntryX` / `logicalXLitEntryX`. -/

/-- The lifted `logicalX` operator at arity 2 (`(lift logicalXOdd D).weaken`). -/
abbrev liftedLX2 (D : OddSurfaceDistance) : STerm 2 .stab :=
  (SC.closed (Term.lift 0 (logicalXOdd D))).weaken

/-- The lifted `logicalX` operator at arity 1 (`lift logicalXOdd D`). -/
abbrev liftedLX1 (D : OddSurfaceDistance) : STerm 1 .stab :=
  SC.closed (Term.lift 0 (logicalXOdd D))

/-- On a column-0 qubit (column guard `q mod d = 0` TRUE), the `logicalX` entry at
the bound qubit is `X`.  ∀-D mirror of `logicalXOnColumnEntryX`. -/
def lxOnColEntryX {Δ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hTrue : SFormula.Deriv Δ (.eqBool (logicalXColGuardAt2 D) (SC.b true))) :
    SFormula.Deriv Δ (.eqPauli (.stabAt (liftedLX2 D) SFormula.boundNat) (SC.p Pauli.X)) := by
  have h := SFormula.Deriv.stabAtClosedIteLamEqThen (Γ := Δ)
    (.eqNat (.mod Formula.qVar (.natLit D.distance)) (.natLit 0))
    (.pauliLit Pauli.X) (.pauliLit Pauli.I)
    (Term.var ⟨0, by decide⟩)
    (SFormula.PureNatTerm.var ⟨0, by decide⟩)
    (by simpa [logicalXColGuardAt2] using hTrue)
  simpa [liftedLX2, logicalXOdd, logicalX, Formula.qVar, SFormula.boundNat, SC.closed, SC.p,
    OddSurfaceDistance.distance, oddDistance,
    STerm.weaken, STerm.lift, Term.instantiateTopNat, Term.instantiateNatAt, Term.lift,
    Term.weaken, Term.weakenVar] using h

/-- The closed `logicalX` column guard `q mod d = 0` at a PURE qubit term `qT`,
true form, at arity 1. -/
abbrev colGuardPure1 (D : OddSurfaceDistance) (qT : Term 1 .nat) : SFormula 1 :=
  .eqBool (SC.closed (.eqNat (.mod qT (.natLit D.distance)) (.natLit 0))) (SC.b true)

/-- At a PURE column-0 qubit `qT`, given the closed column guard `qT mod d = 0`,
the `logicalX` entry is `X`.  Arity-1 ∀-D mirror of `logicalXLitEntryX`. -/
def lxPureEntryX {Γ : List (SFormula 1)} (D : OddSurfaceDistance)
    (qT : Term 1 .nat) (hq : SFormula.PureNatTerm qT)
    (hguardq : SFormula.Deriv Γ (colGuardPure1 D qT)) :
    SFormula.Deriv Γ (.eqPauli (.stabAt (liftedLX1 D) (SC.closed qT)) (SC.p Pauli.X)) := by
  have hguard : SFormula.Deriv Γ
      (.eqBool (SC.closed (Term.instantiateTopNat qT
        (.eqNat (.mod Formula.qVar (.natLit D.distance)) (.natLit 0)))) (SC.b true)) := by
    simpa [colGuardPure1, Formula.qVar,
      Term.instantiateTopNat, Term.instantiateNatAt] using hguardq
  have h := SFormula.Deriv.stabAtClosedIteLamEqThen (Γ := Γ)
    (.eqNat (.mod Formula.qVar (.natLit D.distance)) (.natLit 0))
    (.pauliLit Pauli.X) (.pauliLit Pauli.I)
    qT hq hguard
  simpa [liftedLX1, logicalXOdd, logicalX, Formula.qVar, SC.closed, SC.p,
    Term.instantiateTopNat, Term.instantiateNatAt, Term.lift] using h

/-! ## Arity-2 distance witness and symbolic-qubit flat resolver

Inside the all-others / pointwise premises the row stabilizer is weakened to arity
2 and probed at the symbolic qubit binder `boundNat = SC.closed (var 0)`.  At arity
2 the once-weakened stabilizer index is `k = var 1` and the distance term is
`lift0 (lift0 (natLit d)) = (distAtBoundIdx2 D).dT`. -/

/-- Distance term at arity 2 (the weakening of `dX1`). -/
abbrev dX2 (D : OddSurfaceDistance) : Term 2 .nat := (distAtBoundIdx2 D).dT
/-- Once-weakened stabilizer index `k = var 1` at arity 2. -/
abbrev kX2 : Term 2 .nat := Term.var ⟨1, by decide⟩

/-- **Flat row entry at the symbolic qubit binder.**  At arity 2 the generated row
entry of the (once-weakened) bound stabilizer `k = var 1` at `boundNat = var 0`
equals the flat classifier `baseLeafTreeTA (dX2 D) (var 1) (var 0)`. -/
def xEntryFlat2Bound (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2)
      (.eqPauli (.stabAt (SC.closed (.recCall (dX2 D) kX2)) SFormula.boundNat)
        (SC.closed (baseLeafTreeTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩)))) :=
  rowEntryFlatSym (fuel := D.distance + 2) D.index (distAtBoundIdx2 D) kX2
    (Term.var ⟨0, by decide⟩)
    (SFormula.PureNatTerm.var ⟨1, by decide⟩)
    (SFormula.PureNatTerm.var ⟨0, by decide⟩)

/-! ## Per-`k` row stabilizer (arity 1) -/

/-- The frozen row stabilizer of the per-`k` goal at arity 1. -/
abbrev rowK1 (D : OddSurfaceDistance) : STerm 1 .stab :=
  SC.closed ((Term.lift 0 (Term.natLit D.distance)).recCall (Term.var ⟨0, Formula.normalizesCodeUpTo._proof_1⟩))

/-- The weakened (arity-2) row stabilizer, in the form that appears inside the
pointwise / all-others premises. -/
abbrev rowK2 (D : OddSurfaceDistance) : STerm 2 .stab :=
  (SC.closed ((Term.lift 0 (Term.natLit D.distance)).recCall (Term.var ⟨0, Formula.normalizesCodeUpTo._proof_1⟩))).weaken

/-- **The weakened row stabilizer is the arity-2 `recCall` at `k = var 1`.**
Definitional bridge: `(rowK1 D).weaken = SC.closed (recCall (dX2 D) (var 1))`. -/
theorem rowK2_eq (D : OddSurfaceDistance) :
    rowK2 D = SC.closed (.recCall (dX2 D) kX2) := rfl

/-- The flat row entry at the symbolic qubit binder, with the left stabilizer in
the `rowK2` (weakened) form used inside the premises. -/
def xEntryFlat2BoundW (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2)
      (.eqPauli (.stabAt (rowK2 D) SFormula.boundNat)
        (SC.closed (baseLeafTreeTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩)))) := by
  rw [rowK2_eq]; exact xEntryFlat2Bound D

/-- **Column-0 local commutation from a non-`Z` row entry.**  Given the column
guard true at `boundNat` (so `logicalX` entry is `X`) and the row entry at
`boundNat` equal to a Pauli `p` with `anticommutes p X = false`, the row locally
commutes with `logicalX` at `boundNat`. -/
def colCommFromEntry {Δ : List (SFormula 2)} (D : OddSurfaceDistance) (p : Pauli)
    (hEntry : SFormula.Deriv Δ (.eqPauli (.stabAt (rowK2 D) SFormula.boundNat) (SC.p p)))
    (hAnti : SFormula.Deriv Δ (.eqBool (.anticommutes (SC.p Pauli.X) (SC.p p)) (SC.b false)))
    (hcol : SFormula.Deriv Δ (.eqBool (logicalXColGuardAt2 D) (SC.b true))) :
    SFormula.Deriv Δ (SFormula.localCommutesAt (rowK2 D) (liftedLX2 D) SFormula.boundNat) := by
  refine SFormula.Deriv.localCommutesOfLeftEqNoAntiRight _ _ _ (SC.p p) hEntry ?_
  -- `¬ anticommutes (logicalX entry) p = true`; the logicalX entry is `X`.
  have hX := lxOnColEntryX (Δ := Δ) D hcol
  have hLitFalse : SFormula.Deriv Δ
      (.eqBool (.anticommutes (.stabAt (liftedLX2 D) SFormula.boundNat) (SC.p p)) (SC.b false)) :=
    SFormula.Deriv.anticommutesTransport _ (SC.p Pauli.X) _ (SC.p p) (SC.b false)
      hX (SFormula.Deriv.pauliEqLit p) hAnti
  exact SFormula.Deriv.eqBoolFalseNotTrue _ hLitFalse

/-- The closed column guard at `boundNat`, raw `var0 % d = 0` form, as it appears
after unfolding `logicalXColGuardAt2`. -/
abbrev colGuardRaw2 (D : OddSurfaceDistance) : SFormula 2 :=
  .eqBool (SC.closed (.eqNat (.mod (Term.var ⟨0, by decide⟩) (Term.natLit D.distance)) (Term.natLit 0)))
    (SC.b true)

/-- `logicalXColGuardAt2 D = colGuardRaw2 D` after the instantiation reduces. -/
theorem colGuard2_eq (D : OddSurfaceDistance) :
    (SFormula.eqBool (logicalXColGuardAt2 D) (SC.b true)) = colGuardRaw2 D := by
  simp [logicalXColGuardAt2, colGuardRaw2, Formula.qVar, OddSurfaceDistance.distance,
    Term.instantiateTopNat, Term.instantiateNatAt]

/-! ## Arity-1 quantified arithmetic facts (`arithBool`)

These are the universally-true (class-independent) cell-guard facts over the
qubit `q < nQubits`, with the stabilizer index `k = var 0` symbolic.  Each is in
the `arithBoolFragment` (closed Nat/Bool atoms only) and discharged in one
`arithBool`.  Weakened to arity 2 and eliminated at `boundNat`, they supply the
arity-2 guard facts the column-0 dispatcher needs. -/

/-- The distance term at arity 1, raw form `natLit d` after the lift cancels under
elimination.  (We work with `dX1 D = lift0 (natLit d)`; under the per-`q` body the
guards mention `lift0 (natLit d)` directly.) -/
abbrev dBody : OddSurfaceDistance → Term 2 .nat := fun D => Term.lift 0 (dX1 D)

/-- Body (arity 2, qubit binder `boundNat = var 0`, `k = var 1`): on column 0
(`q % d = 0`), the right-`Z` boundary band guard is `false`.  (Right-`Z` lives in
column `d-1 ≠ 0`.) -/
abbrev rightBandFalseBody (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (colGuardRaw2 D)
    (.eqBool (SC.closed (rightBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.b false))

/-- The qubit-quantifier bound as it appears in the per-`k` goal: the once-lifted
literal `lift0 (natLit nQubits)` (so its weakening matches the `boundNatLt`
introduced by `allNatLtIntroBounded` on the goal). -/
abbrev nQ1 (D : OddSurfaceDistance) : STerm 1 .nat :=
  SC.closed (Term.lift 0 (Term.natLit (nQubits D.distance)))

/-- Quantified right-band-false fact, arity 1. -/
abbrev rightBandFalseF (D : OddSurfaceDistance) : SFormula 1 :=
  .allNatLt (nQ1 D) (rightBandFalseBody D)

/-- The `c = k mod (d-1) = 0` guard at arity 1 (k-only). -/
abbrev cZero1 (D : OddSurfaceDistance) (v : Bool) : SFormula 1 :=
  .eqBool (SC.closed (.eqNat (.mod kX1 (dm1TA (dX1 D))) (.natLit 0))) (SC.b v)
/-- The `c = k mod (d-1) = 0` guard at arity 2 (`k = var 1`). -/
abbrev cZero2 (D : OddSurfaceDistance) (v : Bool) : SFormula 2 :=
  .eqBool (SC.closed (.eqNat (.mod kX2 (dm1TA (dX2 D))) (.natLit 0))) (SC.b v)

/-- Body (arity 2): on column 0, if the bulk band guard holds then `c = 0`. -/
abbrev bandImpCZeroBody (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (colGuardRaw2 D)
    (.imp (.eqBool (SC.closed (baseBulkBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.b true))
      (cZero2 D true))

abbrev bandImpCZeroF (D : OddSurfaceDistance) : SFormula 1 :=
  .allNatLt (nQ1 D) (bandImpCZeroBody D)

def bandImpCZeroPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (bandImpCZeroF D) := by
  refine PureFamilyDerivA.allNatLtIntro _ ?_
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [baseBulkBandGuardTA, cZero2, dX2, distAtBoundIdx2, kX2, dm1TA, orEqSucc, band3,
    bulkCountTA, SFormula.eval, SC.closed, SC.b, STerm.eval, Term.eval, Term.lift, bind, Option.bind]
  -- Abstract the opaque row-match and bulk-range decides; only the column (mod) part matters.
  by_cases hq : rho ⟨0, by decide⟩ % D.distance = 0
  · rw [hq]
    by_cases hc : rho ⟨1, by decide⟩ % (D.distance - 1) = 0
    · -- c = 0 → cZero holds, both branches give `some true`.
      rw [hc]
      generalize (decide (rho ⟨0, by decide⟩ / D.distance = rho ⟨1, by decide⟩ / (D.distance - 1))) = r0
      generalize (decide (rho ⟨0, by decide⟩ / D.distance = rho ⟨1, by decide⟩ / (D.distance - 1) + 1)) = r1
      generalize (decide (rho ⟨1, by decide⟩ < (D.distance - 1) * (D.distance - 1))) = bk
      cases r0 <;> cases r1 <;> cases bk <;> simp
    · -- c ≠ 0 → the column (mod) disjunct is false, so band is false.
      have hc1 : decide (0 = rho ⟨1, by decide⟩ % (D.distance - 1)) = false := by
        simp only [decide_eq_false_iff_not]; omega
      have hc2 : decide (0 = rho ⟨1, by decide⟩ % (D.distance - 1) + 1) = false := by
        simp only [decide_eq_false_iff_not]; omega
      rw [hc1, hc2]
      generalize (decide (rho ⟨0, by decide⟩ / D.distance = rho ⟨1, by decide⟩ / (D.distance - 1))) = r0
      generalize (decide (rho ⟨0, by decide⟩ / D.distance = rho ⟨1, by decide⟩ / (D.distance - 1) + 1)) = r1
      cases r0 <;> cases r1 <;> simp
  · simp only [hq, decide_false, Bool.false_eq_true, if_false, reduceIte]

def rightBandFalsePack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (rightBandFalseF D) := by
  refine PureFamilyDerivA.allNatLtIntro _ ?_
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  have hd0 : (0 : Nat) ≠ D.distance - 1 := by omega
  simp only [rightBandGuardTA, dX2, distAtBoundIdx2, kX2, dm1TA, orEqSucc,
    SFormula.eval, SC.closed, SC.b, STerm.eval, Term.eval, Term.lift, bind, Option.bind]
  by_cases hq : rho ⟨0, by decide⟩ % D.distance = 0
  · -- column 0: inner `if q%d = d-1` is false (0 ≠ d-1 since d ≥ 3).
    rw [hq]
    simp only [hd0, decide_true, decide_false, Bool.false_eq_true, if_false, if_true, reduceIte]
  · simp only [hq, decide_false, Bool.false_eq_true, if_false, reduceIte]

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

/-! ## Two-anti class (a): left-column even-`r` bulk `Z`-plaquettes

`k < (d-1)²`, `k % (d-1) = 0`, `(k/(d-1))` even.  The row anticommutes with
`logicalX` at the two column-0 qubits `q0 = r·d`, `q1 = (r+1)·d` where `r = k/(d-1)`. -/

/-- `r = k / (d-1)` at arity 1. -/
abbrev rA1 (D : OddSurfaceDistance) : Term 1 .nat := .div kX1 (dm1TA (dX1 D))
/-- `q0 = r·d` at arity 1 (first anti qubit). -/
abbrev qa0 (D : OddSurfaceDistance) : Term 1 .nat := .mul (rA1 D) (dX1 D)
/-- `q1 = (r+1)·d` at arity 1 (second anti qubit). -/
abbrev qa1 (D : OddSurfaceDistance) : Term 1 .nat := .mul (.add (rA1 D) (.natLit 1)) (dX1 D)

/-- Purity of the distance term `dX1` (a lifted literal). -/
def dX1_pure (D : OddSurfaceDistance) : SFormula.PureNatTerm (dX1 D) := (distAtBoundIdx D).pure
/-- Purity of `d - 1`. -/
def dm1_pure (D : OddSurfaceDistance) : SFormula.PureNatTerm (dm1TA (dX1 D)) :=
  SFormula.PureNatTerm.sub (dX1_pure D) (SFormula.PureNatTerm.natLit _)
/-- Purity of `r = k/(d-1)`. -/
def rA1_pure (D : OddSurfaceDistance) : SFormula.PureNatTerm (rA1 D) :=
  SFormula.PureNatTerm.div (SFormula.PureNatTerm.var _) (dm1_pure D)

def qa0_pure (D : OddSurfaceDistance) : SFormula.PureNatTerm (qa0 D) :=
  SFormula.PureNatTerm.mul (rA1_pure D) (dX1_pure D)
def qa1_pure (D : OddSurfaceDistance) : SFormula.PureNatTerm (qa1 D) :=
  SFormula.PureNatTerm.mul (SFormula.PureNatTerm.add (rA1_pure D) (SFormula.PureNatTerm.natLit _))
    (dX1_pure D)

/-- The class-(a) k-condition guard pack (arity 1, k = var 0): bulk true, `c = 0`,
kind true (r even), plus the band guards at `q0`/`q1` being true, the `q0 ≠ q1`
fact, and the in-range bounds `q0, q1 < nQubits`.  All are functions of `k` only, so
this is a single closed-in-`k` arithmetic fact discharged by `arithBool`. -/
abbrev classAPackF (D : OddSurfaceDistance) : SFormula 1 :=
  .imp (gBulk1 D true) (.imp (cZero1 D true) (.imp (gKind1 D true)
    (.and (.eqBool (SC.closed (baseBulkBandGuardTA (dX1 D) kX1 (qa0 D))) (SC.b true))
      (.and (.eqBool (SC.closed (baseBulkBandGuardTA (dX1 D) kX1 (qa1 D))) (SC.b true))
        (.and (.eqBool (SC.closed (.eqNat (qa0 D) (qa1 D))) (SC.b false))
          (.and (SFormula.witnessLt (SC.closed (qa0 D)) (SC.n (arity := 1) (nQubits D.distance)))
            (SFormula.witnessLt (SC.closed (qa1 D)) (SC.n (arity := 1) (nQubits D.distance)))))))))

def classAPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (classAPackF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [baseBulkBandGuardTA, cZero1, gBulk1, gKind1, qa0, qa1, rA1, dX1, distAtBoundIdx,
    dm1TA, bulkCountTA, bulkGuardTA, baseKindGuardTA, orEqSucc, band3, SFormula.eval, SC.closed,
    SC.b, SC.n, STerm.eval, SFormula.witnessLt, Term.eval, Term.lift, bind, Option.bind]
  set k := rho ⟨0, by decide⟩ with hk
  set d := D.distance with hdd
  have hdpos : 0 < d := by omega
  by_cases hbulk : k < (d - 1) * (d - 1)
  · -- bulk true
    simp only [hbulk, decide_true, if_true]
    by_cases hc : k % (d - 1) = 0
    · -- c = 0
      simp only [hc, decide_true, if_true]
      by_cases hkind : (k / (d - 1) + 0) % 2 = 0
      · -- kind true (r even).  Prove all band/bound/neq conjuncts.
        simp only [hkind, decide_true, if_true]
        -- Key div/mod facts for `r*d` and `(r+1)*d`.
        have hdiv0 : k / (d - 1) * d / d = k / (d - 1) := Nat.mul_div_cancel _ hdpos
        have hmod0 : k / (d - 1) * d % d = 0 := Nat.mul_mod_left _ _
        have hdiv1 : (k / (d - 1) + 1) * d / d = k / (d - 1) + 1 := Nat.mul_div_cancel _ hdpos
        have hmod1 : (k / (d - 1) + 1) * d % d = 0 := Nat.mul_mod_left _ _
        -- r < d-1, so r+1 ≤ d-1 and both qubits are < d².
        have hr : k / (d - 1) < d - 1 := by
          rcases Nat.lt_or_ge (k / (d-1)) (d-1) with h | h
          · exact h
          · exfalso
            have : (d - 1) * (d - 1) ≤ k / (d - 1) * (d - 1) := Nat.mul_le_mul_right _ h
            have hk2 : k / (d-1) * (d-1) ≤ k := Nat.div_mul_le_self k (d-1)
            omega
        have hb0 : k / (d - 1) * d < nQubits d := by
          simp only [nQubits]
          have h1 : k / (d-1) * d < (d-1) * d := (Nat.mul_lt_mul_right hdpos).mpr hr
          have h2 : (d-1) * d ≤ d * d := (Nat.mul_le_mul_right d (by omega))
          omega
        have hb1 : (k / (d - 1) + 1) * d < nQubits d := by
          simp only [nQubits]
          have h1 : (k / (d-1) + 1) * d ≤ (d-1) * d := (Nat.mul_le_mul_right d (by omega))
          have h2 : (d-1) * d < d * d := (Nat.mul_lt_mul_right hdpos).mpr (by omega)
          omega
        have hne : ¬ (k / (d - 1) * d = (k / (d - 1) + 1) * d) := by
          intro h
          have hlt : k / (d-1) * d < (k / (d-1) + 1) * d :=
            (Nat.mul_lt_mul_right hdpos).mpr (by omega)
          omega
        have hne0 : ¬ (k / (d - 1) = k / (d - 1) + 1) := by omega
        rw [hdiv0, hmod0, hdiv1, hmod1]
        simp only [hc, hbulk, hb0, hb1, hne, hne0, decide_true, decide_false, Nat.lt_irrefl,
          Bool.false_eq_true, if_true, if_false, reduceIte]
        generalize (decide (k / (d - 1) + 1 = k / (d - 1))) = z
        cases z <;> simp
      · simp only [hkind, decide_false, Bool.false_eq_true, if_false, reduceIte]
    · simp only [hc, decide_false, Bool.false_eq_true, if_false, reduceIte]
  · simp only [hbulk, decide_false, Bool.false_eq_true, if_false, reduceIte]

/-- Arity-2 forms of the class-(a) anti qubits (`k = var 1`). -/
abbrev qa0_2 (D : OddSurfaceDistance) : Term 2 .nat := .mul (.div kX2 (dm1TA (dX2 D))) (dX2 D)
abbrev qa1_2 (D : OddSurfaceDistance) : Term 2 .nat :=
  .mul (.add (.div kX2 (dm1TA (dX2 D))) (.natLit 1)) (dX2 D)

/-- `(qa0 D).weaken = qa0_2 D` and similarly for `qa1`. -/
theorem qa0_weaken (D : OddSurfaceDistance) : (qa0 D).weaken = qa0_2 D := rfl
theorem qa1_weaken (D : OddSurfaceDistance) : (qa1 D).weaken = qa1_2 D := rfl

/-- Column guards at the two class-(a) anti qubits: `q0 % d = 0` and `q1 % d = 0`
(both are multiples of `d`).  Closed in `k`, discharged by `arithBool`. -/
abbrev qaColGuardF (D : OddSurfaceDistance) : SFormula 1 :=
  .and (colGuardPure1 D (qa0 D)) (colGuardPure1 D (qa1 D))

def qaColGuardPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (qaColGuardF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [colGuardPure1, qa0, qa1, rA1, dX1, distAtBoundIdx, dm1TA, SFormula.eval, SC.closed,
    SC.b, STerm.eval, Term.eval, Term.lift, bind, Option.bind]
  rw [Nat.mul_mod_left, Nat.mul_mod_left]
  simp

/-- The `bulk-Z` all-others pin for class (a): on column 0, if the bulk band fires
(with `c = 0`), then `boundNat ∈ {q0, q1}`.  Quantified over `q < nQubits`. -/
abbrev classABulkZPinBody (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (colGuardRaw2 D)
    (.imp (.eqBool (SC.closed (baseBulkBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.b true))
      (.imp (cZero2 D true)
        (.or (.eqNat SFormula.boundNat (SC.closed (qa0_2 D)))
          (.eqNat SFormula.boundNat (SC.closed (qa1_2 D))))))

abbrev classABulkZPinF (D : OddSurfaceDistance) : SFormula 1 :=
  .allNatLt (nQ1 D) (classABulkZPinBody D)

def classABulkZPinPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (classABulkZPinF D) := by
  refine PureFamilyDerivA.allNatLtIntro _ ?_
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [classABulkZPinBody, colGuardRaw2, baseBulkBandGuardTA, cZero2, qa0_2, qa1_2, dX2,
    distAtBoundIdx2, kX2, dm1TA, orEqSucc, band3, bulkCountTA, SFormula.eval, SC.closed, SC.b,
    STerm.eval, SFormula.boundNat, Term.eval, Term.lift, bind, Option.bind]
  set q := rho ⟨0, by decide⟩ with hq'
  set k := rho ⟨1, by decide⟩ with hk'
  set d := D.distance with hdd
  have hdpos : 0 < d := by omega
  by_cases hq : q % d = 0
  · simp only [hq, decide_true, if_true]
    by_cases hc : k % (d - 1) = 0
    · -- c = 0; whenever the band fires (row matches), q is `r·d` or `(r+1)·d`.
      simp only [hc, decide_true, if_true]
      have hqdiv : q = q / d * d := (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hq)).symm
      -- Case on the two row-match decides.
      by_cases hrow0 : q / d = k / (d - 1)
      · -- q/d = r → q = r·d = q0
        have hqe : decide (q = k / (d - 1) * d) = true := by
          rw [decide_eq_true_eq, hqdiv, hrow0]
        have hr0 : decide (q / d = k / (d - 1)) = true := by rw [decide_eq_true_eq]; exact hrow0
        simp only [hr0, hqe, decide_true, if_true]
        by_cases hbk : decide (k < (d-1)*(d-1)) = true <;> simp [hbk]
      · by_cases hrow1 : q / d = k / (d - 1) + 1
        · -- q/d = r+1 → q = (r+1)·d = q1
          have hq1 : decide (q = (k / (d - 1) + 1) * d) = true := by
            rw [decide_eq_true_eq, hqdiv, hrow1]
          have hr0 : decide (q / d = k / (d - 1)) = false := by rw [decide_eq_false_iff_not]; exact hrow0
          have hr1 : decide (q / d = k / (d - 1) + 1) = true := by rw [decide_eq_true_eq]; exact hrow1
          have hq0 : decide (q = k / (d - 1) * d) = false := by
            rw [decide_eq_false_iff_not]; intro h; apply hrow0; rw [hqdiv] at h
            exact Nat.eq_of_mul_eq_mul_right hdpos h
          simp only [hr0, hr1, hq0, hq1, decide_true, decide_false, Bool.false_eq_true,
            if_true, if_false, reduceIte]
          by_cases hbk : decide (k < (d-1)*(d-1)) = true <;> simp [hbk]
        · -- neither: band false, antecedent vacuous
          have hr0 : decide (q / d = k / (d - 1)) = false := by rw [decide_eq_false_iff_not]; exact hrow0
          have hr1 : decide (q / d = k / (d - 1) + 1) = false := by rw [decide_eq_false_iff_not]; exact hrow1
          simp only [hr0, hr1, decide_false, Bool.false_eq_true, if_false, reduceIte]
    · -- c ≠ 0: the cZero antecedent is false, so the conclusion is vacuous (`some true`).
      have hcz : decide (decide (k % (d - 1) = 0) = true) = false := by
        rw [decide_eq_false_iff_not]; simp [hc]
      simp only [hc, hcz, decide_false, Bool.false_eq_true, if_false, reduceIte]
      generalize (decide (q / d = k / (d - 1))) = z0
      generalize (decide (q / d = k / (d - 1) + 1)) = z1
      generalize (decide (0 = k % (d - 1))) = z2
      generalize (decide (0 = k % (d - 1) + 1)) = z3
      generalize (decide (k < (d - 1) * (d - 1))) = z4
      cases z0 <;> cases z1 <;> cases z2 <;> cases z3 <;> cases z4 <;> simp
  · simp only [hq, decide_false, Bool.false_eq_true, if_false, reduceIte]

/-! ## Class-(a) two-anti per-`k` commutation -/

/-- Entry-at-`q0` resolves to `Z` (bulk, band-at-q0, kind), given the class-(a)
guard pack extracted at `q0`. -/
def antiZAtA (D : OddSurfaceDistance) {Γ : List (SFormula 1)} (qT : Term 1 .nat)
    (hqpure : SFormula.PureNatTerm qT)
    (hEntry : SFormula.Deriv Γ
      (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed qT))
        (SC.closed (baseLeafTreeTA (dX1 D) kX1 qT))))
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dX1 D) kX1)) (SC.b true)))
    (hBand : SFormula.Deriv Γ (.eqBool (SC.closed (baseBulkBandGuardTA (dX1 D) kX1 qT)) (SC.b true)))
    (hKind : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dX1 D) kX1)) (SC.b true))) :
    SFormula.Deriv Γ (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed qT)) (SC.p Pauli.Z)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ hEntry (baseLeafZ _ _ _ hBulk hBand hKind)

/-- Extract the class-(a) bulk-`Z` pin disjunction at `boundNat`. -/
def classABulkZPinAt {Δ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hW : SFormula.Deriv Δ (classABulkZPinF D).weaken)
    (hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nQ1 D).weaken))
    (hcol : SFormula.Deriv Δ (colGuardRaw2 D))
    (hband : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.b true)))
    (hcz : SFormula.Deriv Δ (cZero2 D true)) :
    SFormula.Deriv Δ
      (.or (.eqNat SFormula.boundNat (SC.closed (qa0_2 D)))
        (.eqNat SFormula.boundNat (SC.closed (qa1_2 D)))) := by
  have hElim := SFormula.Deriv.allNatLtElim (nQ1 D).weaken
    ((classABulkZPinBody D).lift 1) SFormula.boundNat hW hq
  have hBody := SFormula.Deriv.applyNatBoundNatBeta (classABulkZPinBody D) hElim
  exact SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp hBody hcol) hband) hcz

/-- **Class-(a) two-anti per-`k` commutation.**  Given the class conditions and the
supporting packs in `Γ`, the row commutes with `logicalX` by the even-parity rule:
it anticommutes at exactly `q0 = r·d` and `q1 = (r+1)·d`, and commutes elsewhere. -/
def commTwoAntiA {Γ : List (SFormula 1)} (D : OddSurfaceDistance)
    (hBulk : SFormula.Deriv Γ (gBulk1 D true))
    (hCZ : SFormula.Deriv Γ (cZero1 D true))
    (hKind : SFormula.Deriv Γ (gKind1 D true))
    (hClassA : SFormula.Deriv Γ (classAPackF D))
    (hCol : SFormula.Deriv Γ (qaColGuardF D))
    (hPin : SFormula.Deriv Γ (classABulkZPinF D))
    (hEntryF : SFormula.Deriv Γ (entryFlatF1 D))
    (hRBFF : SFormula.Deriv Γ (rightBandFalseF D))
    (hEntry0 : SFormula.Deriv Γ
      (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed (qa0 D)))
        (SC.closed (baseLeafTreeTA (dX1 D) kX1 (qa0 D)))))
    (hEntry1 : SFormula.Deriv Γ
      (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed (qa1 D)))
        (SC.closed (baseLeafTreeTA (dX1 D) kX1 (qa1 D))))) :
    SFormula.Deriv Γ (commGoal1 D) := by
  -- Extract the class-(a) guard facts at q0/q1.
  have hPack := SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp hClassA hBulk) hCZ) hKind
  have hBand0 := SFormula.Deriv.andElimLeft hPack
  have hBand1 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hPack)
  have hNe := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hPack))
  have hLt0 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hPack)))
  have hLt1 := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hPack)))
  -- Entry = Z at q0, q1.
  have hZ0 := antiZAtA D (qa0 D) (qa0_pure D) hEntry0 hBulk hBand0 hKind
  have hZ1 := antiZAtA D (qa1 D) (qa1_pure D) hEntry1 hBulk hBand1 hKind
  -- logicalX = X at q0, q1.
  have hX0 := lxPureEntryX D (qa0 D) (qa0_pure D) (SFormula.Deriv.andElimLeft hCol)
  have hX1 := lxPureEntryX D (qa1 D) (qa1_pure D) (SFormula.Deriv.andElimRight hCol)
  -- The `commutesOfTwoAnti` rule with q0 = qa0, q1 = qa1.
  refine SFormula.Deriv.commutesOfTwoAnti _ _ _ (SC.closed (qa0 D)) (SC.closed (qa1 D))
    ?wlt0 ?wlt1 ?wne ?wanti0 ?wanti1 ?wrest
  case wlt0 => exact hLt0
  case wlt1 => exact hLt1
  case wne =>
    -- q0 ≠ q1 from the `eqNat q0 q1 = false` guard fact.
    refine SFormula.Deriv.notIntro ?_
    refine SFormula.Deriv.notElim
      (SFormula.Deriv.eqNatBoolTrue (Γ := _) (qa0 D) (qa1 D) .assumption) ?_
    exact SFormula.Deriv.eqBoolFalseNotTrue _ (cw1 hNe)
  case wanti0 =>
    exact SFormula.Deriv.anticommutesTransport _ (SC.p Pauli.Z) _ (SC.p Pauli.X) (SC.b true)
      hZ0 hX0 (SFormula.Deriv.pauliAnticommutesLit Pauli.Z Pauli.X)
  case wanti1 =>
    exact SFormula.Deriv.anticommutesTransport _ (SC.p Pauli.Z) _ (SC.p Pauli.X) (SC.b true)
      hZ1 hX1 (SFormula.Deriv.pauliAnticommutesLit Pauli.Z Pauli.X)
  case wrest =>
    -- all-others: introduce qubit binder + two exclusions, boolCases column.
    refine SFormula.Deriv.allNatLtIntroBounded _ _ ?_
    refine SFormula.Deriv.impIntro (SFormula.Deriv.impIntro ?_)
    -- context: ¬q=q1 :: ¬q=q0 :: boundNatLt :: Γ.map weaken
    refine SFormula.Deriv.boolCases (logicalXColGuardAt2 D) _ ?_ ?_
    · -- column TRUE
      -- The dispatcher context (5 leading hyps over `Γ.map weaken`).
      set ΔT : List (SFormula 2) := .eqBool (logicalXColGuardAt2 D) (SC.b true)
        :: .not (.eqNat SFormula.boundNat (SC.closed (qa1 D)).weaken)
        :: .not (.eqNat SFormula.boundNat (SC.closed (qa0 D)).weaken)
        :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ with hΔT
      -- weaken the needed Γ-facts into the dispatcher context Δ.
      have hEntryW : SFormula.Deriv ΔT (entryFlatF1 D).weaken :=
        cw4 (SFormula.Deriv.weakenFresh (A := entryFlatF1 D) hEntryF)
      have hRBFW : SFormula.Deriv ΔT (rightBandFalseF D).weaken :=
        cw4 (SFormula.Deriv.weakenFresh (A := rightBandFalseF D) hRBFF)
      have hq : SFormula.Deriv ΔT (SFormula.witnessLt SFormula.boundNat (nQ1 D).weaken) :=
        SFormula.Deriv.hyp (by rw [hΔT]; right; right; right; exact List.mem_cons_self)
      have hcolT : SFormula.Deriv ΔT (.eqBool (logicalXColGuardAt2 D) (SC.b true)) := by
        rw [hΔT]; exact .assumption
      have hcolRaw : SFormula.Deriv ΔT (colGuardRaw2 D) := by rw [← colGuard2_eq]; exact hcolT
      have hEntry := entryAtBound D hEntryW hq
      have hRBF := rbfAtBound D hRBFW hq hcolRaw
      refine colDispatchOnTrue D hEntry hcolT hRBF ?hZbulk ?hZleft
      case hZbulk =>
        intro Δ' lift _ hcolΔ hBulkΔ hBandΔ _
        -- bulk-Z: use the pin (col ∧ band ∧ c=0) → q=q0 ∨ q=q1, contradicting exclusions.
        have hcolRaw' : SFormula.Deriv Δ' (colGuardRaw2 D) := by rw [← colGuard2_eq]; exact hcolΔ
        have hczΔ0 : SFormula.Deriv ΔT (cZero2 D true) :=
          cw4 (SFormula.Deriv.weakenFresh (A := cZero1 D true) hCZ)
        have hPinW0 : SFormula.Deriv ΔT (classABulkZPinF D).weaken :=
          cw4 (SFormula.Deriv.weakenFresh (A := classABulkZPinF D) hPin)
        have hdisj := classABulkZPinAt D (lift hPinW0) (lift hq) hcolRaw' hBandΔ (lift hczΔ0)
        -- exclusions, lifted into Δ'
        have hne0 : SFormula.Deriv ΔT (.not (.eqNat SFormula.boundNat (SC.closed (qa0 D)).weaken)) := by
          rw [hΔT]; exact .hyp (by right; right; exact List.mem_cons_self)
        have hne1 : SFormula.Deriv ΔT (.not (.eqNat SFormula.boundNat (SC.closed (qa1 D)).weaken)) := by
          rw [hΔT]; exact .hyp (by right; exact List.mem_cons_self)
        refine SFormula.Deriv.orElim hdisj ?_ ?_
        · exact SFormula.Deriv.botElim (SFormula.Deriv.notElim (.assumption) (cw1 (lift hne0)))
        · exact SFormula.Deriv.botElim (SFormula.Deriv.notElim (.assumption) (cw1 (lift hne1)))
      case hZleft =>
        intro Δ' lift _ _ hBulkFalseΔ _ _ _ _
        -- left-Z: class (a) has bulk TRUE, contradicting cascade bulk FALSE.
        have hBulkTrue0 : SFormula.Deriv ΔT (gBulk D true) :=
          cw4 (SFormula.Deriv.weakenFresh (A := gBulk1 D true) hBulk)
        exact eqBoolContra _ (lift hBulkTrue0) hBulkFalseΔ
    · -- column FALSE → off-column
      exact logicalXOffColumnLocalCommutes D (rowK2 D) .assumption

/-! ## Two-anti class (b): left-`Z` boundary stabilizers

`¬(k < (d-1)²)`, left-`Z` band `2·half ≤ b < 3·half` (`b = k - (d-1)²`,
`half = (d-1)/2`).  Anti qubits `q0 = (2·bbL+1)·d`, `q1 = (2·bbL+2)·d`,
`bbL = b - 2·half`. -/

/-- `bbL = (k - (d-1)²) - 2·((d-1)/2)` at arity 1. -/
abbrev bbL1 (D : OddSurfaceDistance) : Term 1 .nat :=
  .sub (baseBTA (dX1 D) kX1) (.mul (.natLit 2) (baseHalfTA (dX1 D)))
abbrev qb0 (D : OddSurfaceDistance) : Term 1 .nat :=
  .mul (.add (.mul (.natLit 2) (bbL1 D)) (.natLit 1)) (dX1 D)
abbrev qb1 (D : OddSurfaceDistance) : Term 1 .nat :=
  .mul (.add (.mul (.natLit 2) (bbL1 D)) (.natLit 2)) (dX1 D)

def bbL1_pure (D : OddSurfaceDistance) : SFormula.PureNatTerm (bbL1 D) :=
  SFormula.PureNatTerm.sub
    (SFormula.PureNatTerm.sub (SFormula.PureNatTerm.var _)
      (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.sub (dX1_pure D) (SFormula.PureNatTerm.natLit _))
        (SFormula.PureNatTerm.sub (dX1_pure D) (SFormula.PureNatTerm.natLit _))))
    (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.natLit _)
      (SFormula.PureNatTerm.div (SFormula.PureNatTerm.sub (dX1_pure D) (SFormula.PureNatTerm.natLit _))
        (SFormula.PureNatTerm.natLit _)))
def qb0_pure (D : OddSurfaceDistance) : SFormula.PureNatTerm (qb0 D) :=
  SFormula.PureNatTerm.mul (SFormula.PureNatTerm.add
    (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.natLit _) (bbL1_pure D))
    (SFormula.PureNatTerm.natLit _)) (dX1_pure D)
def qb1_pure (D : OddSurfaceDistance) : SFormula.PureNatTerm (qb1 D) :=
  SFormula.PureNatTerm.mul (SFormula.PureNatTerm.add
    (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.natLit _) (bbL1_pure D))
    (SFormula.PureNatTerm.natLit _)) (dX1_pure D)

/-- Arity-2 forms of the class-(b) anti qubits. -/
abbrev bbL2 (D : OddSurfaceDistance) : Term 2 .nat :=
  .sub (baseBTA (dX2 D) kX2) (.mul (.natLit 2) (baseHalfTA (dX2 D)))
abbrev qb0_2 (D : OddSurfaceDistance) : Term 2 .nat :=
  .mul (.add (.mul (.natLit 2) (bbL2 D)) (.natLit 1)) (dX2 D)
abbrev qb1_2 (D : OddSurfaceDistance) : Term 2 .nat :=
  .mul (.add (.mul (.natLit 2) (bbL2 D)) (.natLit 2)) (dX2 D)
theorem qb0_weaken (D : OddSurfaceDistance) : (qb0 D).weaken = qb0_2 D := rfl
theorem qb1_weaken (D : OddSurfaceDistance) : (qb1 D).weaken = qb1_2 D := rfl

/-- Class-(b) guard pack: given `¬bulk`, `¬rightClass`, `leftClass` (so `2half ≤ b
< 3half`), the left-`Z` band fires at `q0`/`q1`, `q0 ≠ q1`, and both `< nQubits`. -/
abbrev classBPackF (D : OddSurfaceDistance) : SFormula 1 :=
  .imp (gBulk1 D false) (.imp (gRightC1 D false) (.imp (gLeftC1 D true)
    (.and (.eqBool (SC.closed (leftBandGuardTA (dX1 D) kX1 (qb0 D))) (SC.b true))
      (.and (.eqBool (SC.closed (leftBandGuardTA (dX1 D) kX1 (qb1 D))) (SC.b true))
        (.and (.eqBool (SC.closed (.eqNat (qb0 D) (qb1 D))) (SC.b false))
          (.and (SFormula.witnessLt (SC.closed (qb0 D)) (SC.n (arity := 1) (nQubits D.distance)))
            (SFormula.witnessLt (SC.closed (qb1 D)) (SC.n (arity := 1) (nQubits D.distance)))))))))

def classBPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (classBPackF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [classBPackF, leftBandGuardTA, gBulk1, gRightC1, gLeftC1, bulkGuardTA, rightClassGuardTA,
    leftClassGuardTA, baseBTA, baseHalfTA, bulkCountTA, qb0, qb1, bbL1, dX1, distAtBoundIdx, dm1TA,
    orEqPair, SFormula.eval, SC.closed, SC.b, SC.n, STerm.eval, SFormula.witnessLt, Term.eval,
    Term.lift, bind, Option.bind]
  set k := rho ⟨0, by decide⟩ with hk
  set d := D.distance with hdd
  have hdpos : 0 < d := by omega
  have hdge : 3 ≤ d := by omega
  by_cases hbulk : k < (d - 1) * (d - 1)
  · -- bulk true → `gBulk1 D false` antecedent false → vacuous.
    have : decide (decide (k < (d - 1) * (d - 1)) = false) = false := by
      rw [decide_eq_false_iff_not]; simp [hbulk]
    simp only [this, Bool.false_eq_true, if_false, reduceIte]
  · by_cases hrc : k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)
    · -- rightClass true → `gRightC1 D false` antecedent false → vacuous.
      have hb : decide (decide (k < (d - 1) * (d - 1)) = false) = true := by
        rw [decide_eq_true_eq]; simp [hbulk]
      have hr : decide (decide (k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = false := by
        rw [decide_eq_false_iff_not]; simp [hrc]
      simp only [hb, hr, Bool.false_eq_true, if_false, if_true, reduceIte]
    · by_cases hlc : k - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)
      · -- the genuine class-(b) case.
        set L := k - (d - 1) * (d - 1) - 2 * ((d - 1) / 2) with hL
        have hb : decide (decide (k < (d - 1) * (d - 1)) = false) = true := by
          rw [decide_eq_true_eq]; simp [hbulk]
        have hr : decide (decide (k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = true := by
          rw [decide_eq_true_eq]; simp [hrc]
        have hlcd : decide (decide (k - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)) = true) = true := by
          rw [decide_eq_true_eq]; simp [hlc]
        simp only [hb, hr, hlcd, if_true]
        have hdiv0 : (2 * L + 1) * d / d = 2 * L + 1 := Nat.mul_div_cancel _ hdpos
        have hmod0 : (2 * L + 1) * d % d = 0 := Nat.mul_mod_left _ _
        have hdiv1 : (2 * L + 2) * d / d = 2 * L + 2 := Nat.mul_div_cancel _ hdpos
        have hmod1 : (2 * L + 2) * d % d = 0 := Nat.mul_mod_left _ _
        have hLlt : 2 * L + 2 ≤ d - 1 := by
          have hhf2 : 2 * ((d - 1) / 2) = d - 1 := by omega
          omega
        have hb0 : (2 * L + 1) * d < nQubits d := by
          simp only [nQubits]
          have h1 : (2 * L + 1) * d ≤ (d - 1) * d := Nat.mul_le_mul_right d (by omega)
          have h2 : (d-1) * d < d * d := (Nat.mul_lt_mul_right hdpos).mpr (by omega)
          omega
        have hb1 : (2 * L + 2) * d < nQubits d := by
          simp only [nQubits]
          have h1 : (2 * L + 2) * d ≤ (d - 1) * d := Nat.mul_le_mul_right d (by omega)
          have h2 : (d-1) * d < d * d := (Nat.mul_lt_mul_right hdpos).mpr (by omega)
          omega
        have hne : ¬ ((2 * L + 1) * d = (2 * L + 2) * d) := by
          intro h
          have : (2*L+1) * d < (2*L+2) * d := (Nat.mul_lt_mul_right hdpos).mpr (by omega)
          omega
        have hbd0 : decide ((2 * L + 1) * d % d = 0) = true := by rw [hmod0]; simp
        have hbd1 : decide ((2 * L + 2) * d % d = 0) = true := by rw [hmod1]; simp
        have hbdiv0 : decide ((2 * L + 1) * d / d = 2 * L + 1) = true := by rw [hdiv0]; simp
        have hbdiv1a : decide ((2 * L + 2) * d / d = 2 * L + 1) = false := by
          rw [hdiv1]; rw [decide_eq_false_iff_not]; omega
        have hbdiv1b : decide ((2 * L + 2) * d / d = 2 * L + 2) = true := by rw [hdiv1]; simp
        have hbne : decide (decide ((2 * L + 1) * d = (2 * L + 2) * d) = false) = true := by
          rw [decide_eq_true_eq, decide_eq_false_iff_not]; exact hne
        have hbb0 : decide (decide ((2 * L + 1) * d < nQubits d) = true) = true := by
          rw [decide_eq_true_eq, decide_eq_true_eq]; exact hb0
        have hbb1 : decide (decide ((2 * L + 2) * d < nQubits d) = true) = true := by
          rw [decide_eq_true_eq, decide_eq_true_eq]; exact hb1
        simp only [hbd0, hbd1, hbdiv0, hbdiv1a, hbdiv1b, hbne, hbb0, hbb1,
          decide_true, decide_false, Bool.false_eq_true, if_true, if_false, reduceIte]
      · -- leftClass false → `gLeftC1 D true` antecedent false → vacuous.
        have hb : decide (decide (k < (d - 1) * (d - 1)) = false) = true := by
          rw [decide_eq_true_eq]; simp [hbulk]
        have hr : decide (decide (k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = true := by
          rw [decide_eq_true_eq]; simp [hrc]
        have hlcd : decide (decide (k - (d - 1) * (d - 1) < 3 * ((d - 1) / 2)) = true) = false := by
          rw [decide_eq_false_iff_not]; simp [hlc]
        simp only [hb, hr, hlcd, Bool.false_eq_true, if_false, if_true, reduceIte]

/-- Column guards at the class-(b) anti qubits (`q0, q1` are multiples of `d`). -/
abbrev qbColGuardF (D : OddSurfaceDistance) : SFormula 1 :=
  .and (colGuardPure1 D (qb0 D)) (colGuardPure1 D (qb1 D))

def qbColGuardPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (qbColGuardF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [colGuardPure1, qb0, qb1, bbL1, baseBTA, baseHalfTA, bulkCountTA, dX1, distAtBoundIdx,
    dm1TA, SFormula.eval, SC.closed, SC.b, STerm.eval, Term.eval, Term.lift, bind, Option.bind]
  rw [Nat.mul_mod_left, Nat.mul_mod_left]
  simp

/-- The left-`Z` all-others pin for class (b): on column 0, if the left band fires,
then `boundNat ∈ {q0, q1}`. -/
abbrev classBLeftZPinBody (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (colGuardRaw2 D)
    (.imp (.eqBool (SC.closed (leftBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.b true))
      (.or (.eqNat SFormula.boundNat (SC.closed (qb0_2 D)))
        (.eqNat SFormula.boundNat (SC.closed (qb1_2 D)))))

abbrev classBLeftZPinF (D : OddSurfaceDistance) : SFormula 1 :=
  .allNatLt (nQ1 D) (classBLeftZPinBody D)

def classBLeftZPinPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (classBLeftZPinF D) := by
  refine PureFamilyDerivA.allNatLtIntro _ ?_
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [classBLeftZPinBody, colGuardRaw2, leftBandGuardTA, qb0_2, qb1_2, bbL2, baseBTA,
    baseHalfTA, bulkCountTA, dX2, distAtBoundIdx2, kX2, dm1TA, orEqPair, SFormula.eval, SC.closed,
    SC.b, STerm.eval, SFormula.boundNat, Term.eval, Term.lift, bind, Option.bind]
  set q := rho ⟨0, by decide⟩ with hq'
  set k := rho ⟨1, by decide⟩ with hk'
  set d := D.distance with hdd
  have hdpos : 0 < d := by omega
  set L := k - (d - 1) * (d - 1) - 2 * ((d - 1) / 2) with hL
  by_cases hq : q % d = 0
  · simp only [hq, decide_true, if_true]
    have hqdiv : q = q / d * d := (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hq)).symm
    by_cases hr0 : q / d = 2 * L + 1
    · have hqe : decide (q = (2 * L + 1) * d) = true := by rw [decide_eq_true_eq, hqdiv, hr0]
      have hr0d : decide (q / d = 2 * L + 1) = true := by rw [decide_eq_true_eq]; exact hr0
      simp only [hr0d, hqe, decide_true, if_true]
    · by_cases hr1 : q / d = 2 * L + 2
      · have hqe : decide (q = (2 * L + 2) * d) = true := by rw [decide_eq_true_eq, hqdiv, hr1]
        have hr0d : decide (q / d = 2 * L + 1) = false := by rw [decide_eq_false_iff_not]; exact hr0
        have hr1d : decide (q / d = 2 * L + 2) = true := by rw [decide_eq_true_eq]; exact hr1
        have hq0 : decide (q = (2 * L + 1) * d) = false := by
          rw [decide_eq_false_iff_not]; intro h; apply hr0; rw [hqdiv] at h
          exact Nat.eq_of_mul_eq_mul_right hdpos h
        simp only [hr0d, hr1d, hqe, hq0, decide_true, decide_false, Bool.false_eq_true,
          if_true, if_false, reduceIte]
      · have hr0d : decide (q / d = 2 * L + 1) = false := by rw [decide_eq_false_iff_not]; exact hr0
        have hr1d : decide (q / d = 2 * L + 2) = false := by rw [decide_eq_false_iff_not]; exact hr1
        simp only [hr0d, hr1d, decide_false, Bool.false_eq_true, if_false, reduceIte]
  · simp only [hq, decide_false, Bool.false_eq_true, if_false, reduceIte]

/-- Entry-at-`q` resolves to `Z` via the left-`Z` boundary leaf. -/
def antiZAtB (D : OddSurfaceDistance) {Γ : List (SFormula 1)} (qT : Term 1 .nat)
    (hEntry : SFormula.Deriv Γ
      (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed qT))
        (SC.closed (baseLeafTreeTA (dX1 D) kX1 qT))))
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dX1 D) kX1)) (SC.b false)))
    (hTopC : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dX1 D) kX1)) (SC.b false)))
    (hRightC : SFormula.Deriv Γ (.eqBool (SC.closed (rightClassGuardTA (dX1 D) kX1)) (SC.b false)))
    (hLeftC : SFormula.Deriv Γ (.eqBool (SC.closed (leftClassGuardTA (dX1 D) kX1)) (SC.b true)))
    (hLeftB : SFormula.Deriv Γ (.eqBool (SC.closed (leftBandGuardTA (dX1 D) kX1 qT)) (SC.b true))) :
    SFormula.Deriv Γ (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed qT)) (SC.p Pauli.Z)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ hEntry (baseLeafLeftZ _ _ _ hBulk hTopC hRightC hLeftC hLeftB)

/-- Extract the class-(b) left-`Z` pin disjunction at `boundNat`. -/
def classBLeftZPinAt {Δ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hW : SFormula.Deriv Δ (classBLeftZPinF D).weaken)
    (hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nQ1 D).weaken))
    (hcol : SFormula.Deriv Δ (colGuardRaw2 D))
    (hband : SFormula.Deriv Δ (.eqBool (SC.closed (leftBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.b true))) :
    SFormula.Deriv Δ
      (.or (.eqNat SFormula.boundNat (SC.closed (qb0_2 D)))
        (.eqNat SFormula.boundNat (SC.closed (qb1_2 D)))) := by
  have hElim := SFormula.Deriv.allNatLtElim (nQ1 D).weaken
    ((classBLeftZPinBody D).lift 1) SFormula.boundNat hW hq
  have hBody := SFormula.Deriv.applyNatBoundNatBeta (classBLeftZPinBody D) hElim
  exact SFormula.Deriv.mp (SFormula.Deriv.mp hBody hcol) hband

/-- **Class-(b) two-anti per-`k` commutation.** -/
def commTwoAntiB {Γ : List (SFormula 1)} (D : OddSurfaceDistance)
    (hBulk : SFormula.Deriv Γ (gBulk1 D false))
    (hTopC : SFormula.Deriv Γ (gTopC1 D false))
    (hRightC : SFormula.Deriv Γ (gRightC1 D false))
    (hLeftC : SFormula.Deriv Γ (gLeftC1 D true))
    (hClassB : SFormula.Deriv Γ (classBPackF D))
    (hCol : SFormula.Deriv Γ (qbColGuardF D))
    (hPin : SFormula.Deriv Γ (classBLeftZPinF D))
    (hEntryF : SFormula.Deriv Γ (entryFlatF1 D))
    (hRBFF : SFormula.Deriv Γ (rightBandFalseF D))
    (hEntry0 : SFormula.Deriv Γ
      (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed (qb0 D)))
        (SC.closed (baseLeafTreeTA (dX1 D) kX1 (qb0 D)))))
    (hEntry1 : SFormula.Deriv Γ
      (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed (qb1 D)))
        (SC.closed (baseLeafTreeTA (dX1 D) kX1 (qb1 D))))) :
    SFormula.Deriv Γ (commGoal1 D) := by
  have hPack := SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp hClassB hBulk) hRightC) hLeftC
  have hBand0 := SFormula.Deriv.andElimLeft hPack
  have hBand1 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hPack)
  have hNe := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hPack))
  have hLt0 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hPack)))
  have hLt1 := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hPack)))
  have hZ0 := antiZAtB D (qb0 D) hEntry0 hBulk hTopC hRightC hLeftC hBand0
  have hZ1 := antiZAtB D (qb1 D) hEntry1 hBulk hTopC hRightC hLeftC hBand1
  have hX0 := lxPureEntryX D (qb0 D) (qb0_pure D) (SFormula.Deriv.andElimLeft hCol)
  have hX1 := lxPureEntryX D (qb1 D) (qb1_pure D) (SFormula.Deriv.andElimRight hCol)
  refine SFormula.Deriv.commutesOfTwoAnti _ _ _ (SC.closed (qb0 D)) (SC.closed (qb1 D))
    ?wlt0 ?wlt1 ?wne ?wanti0 ?wanti1 ?wrest
  case wlt0 => exact hLt0
  case wlt1 => exact hLt1
  case wne =>
    refine SFormula.Deriv.notIntro ?_
    refine SFormula.Deriv.notElim
      (SFormula.Deriv.eqNatBoolTrue (Γ := _) (qb0 D) (qb1 D) .assumption) ?_
    exact SFormula.Deriv.eqBoolFalseNotTrue _ (cw1 hNe)
  case wanti0 =>
    exact SFormula.Deriv.anticommutesTransport _ (SC.p Pauli.Z) _ (SC.p Pauli.X) (SC.b true)
      hZ0 hX0 (SFormula.Deriv.pauliAnticommutesLit Pauli.Z Pauli.X)
  case wanti1 =>
    exact SFormula.Deriv.anticommutesTransport _ (SC.p Pauli.Z) _ (SC.p Pauli.X) (SC.b true)
      hZ1 hX1 (SFormula.Deriv.pauliAnticommutesLit Pauli.Z Pauli.X)
  case wrest =>
    refine SFormula.Deriv.allNatLtIntroBounded _ _ ?_
    refine SFormula.Deriv.impIntro (SFormula.Deriv.impIntro ?_)
    refine SFormula.Deriv.boolCases (logicalXColGuardAt2 D) _ ?_ ?_
    · set ΔT : List (SFormula 2) := .eqBool (logicalXColGuardAt2 D) (SC.b true)
        :: .not (.eqNat SFormula.boundNat (SC.closed (qb1 D)).weaken)
        :: .not (.eqNat SFormula.boundNat (SC.closed (qb0 D)).weaken)
        :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ with hΔT
      have hEntryW : SFormula.Deriv ΔT (entryFlatF1 D).weaken :=
        cw4 (SFormula.Deriv.weakenFresh (A := entryFlatF1 D) hEntryF)
      have hRBFW : SFormula.Deriv ΔT (rightBandFalseF D).weaken :=
        cw4 (SFormula.Deriv.weakenFresh (A := rightBandFalseF D) hRBFF)
      have hq : SFormula.Deriv ΔT (SFormula.witnessLt SFormula.boundNat (nQ1 D).weaken) :=
        SFormula.Deriv.hyp (by rw [hΔT]; right; right; right; exact List.mem_cons_self)
      have hcolT : SFormula.Deriv ΔT (.eqBool (logicalXColGuardAt2 D) (SC.b true)) := by
        rw [hΔT]; exact .assumption
      have hcolRaw : SFormula.Deriv ΔT (colGuardRaw2 D) := by rw [← colGuard2_eq]; exact hcolT
      have hEntry := entryAtBound D hEntryW hq
      have hRBF := rbfAtBound D hRBFW hq hcolRaw
      refine colDispatchOnTrue D hEntry hcolT hRBF ?hZbulk ?hZleft
      case hZbulk =>
        intro Δ' lift _ _ hBulkTrueΔ _ _
        -- bulk-Z: class (b) has bulk FALSE, contradicting cascade bulk TRUE.
        have hBulkFalse0 : SFormula.Deriv ΔT (gBulk D false) :=
          cw4 (SFormula.Deriv.weakenFresh (A := gBulk1 D false) hBulk)
        exact eqBoolContra _ hBulkTrueΔ (lift hBulkFalse0)
      case hZleft =>
        intro Δ' lift _ hcolΔ _ _ _ _ hLeftBΔ
        -- left-Z: use the left-Z pin → q ∈ {q0, q1}, contradicting exclusions.
        have hcolRaw' : SFormula.Deriv Δ' (colGuardRaw2 D) := by rw [← colGuard2_eq]; exact hcolΔ
        have hPinW0 : SFormula.Deriv ΔT (classBLeftZPinF D).weaken :=
          cw4 (SFormula.Deriv.weakenFresh (A := classBLeftZPinF D) hPin)
        have hdisj := classBLeftZPinAt D (lift hPinW0) (lift hq) hcolRaw' hLeftBΔ
        have hne0 : SFormula.Deriv ΔT (.not (.eqNat SFormula.boundNat (SC.closed (qb0 D)).weaken)) := by
          rw [hΔT]; exact .hyp (by right; right; exact List.mem_cons_self)
        have hne1 : SFormula.Deriv ΔT (.not (.eqNat SFormula.boundNat (SC.closed (qb1 D)).weaken)) := by
          rw [hΔT]; exact .hyp (by right; exact List.mem_cons_self)
        refine SFormula.Deriv.orElim hdisj ?_ ?_
        · exact SFormula.Deriv.botElim (SFormula.Deriv.notElim (.assumption) (cw1 (lift hne0)))
        · exact SFormula.Deriv.botElim (SFormula.Deriv.notElim (.assumption) (cw1 (lift hne1)))
    · exact logicalXOffColumnLocalCommutes D (rowK2 D) .assumption

/-! ## Top-level: bundle the supporting packs and classify `k` -/

/-- `rightClass = false → topClass = false` (since `topClass ⊆ rightClass`).
A closed-in-`k` arithmetic implication, discharged by `arithBool`. -/
abbrev topCFromRightCF (D : OddSurfaceDistance) : SFormula 1 :=
  .imp (gRightC1 D false) (gTopC1 D false)

def topCFromRightCPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (topCFromRightCF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [topCFromRightCF, gRightC1, gTopC1, topClassGuardTA, rightClassGuardTA, baseBTA,
    baseHalfTA, bulkCountTA, dX1, distAtBoundIdx, dm1TA, SFormula.eval, SC.closed, SC.b, STerm.eval,
    Term.eval, Term.lift, bind, Option.bind]
  set k := rho ⟨0, by decide⟩
  set d := D.distance
  by_cases hrc : k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)
  · have : decide (decide (k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = false := by
      rw [decide_eq_false_iff_not]; simp [hrc]
    simp only [this, Bool.false_eq_true, if_false, reduceIte]
  · have hrcd : decide (decide (k - (d - 1) * (d - 1) < 2 * ((d - 1) / 2)) = false) = true := by
      rw [decide_eq_true_eq]; simp [hrc]
    have htc : decide (k - (d - 1) * (d - 1) < (d - 1) / 2) = false := by
      rw [decide_eq_false_iff_not]
      have : (d - 1) / 2 ≤ 2 * ((d - 1) / 2) := by omega
      omega
    simp only [hrcd, htc, decide_false, decide_true, Bool.false_eq_true, if_false, if_true, reduceIte]

/-- Entry-at-`q` facts at the four anti qubits, as formulas (cut into context). -/
abbrev entryAtF (D : OddSurfaceDistance) (qT : Term 1 .nat) : SFormula 1 :=
  .eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed qT))
    (SC.closed (baseLeafTreeTA (dX1 D) kX1 qT))

/-- The big conjunction of every supporting pack used by the per-`k` classification. -/
abbrev xBundleF (D : OddSurfaceDistance) : SFormula 1 :=
  .and (entryFlatF1 D)
  (.and (rightBandFalseF D)
  (.and (classAPackF D)
  (.and (qaColGuardF D)
  (.and (classABulkZPinF D)
  (.and (classBPackF D)
  (.and (qbColGuardF D)
  (.and (classBLeftZPinF D)
  (.and (entryAtF D (qa0 D))
  (.and (entryAtF D (qa1 D))
  (.and (entryAtF D (qb0 D))
  (.and (entryAtF D (qb1 D))
  (.and (topCFromRightCF D) (bandImpCZeroF D)))))))))))))

/-- Combine two PFDA facts into their conjunction. -/
def pfdaAnd {D : OddSurfaceDistance} {A B : SFormula 1}
    (hA : PureFamilyDerivA Surface.code.body (D.distance + 2) A)
    (hB : PureFamilyDerivA Surface.code.body (D.distance + 2) B) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (.and A B) :=
  PureFamilyDerivA.cut2 (SFormula.Deriv.andIntro .assumption (.hyp (by right; exact List.mem_cons_self))) hA hB

def xBundle (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (xBundleF D) :=
  pfdaAnd (entryFlatPack D) (pfdaAnd (rightBandFalsePack D)
    (pfdaAnd (classAPack D) (pfdaAnd (qaColGuardPack D)
      (pfdaAnd (classABulkZPinPack D) (pfdaAnd (classBPack D)
        (pfdaAnd (qbColGuardPack D) (pfdaAnd (classBLeftZPinPack D)
          (pfdaAnd (xEntryFlat1 D (qa0 D) (qa0_pure D))
            (pfdaAnd (xEntryFlat1 D (qa1 D) (qa1_pure D))
              (pfdaAnd (xEntryFlat1 D (qb0 D) (qb0_pure D))
                (pfdaAnd (xEntryFlat1 D (qb1 D) (qb1_pure D))
                  (pfdaAnd (topCFromRightCPack D) (bandImpCZeroPack D)))))))))))))

/-! ### Pointwise Z-handler helpers (close `Z` leaves by `k`-fact contradiction) -/

/-- A bulk-`Z` handler that kills the leaf because the cascade's `gKind D true`
contradicts a context `gKind1 D false` fact (carried via `lift`). -/
def zhBulkByKindFalse {Γ : List (SFormula 1)} (D : OddSurfaceDistance)
    (hKindF : SFormula.Deriv Γ (gKind1 D false)) :
    ∀ (Δ' : List (SFormula 2)),
      (∀ {A : SFormula 2}, SFormula.Deriv (.eqBool (logicalXColGuardAt2 D) (SC.b true)
          :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (entryFlat2F D) →
      SFormula.Deriv Δ' (.eqBool (logicalXColGuardAt2 D) (SC.b true)) →
      SFormula.Deriv Δ' (gBulk D true) → SFormula.Deriv Δ' (gBand D true) →
      SFormula.Deriv Δ' (gKind D true) → SFormula.Deriv Δ' (lcGoal D) := by
  intro Δ' lift _ _ _ _ hKindT
  have hKF : SFormula.Deriv _ (gKind D false) :=
    lift (cw2 (SFormula.Deriv.weakenFresh (A := gKind1 D false) hKindF))
  exact eqBoolContra _ hKindT hKF

/-- A bulk-`Z` handler that kills the leaf because the band-pin (`band ∧ col → c=0`)
contradicts a context `cZero1 D false` (`c ≠ 0`) fact. -/
def zhBulkByCNZ {Γ : List (SFormula 1)} (D : OddSurfaceDistance)
    (hCNZ : SFormula.Deriv Γ (cZero1 D false))
    (hImp : SFormula.Deriv Γ (bandImpCZeroF D)) :
    ∀ (Δ' : List (SFormula 2)),
      (∀ {A : SFormula 2}, SFormula.Deriv (.eqBool (logicalXColGuardAt2 D) (SC.b true)
          :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (entryFlat2F D) →
      SFormula.Deriv Δ' (.eqBool (logicalXColGuardAt2 D) (SC.b true)) →
      SFormula.Deriv Δ' (gBulk D true) → SFormula.Deriv Δ' (gBand D true) →
      SFormula.Deriv Δ' (gKind D true) → SFormula.Deriv Δ' (lcGoal D) := by
  intro Δ' lift _ hcolΔ _ hBandΔ _
  have hcolRaw : SFormula.Deriv Δ' (colGuardRaw2 D) := by rw [← colGuard2_eq]; exact hcolΔ
  -- pin: from col ∧ band → c = 0
  have hImpW : SFormula.Deriv _ (bandImpCZeroF D).weaken :=
    lift (cw2 (SFormula.Deriv.weakenFresh (A := bandImpCZeroF D) hImp))
  have hq : SFormula.Deriv _ (SFormula.witnessLt SFormula.boundNat (nQ1 D).weaken) :=
    lift (.hyp (by right; exact List.mem_cons_self))
  have hElim := SFormula.Deriv.allNatLtElim (nQ1 D).weaken ((bandImpCZeroBody D).lift 1)
    SFormula.boundNat hImpW hq
  have hBody := SFormula.Deriv.applyNatBoundNatBeta (bandImpCZeroBody D) hElim
  have hCZtrue := SFormula.Deriv.mp (SFormula.Deriv.mp hBody hcolRaw) hBandΔ
  have hCZfalse : SFormula.Deriv _ (cZero2 D false) :=
    lift (cw2 (SFormula.Deriv.weakenFresh (A := cZero1 D false) hCNZ))
  exact eqBoolContra _ hCZtrue hCZfalse

/-- A bulk-`Z` handler that kills the leaf because the cascade's `gBulk D true`
contradicts a context `gBulk1 D false` fact. -/
def zhBulkByBulkFalse {Γ : List (SFormula 1)} (D : OddSurfaceDistance)
    (hBulkF : SFormula.Deriv Γ (gBulk1 D false)) :
    ∀ (Δ' : List (SFormula 2)),
      (∀ {A : SFormula 2}, SFormula.Deriv (.eqBool (logicalXColGuardAt2 D) (SC.b true)
          :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (entryFlat2F D) →
      SFormula.Deriv Δ' (.eqBool (logicalXColGuardAt2 D) (SC.b true)) →
      SFormula.Deriv Δ' (gBulk D true) → SFormula.Deriv Δ' (gBand D true) →
      SFormula.Deriv Δ' (gKind D true) → SFormula.Deriv Δ' (lcGoal D) := by
  intro Δ' lift _ _ hBulkT _ _
  have hBF : SFormula.Deriv _ (gBulk D false) :=
    lift (cw2 (SFormula.Deriv.weakenFresh (A := gBulk1 D false) hBulkF))
  exact eqBoolContra _ hBulkT hBF

/-- A left-`Z` handler that kills the leaf because the cascade's `gBulk D false`
contradicts a context `gBulk1 D true` fact. -/
def zhLeftByBulkTrue {Γ : List (SFormula 1)} (D : OddSurfaceDistance)
    (hBulkT : SFormula.Deriv Γ (gBulk1 D true)) :
    ∀ (Δ' : List (SFormula 2)),
      (∀ {A : SFormula 2}, SFormula.Deriv (.eqBool (logicalXColGuardAt2 D) (SC.b true)
          :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (entryFlat2F D) →
      SFormula.Deriv Δ' (.eqBool (logicalXColGuardAt2 D) (SC.b true)) →
      SFormula.Deriv Δ' (gBulk D false) → SFormula.Deriv Δ' (gTopC D false) →
      SFormula.Deriv Δ' (gRightC D false) → SFormula.Deriv Δ' (gLeftC D true) →
      SFormula.Deriv Δ' (gLeftB D true) → SFormula.Deriv Δ' (lcGoal D) := by
  intro Δ' lift _ _ hBulkFΔ _ _ _ _
  have hBT : SFormula.Deriv _ (gBulk D true) :=
    lift (cw2 (SFormula.Deriv.weakenFresh (A := gBulk1 D true) hBulkT))
  exact eqBoolContra _ hBT hBulkFΔ

/-- A left-`Z` handler that kills the leaf because the cascade's `gLeftC D true`
contradicts a context `gLeftC1 D false` fact. -/
def zhLeftByLeftCFalse {Γ : List (SFormula 1)} (D : OddSurfaceDistance)
    (hLeftCF : SFormula.Deriv Γ (gLeftC1 D false)) :
    ∀ (Δ' : List (SFormula 2)),
      (∀ {A : SFormula 2}, SFormula.Deriv (.eqBool (logicalXColGuardAt2 D) (SC.b true)
          :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (entryFlat2F D) →
      SFormula.Deriv Δ' (.eqBool (logicalXColGuardAt2 D) (SC.b true)) →
      SFormula.Deriv Δ' (gBulk D false) → SFormula.Deriv Δ' (gTopC D false) →
      SFormula.Deriv Δ' (gRightC D false) → SFormula.Deriv Δ' (gLeftC D true) →
      SFormula.Deriv Δ' (gLeftB D true) → SFormula.Deriv Δ' (lcGoal D) := by
  intro Δ' lift _ _ _ _ _ hLeftCTΔ _
  have hLF : SFormula.Deriv _ (gLeftC D false) :=
    lift (cw2 (SFormula.Deriv.weakenFresh (A := gLeftC1 D false) hLeftCF))
  exact eqBoolContra _ hLeftCTΔ hLF

/-- A left-`Z` handler that kills the leaf because the cascade's `gRightC D false`
contradicts a context `gRightC1 D true` fact. -/
def zhLeftByRightCTrue {Γ : List (SFormula 1)} (D : OddSurfaceDistance)
    (hRightCT : SFormula.Deriv Γ (gRightC1 D true)) :
    ∀ (Δ' : List (SFormula 2)),
      (∀ {A : SFormula 2}, SFormula.Deriv (.eqBool (logicalXColGuardAt2 D) (SC.b true)
          :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (entryFlat2F D) →
      SFormula.Deriv Δ' (.eqBool (logicalXColGuardAt2 D) (SC.b true)) →
      SFormula.Deriv Δ' (gBulk D false) → SFormula.Deriv Δ' (gTopC D false) →
      SFormula.Deriv Δ' (gRightC D false) → SFormula.Deriv Δ' (gLeftC D true) →
      SFormula.Deriv Δ' (gLeftB D true) → SFormula.Deriv Δ' (lcGoal D) := by
  intro Δ' lift _ _ _ _ hRightCFΔ _ _
  have hRT : SFormula.Deriv _ (gRightC D true) :=
    lift (cw2 (SFormula.Deriv.weakenFresh (A := gRightC1 D true) hRightCT))
  exact eqBoolContra _ hRT hRightCFΔ

/-! ### Bundle extractors (project the 12 packs from a context `xBundleF` hyp) -/

namespace BundleExtract
variable {Γ : List (SFormula 1)} {D : OddSurfaceDistance}
def entryF (h : SFormula.Deriv Γ (xBundleF D)) : SFormula.Deriv Γ (entryFlatF1 D) :=
  SFormula.Deriv.andElimLeft h
def rbf (h : SFormula.Deriv Γ (xBundleF D)) : SFormula.Deriv Γ (rightBandFalseF D) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight h)
def classA (h : SFormula.Deriv Γ (xBundleF D)) : SFormula.Deriv Γ (classAPackF D) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight h))
def qaCol (h : SFormula.Deriv Γ (xBundleF D)) : SFormula.Deriv Γ (qaColGuardF D) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight h)))
def aPin (h : SFormula.Deriv Γ (xBundleF D)) : SFormula.Deriv Γ (classABulkZPinF D) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight h))))
def classB (h : SFormula.Deriv Γ (xBundleF D)) : SFormula.Deriv Γ (classBPackF D) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight h)))))
def qbCol (h : SFormula.Deriv Γ (xBundleF D)) : SFormula.Deriv Γ (qbColGuardF D) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight h))))))
def bPin (h : SFormula.Deriv Γ (xBundleF D)) : SFormula.Deriv Γ (classBLeftZPinF D) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight h)))))))
def eqa0 (h : SFormula.Deriv Γ (xBundleF D)) : SFormula.Deriv Γ (entryAtF D (qa0 D)) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight h))))))))
def eqa1 (h : SFormula.Deriv Γ (xBundleF D)) : SFormula.Deriv Γ (entryAtF D (qa1 D)) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
        (SFormula.Deriv.andElimRight h)))))))))
def eqb0 (h : SFormula.Deriv Γ (xBundleF D)) : SFormula.Deriv Γ (entryAtF D (qb0 D)) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
        (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight h))))))))))
def eqb1 (h : SFormula.Deriv Γ (xBundleF D)) : SFormula.Deriv Γ (entryAtF D (qb1 D)) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
        (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
          (SFormula.Deriv.andElimRight h)))))))))))
def topC (h : SFormula.Deriv Γ (xBundleF D)) : SFormula.Deriv Γ (topCFromRightCF D) :=
  h.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimLeft
def bandImpC (h : SFormula.Deriv Γ (xBundleF D)) : SFormula.Deriv Γ (bandImpCZeroF D) :=
  h.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight
end BundleExtract

/-- **The symbolic (∀ D) `logicalX` normalizer.**  For every `OddSurfaceDistance`,
`logicalX` commutes with every generated stabilizer row of the recursive Surface
code.  Proof: `allNatLtIntro` the stabilizer index `k`, `cut1` the supporting pack
bundle, then classify `k` by its (purely arithmetic) cell guards via nested
`boolCases`, dispatching each class to `commPointwiseSym` / `commTwoAntiA` /
`commTwoAntiB`. -/
def xNormCommuteSym (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2)
      (closedSF (logicalXNormalizesOddF D)) := by
  unfold closedSF logicalXNormalizesOddF Formula.normalizesCodeUpTo
  simp only [closedSF, Formula.codeRow, Term.weaken]
  refine PureFamilyDerivA.allNatLtIntro _ ?_
  -- Per-`k` goal `commGoal1 D`; cut in the bundle.
  refine PureFamilyDerivA.cut1 ?_ (xBundle D)
  -- Context: [xBundleF D].  Classify `k` by its k-only cell guards.
  open BundleExtract in
  refine SFormula.Deriv.boolCases (SC.closed (bulkGuardTA (dX1 D) kX1)) _ ?bulkT ?bulkF
  case bulkT =>
    -- bulk TRUE.  Context: [gBulk1 true, xBundle].
    refine SFormula.Deriv.boolCases (SC.closed (.eqNat (.mod kX1 (dm1TA (dX1 D))) (.natLit 0))) _ ?cz ?cnz
    case cz =>
      -- c = 0.  Context: [cZero1 true, gBulk1 true, xBundle].
      refine SFormula.Deriv.boolCases (SC.closed (baseKindGuardTA (dX1 D) kX1)) _ ?kt ?kf
      case kt =>
        -- kind TRUE → class (a).
        exact commTwoAntiA D
          (.hyp (by right; right; exact List.mem_cons_self))   -- gBulk1 true
          (.hyp (by right; exact List.mem_cons_self))          -- cZero1 true
          (.assumption)                                        -- gKind1 true
          (BundleExtract.classA (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtract.qaCol (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtract.aPin (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtract.entryF (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtract.rbf (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtract.eqa0 (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtract.eqa1 (.hyp (by right; right; right; exact List.mem_cons_self)))
      case kf =>
        -- kind FALSE → pointwise.
        refine commPointwiseSym D
          (BundleExtract.entryF (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtract.rbf (.hyp (by right; right; right; exact List.mem_cons_self)))
          (zhBulkByKindFalse D (.assumption))
          (zhLeftByBulkTrue D (.hyp (by right; right; exact List.mem_cons_self)))
    case cnz =>
      -- c ≠ 0 → pointwise.  Context: [cZero1 false, gBulk1 true, xBundle].
      refine commPointwiseSym D
        (BundleExtract.entryF (.hyp (by right; right; exact List.mem_cons_self)))
        (BundleExtract.rbf (.hyp (by right; right; exact List.mem_cons_self)))
        (zhBulkByCNZ D (.assumption)
          (BundleExtract.bandImpC (.hyp (by right; right; exact List.mem_cons_self))))
        (zhLeftByBulkTrue D (.hyp (by right; exact List.mem_cons_self)))
  case bulkF =>
    -- bulk FALSE.  Context: [gBulk1 false, xBundle].
    refine SFormula.Deriv.boolCases (SC.closed (leftClassGuardTA (dX1 D) kX1)) _ ?lt ?lf
    case lt =>
      -- leftClass TRUE.  Context: [gLeftC1 true, gBulk1 false, xBundle].
      refine SFormula.Deriv.boolCases (SC.closed (rightClassGuardTA (dX1 D) kX1)) _ ?rt ?rf
      case rt =>
        -- rightClass TRUE → pointwise.
        refine commPointwiseSym D
          (BundleExtract.entryF (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtract.rbf (.hyp (by right; right; right; exact List.mem_cons_self)))
          (zhBulkByBulkFalse D (.hyp (by right; right; exact List.mem_cons_self)))
          (zhLeftByRightCTrue D (.assumption))
      case rf =>
        -- rightClass FALSE → class (b).  Context: [gRightC1 false, gLeftC1 true, gBulk1 false, xBundle].
        exact commTwoAntiB D
          (.hyp (by right; right; exact List.mem_cons_self))          -- gBulk1 false
          (SFormula.Deriv.mp
            (BundleExtract.topC (.hyp (by right; right; right; exact List.mem_cons_self)))
            (.assumption))                                            -- gTopC1 false (from rightC false)
          (.assumption)                                              -- gRightC1 false
          (.hyp (by right; exact List.mem_cons_self))                -- gLeftC1 true
          (BundleExtract.classB (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtract.qbCol (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtract.bPin (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtract.entryF (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtract.rbf (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtract.eqb0 (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtract.eqb1 (.hyp (by right; right; right; exact List.mem_cons_self)))
    case lf =>
      -- leftClass FALSE → pointwise.  Context: [gLeftC1 false, gBulk1 false, xBundle].
      refine commPointwiseSym D
        (BundleExtract.entryF (.hyp (by right; right; exact List.mem_cons_self)))
        (BundleExtract.rbf (.hyp (by right; right; exact List.mem_cons_self)))
        (zhBulkByBulkFalse D (.hyp (by right; exact List.mem_cons_self)))
        (zhLeftByLeftCFalse D (.assumption))


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

/-! ## Two-anti class (a) [Z]: top-row odd-`c` bulk `X`-plaquettes

`k < (d-1)²`, `r = k/(d-1) = 0`, `c = k%(d-1)` odd (so kind FALSE).  The row
anticommutes with `logicalZ` at the two ROW-0 qubits `q0 = c`, `q1 = c+1`. -/

/-- `c = k % (d-1)` at arity 1 = first class-(a) anti qubit. -/
abbrev qza0 (D : OddSurfaceDistance) : Term 1 .nat := .mod kX1 (dm1TA (dX1 D))
/-- `c + 1` = second class-(a) anti qubit. -/
abbrev qza1 (D : OddSurfaceDistance) : Term 1 .nat := .add (.mod kX1 (dm1TA (dX1 D))) (.natLit 1)

def qza0_pure (D : OddSurfaceDistance) : SFormula.PureNatTerm (qza0 D) :=
  SFormula.PureNatTerm.mod (SFormula.PureNatTerm.var _) (dm1_pure D)
def qza1_pure (D : OddSurfaceDistance) : SFormula.PureNatTerm (qza1 D) :=
  SFormula.PureNatTerm.add (SFormula.PureNatTerm.mod (SFormula.PureNatTerm.var _) (dm1_pure D))
    (SFormula.PureNatTerm.natLit _)

/-- The class-(a) k-condition guard pack: given bulk true, `r = 0`, kind false (`c`
odd), the bulk band fires at `q0 = c` and `q1 = c+1`, `q0 ≠ q1`, both `< nQubits`. -/
abbrev classZAPackF (D : OddSurfaceDistance) : SFormula 1 :=
  .imp (gBulk1 D true) (.imp (gRZero1 D true) (.imp (gKind1 D false)
    (.and (.eqBool (SC.closed (baseBulkBandGuardTA (dX1 D) kX1 (qza0 D))) (SC.b true))
      (.and (.eqBool (SC.closed (baseBulkBandGuardTA (dX1 D) kX1 (qza1 D))) (SC.b true))
        (.and (.eqBool (SC.closed (.eqNat (qza0 D) (qza1 D))) (SC.b false))
          (.and (SFormula.witnessLt (SC.closed (qza0 D)) (SC.n (arity := 1) (nQubits D.distance)))
            (SFormula.witnessLt (SC.closed (qza1 D)) (SC.n (arity := 1) (nQubits D.distance)))))))))

def classZAPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (classZAPackF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [classZAPackF, baseBulkBandGuardTA, gBulk1, gRZero1, gKind1, qza0, qza1, dX1,
    distAtBoundIdx, dm1TA, bulkCountTA, bulkGuardTA, baseKindGuardTA, orEqSucc, band3,
    SFormula.eval, SC.closed, SC.b, SC.n, STerm.eval, SFormula.witnessLt, Term.eval, Term.lift,
    bind, Option.bind]
  set k := rho ⟨0, by decide⟩ with hk
  set d := D.distance with hdd
  have hdpos : 0 < d := by omega
  have hdge : 3 ≤ d := by omega
  by_cases hbulk : k < (d - 1) * (d - 1)
  · simp only [hbulk, decide_true, if_true]
    by_cases hr : k / (d - 1) = 0
    · simp only [hr, decide_true, if_true]
      by_cases hkind : (0 + k % (d - 1)) % 2 = 0
      · -- kind TRUE → `gKind1 D false` antecedent false → vacuous.
        have hkv : decide (decide ((0 + k % (d - 1)) % 2 = 0) = false) = false := by
          rw [decide_eq_false_iff_not]; simp only [decide_eq_false_iff_not]; omega
        simp only [hkv, Bool.false_eq_true, if_false, reduceIte]
      · -- kind FALSE (c odd): the genuine class-(a) case.
        have hkd : decide (decide ((0 + k % (d - 1)) % 2 = 0) = false) = true := by
          rw [decide_eq_true_eq, decide_eq_false_iff_not]; omega
        simp only [hkd, if_true]
        -- c = k % (d-1) < d-1, so c+1 ≤ d-1 < d; q0 = c, q1 = c+1 are row-0 qubits.
        set c := k % (d - 1) with hc
        have hclt : c < d - 1 := Nat.mod_lt _ (by omega)
        have hc0div : c / d = 0 := Nat.div_eq_of_lt (by omega)
        have hc0mod : c % d = c := Nat.mod_eq_of_lt (by omega)
        have hc1div : (c + 1) / d = 0 := Nat.div_eq_of_lt (by omega)
        have hc1mod : (c + 1) % d = c + 1 := Nat.mod_eq_of_lt (by omega)
        have hb0 : c < nQubits d := by
          have hh : c < d := by omega
          simp only [nQubits]; calc c < d := hh
            _ ≤ d * d := Nat.le_mul_of_pos_left d hdpos
        have hb1 : c + 1 < nQubits d := by
          have hh : c + 1 < d := by omega
          simp only [nQubits]; calc c + 1 < d := hh
            _ ≤ d * d := Nat.le_mul_of_pos_left d hdpos
        -- decide the band conjuncts at q0 = c (q/d=0) and q1 = c+1 (q/d=0), r = 0.
        have hd00 : decide (c / d = 0) = true := by rw [hc0div]; simp
        have hd01 : decide (c % d = c) = true := by rw [hc0mod]; simp
        have hd10a : decide ((c + 1) / d = 0) = true := by rw [hc1div]; simp
        have hd11a : decide ((c + 1) % d = c) = false := by
          rw [hc1mod]; rw [decide_eq_false_iff_not]; omega
        have hd11b : decide ((c + 1) % d = c + 1) = true := by rw [hc1mod]; simp
        have hbne : decide (c = c + 1) = false := by rw [decide_eq_false_iff_not]; omega
        have hbb0 : decide (c < nQubits d) = true := by rw [decide_eq_true_eq]; exact hb0
        have hbb1 : decide (c + 1 < nQubits d) = true := by rw [decide_eq_true_eq]; exact hb1
        simp only [hd00, hd01, hd10a, hd11a, hd11b, hbne, hbb0, hbb1, hbulk,
          decide_true, decide_false, Bool.false_eq_true, if_true, if_false, reduceIte]
    · -- r ≠ 0 → `gRZero1 D true` antecedent false → vacuous.
      have hrv : decide (k / (d - 1) = 0) = false := by rw [decide_eq_false_iff_not]; exact hr
      simp only [hrv, decide_false, Bool.false_eq_true, if_false, reduceIte]
  · -- bulk false → `gBulk1 D true` antecedent false → vacuous.
    simp only [hbulk, decide_false, Bool.false_eq_true, if_false, reduceIte]

/-- Arity-2 forms of the class-(a) [Z] anti qubits (`k = var 1`). -/
abbrev qza0_2 (D : OddSurfaceDistance) : Term 2 .nat := .mod kX2 (dm1TA (dX2 D))
abbrev qza1_2 (D : OddSurfaceDistance) : Term 2 .nat := .add (.mod kX2 (dm1TA (dX2 D))) (.natLit 1)
theorem qza0_weaken (D : OddSurfaceDistance) : (qza0 D).weaken = qza0_2 D := rfl
theorem qza1_weaken (D : OddSurfaceDistance) : (qza1 D).weaken = qza1_2 D := rfl

/-- Row guards at the two class-(a) anti qubits: `q0 / d = 0` and `q1 / d = 0`
(both are `< d` since `c = k%(d-1) < d-1`).  Closed in `k`, discharged by
`arithBool`. -/
abbrev qzaRowGuardF (D : OddSurfaceDistance) : SFormula 1 :=
  .and (rowGuardPure1 D (qza0 D)) (rowGuardPure1 D (qza1 D))

def qzaRowGuardPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (qzaRowGuardF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [rowGuardPure1, qza0, qza1, dX1, distAtBoundIdx, dm1TA, SFormula.eval, SC.closed,
    SC.b, STerm.eval, Term.eval, Term.lift, bind, Option.bind]
  set k := rho ⟨0, by decide⟩ with hk
  set d := D.distance with hdd
  have hdpos : 0 < d := by omega
  have hclt : k % (d - 1) < d - 1 := Nat.mod_lt _ (by omega)
  have h0 : k % (d - 1) / d = 0 := Nat.div_eq_of_lt (by omega)
  have h1 : (k % (d - 1) + 1) / d = 0 := Nat.div_eq_of_lt (by omega)
  rw [h0, h1]
  simp

/-- The bulk-`X` all-others pin for class (a) [Z]: on row 0, if the bulk band fires
(with `r = 0`), then `boundNat ∈ {q0, q1}`.  Quantified over `q < nQubits`. -/
abbrev classZABulkXPinBody (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (rowGuardRaw2 D)
    (.imp (.eqBool (SC.closed (baseBulkBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.b true))
      (.imp (gRZero2 D true)
        (.or (.eqNat SFormula.boundNat (SC.closed (qza0_2 D)))
          (.eqNat SFormula.boundNat (SC.closed (qza1_2 D))))))

abbrev classZABulkXPinF (D : OddSurfaceDistance) : SFormula 1 :=
  .allNatLt (nQ1 D) (classZABulkXPinBody D)

def classZABulkXPinPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (classZABulkXPinF D) := by
  refine PureFamilyDerivA.allNatLtIntro _ ?_
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [classZABulkXPinBody, rowGuardRaw2, baseBulkBandGuardTA, gRZero2, qza0_2, qza1_2, dX2,
    distAtBoundIdx2, kX2, dm1TA, orEqSucc, band3, bulkCountTA, SFormula.eval, SC.closed, SC.b,
    STerm.eval, SFormula.boundNat, Term.eval, Term.lift, bind, Option.bind]
  set q := rho ⟨0, by decide⟩ with hq'
  set k := rho ⟨1, by decide⟩ with hk'
  set d := D.distance with hdd
  have hdpos : 0 < d := by omega
  by_cases hq : q / d = 0
  · simp only [hq, decide_true, if_true]
    by_cases hrz : k / (d - 1) = 0
    · -- r = 0; whenever the band fires (col matches), q is `c` or `c+1`.
      simp only [hrz, decide_true, if_true]
      -- on row 0 (q/d=0=r), band fires iff q%d ∈ {c, c+1}; and q = q%d since q < d.
      have hqd : q % d = q := Nat.mod_eq_of_lt (Nat.lt_of_div_eq_zero hdpos hq)
      by_cases hcol0 : q % d = k % (d - 1)
      · -- q%d = c → q = c = q0
        have hqe : decide (q = k % (d - 1)) = true := by rw [decide_eq_true_eq, ← hqd]; exact hcol0
        have hc0 : decide (q % d = k % (d - 1)) = true := by rw [decide_eq_true_eq]; exact hcol0
        simp only [hc0, hqe, decide_true, if_true]
        by_cases hbk : decide (k < (d-1)*(d-1)) = true <;> simp [hbk]
      · by_cases hcol1 : q % d = k % (d - 1) + 1
        · -- q%d = c+1 → q = c+1 = q1
          have hqe : decide (q = k % (d - 1) + 1) = true := by rw [decide_eq_true_eq, ← hqd]; exact hcol1
          have hc0 : decide (q % d = k % (d - 1)) = false := by rw [decide_eq_false_iff_not]; exact hcol0
          have hc1 : decide (q % d = k % (d - 1) + 1) = true := by rw [decide_eq_true_eq]; exact hcol1
          have hq0 : decide (q = k % (d - 1)) = false := by
            rw [decide_eq_false_iff_not, ← hqd]; exact hcol0
          simp only [hc0, hc1, hq0, hqe, decide_true, decide_false, Bool.false_eq_true,
            if_true, if_false, reduceIte]
          by_cases hbk : decide (k < (d-1)*(d-1)) = true <;> simp [hbk]
        · -- neither: band false, antecedent vacuous
          have hc0 : decide (q % d = k % (d - 1)) = false := by rw [decide_eq_false_iff_not]; exact hcol0
          have hc1 : decide (q % d = k % (d - 1) + 1) = false := by rw [decide_eq_false_iff_not]; exact hcol1
          simp only [hc0, hc1, decide_false, Bool.false_eq_true, if_false, reduceIte]
    · -- r ≠ 0: on row 0 (q/d=0) the band disjuncts `0 = r`, `0 = r+1` are both
      -- false, so the band is false and the conclusion is vacuous.
      have hrz' : decide (decide (k / (d - 1) = 0) = true) = false := by
        rw [decide_eq_false_iff_not]; simp [hrz]
      have hb0 : decide (0 = k / (d - 1)) = false := by
        rw [decide_eq_false_iff_not]; exact fun h => hrz h.symm
      have hb1 : decide (0 = k / (d - 1) + 1) = false := by
        rw [decide_eq_false_iff_not]; exact fun h => Nat.succ_ne_zero _ h.symm
      simp only [hrz, hrz', hb0, hb1, decide_false, Bool.false_eq_true, if_false, reduceIte]
  · simp only [hq, decide_false, Bool.false_eq_true, if_false, reduceIte]

/-! ### Class-(a) [Z] two-anti per-`k` commutation -/

/-- Entry-at-`q` resolves to `X` (bulk, band-at-q, kind FALSE), given the class-(a)
[Z] guard pack extracted at `q`.  Mirror of `antiZAtA` (bulk-`X` leaf). -/
def antiXAtA (D : OddSurfaceDistance) {Γ : List (SFormula 1)} (qT : Term 1 .nat)
    (hEntry : SFormula.Deriv Γ
      (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed qT))
        (SC.closed (baseLeafTreeTA (dX1 D) kX1 qT))))
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dX1 D) kX1)) (SC.b true)))
    (hBand : SFormula.Deriv Γ (.eqBool (SC.closed (baseBulkBandGuardTA (dX1 D) kX1 qT)) (SC.b true)))
    (hKind : SFormula.Deriv Γ (.eqBool (SC.closed (baseKindGuardTA (dX1 D) kX1)) (SC.b false))) :
    SFormula.Deriv Γ (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed qT)) (SC.p Pauli.X)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ hEntry (baseLeafBulkX _ _ _ hBulk hBand hKind)

/-- Extract the class-(a) [Z] bulk-`X` pin disjunction at `boundNat`. -/
def classZABulkXPinAt {Δ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hW : SFormula.Deriv Δ (classZABulkXPinF D).weaken)
    (hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nQ1 D).weaken))
    (hrow : SFormula.Deriv Δ (rowGuardRaw2 D))
    (hband : SFormula.Deriv Δ (.eqBool (SC.closed (baseBulkBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.b true)))
    (hrz : SFormula.Deriv Δ (gRZero2 D true)) :
    SFormula.Deriv Δ
      (.or (.eqNat SFormula.boundNat (SC.closed (qza0_2 D)))
        (.eqNat SFormula.boundNat (SC.closed (qza1_2 D)))) := by
  have hElim := SFormula.Deriv.allNatLtElim (nQ1 D).weaken
    ((classZABulkXPinBody D).lift 1) SFormula.boundNat hW hq
  have hBody := SFormula.Deriv.applyNatBoundNatBeta (classZABulkXPinBody D) hElim
  exact SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp hBody hrow) hband) hrz

/-- **Class-(a) [Z] two-anti per-`k` commutation.**  Given bulk true, `r = 0`, kind
false, and the supporting packs in `Γ`, the row commutes with `logicalZ` by the
even-parity rule: it anticommutes at exactly `q0 = c` and `q1 = c+1`, and commutes
elsewhere.  Transpose of `commTwoAntiA`. -/
def commZTwoAntiA {Γ : List (SFormula 1)} (D : OddSurfaceDistance)
    (hBulk : SFormula.Deriv Γ (gBulk1 D true))
    (hRZ : SFormula.Deriv Γ (gRZero1 D true))
    (hKind : SFormula.Deriv Γ (gKind1 D false))
    (hClassA : SFormula.Deriv Γ (classZAPackF D))
    (hRow : SFormula.Deriv Γ (qzaRowGuardF D))
    (hPin : SFormula.Deriv Γ (classZABulkXPinF D))
    (hEntryF : SFormula.Deriv Γ (entryFlatF1 D))
    (hBBFF : SFormula.Deriv Γ (bottomBandFalseF D))
    (hEntry0 : SFormula.Deriv Γ
      (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed (qza0 D)))
        (SC.closed (baseLeafTreeTA (dX1 D) kX1 (qza0 D)))))
    (hEntry1 : SFormula.Deriv Γ
      (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed (qza1 D)))
        (SC.closed (baseLeafTreeTA (dX1 D) kX1 (qza1 D))))) :
    SFormula.Deriv Γ (commGoalZ1 D) := by
  have hPack := SFormula.Deriv.mp (SFormula.Deriv.mp (SFormula.Deriv.mp hClassA hBulk) hRZ) hKind
  have hBand0 := SFormula.Deriv.andElimLeft hPack
  have hBand1 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hPack)
  have hNe := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hPack))
  have hLt0 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hPack)))
  have hLt1 := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hPack)))
  -- Entry = X at q0, q1.
  have hX0 := antiXAtA D (qza0 D) hEntry0 hBulk hBand0 hKind
  have hX1 := antiXAtA D (qza1 D) hEntry1 hBulk hBand1 hKind
  -- logicalZ = Z at q0, q1.
  have hZ0 := lzPureEntryZ D (qza0 D) (qza0_pure D) (SFormula.Deriv.andElimLeft hRow)
  have hZ1 := lzPureEntryZ D (qza1 D) (qza1_pure D) (SFormula.Deriv.andElimRight hRow)
  refine SFormula.Deriv.commutesOfTwoAnti _ _ _ (SC.closed (qza0 D)) (SC.closed (qza1 D))
    ?wlt0 ?wlt1 ?wne ?wanti0 ?wanti1 ?wrest
  case wlt0 => exact hLt0
  case wlt1 => exact hLt1
  case wne =>
    refine SFormula.Deriv.notIntro ?_
    refine SFormula.Deriv.notElim
      (SFormula.Deriv.eqNatBoolTrue (Γ := _) (qza0 D) (qza1 D) .assumption) ?_
    exact SFormula.Deriv.eqBoolFalseNotTrue _ (cw1 hNe)
  case wanti0 =>
    exact SFormula.Deriv.anticommutesTransport _ (SC.p Pauli.X) _ (SC.p Pauli.Z) (SC.b true)
      hX0 hZ0 (SFormula.Deriv.pauliAnticommutesLit Pauli.X Pauli.Z)
  case wanti1 =>
    exact SFormula.Deriv.anticommutesTransport _ (SC.p Pauli.X) _ (SC.p Pauli.Z) (SC.b true)
      hX1 hZ1 (SFormula.Deriv.pauliAnticommutesLit Pauli.X Pauli.Z)
  case wrest =>
    refine SFormula.Deriv.allNatLtIntroBounded _ _ ?_
    refine SFormula.Deriv.impIntro (SFormula.Deriv.impIntro ?_)
    refine SFormula.Deriv.boolCases (logicalZRowGuardAt2 D) _ ?_ ?_
    · set ΔT : List (SFormula 2) := .eqBool (logicalZRowGuardAt2 D) (SC.b true)
        :: .not (.eqNat SFormula.boundNat (SC.closed (qza1 D)).weaken)
        :: .not (.eqNat SFormula.boundNat (SC.closed (qza0 D)).weaken)
        :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ with hΔT
      have hEntryW : SFormula.Deriv ΔT (entryFlatF1 D).weaken :=
        cw4 (SFormula.Deriv.weakenFresh (A := entryFlatF1 D) hEntryF)
      have hBBFW : SFormula.Deriv ΔT (bottomBandFalseF D).weaken :=
        cw4 (SFormula.Deriv.weakenFresh (A := bottomBandFalseF D) hBBFF)
      have hq : SFormula.Deriv ΔT (SFormula.witnessLt SFormula.boundNat (nQ1 D).weaken) :=
        SFormula.Deriv.hyp (by rw [hΔT]; right; right; right; exact List.mem_cons_self)
      have hrowT : SFormula.Deriv ΔT (.eqBool (logicalZRowGuardAt2 D) (SC.b true)) := by
        rw [hΔT]; exact .assumption
      have hrowRaw : SFormula.Deriv ΔT (rowGuardRaw2 D) := by rw [← rowGuard2_eq]; exact hrowT
      have hEntry := entryAtBound D hEntryW hq
      have hBBF := bbfAtBound D hBBFW hq hrowRaw
      refine rowDispatchOnTrue D hEntry hrowT hBBF ?hXbulk ?hXtop
      case hXbulk =>
        intro Δ' lift _ hrowΔ hBulkΔ hBandΔ _
        -- bulk-X: use the pin (row ∧ band ∧ r=0) → q=q0 ∨ q=q1, contradicting exclusions.
        have hrowRaw' : SFormula.Deriv Δ' (rowGuardRaw2 D) := by rw [← rowGuard2_eq]; exact hrowΔ
        have hrzΔ0 : SFormula.Deriv ΔT (gRZero2 D true) :=
          cw4 (SFormula.Deriv.weakenFresh (A := gRZero1 D true) hRZ)
        have hPinW0 : SFormula.Deriv ΔT (classZABulkXPinF D).weaken :=
          cw4 (SFormula.Deriv.weakenFresh (A := classZABulkXPinF D) hPin)
        have hdisj := classZABulkXPinAt D (lift hPinW0) (lift hq) hrowRaw' hBandΔ (lift hrzΔ0)
        have hne0 : SFormula.Deriv ΔT (.not (.eqNat SFormula.boundNat (SC.closed (qza0 D)).weaken)) := by
          rw [hΔT]; exact .hyp (by right; right; exact List.mem_cons_self)
        have hne1 : SFormula.Deriv ΔT (.not (.eqNat SFormula.boundNat (SC.closed (qza1 D)).weaken)) := by
          rw [hΔT]; exact .hyp (by right; exact List.mem_cons_self)
        refine SFormula.Deriv.orElim hdisj ?_ ?_
        · exact SFormula.Deriv.botElim (SFormula.Deriv.notElim (.assumption) (cw1 (lift hne0)))
        · exact SFormula.Deriv.botElim (SFormula.Deriv.notElim (.assumption) (cw1 (lift hne1)))
      case hXtop =>
        intro Δ' lift _ _ hBulkFalseΔ _ _
        -- top-X: class (a) has bulk TRUE, contradicting cascade bulk FALSE.
        have hBulkTrue0 : SFormula.Deriv ΔT (gBulk D true) :=
          cw4 (SFormula.Deriv.weakenFresh (A := gBulk1 D true) hBulk)
        exact eqBoolContra _ (lift hBulkTrue0) hBulkFalseΔ
    · exact logicalZOffRowLocalCommutes D (rowK2 D) .assumption

/-! ## Two-anti class (b) [Z]: top-`X` boundary stabilizers

`¬(k < (d-1)²)`, top-`X` band `b < half` (`b = k - (d-1)²`, `half = (d-1)/2`).
Anti qubits `q0 = 2b`, `q1 = 2b+1` on ROW 0. -/

/-- `q0 = 2·b` at arity 1 (first class-(b) anti qubit), `b = baseBTA`. -/
abbrev qzb0 (D : OddSurfaceDistance) : Term 1 .nat := .mul (.natLit 2) (baseBTA (dX1 D) kX1)
/-- `q1 = 2·b + 1` at arity 1. -/
abbrev qzb1 (D : OddSurfaceDistance) : Term 1 .nat :=
  .add (.mul (.natLit 2) (baseBTA (dX1 D) kX1)) (.natLit 1)

def baseB1_pure (D : OddSurfaceDistance) : SFormula.PureNatTerm (baseBTA (dX1 D) kX1) :=
  SFormula.PureNatTerm.sub (SFormula.PureNatTerm.var _)
    (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.sub (dX1_pure D) (SFormula.PureNatTerm.natLit _))
      (SFormula.PureNatTerm.sub (dX1_pure D) (SFormula.PureNatTerm.natLit _)))
def qzb0_pure (D : OddSurfaceDistance) : SFormula.PureNatTerm (qzb0 D) :=
  SFormula.PureNatTerm.mul (SFormula.PureNatTerm.natLit _) (baseB1_pure D)
def qzb1_pure (D : OddSurfaceDistance) : SFormula.PureNatTerm (qzb1 D) :=
  SFormula.PureNatTerm.add (SFormula.PureNatTerm.mul (SFormula.PureNatTerm.natLit _) (baseB1_pure D))
    (SFormula.PureNatTerm.natLit _)

/-- Arity-2 forms of the class-(b) [Z] anti qubits (`k = var 1`). -/
abbrev qzb0_2 (D : OddSurfaceDistance) : Term 2 .nat := .mul (.natLit 2) (baseBTA (dX2 D) kX2)
abbrev qzb1_2 (D : OddSurfaceDistance) : Term 2 .nat :=
  .add (.mul (.natLit 2) (baseBTA (dX2 D) kX2)) (.natLit 1)
theorem qzb0_weaken (D : OddSurfaceDistance) : (qzb0 D).weaken = qzb0_2 D := rfl
theorem qzb1_weaken (D : OddSurfaceDistance) : (qzb1 D).weaken = qzb1_2 D := rfl

/-- Class-(b) [Z] guard pack: given `¬bulk`, `topClass` (so `b < half`), the top-`X`
band fires at `q0 = 2b`/`q1 = 2b+1`, `q0 ≠ q1`, and both `< nQubits`. -/
abbrev classZBPackF (D : OddSurfaceDistance) : SFormula 1 :=
  .imp (gBulk1 D false) (.imp (gTopC1 D true)
    (.and (.eqBool (SC.closed (topBandGuardTA (dX1 D) kX1 (qzb0 D))) (SC.b true))
      (.and (.eqBool (SC.closed (topBandGuardTA (dX1 D) kX1 (qzb1 D))) (SC.b true))
        (.and (.eqBool (SC.closed (.eqNat (qzb0 D) (qzb1 D))) (SC.b false))
          (.and (SFormula.witnessLt (SC.closed (qzb0 D)) (SC.n (arity := 1) (nQubits D.distance)))
            (SFormula.witnessLt (SC.closed (qzb1 D)) (SC.n (arity := 1) (nQubits D.distance))))))))

def classZBPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (classZBPackF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [classZBPackF, topBandGuardTA, gBulk1, gTopC1, bulkGuardTA, topClassGuardTA, baseBTA,
    baseHalfTA, bulkCountTA, qzb0, qzb1, dX1, distAtBoundIdx, dm1TA, orEqSucc, band3,
    SFormula.eval, SC.closed, SC.b, SC.n, STerm.eval, SFormula.witnessLt, Term.eval, Term.lift,
    bind, Option.bind]
  set k := rho ⟨0, by decide⟩ with hk
  set d := D.distance with hdd
  have hdpos : 0 < d := by omega
  have hdge : 3 ≤ d := by omega
  by_cases hbulk : k < (d - 1) * (d - 1)
  · -- bulk true → `gBulk1 D false` antecedent false → vacuous.
    have hbv : decide (decide (k < (d - 1) * (d - 1)) = false) = false := by
      rw [decide_eq_false_iff_not]; simp [hbulk]
    simp only [hbv, Bool.false_eq_true, if_false, reduceIte]
  · by_cases htc : k - (d - 1) * (d - 1) < (d - 1) / 2
    · -- the genuine class-(b) case.
      have hbv : decide (decide (k < (d - 1) * (d - 1)) = false) = true := by
        rw [decide_eq_true_eq]; simp [hbulk]
      have htcd : decide (decide (k - (d - 1) * (d - 1) < (d - 1) / 2) = true) = true := by
        rw [decide_eq_true_eq]; simp [htc]
      simp only [hbv, htcd, if_true]
      set b := k - (d - 1) * (d - 1) with hb
      -- 2b < d-1, 2b+1 ≤ d-1 < d; q0 = 2b, q1 = 2b+1 row-0 qubits.
      have hhalf : (d - 1) / 2 ≤ (d - 1) := Nat.div_le_self _ _
      have hblt : b < (d - 1) / 2 := htc
      have h2blt : 2 * b < d - 1 := by omega
      have hq0div : 2 * b / d = 0 := Nat.div_eq_of_lt (by omega)
      have hq0mod : 2 * b % d = 2 * b := Nat.mod_eq_of_lt (by omega)
      have hq1div : (2 * b + 1) / d = 0 := Nat.div_eq_of_lt (by omega)
      have hq1mod : (2 * b + 1) % d = 2 * b + 1 := Nat.mod_eq_of_lt (by omega)
      have hk2 : (d - 1) * (d - 1) ≤ k := by omega
      have hkd2 : k < d * d - 1 := by
        have hbnd : k < (d-1)*(d-1) + (d-1)/2 := by omega
        -- (d-1)*(d-1) ≤ d*d - d  since (d-1)*(d-1) ≤ (d-1)*d = d*d - d.
        have hle : (d - 1) * (d - 1) ≤ (d - 1) * d := Nat.mul_le_mul_left (d-1) (by omega)
        have hdd2 : (d - 1) * d = d * d - d := by rw [Nat.sub_mul]; omega
        have hab : (d - 1) * (d - 1) ≤ d * d - d := by rw [← hdd2]; exact hle
        have hdf : d ≤ d * d := Nat.le_mul_of_pos_left d hdpos
        omega
      have hb0 : 2 * b < nQubits d := by
        simp only [nQubits]; have hlt : 2 * b < d := by omega
        calc 2 * b < d := hlt
          _ ≤ d * d := Nat.le_mul_of_pos_left d hdpos
      have hb1 : 2 * b + 1 < nQubits d := by
        simp only [nQubits]; have hlt : 2 * b + 1 < d := by omega
        calc 2 * b + 1 < d := hlt
          _ ≤ d * d := Nat.le_mul_of_pos_left d hdpos
      -- decide the band conjuncts: k < d²-1, q/d=0, q%d ∈ {2b, 2b+1}.
      have hkd : decide (k < d * d - 1) = true := by rw [decide_eq_true_eq]; exact hkd2
      have hq0d0 : decide (2 * b / d = 0) = true := by rw [hq0div]; simp
      have hq0m : decide (2 * b % d = 2 * b) = true := by rw [hq0mod]; simp
      have hq1d0 : decide ((2 * b + 1) / d = 0) = true := by rw [hq1div]; simp
      have hq1ma : decide ((2 * b + 1) % d = 2 * b) = false := by
        rw [hq1mod]; rw [decide_eq_false_iff_not]; omega
      have hq1mb : decide ((2 * b + 1) % d = 2 * b + 1) = true := by rw [hq1mod]; simp
      have hbne : decide (2 * b = 2 * b + 1) = false := by rw [decide_eq_false_iff_not]; omega
      have hbb0 : decide (2 * b < nQubits d) = true := by rw [decide_eq_true_eq]; exact hb0
      have hbb1 : decide (2 * b + 1 < nQubits d) = true := by rw [decide_eq_true_eq]; exact hb1
      simp only [hkd, hq0d0, hq0m, hq1d0, hq1ma, hq1mb, hbne, hbb0, hbb1,
        decide_true, decide_false, Bool.false_eq_true, if_true, if_false, reduceIte]
    · -- topClass false → `gTopC1 D true` antecedent false → vacuous.
      have hbv : decide (decide (k < (d - 1) * (d - 1)) = false) = true := by
        rw [decide_eq_true_eq]; simp [hbulk]
      have htcd : decide (decide (k - (d - 1) * (d - 1) < (d - 1) / 2) = true) = false := by
        rw [decide_eq_false_iff_not]; simp [htc]
      simp only [hbv, htcd, Bool.false_eq_true, if_false, if_true, reduceIte]

/-- Row guards at the class-(b) [Z] anti qubits (`q0, q1 < d` since `2b+1 ≤ d-1`).
Conditional on the class condition.  Discharged by `arithBool`. -/
abbrev qzbRowGuardF (D : OddSurfaceDistance) : SFormula 1 :=
  .imp (gBulk1 D false) (.imp (gTopC1 D true)
    (.and (rowGuardPure1 D (qzb0 D)) (rowGuardPure1 D (qzb1 D))))

def qzbRowGuardPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (qzbRowGuardF D) := by
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [qzbRowGuardF, rowGuardPure1, gBulk1, gTopC1, bulkGuardTA, topClassGuardTA, baseBTA,
    baseHalfTA, bulkCountTA, qzb0, qzb1, dX1, distAtBoundIdx, dm1TA, SFormula.eval, SC.closed,
    SC.b, STerm.eval, Term.eval, Term.lift, bind, Option.bind]
  set k := rho ⟨0, by decide⟩ with hk
  set d := D.distance with hdd
  have hdpos : 0 < d := by omega
  have hdge : 3 ≤ d := by omega
  by_cases hbulk : k < (d - 1) * (d - 1)
  · have hbv : decide (decide (k < (d - 1) * (d - 1)) = false) = false := by
      rw [decide_eq_false_iff_not]; simp [hbulk]
    simp only [hbv, Bool.false_eq_true, if_false, reduceIte]
  · by_cases htc : k - (d - 1) * (d - 1) < (d - 1) / 2
    · have hbv : decide (decide (k < (d - 1) * (d - 1)) = false) = true := by
        rw [decide_eq_true_eq]; simp [hbulk]
      have htcd : decide (decide (k - (d - 1) * (d - 1) < (d - 1) / 2) = true) = true := by
        rw [decide_eq_true_eq]; simp [htc]
      simp only [hbv, htcd, if_true]
      set b := k - (d - 1) * (d - 1) with hb
      have hhalf : (d - 1) / 2 ≤ (d - 1) := Nat.div_le_self _ _
      have hblt : b < (d - 1) / 2 := htc
      have h2blt : 2 * b < d - 1 := by omega
      have hq0div : 2 * b / d = 0 := Nat.div_eq_of_lt (by omega)
      have hq1div : (2 * b + 1) / d = 0 := Nat.div_eq_of_lt (by omega)
      rw [hq0div, hq1div]; simp
    · have hbv : decide (decide (k < (d - 1) * (d - 1)) = false) = true := by
        rw [decide_eq_true_eq]; simp [hbulk]
      have htcd : decide (decide (k - (d - 1) * (d - 1) < (d - 1) / 2) = true) = false := by
        rw [decide_eq_false_iff_not]; simp [htc]
      simp only [hbv, htcd, Bool.false_eq_true, if_false, if_true, reduceIte]

/-- The top-`X` all-others pin for class (b) [Z]: on row 0, if the top band fires,
then `boundNat ∈ {q0, q1}`.  Mirror of `classBLeftZPinPack`. -/
abbrev classZBTopXPinBody (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (rowGuardRaw2 D)
    (.imp (.eqBool (SC.closed (topBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.b true))
      (.or (.eqNat SFormula.boundNat (SC.closed (qzb0_2 D)))
        (.eqNat SFormula.boundNat (SC.closed (qzb1_2 D)))))

abbrev classZBTopXPinF (D : OddSurfaceDistance) : SFormula 1 :=
  .allNatLt (nQ1 D) (classZBTopXPinBody D)

def classZBTopXPinPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (classZBTopXPinF D) := by
  refine PureFamilyDerivA.allNatLtIntro _ ?_
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [classZBTopXPinBody, rowGuardRaw2, topBandGuardTA, qzb0_2, qzb1_2, baseBTA,
    bulkCountTA, dX2, distAtBoundIdx2, kX2, dm1TA, orEqSucc, band3, SFormula.eval, SC.closed,
    SC.b, STerm.eval, SFormula.boundNat, Term.eval, Term.lift, bind, Option.bind]
  set q := rho ⟨0, by decide⟩ with hq'
  set k := rho ⟨1, by decide⟩ with hk'
  set d := D.distance with hdd
  have hdpos : 0 < d := by omega
  set b := k - (d - 1) * (d - 1) with hb
  by_cases hq : q / d = 0
  · simp only [hq, decide_true, if_true]
    have hqd : q % d = q := Nat.mod_eq_of_lt (Nat.lt_of_div_eq_zero hdpos hq)
    by_cases hkd : k < d * d - 1
    · -- top band's k-bound holds; fires iff q%d ∈ {2b, 2b+1}.
      have hkdd : decide (k < d * d - 1) = true := by rw [decide_eq_true_eq]; exact hkd
      simp only [hkdd, decide_true, if_true]
      by_cases hcol0 : q % d = 2 * b
      · have hqe : decide (q = 2 * b) = true := by rw [decide_eq_true_eq, ← hqd]; exact hcol0
        have hc0 : decide (q % d = 2 * b) = true := by rw [decide_eq_true_eq]; exact hcol0
        simp only [hc0, hqe, decide_true, if_true]
      · by_cases hcol1 : q % d = 2 * b + 1
        · have hqe : decide (q = 2 * b + 1) = true := by rw [decide_eq_true_eq, ← hqd]; exact hcol1
          have hc0 : decide (q % d = 2 * b) = false := by rw [decide_eq_false_iff_not]; exact hcol0
          have hc1 : decide (q % d = 2 * b + 1) = true := by rw [decide_eq_true_eq]; exact hcol1
          have hq0 : decide (q = 2 * b) = false := by rw [decide_eq_false_iff_not, ← hqd]; exact hcol0
          simp only [hc0, hc1, hq0, hqe, decide_true, decide_false, Bool.false_eq_true,
            if_true, if_false, reduceIte]
        · have hc0 : decide (q % d = 2 * b) = false := by rw [decide_eq_false_iff_not]; exact hcol0
          have hc1 : decide (q % d = 2 * b + 1) = false := by rw [decide_eq_false_iff_not]; exact hcol1
          simp only [hc0, hc1, decide_false, Bool.false_eq_true, if_false, reduceIte]
    · -- k ≥ d²-1: top band's first conjunct false → band false → vacuous.
      have hkdd : decide (k < d * d - 1) = false := by rw [decide_eq_false_iff_not]; exact hkd
      simp only [hkdd, decide_false, Bool.false_eq_true, if_false, reduceIte]
  · simp only [hq, decide_false, Bool.false_eq_true, if_false, reduceIte]

/-! ### Class-(b) [Z] two-anti per-`k` commutation -/

/-- Entry-at-`q` resolves to `X` via the top-`X` boundary leaf.  Mirror of
`antiZAtB` (top-`X` leaf). -/
def antiXAtB (D : OddSurfaceDistance) {Γ : List (SFormula 1)} (qT : Term 1 .nat)
    (hEntry : SFormula.Deriv Γ
      (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed qT))
        (SC.closed (baseLeafTreeTA (dX1 D) kX1 qT))))
    (hBulk : SFormula.Deriv Γ (.eqBool (SC.closed (bulkGuardTA (dX1 D) kX1)) (SC.b false)))
    (hTopC : SFormula.Deriv Γ (.eqBool (SC.closed (topClassGuardTA (dX1 D) kX1)) (SC.b true)))
    (hTopB : SFormula.Deriv Γ (.eqBool (SC.closed (topBandGuardTA (dX1 D) kX1 qT)) (SC.b true))) :
    SFormula.Deriv Γ (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed qT)) (SC.p Pauli.X)) :=
  SFormula.Deriv.eqPauliTrans _ _ _ hEntry (baseLeafTopX _ _ _ hBulk hTopC hTopB)

/-- Extract the class-(b) [Z] top-`X` pin disjunction at `boundNat`. -/
def classZBTopXPinAt {Δ : List (SFormula 2)} (D : OddSurfaceDistance)
    (hW : SFormula.Deriv Δ (classZBTopXPinF D).weaken)
    (hq : SFormula.Deriv Δ (SFormula.witnessLt SFormula.boundNat (nQ1 D).weaken))
    (hrow : SFormula.Deriv Δ (rowGuardRaw2 D))
    (hband : SFormula.Deriv Δ (.eqBool (SC.closed (topBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.b true))) :
    SFormula.Deriv Δ
      (.or (.eqNat SFormula.boundNat (SC.closed (qzb0_2 D)))
        (.eqNat SFormula.boundNat (SC.closed (qzb1_2 D)))) := by
  have hElim := SFormula.Deriv.allNatLtElim (nQ1 D).weaken
    ((classZBTopXPinBody D).lift 1) SFormula.boundNat hW hq
  have hBody := SFormula.Deriv.applyNatBoundNatBeta (classZBTopXPinBody D) hElim
  exact SFormula.Deriv.mp (SFormula.Deriv.mp hBody hrow) hband

/-- **Class-(b) [Z] two-anti per-`k` commutation.**  Transpose of `commTwoAntiB`. -/
def commZTwoAntiB {Γ : List (SFormula 1)} (D : OddSurfaceDistance)
    (hBulk : SFormula.Deriv Γ (gBulk1 D false))
    (hTopC : SFormula.Deriv Γ (gTopC1 D true))
    (hClassB : SFormula.Deriv Γ (classZBPackF D))
    (hRow : SFormula.Deriv Γ (qzbRowGuardF D))
    (hPin : SFormula.Deriv Γ (classZBTopXPinF D))
    (hEntryF : SFormula.Deriv Γ (entryFlatF1 D))
    (hBBFF : SFormula.Deriv Γ (bottomBandFalseF D))
    (hEntry0 : SFormula.Deriv Γ
      (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed (qzb0 D)))
        (SC.closed (baseLeafTreeTA (dX1 D) kX1 (qzb0 D)))))
    (hEntry1 : SFormula.Deriv Γ
      (.eqPauli (.stabAt (SC.closed (.recCall (dX1 D) kX1)) (SC.closed (qzb1 D)))
        (SC.closed (baseLeafTreeTA (dX1 D) kX1 (qzb1 D))))) :
    SFormula.Deriv Γ (commGoalZ1 D) := by
  have hPack := SFormula.Deriv.mp (SFormula.Deriv.mp hClassB hBulk) hTopC
  have hBand0 := SFormula.Deriv.andElimLeft hPack
  have hBand1 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight hPack)
  have hNe := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hPack))
  have hLt0 := SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hPack)))
  have hLt1 := SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight hPack)))
  have hRowPack := SFormula.Deriv.mp (SFormula.Deriv.mp hRow hBulk) hTopC
  have hX0 := antiXAtB D (qzb0 D) hEntry0 hBulk hTopC hBand0
  have hX1 := antiXAtB D (qzb1 D) hEntry1 hBulk hTopC hBand1
  have hZ0 := lzPureEntryZ D (qzb0 D) (qzb0_pure D) (SFormula.Deriv.andElimLeft hRowPack)
  have hZ1 := lzPureEntryZ D (qzb1 D) (qzb1_pure D) (SFormula.Deriv.andElimRight hRowPack)
  refine SFormula.Deriv.commutesOfTwoAnti _ _ _ (SC.closed (qzb0 D)) (SC.closed (qzb1 D))
    ?wlt0 ?wlt1 ?wne ?wanti0 ?wanti1 ?wrest
  case wlt0 => exact hLt0
  case wlt1 => exact hLt1
  case wne =>
    refine SFormula.Deriv.notIntro ?_
    refine SFormula.Deriv.notElim
      (SFormula.Deriv.eqNatBoolTrue (Γ := _) (qzb0 D) (qzb1 D) .assumption) ?_
    exact SFormula.Deriv.eqBoolFalseNotTrue _ (cw1 hNe)
  case wanti0 =>
    exact SFormula.Deriv.anticommutesTransport _ (SC.p Pauli.X) _ (SC.p Pauli.Z) (SC.b true)
      hX0 hZ0 (SFormula.Deriv.pauliAnticommutesLit Pauli.X Pauli.Z)
  case wanti1 =>
    exact SFormula.Deriv.anticommutesTransport _ (SC.p Pauli.X) _ (SC.p Pauli.Z) (SC.b true)
      hX1 hZ1 (SFormula.Deriv.pauliAnticommutesLit Pauli.X Pauli.Z)
  case wrest =>
    refine SFormula.Deriv.allNatLtIntroBounded _ _ ?_
    refine SFormula.Deriv.impIntro (SFormula.Deriv.impIntro ?_)
    refine SFormula.Deriv.boolCases (logicalZRowGuardAt2 D) _ ?_ ?_
    · set ΔT : List (SFormula 2) := .eqBool (logicalZRowGuardAt2 D) (SC.b true)
        :: .not (.eqNat SFormula.boundNat (SC.closed (qzb1 D)).weaken)
        :: .not (.eqNat SFormula.boundNat (SC.closed (qzb0 D)).weaken)
        :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ with hΔT
      have hEntryW : SFormula.Deriv ΔT (entryFlatF1 D).weaken :=
        cw4 (SFormula.Deriv.weakenFresh (A := entryFlatF1 D) hEntryF)
      have hBBFW : SFormula.Deriv ΔT (bottomBandFalseF D).weaken :=
        cw4 (SFormula.Deriv.weakenFresh (A := bottomBandFalseF D) hBBFF)
      have hq : SFormula.Deriv ΔT (SFormula.witnessLt SFormula.boundNat (nQ1 D).weaken) :=
        SFormula.Deriv.hyp (by rw [hΔT]; right; right; right; exact List.mem_cons_self)
      have hrowT : SFormula.Deriv ΔT (.eqBool (logicalZRowGuardAt2 D) (SC.b true)) := by
        rw [hΔT]; exact .assumption
      have hrowRaw : SFormula.Deriv ΔT (rowGuardRaw2 D) := by rw [← rowGuard2_eq]; exact hrowT
      have hEntry := entryAtBound D hEntryW hq
      have hBBF := bbfAtBound D hBBFW hq hrowRaw
      refine rowDispatchOnTrue D hEntry hrowT hBBF ?hXbulk ?hXtop
      case hXbulk =>
        intro Δ' lift _ _ hBulkTrueΔ _ _
        -- bulk-X: class (b) has bulk FALSE, contradicting cascade bulk TRUE.
        have hBulkFalse0 : SFormula.Deriv ΔT (gBulk D false) :=
          cw4 (SFormula.Deriv.weakenFresh (A := gBulk1 D false) hBulk)
        exact eqBoolContra _ hBulkTrueΔ (lift hBulkFalse0)
      case hXtop =>
        intro Δ' lift _ hrowΔ _ _ hTopBΔ
        -- top-X: use the top-X pin → q ∈ {q0, q1}, contradicting exclusions.
        have hrowRaw' : SFormula.Deriv Δ' (rowGuardRaw2 D) := by rw [← rowGuard2_eq]; exact hrowΔ
        have hPinW0 : SFormula.Deriv ΔT (classZBTopXPinF D).weaken :=
          cw4 (SFormula.Deriv.weakenFresh (A := classZBTopXPinF D) hPin)
        have hdisj := classZBTopXPinAt D (lift hPinW0) (lift hq) hrowRaw' hTopBΔ
        have hne0 : SFormula.Deriv ΔT (.not (.eqNat SFormula.boundNat (SC.closed (qzb0 D)).weaken)) := by
          rw [hΔT]; exact .hyp (by right; right; exact List.mem_cons_self)
        have hne1 : SFormula.Deriv ΔT (.not (.eqNat SFormula.boundNat (SC.closed (qzb1 D)).weaken)) := by
          rw [hΔT]; exact .hyp (by right; exact List.mem_cons_self)
        refine SFormula.Deriv.orElim hdisj ?_ ?_
        · exact SFormula.Deriv.botElim (SFormula.Deriv.notElim (.assumption) (cw1 (lift hne0)))
        · exact SFormula.Deriv.botElim (SFormula.Deriv.notElim (.assumption) (cw1 (lift hne1)))
    · exact logicalZOffRowLocalCommutes D (rowK2 D) .assumption

/-! ## Top-level [Z]: bundle the supporting packs and classify `k`

The transpose of the `logicalX` top-level assembly: bundle every supporting pack,
then classify `k` by its (purely arithmetic) cell guards via nested `boolCases`,
dispatching each class to `commPointwiseZSym` / `commZTwoAntiA` / `commZTwoAntiB`. -/

/-- On row 0, if the bulk band fires then `r = k/(d-1) = 0`.  Quantified over
`q < nQubits`.  Transpose of `bandImpCZeroPack`. -/
abbrev bandImpRZeroBody (D : OddSurfaceDistance) : SFormula 2 :=
  .imp (rowGuardRaw2 D)
    (.imp (.eqBool (SC.closed (baseBulkBandGuardTA (dX2 D) kX2 (Term.var ⟨0, by decide⟩))) (SC.b true))
      (gRZero2 D true))

abbrev bandImpRZeroF (D : OddSurfaceDistance) : SFormula 1 :=
  .allNatLt (nQ1 D) (bandImpRZeroBody D)

def bandImpRZeroPack (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (bandImpRZeroF D) := by
  refine PureFamilyDerivA.allNatLtIntro _ ?_
  refine PureFamilyDerivA.arithBool _ rfl ?_
  intro rho E
  have hd : D.distance = 2 * D.index + 3 := rfl
  simp only [bandImpRZeroBody, rowGuardRaw2, baseBulkBandGuardTA, gRZero2, dX2,
    distAtBoundIdx2, kX2, dm1TA, orEqSucc, band3, bulkCountTA, SFormula.eval, SC.closed, SC.b,
    STerm.eval, Term.eval, Term.lift, bind, Option.bind]
  set q := rho ⟨0, by decide⟩ with hq'
  set k := rho ⟨1, by decide⟩ with hk'
  set d := D.distance with hdd
  have hdpos : 0 < d := by omega
  by_cases hq : q / d = 0
  · rw [hq]
    by_cases hrz : k / (d - 1) = 0
    · -- r = 0 → conclusion `decide (k/(d-1)=0) = true` holds; whatever the band
      -- evaluates to, the implication result is `some true`.
      rw [hrz]
      by_cases hc0 : q % d = k % (d - 1)
      · simp only [hc0, if_true]
        cases (decide (k < (d - 1) * (d - 1))) <;> simp
      · by_cases hc1 : q % d = k % (d - 1) + 1 <;> simp_all
    · -- r ≠ 0 → on row 0 the band disjuncts `0 = r`, `0 = r+1` are false, band false.
      have hb0 : decide (0 = k / (d - 1)) = false := by
        rw [decide_eq_false_iff_not]; exact fun h => hrz h.symm
      have hb1 : decide (0 = k / (d - 1) + 1) = false := by
        rw [decide_eq_false_iff_not]; exact fun h => Nat.succ_ne_zero _ h.symm
      simp only [hb0, hb1, decide_false, Bool.false_eq_true, if_false]
      cases (decide (k / (d - 1) = 0)) <;> simp
  · simp only [hq, decide_false, Bool.false_eq_true, if_false]

/-! ### Pointwise X-handler helpers (close `X` leaves by `k`-fact contradiction) -/

/-- A bulk-`X` handler that kills the leaf because the cascade's `gKind D false`
contradicts a context `gKind1 D true` fact. -/
def zhXbulkByKindTrue {Γ : List (SFormula 1)} (D : OddSurfaceDistance)
    (hKindT : SFormula.Deriv Γ (gKind1 D true)) :
    ∀ (Δ' : List (SFormula 2)),
      (∀ {A : SFormula 2}, SFormula.Deriv (.eqBool (logicalZRowGuardAt2 D) (SC.b true)
          :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (entryFlat2F D) →
      SFormula.Deriv Δ' (.eqBool (logicalZRowGuardAt2 D) (SC.b true)) →
      SFormula.Deriv Δ' (gBulk D true) → SFormula.Deriv Δ' (gBand D true) →
      SFormula.Deriv Δ' (gKind D false) → SFormula.Deriv Δ' (lcGoalZ D) := by
  intro Δ' lift _ _ _ _ hKindF
  have hKT : SFormula.Deriv _ (gKind D true) :=
    lift (cw2 (SFormula.Deriv.weakenFresh (A := gKind1 D true) hKindT))
  exact eqBoolContra _ hKT hKindF

/-- A bulk-`X` handler that kills the leaf because the band-pin (`band ∧ row → r=0`)
contradicts a context `gRZero1 D false` (`r ≠ 0`) fact. -/
def zhXbulkByRNZ {Γ : List (SFormula 1)} (D : OddSurfaceDistance)
    (hRNZ : SFormula.Deriv Γ (gRZero1 D false))
    (hImp : SFormula.Deriv Γ (bandImpRZeroF D)) :
    ∀ (Δ' : List (SFormula 2)),
      (∀ {A : SFormula 2}, SFormula.Deriv (.eqBool (logicalZRowGuardAt2 D) (SC.b true)
          :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (entryFlat2F D) →
      SFormula.Deriv Δ' (.eqBool (logicalZRowGuardAt2 D) (SC.b true)) →
      SFormula.Deriv Δ' (gBulk D true) → SFormula.Deriv Δ' (gBand D true) →
      SFormula.Deriv Δ' (gKind D false) → SFormula.Deriv Δ' (lcGoalZ D) := by
  intro Δ' lift _ hrowΔ _ hBandΔ _
  have hrowRaw : SFormula.Deriv Δ' (rowGuardRaw2 D) := by rw [← rowGuard2_eq]; exact hrowΔ
  have hImpW : SFormula.Deriv _ (bandImpRZeroF D).weaken :=
    lift (cw2 (SFormula.Deriv.weakenFresh (A := bandImpRZeroF D) hImp))
  have hq : SFormula.Deriv _ (SFormula.witnessLt SFormula.boundNat (nQ1 D).weaken) :=
    lift (.hyp (by right; exact List.mem_cons_self))
  have hElim := SFormula.Deriv.allNatLtElim (nQ1 D).weaken ((bandImpRZeroBody D).lift 1)
    SFormula.boundNat hImpW hq
  have hBody := SFormula.Deriv.applyNatBoundNatBeta (bandImpRZeroBody D) hElim
  have hRZtrue := SFormula.Deriv.mp (SFormula.Deriv.mp hBody hrowRaw) hBandΔ
  have hRZfalse : SFormula.Deriv _ (gRZero2 D false) :=
    lift (cw2 (SFormula.Deriv.weakenFresh (A := gRZero1 D false) hRNZ))
  exact eqBoolContra _ hRZtrue hRZfalse

/-- A bulk-`X` handler that kills the leaf because the cascade's `gBulk D true`
contradicts a context `gBulk1 D false` fact. -/
def zhXbulkByBulkFalse {Γ : List (SFormula 1)} (D : OddSurfaceDistance)
    (hBulkF : SFormula.Deriv Γ (gBulk1 D false)) :
    ∀ (Δ' : List (SFormula 2)),
      (∀ {A : SFormula 2}, SFormula.Deriv (.eqBool (logicalZRowGuardAt2 D) (SC.b true)
          :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (entryFlat2F D) →
      SFormula.Deriv Δ' (.eqBool (logicalZRowGuardAt2 D) (SC.b true)) →
      SFormula.Deriv Δ' (gBulk D true) → SFormula.Deriv Δ' (gBand D true) →
      SFormula.Deriv Δ' (gKind D false) → SFormula.Deriv Δ' (lcGoalZ D) := by
  intro Δ' lift _ _ hBulkT _ _
  have hBF : SFormula.Deriv _ (gBulk D false) :=
    lift (cw2 (SFormula.Deriv.weakenFresh (A := gBulk1 D false) hBulkF))
  exact eqBoolContra _ hBulkT hBF

/-- A top-`X` handler that kills the leaf because the cascade's `gBulk D false`
contradicts a context `gBulk1 D true` fact. -/
def zhXtopByBulkTrue {Γ : List (SFormula 1)} (D : OddSurfaceDistance)
    (hBulkT : SFormula.Deriv Γ (gBulk1 D true)) :
    ∀ (Δ' : List (SFormula 2)),
      (∀ {A : SFormula 2}, SFormula.Deriv (.eqBool (logicalZRowGuardAt2 D) (SC.b true)
          :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (entryFlat2F D) →
      SFormula.Deriv Δ' (.eqBool (logicalZRowGuardAt2 D) (SC.b true)) →
      SFormula.Deriv Δ' (gBulk D false) → SFormula.Deriv Δ' (gTopC D true) →
      SFormula.Deriv Δ' (gTopB D true) → SFormula.Deriv Δ' (lcGoalZ D) := by
  intro Δ' lift _ _ hBulkFΔ _ _
  have hBT : SFormula.Deriv _ (gBulk D true) :=
    lift (cw2 (SFormula.Deriv.weakenFresh (A := gBulk1 D true) hBulkT))
  exact eqBoolContra _ hBT hBulkFΔ

/-- A top-`X` handler that kills the leaf because the cascade's `gTopC D true`
contradicts a context `gTopC1 D false` fact. -/
def zhXtopByTopCFalse {Γ : List (SFormula 1)} (D : OddSurfaceDistance)
    (hTopCF : SFormula.Deriv Γ (gTopC1 D false)) :
    ∀ (Δ' : List (SFormula 2)),
      (∀ {A : SFormula 2}, SFormula.Deriv (.eqBool (logicalZRowGuardAt2 D) (SC.b true)
          :: SFormula.boundNatLt (nQ1 D) :: List.map (fun G => G.weaken) Γ) A → SFormula.Deriv Δ' A) →
      SFormula.Deriv Δ' (entryFlat2F D) →
      SFormula.Deriv Δ' (.eqBool (logicalZRowGuardAt2 D) (SC.b true)) →
      SFormula.Deriv Δ' (gBulk D false) → SFormula.Deriv Δ' (gTopC D true) →
      SFormula.Deriv Δ' (gTopB D true) → SFormula.Deriv Δ' (lcGoalZ D) := by
  intro Δ' lift _ _ _ hTopCTΔ _
  have hTF : SFormula.Deriv _ (gTopC D false) :=
    lift (cw2 (SFormula.Deriv.weakenFresh (A := gTopC1 D false) hTopCF))
  exact eqBoolContra _ hTopCTΔ hTF

/-! ### The Z supporting-pack bundle and the classification driver -/

/-- The big conjunction of every supporting pack used by the per-`k` [Z]
classification.  Transpose of `xBundleF`. -/
abbrev zBundleF (D : OddSurfaceDistance) : SFormula 1 :=
  .and (entryFlatF1 D)
  (.and (bottomBandFalseF D)
  (.and (classZAPackF D)
  (.and (qzaRowGuardF D)
  (.and (classZABulkXPinF D)
  (.and (classZBPackF D)
  (.and (qzbRowGuardF D)
  (.and (classZBTopXPinF D)
  (.and (entryAtF D (qza0 D))
  (.and (entryAtF D (qza1 D))
  (.and (entryAtF D (qzb0 D))
  (.and (entryAtF D (qzb1 D))
  (bandImpRZeroF D))))))))))))

def zBundle (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2) (zBundleF D) :=
  pfdaAnd (entryFlatPack D) (pfdaAnd (bottomBandFalsePack D)
    (pfdaAnd (classZAPack D) (pfdaAnd (qzaRowGuardPack D)
      (pfdaAnd (classZABulkXPinPack D) (pfdaAnd (classZBPack D)
        (pfdaAnd (qzbRowGuardPack D) (pfdaAnd (classZBTopXPinPack D)
          (pfdaAnd (xEntryFlat1 D (qza0 D) (qza0_pure D))
            (pfdaAnd (xEntryFlat1 D (qza1 D) (qza1_pure D))
              (pfdaAnd (xEntryFlat1 D (qzb0 D) (qzb0_pure D))
                (pfdaAnd (xEntryFlat1 D (qzb1 D) (qzb1_pure D))
                  (bandImpRZeroPack D))))))))))))

namespace BundleExtractZ
variable {Γ : List (SFormula 1)} {D : OddSurfaceDistance}
def entryF (h : SFormula.Deriv Γ (zBundleF D)) : SFormula.Deriv Γ (entryFlatF1 D) :=
  SFormula.Deriv.andElimLeft h
def bbf (h : SFormula.Deriv Γ (zBundleF D)) : SFormula.Deriv Γ (bottomBandFalseF D) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight h)
def classA (h : SFormula.Deriv Γ (zBundleF D)) : SFormula.Deriv Γ (classZAPackF D) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight h))
def qzaRow (h : SFormula.Deriv Γ (zBundleF D)) : SFormula.Deriv Γ (qzaRowGuardF D) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight h)))
def aPin (h : SFormula.Deriv Γ (zBundleF D)) : SFormula.Deriv Γ (classZABulkXPinF D) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight h))))
def classB (h : SFormula.Deriv Γ (zBundleF D)) : SFormula.Deriv Γ (classZBPackF D) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight h)))))
def qzbRow (h : SFormula.Deriv Γ (zBundleF D)) : SFormula.Deriv Γ (qzbRowGuardF D) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight h))))))
def bPin (h : SFormula.Deriv Γ (zBundleF D)) : SFormula.Deriv Γ (classZBTopXPinF D) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight h)))))))
def eqa0 (h : SFormula.Deriv Γ (zBundleF D)) : SFormula.Deriv Γ (entryAtF D (qza0 D)) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight h))))))))
def eqa1 (h : SFormula.Deriv Γ (zBundleF D)) : SFormula.Deriv Γ (entryAtF D (qza1 D)) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
        (SFormula.Deriv.andElimRight h)))))))))
def eqb0 (h : SFormula.Deriv Γ (zBundleF D)) : SFormula.Deriv Γ (entryAtF D (qzb0 D)) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
        (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight h))))))))))
def eqb1 (h : SFormula.Deriv Γ (zBundleF D)) : SFormula.Deriv Γ (entryAtF D (qzb1 D)) :=
  SFormula.Deriv.andElimLeft (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
    (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
      (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
        (SFormula.Deriv.andElimRight (SFormula.Deriv.andElimRight
          (SFormula.Deriv.andElimRight h)))))))))))
def bandImpR (h : SFormula.Deriv Γ (zBundleF D)) : SFormula.Deriv Γ (bandImpRZeroF D) :=
  h.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight.andElimRight
end BundleExtractZ

/-- **The symbolic (∀ D) `logicalZ` normalizer.**  For every `OddSurfaceDistance`,
`logicalZ` commutes with every generated stabilizer row of the recursive Surface
code.  Transpose of `xNormCommuteSym`: `allNatLtIntro` the stabilizer index `k`,
`cut1` the Z pack bundle, then classify `k` by its (purely arithmetic) cell guards
via nested `boolCases`, dispatching each class to `commPointwiseZSym` /
`commZTwoAntiA` / `commZTwoAntiB`. -/
def zNormCommuteSym (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2)
      (closedSF (logicalZNormalizesOddF D)) := by
  unfold closedSF logicalZNormalizesOddF Formula.normalizesCodeUpTo
  simp only [closedSF, Formula.codeRow, Term.weaken]
  refine PureFamilyDerivA.allNatLtIntro _ ?_
  refine PureFamilyDerivA.cut1 ?_ (zBundle D)
  -- Context: [zBundleF D].  Classify `k` by its k-only cell guards.
  open BundleExtractZ in
  refine SFormula.Deriv.boolCases (SC.closed (bulkGuardTA (dX1 D) kX1)) _ ?bulkT ?bulkF
  case bulkT =>
    -- bulk TRUE.  Context: [gBulk1 true, zBundle].
    refine SFormula.Deriv.boolCases (SC.closed (.eqNat (.div kX1 (dm1TA (dX1 D))) (.natLit 0))) _ ?rz ?rnz
    case rz =>
      -- r = 0.  Context: [gRZero1 true, gBulk1 true, zBundle].
      refine SFormula.Deriv.boolCases (SC.closed (baseKindGuardTA (dX1 D) kX1)) _ ?kt ?kf
      case kt =>
        -- kind TRUE → pointwise.
        refine commPointwiseZSym D
          (BundleExtractZ.entryF (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtractZ.bbf (.hyp (by right; right; right; exact List.mem_cons_self)))
          (zhXbulkByKindTrue D (.assumption))
          (zhXtopByBulkTrue D (.hyp (by right; right; exact List.mem_cons_self)))
      case kf =>
        -- kind FALSE → class (a).
        exact commZTwoAntiA D
          (.hyp (by right; right; exact List.mem_cons_self))   -- gBulk1 true
          (.hyp (by right; exact List.mem_cons_self))          -- gRZero1 true
          (.assumption)                                        -- gKind1 false
          (BundleExtractZ.classA (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtractZ.qzaRow (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtractZ.aPin (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtractZ.entryF (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtractZ.bbf (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtractZ.eqa0 (.hyp (by right; right; right; exact List.mem_cons_self)))
          (BundleExtractZ.eqa1 (.hyp (by right; right; right; exact List.mem_cons_self)))
    case rnz =>
      -- r ≠ 0 → pointwise.  Context: [gRZero1 false, gBulk1 true, zBundle].
      refine commPointwiseZSym D
        (BundleExtractZ.entryF (.hyp (by right; right; exact List.mem_cons_self)))
        (BundleExtractZ.bbf (.hyp (by right; right; exact List.mem_cons_self)))
        (zhXbulkByRNZ D (.assumption)
          (BundleExtractZ.bandImpR (.hyp (by right; right; exact List.mem_cons_self))))
        (zhXtopByBulkTrue D (.hyp (by right; exact List.mem_cons_self)))
  case bulkF =>
    -- bulk FALSE.  Context: [gBulk1 false, zBundle].
    refine SFormula.Deriv.boolCases (SC.closed (topClassGuardTA (dX1 D) kX1)) _ ?tt ?tf
    case tt =>
      -- topClass TRUE → class (b).
      exact commZTwoAntiB D
        (.hyp (by right; exact List.mem_cons_self))          -- gBulk1 false
        (.assumption)                                        -- gTopC1 true
        (BundleExtractZ.classB (.hyp (by right; right; exact List.mem_cons_self)))
        (BundleExtractZ.qzbRow (.hyp (by right; right; exact List.mem_cons_self)))
        (BundleExtractZ.bPin (.hyp (by right; right; exact List.mem_cons_self)))
        (BundleExtractZ.entryF (.hyp (by right; right; exact List.mem_cons_self)))
        (BundleExtractZ.bbf (.hyp (by right; right; exact List.mem_cons_self)))
        (BundleExtractZ.eqb0 (.hyp (by right; right; exact List.mem_cons_self)))
        (BundleExtractZ.eqb1 (.hyp (by right; right; exact List.mem_cons_self)))
    case tf =>
      -- topClass FALSE → pointwise.  Context: [gTopC1 false, gBulk1 false, zBundle].
      refine commPointwiseZSym D
        (BundleExtractZ.entryF (.hyp (by right; right; exact List.mem_cons_self)))
        (BundleExtractZ.bbf (.hyp (by right; right; exact List.mem_cons_self)))
        (zhXbulkByBulkFalse D (.hyp (by right; exact List.mem_cons_self)))
        (zhXtopByTopCFalse D (.assumption))


/-- Scaffold: reduce `logicalXNormalizesOddF` to the per-row commutation of the
resolved tree against `logicalX`.

* `allNatLtIntro` introduces the stabilizer index `k = var 0` (arity 1).
* `cut1 _ boundRowsResolved` makes the resolved-row equality
  `∀ q < n, stabAt (recCall (lift d) k) q = rowSymTreeA D.index (lift d) k q`
  available as an `SFormula.Deriv` hypothesis, eliminating `recCall`.

The remaining `SFormula.Deriv` goal is
  `commutesUpTo n (recCall (lift d) (var 0)) (lift logicalX)`.
The OFF-column-0 half of this is fully discharged by the sorry-free reusable
lemma `logicalXOffColumnLocalCommutes` (the `logicalX` entry is `I` wherever the
column guard is `false`).  What genuinely remains is the COLUMN-0 even-parity
argument: classify `k` by geometry and supply, via `commutesOfTwoAnti`, the two
column-0 qubits `q0 k, q1 k` where the Z-type row anticommutes with `logicalX`
(and `commutesOfPointwise` for X-type rows).  Identifying `q0/q1` as functions of
the symbolic recursion depth `D.index` mirrors the whole `rowSymTreeA` recursion
and is the genuinely deep residual — OPEN. -/
def xNormScaffold (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2)
      (closedSF (logicalXNormalizesOddF D)) :=
  -- Closed by the symbolic geometric classification developed above: classify the
  -- bound stabilizer index `k` by its (purely arithmetic) cell guards, and supply
  -- the two anticommuting column-0 qubits for the Z-type rows (`commutesOfTwoAnti`,
  -- classes (a) and (b)) and pointwise commutation for the X/I-type rows.
  xNormCommuteSym D

/-- Scaffold for `zNorm` — the transpose of `xNormScaffold`.  Identical reduction:
`allNatLtIntro` + `cut1 _ boundRowsResolved` discharge `recCall`, leaving the
`SFormula.Deriv` goal `commutesUpTo n (recCall (lift d) (var 0)) (lift logicalZ)`.
The OFF-row half is fully discharged by the sorry-free reusable lemma
`logicalZOffRowLocalCommutes` (the `logicalZ` entry is `I` wherever the row guard
`q / d = 0` is `false`).  The residual is the TOP-ROW even-parity argument —
the row/column transpose of `xNorm`'s frontier — supplying the two anti qubits
for Z-vs-Z overlaps via `commutesOfTwoAnti`, by recursion on `D.index`.
Genuinely deep; OPEN at the same isolated frontier. -/
def zNormScaffold (D : OddSurfaceDistance) :
    PureFamilyDerivA Surface.code.body (D.distance + 2)
      (closedSF (logicalZNormalizesOddF D)) :=
  -- Closed by the symbolic geometric classification developed above (the transpose
  -- of `xNormCommuteSym`): classify the bound stabilizer index `k` by its (purely
  -- arithmetic) cell guards, and supply the two anticommuting ROW-0 qubits for the
  -- X-type rows (`commZTwoAntiA`/`commZTwoAntiB`, classes (a)/(b)) and pointwise
  -- commutation for the Z/I-type rows (`commPointwiseZSym`).
  zNormCommuteSym D

#print axioms logicalXOffColumnLocalCommutes
#print axioms logicalZOffRowLocalCommutes
#print axioms xNormScaffold
#print axioms xNormCommuteSym
#print axioms zNormScaffold
#print axioms zNormCommuteSym

end QHL.CodeLang.Surface.Verify
