import QStab.QHL.Verify.SurfaceRowCharacterizationSymbolic
import QStab.QHL.Verify.SurfaceCodeLevelPure
import QStab.QHL.Verify.SurfaceFlatBridge

/-!
# Logical-normalizer consumers — XSetup

X normaliser setup: the consumer-arity distance witness, discharging the `recCall`
obstacle (universally-quantified resolved rows), and the reusable off-support local-commutation lemmas.
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

end QHL.CodeLang.Surface.Verify
