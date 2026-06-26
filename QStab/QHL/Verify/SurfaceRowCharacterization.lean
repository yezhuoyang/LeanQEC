import QStab.QHL.Verify.SurfaceGeneratedRowsPure

/-!
# Recursive generated-row entry characterization for the Surface code

This prover-side file builds the *foundation* lemma for the recursive
Surface-code distance proof: a reusable, pure (`PureFamilyDerivA`) derivation
giving, for the Surface code at any odd distance, the Pauli entry of each
generated stabilizer row at each qubit, **without** running the evaluator as a
distance proof.

The characterization is expressed entirely through already-trusted pure rules:
`recUnfold` (one recursion-layer unfold), `iteSelect*`/`pauliIteSelect*`
(branch selection from a closed boolean guard), `closedStabAtSplit`,
`eqPauli{Refl,Symm,Trans}`, plus the boolean-guard rule `arithBool`.

Nothing here adds a new trusted rule, uses `native_decide`, `Formula.check`,
`Formula.eval`-as-distance, `deriveTrue?`, `admit`, or a new axiom.
-/

namespace QHL.CodeLang.Surface.Verify

open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface

set_option maxRecDepth 65536

/-! ## Closed boolean-guard helpers

These wrap `PureFamilyDerivA.arithBool` for the *closed* boolean guards that
appear inside a generated row body after the distance and stabilizer index have
been substituted to literals.  Only the qubit variable remains free, but each
particular cell we characterize fixes the qubit to a literal, so the guard is a
closed boolean that evaluates by `decide`.
-/

/-- A closed boolean term that evaluates (under any environment / partial
stabilizer) to `true` can be proven `= true` by `arithBool`, provided the term
is in the `arithBoolFragment`. -/
def closedBoolTrue {arity fuel : Nat} (b : Term arity .bool)
    (hFrag : arithBoolFragment (.eqBool (SC.closed b) (SC.b true)) = true)
    (hEval : forall (rho : Env arity) (_E : PartialStabilizer),
      Term.eval Surface.code.body fuel b rho = some true) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed b) (SC.b true)) :=
  PureFamilyDerivA.arithBool _ hFrag (by
    intro rho E
    simp [SFormula.eval, STerm.eval, Term.eval, SC.closed, SC.b, hEval rho E])

/-- A closed boolean term that evaluates to `false`. -/
def closedBoolFalse {arity fuel : Nat} (b : Term arity .bool)
    (hFrag : arithBoolFragment (.eqBool (SC.closed b) (SC.b false)) = true)
    (hEval : forall (rho : Env arity) (_E : PartialStabilizer),
      Term.eval Surface.code.body fuel b rho = some false) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed b) (SC.b false)) :=
  PureFamilyDerivA.arithBool _ hFrag (by
    intro rho E
    simp [SFormula.eval, STerm.eval, Term.eval, SC.closed, SC.b, hEval rho E])

/-! ## Bridge from the entry-at lemmas to the directly-peelable form

`surfaceCodeBaseEntryAt` / `surfaceCodeRecursiveEntryAt` produce the right-hand
side `SC.closed (.stabAt (.stabLam body) q)`, where the whole `.stabAt` is
wrapped by `SC.closed`.  The peeling rules `pureStabAtClosedIteLam{Then,Else}`
instead consume the *split* form `.stabAt (SC.closed (.stabLam body)) (SC.closed q)`.
The trusted rule `closedStabAtSplit` bridges the two. -/

/-- Split a closed `stabAt` of a closed `stabLam` into the projected form. -/
def closedStabLamSplit {arity fuel : Nat}
    (entry : Term (arity + 1) .pauli) (q : Term arity .nat) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (SC.closed (.stabAt (.stabLam entry) q))
        (.stabAt (SC.closed (.stabLam entry)) (SC.closed q))) :=
  PureFamilyDerivA.closedStabAtSplit (.stabLam entry) q

/-! ## Generic entry-characterization combinators

The two combinators below take a `peel` derivation that resolves the substituted
entry body at the qubit to a concrete (or recursive) leaf Pauli, and chain it
with the appropriate row-selection lemma.  They are the reusable engine: a
caller supplies the `peel` proof for whatever cell of the grid it cares about. -/

/-- Base-branch (`d < 5`) entry characterization, chained to an arbitrary leaf.

Given a pure derivation `peel` that the *split* projection of the substituted
base entry equals the closed leaf Pauli `p`, conclude that the generated row
entry at `q` equals `p`. -/
def surfaceCodeBaseEntryEq {arity fuel : Nat}
    (n : STerm arity .nat) (dT kT qT : Term arity .nat) (p : Term arity .pauli)
    (hdPure : SFormula.PureNatTerm dT) (hkPure : SFormula.PureNatTerm kT)
    (hGuard :
      PureFamilyDerivA Surface.code.body fuel
        (.eqBool (SC.closed (.ltNat dT (n5 : Term arity .nat))) (SC.b true)))
    (peel :
      PureFamilyDerivA Surface.code.body fuel
        (.eqPauli
          (.stabAt
            (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.baseEntry)))
            (SC.closed qT))
          (SC.closed p))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.recCall dT kT)) (SC.closed qT))
        (SC.closed p)) := by
  let body := codeSubstAt dT kT 1 SurfaceASTPublic.baseEntry
  -- step 1: row entry = SC.closed (stabAt (stabLam body) q)
  have h1 := surfaceCodeBaseEntryAt n dT kT qT hdPure hkPure hGuard
  -- step 2: SC.closed (stabAt (stabLam body) q) = split form
  have h2 := closedStabLamSplit (fuel := fuel) body qT
  -- chain h1, h2, peel
  exact PureFamilyDerivA.eqPauliTrans
    (.stabAt (SC.closed (.recCall dT kT)) (SC.closed qT))
    (.stabAt (SC.closed (.stabLam body)) (SC.closed qT))
    (SC.closed p)
    (PureFamilyDerivA.eqPauliTrans
      (.stabAt (SC.closed (.recCall dT kT)) (SC.closed qT))
      (SC.closed (.stabAt (.stabLam body) qT))
      (.stabAt (SC.closed (.stabLam body)) (SC.closed qT))
      h1 h2)
    peel

/-- Recursive-branch (`d ≥ 5`) entry characterization, chained to an arbitrary
leaf.  Symmetric to `surfaceCodeBaseEntryEq` but uses `recursiveEntry` and the
false distance guard. -/
def surfaceCodeRecursiveEntryEq {arity fuel : Nat}
    (n : STerm arity .nat) (dT kT qT : Term arity .nat) (p : Term arity .pauli)
    (hdPure : SFormula.PureNatTerm dT) (hkPure : SFormula.PureNatTerm kT)
    (hGuard :
      PureFamilyDerivA Surface.code.body fuel
        (.eqBool (SC.closed (.ltNat dT (n5 : Term arity .nat))) (SC.b false)))
    (peel :
      PureFamilyDerivA Surface.code.body fuel
        (.eqPauli
          (.stabAt
            (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
            (SC.closed qT))
          (SC.closed p))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.recCall dT kT)) (SC.closed qT))
        (SC.closed p)) := by
  let body := codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry
  have h1 := surfaceCodeRecursiveEntryAt n dT kT qT hdPure hkPure hGuard
  have h2 := closedStabLamSplit (fuel := fuel) body qT
  exact PureFamilyDerivA.eqPauliTrans
    (.stabAt (SC.closed (.recCall dT kT)) (SC.closed qT))
    (.stabAt (SC.closed (.stabLam body)) (SC.closed qT))
    (SC.closed p)
    (PureFamilyDerivA.eqPauliTrans
      (.stabAt (SC.closed (.recCall dT kT)) (SC.closed qT))
      (SC.closed (.stabAt (.stabLam body) qT))
      (.stabAt (SC.closed (.stabLam body)) (SC.closed qT))
      h1 h2)
    peel

/-! ## Concrete-cell leaf peeling

The combinators above reduce a row-entry characterization to a `peel` obligation
on the substituted entry body.  For a *concrete* cell (literal distance,
stabilizer index, qubit), that body is a closed `ite` tree whose guards are
closed arithmetic booleans, which we peel by a single `stabLam`-strip
(`pureStabAtClosedIteLamThen/Else`) followed by a chain of bare-Pauli `ite`
selections (`pauliIteSelectThen/Else`).  All guards are discharged by
`PureFamilyDerivA.arithBool` (closed numeric decision), never by an evaluator
used as a distance proof. -/

/-- Discharge a closed boolean guard `cond` to `true` by closed numeric
decision.  `cond` must lie in the arithmetic-boolean fragment (true by `rfl`)
and evaluate to `true` under the canonical body (true by `decide`-style `simp`).
-/
def guardTrue {fuel : Nat} (cond : Term 0 .bool)
    (hFrag : arithBoolFragment
      (.eqBool (SC.closed cond) (SC.b true)) = true := by rfl)
    (hEval : forall (rho : Env 0),
      Term.eval Surface.code.body fuel cond rho = some true := by
        intro rho; rfl) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed cond) (SC.b true)) :=
  PureFamilyDerivA.arithBool _ hFrag (by
    intro rho E
    simp [SFormula.eval, STerm.eval, Term.eval, SC.closed, SC.b, hEval rho])

/-- Discharge a closed boolean guard `cond` to `false`. -/
def guardFalse {fuel : Nat} (cond : Term 0 .bool)
    (hFrag : arithBoolFragment
      (.eqBool (SC.closed cond) (SC.b false)) = true := by rfl)
    (hEval : forall (rho : Env 0),
      Term.eval Surface.code.body fuel cond rho = some false := by
        intro rho; rfl) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed cond) (SC.b false)) :=
  PureFamilyDerivA.arithBool _ hFrag (by
    intro rho E
    simp [SFormula.eval, STerm.eval, Term.eval, SC.closed, SC.b, hEval rho])

/-- **Worked representative base cell.**

The generated row `0` of the `d = 3` Surface code (a bulk Z-plaquette) carries a
`Z` at qubit `0`.  This is proved end-to-end through the pure pipeline:
`recUnfold` → base-branch selection → `stabLam` strip → bare-Pauli `ite`
selections, with every guard discharged by `arithBool`.  It validates that the
foundation combinators compose into a sorry-free leaf characterization. -/
def surfaceD3Cell_k0_q0 {fuel : Nat} :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt
          (SC.closed (.stabLam (codeSubstAt (.natLit (arity := 0) 3) (.natLit 0) 1
            SurfaceASTPublic.baseEntry)))
          (SC.closed (.natLit 0)))
        (SC.closed (.pauliLit Pauli.Z))) := by
  simp only [SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
    SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN,
    Term.weaken, Term.lift, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, orEqSucc, orEqPair]
  -- Strip the outer `stabLam` and select the `bulk` branch (outer guard `0 < 4`).
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (pureStabAtClosedIteLamThen (fuel := fuel)
      (.ltNat (.natLit 0)
        (.mul (.sub (.natLit 3) (.natLit 1)) (.sub (.natLit 3) (.natLit 1))))
      _ _ (.natLit 0) (by constructor)
      (guardTrue _
        (by simp only [Term.instantiateTopNat, Term.instantiateNatAt]; decide)
        (by intro rho;
            simp only [Term.instantiateTopNat, Term.instantiateNatAt, Term.eval]; rfl)))
    ?_
  -- push the top-instantiation through the residual `ite` tree
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, Nat.reduceLT, reduceDIte,
    dite_true]
  -- select the `bulk`-inner `kind` branch, then `Z`; both guards are closed and true
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectThen _ _ _
      (guardTrue _ (by decide) (by intro rho; simp [Term.eval])))
    (PureFamilyDerivA.pauliIteSelectThen _ _ _
      (guardTrue _ (by decide) (by intro rho; simp [Term.eval])))

/-- **Consumer-facing `d = 3` row-entry characterization (representative cell).**

This is the shape the downstream consumers (`rowsCommute`, normalizers, bridge
leaves) actually project: the generated *code row* `Formula.codeRow (oddDistance 0) k`
evaluated at a qubit equals an explicit leaf Pauli.  Here, row `0`, qubit `0`
carries `Z`.  It is obtained purely by chaining the row-selection lemma
`surfaceCodeD3BaseEntryAt`, the split bridge `closedStabLamSplit`, and the peeled
leaf `surfaceD3Cell_k0_q0`. -/
def surfaceD3Row_k0_q0 {fuel : Nat} :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt
          (SC.closed (Formula.codeRow (.natLit (arity := 0) (oddDistance 0))
            (.natLit (arity := 0) 0)))
          (SC.n (arity := 0) 0))
        (SC.closed (.pauliLit Pauli.Z))) :=
  PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (surfaceCodeD3BaseEntryAt (fuel := fuel) (SC.n (nQubits (oddDistance 0))) 0 0)
      (closedStabLamSplit (fuel := fuel)
        (codeSubstAt (.natLit (oddDistance 0)) (.natLit 0) 1 SurfaceASTPublic.baseEntry)
        (.natLit 0)))
    surfaceD3Cell_k0_q0

/-! ## Recursive step validation (`d = 5` interior cell recurses to `d = 3`)

The genuinely recursive content: at `d = oddDistance 1 = 5`, an *interior* cell
of the recursive entry references the inner code row `.stabAt (.recCall 3 k') q'`.
The cell `(k = 5, q = 6)` maps to the inner reference `.stabAt (.recCall 3 0) 0`.
This is the witness that `surfaceCodeRecursiveEntryEq` composes with the
inductive hypothesis (the `d = 3` characterization) across one recursion layer. -/

/-- The `d = 5` recursive entry, substituted at `k = 5`, projected at qubit `6`,
peels to the inner-code reference `.stabAt (.recCall innerD interiorK) innerQ` where
`innerD = d - 2`, `interiorK = (r-1)*innerDm1 + (c-1)`, `innerQ = (row-1)*innerD + (col-1)`.

The leaf is the *honest, unreduced* reference AST that the peel actually produces:
the substituted recursion-step arithmetic (`.sub (.natLit 5) (.natLit 2)`, etc.) does
*not* collapse to the literals `(.recCall 3 0) 0` because those are distinct `Term`
constructor trees and there is no closed-Pauli evaluator rule that would bridge them.
Numerically the reference denotes the inner `d = 3` code row `(.recCall 3 0)` at qubit
`0`: `innerD = 5 - 2 = 3`, `interiorK = (5/4 - 1)*((5-2)-1) + (5%4 - 1) = 0*2 + 0 = 0`,
`innerQ = (6/5 - 1)*(5-2) + (6%5 - 1) = 0*3 + 0 = 0`. -/
def surfaceD5Cell_k5_q6_interior {fuel : Nat} :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt
          (SC.closed (.stabLam (codeSubstAt (.natLit (arity := 0) 5) (.natLit 5) 1
            SurfaceASTPublic.recursiveEntry)))
          (SC.closed (.natLit 6)))
        (SC.closed (.stabAt
          (.recCall
            (.sub (.natLit 5) (.natLit 2))
            (.add
              (.mul (.sub (.div (.natLit 5) (.sub (.natLit 5) (.natLit 1))) (.natLit 1))
                (.sub (.sub (.natLit 5) (.natLit 2)) (.natLit 1)))
              (.sub (.mod (.natLit 5) (.sub (.natLit 5) (.natLit 1))) (.natLit 1))))
          (.add
            (.mul (.sub (.div (.natLit 6) (.natLit 5)) (.natLit 1)) (.sub (.natLit 5) (.natLit 2)))
            (.sub (.mod (.natLit 6) (.natLit 5)) (.natLit 1)))))) := by
  simp only [SurfaceASTPublic.recursiveEntry, SurfaceASTPublic.promotedBoundaryEntry,
    SurfaceASTPublic.k, SurfaceASTPublic.d, SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q,
    codeSubstAt, liftTopN, Term.weaken, Term.lift, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
    eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, band4, orEqSucc, le]
  -- Strip the outer `stabLam` + select the `bulk` branch (outer guard `5 < 16` TRUE).
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (pureStabAtClosedIteLamThen (fuel := fuel)
      (.ltNat (.natLit 5)
        (.mul (.sub (.natLit 5) (.natLit 1)) (.sub (.natLit 5) (.natLit 1))))
      _ _ (.natLit 6) (by constructor)
      (guardTrue _
        (by simp only [Term.instantiateTopNat, Term.instantiateNatAt]; decide)
        (by intro rho;
            simp only [Term.instantiateTopNat, Term.instantiateNatAt, Term.eval]; rfl)))
    ?_
  -- push the top-instantiation (q -> 6) through the residual `ite` tree
  simp only [Term.instantiateTopNat, Term.instantiateNatAt, Nat.reduceLT, dite_true, dite_false]
  -- select `interiorCell` (TRUE), then `inside` (TRUE), landing on the inner ref.
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.pauliIteSelectThen _ _ _
      (guardTrue _ (by decide) (by intro rho; simp [Term.eval])))
    (PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectThen _ _ _
        (guardTrue _ (by decide) (by intro rho; simp [Term.eval])))
      (PureFamilyDerivA.eqPauliRefl _))

/-- The inner-code reference produced by the `d = 5` interior cell, namely
`.recCall (.sub 5 2) interiorK` projected at `innerQ`, resolves to the leaf `Z`.

This is the *inductive-hypothesis application*: the inner distance argument
`.sub (.natLit 5) (.natLit 2)` is a `PureNatTerm` evaluating to `3`, so the same
`recUnfold` + base-branch selection + `baseEntry` peel machinery (all guards
discharged numerically by `arithBool`) applies one layer down, yielding the same
`Z` as the standalone `d = 3` cell.  All guards still evaluate numerically. -/
def surfaceD5InnerRef_resolves_Z {fuel : Nat} :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (SC.closed ((.stabAt
          (.recCall
            (.sub (.natLit 5) (.natLit 2))
            (.add
              (.mul (.sub (.div (.natLit 5) (.sub (.natLit 5) (.natLit 1))) (.natLit 1))
                (.sub (.sub (.natLit 5) (.natLit 2)) (.natLit 1)))
              (.sub (.mod (.natLit 5) (.sub (.natLit 5) (.natLit 1))) (.natLit 1))))
          (.add
            (.mul (.sub (.div (.natLit 6) (.natLit 5)) (.natLit 1)) (.sub (.natLit 5) (.natLit 2)))
            (.sub (.mod (.natLit 6) (.natLit 5)) (.natLit 1)))) : Term 0 .pauli))
        (SC.closed (.pauliLit (arity := 0) Pauli.Z))) := by
  refine PureFamilyDerivA.eqPauliTrans _ _ _
    (PureFamilyDerivA.closedStabAtSplit _ _)
    (surfaceCodeBaseEntryEq (SC.n 0) _ _ _ (.pauliLit Pauli.Z)
      (.sub (.nat 5) (.nat 2))
      (.add
        (.mul (.sub (.div (.nat 5) (.sub (.nat 5) (.nat 1))) (.nat 1))
          (.sub (.sub (.nat 5) (.nat 2)) (.nat 1)))
        (.sub (.mod (.nat 5) (.sub (.nat 5) (.nat 1))) (.nat 1)))
      (guardTrue _ (by rfl) (by intro rho; simp only [n5, Term.eval]; rfl))
      ?peel)
  case peel =>
    simp only [SurfaceASTPublic.baseEntry, SurfaceASTPublic.k, SurfaceASTPublic.d,
      SurfaceASTPublic.q, C.Entry.k, C.Entry.d, C.Entry.q, codeSubstAt, liftTopN,
      Term.weaken, Term.lift, Nat.reduceLT, Nat.reduceEqDiff, reduceDIte,
      eq_mp_eq_cast, eq_mpr_eq_cast, cast_eq, band3, orEqSucc, orEqPair]
    refine PureFamilyDerivA.eqPauliTrans _ _ _
      (pureStabAtClosedIteLamThen (fuel := fuel) _ _ _ _
        (.add
          (.mul (.sub (.div (.nat 6) (.nat 5)) (.nat 1)) (.sub (.nat 5) (.nat 2)))
          (.sub (.mod (.nat 6) (.nat 5)) (.nat 1)))
        (guardTrue _
          (by simp only [Term.instantiateTopNat, Term.instantiateNatAt]; decide)
          (by intro rho;
              simp only [Term.instantiateTopNat, Term.instantiateNatAt, Term.eval]; rfl)))
      ?_
    simp only [Term.instantiateTopNat, Term.instantiateNatAt, Nat.reduceLT, reduceDIte,
      dite_true]
    refine PureFamilyDerivA.eqPauliTrans _ _ _
      (PureFamilyDerivA.pauliIteSelectThen _ _ _
        (guardTrue _ (by decide) (by intro rho; simp [Term.eval])))
      (PureFamilyDerivA.pauliIteSelectThen _ _ _
        (guardTrue _ (by decide) (by intro rho; simp [Term.eval])))

/-- **Capstone: full recursive composition across one layer.**

The generated *code row* `5` of the `d = 5` Surface code, evaluated at qubit `6`,
carries `Z` — proved entirely through the recursive pipeline:

  `recCall` (one `recUnfold`) → recursive-branch selection (`d ≥ 5`) → interior
  cell peel to the inner-code reference (`surfaceD5Cell_k5_q6_interior`) →
  inductive-hypothesis application that resolves the inner `d = 3` reference to a
  leaf (`surfaceD5InnerRef_resolves_Z`).

This is the witness that `surfaceCodeRecursiveEntryEq` (the recursive combinator)
composes with the base-layer characterization across a recursion layer — the
structural heart that an induction on `OddSurfaceDistance.index` consumes. -/
def surfaceD5Row_k5_q6 {fuel : Nat} :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.recCall (.natLit (arity := 0) 5) (.natLit 5)))
          (SC.closed (.natLit 6)))
        (SC.closed (.pauliLit Pauli.Z))) :=
  surfaceCodeRecursiveEntryEq (SC.n (nQubits 5)) (.natLit 5) (.natLit 5) (.natLit 6)
    (.pauliLit Pauli.Z)
    (SFormula.PureNatTerm.nat 5) (SFormula.PureNatTerm.nat 5)
    (guardFalse _ (by rfl) (by intro rho; simp only [n5, Term.eval]; rfl))
    (PureFamilyDerivA.eqPauliTrans _ _ _
      surfaceD5Cell_k5_q6_interior
      surfaceD5InnerRef_resolves_Z)

end QHL.CodeLang.Surface.Verify
