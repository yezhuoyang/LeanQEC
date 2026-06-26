import QStab.QHL.Verify.SurfaceASTPublic
import QStab.QHL.Verify.SurfaceCodeLevelPure

/-!
# Pure generated-row helpers for the recursive Surface AST

This module contains prover-side abbreviations for the shared recursive row
characterization.  The definitions below do not introduce rules and do not run
the evaluator as a distance proof; they merely compose already-trusted pure
rules (`recUnfold` and `eqPauliProj`) into the reusable shapes needed by the
row/bridge assembly.
-/

namespace QHL.CodeLang.Surface.Verify

open QHL.CodeLang
open QHL.CodeLang.StabBinder
open QHL.CodeLang.Verify
open QHL.CodeLang.Surface

/-- One-step unfolding of a generated code row, with symbolic natural arguments.

This is just the trusted generic `recUnfold` rule specialized to the canonical
Surface code body.  It proves equality of the recursive call with the code body
instantiated at the same symbolic distance and row terms; it does not inspect
or evaluate the generated row. -/
def surfaceCodeRowUnfold {arity : Nat} {fuel : Nat}
    (n : STerm arity .nat) (dT kT : Term arity .nat)
    (hdPure : SFormula.PureNatTerm dT) (hkPure : SFormula.PureNatTerm kT) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqStabUpTo n
        (SC.closed (.recCall dT kT))
        (SC.closed (codeSubstTerm Surface.code.body dT kT))) :=
  PureFamilyDerivA.recUnfold n dT kT hdPure hkPure

/-- Pointwise projection of `surfaceCodeRowUnfold` at a symbolic qubit.

This is the entry-level bridge used by the generated-row characterization:
after unfolding one recursive layer, reasoning continues on the instantiated
body entry at the same qubit.  The qubit range obligation is part of
`PureFamilyDerivA.DefinedObligations`, not a semantic proof leaf. -/
def surfaceCodeRowUnfoldEntry {arity : Nat} {fuel : Nat}
    (n : STerm arity .nat) (dT kT : Term arity .nat) (qT : STerm arity .nat)
    (hdPure : SFormula.PureNatTerm dT) (hkPure : SFormula.PureNatTerm kT) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.recCall dT kT)) qT)
        (.stabAt (SC.closed (codeSubstTerm Surface.code.body dT kT)) qT)) :=
  PureFamilyDerivA.eqPauliProj n
    (SC.closed (.recCall dT kT))
    (SC.closed (codeSubstTerm Surface.code.body dT kT))
    qT
    (surfaceCodeRowUnfold n dT kT hdPure hkPure)

/-- Closed-distance specialization of one-step row unfolding. -/
def surfaceCodeRowUnfoldClosed {fuel : Nat}
    (n : STerm 0 .nat) (dist row : Nat) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqStabUpTo n
        (SC.closed (.recCall (.natLit dist) (.natLit row)))
        (SC.closed (codeSubstTerm Surface.code.body (.natLit dist) (.natLit row)))) :=
  surfaceCodeRowUnfold n (.natLit dist) (.natLit row)
    (SFormula.PureNatTerm.nat dist)
    (SFormula.PureNatTerm.nat row)

/-- Closed-distance, symbolic-row specialization used under bounded row binders. -/
def surfaceCodeRowUnfoldAtBound {fuel : Nat}
    (dist : Nat) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqStabUpTo
        (SC.n (arity := 1) (nQubits dist))
        (SC.closed (.recCall (.natLit dist) rowVar1))
        (SC.closed (codeSubstTerm Surface.code.body (.natLit dist) rowVar1))) :=
  surfaceCodeRowUnfold
    (SC.n (arity := 1) (nQubits dist))
    (.natLit dist)
    rowVar1
    (SFormula.PureNatTerm.nat dist)
    (SFormula.PureNatTerm.var ⟨0, by decide⟩)

/-! ## Selecting the exposed Surface body branch -/

/-! ### Small derived pure combinators -/

def pureEqStabTrans {arity fuel : Nat}
    (n : STerm arity .nat) (A B C : STerm arity .stab)
    (hAB : PureFamilyDerivA Surface.code.body fuel (.eqStabUpTo n A B))
    (hBC : PureFamilyDerivA Surface.code.body fuel (.eqStabUpTo n B C)) :
    PureFamilyDerivA Surface.code.body fuel (.eqStabUpTo n A C) :=
  PureFamilyDerivA.cut2
    (SFormula.Deriv.eqStabTrans n A B C (.hyp (by simp)) (.hyp (by simp)))
    hAB hBC

def pureStabAtClosedIteLamThen {arity fuel : Nat}
    (cond : Term (arity + 1) .bool) (thenP elseP : Term (arity + 1) .pauli)
    (q : Term arity .nat) (hq : SFormula.PureNatTerm q)
    (hGuard :
      PureFamilyDerivA Surface.code.body fuel
        (.eqBool (SC.closed (Term.instantiateTopNat q cond)) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (.ite cond thenP elseP))) (SC.closed q))
        (SC.closed (Term.instantiateTopNat q thenP))) := by
  let A : SFormula arity :=
    .eqBool (SC.closed (Term.instantiateTopNat q cond)) (SC.b true)
  let D : SFormula.Deriv [A]
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (.ite cond thenP elseP))) (SC.closed q))
        (SC.closed (Term.instantiateTopNat q thenP))) :=
    SFormula.Deriv.stabAtClosedIteLamEqThen cond thenP elseP q hq .assumption
  exact PureFamilyDerivA.cut1 D hGuard

def pureStabAtClosedIteLamElse {arity fuel : Nat}
    (cond : Term (arity + 1) .bool) (thenP elseP : Term (arity + 1) .pauli)
    (q : Term arity .nat) (hq : SFormula.PureNatTerm q)
    (hGuard :
      PureFamilyDerivA Surface.code.body fuel
        (.eqBool (SC.closed (Term.instantiateTopNat q cond)) (SC.b false))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (.ite cond thenP elseP))) (SC.closed q))
        (SC.closed (Term.instantiateTopNat q elseP))) := by
  let A : SFormula arity :=
    .eqBool (SC.closed (Term.instantiateTopNat q cond)) (SC.b false)
  let D : SFormula.Deriv [A]
      (.eqPauli
        (.stabAt (SC.closed (.stabLam (.ite cond thenP elseP))) (SC.closed q))
        (SC.closed (Term.instantiateTopNat q elseP))) :=
    SFormula.Deriv.stabAtClosedIteLamEqElse cond thenP elseP q hq .assumption
  exact PureFamilyDerivA.cut1 D hGuard

def purePauliLitRefl {arity fuel : Nat} (p : Pauli) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli (SC.p (arity := arity) p) (SC.p p)) :=
  PureFamilyDerivA.eqPauliRefl (SC.p p)

@[simp] theorem codeSubstAt_code_k {arity : Nat} (dT kT : Term arity .nat) :
    codeSubstAt dT kT 0 C.Code.k = kT := by
  unfold C.Code.k codeSubstAt liftTopN
  simp

@[simp] theorem codeSubstAt_code_d {arity : Nat} (dT kT : Term arity .nat) :
    codeSubstAt dT kT 0 C.Code.d = dT := by
  unfold C.Code.d codeSubstAt liftTopN
  simp

def closedLtFiveTrue {fuel : Nat} {dist : Nat} (h : dist < 5) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat (.natLit dist) (n5 : Term 0 .nat))) (SC.b true)) :=
  PureFamilyDerivA.arithBool _ (by rfl) (by
    intro rho E
    simp [SFormula.eval, STerm.eval, Term.eval, SC.closed, SC.b, n5, h])

def closedLtFiveFalse {fuel : Nat} {dist : Nat} (h : ¬ dist < 5) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqBool (SC.closed (.ltNat (.natLit dist) (n5 : Term 0 .nat))) (SC.b false)) :=
  PureFamilyDerivA.arithBool _ (by rfl) (by
    intro rho E
    simp [SFormula.eval, STerm.eval, Term.eval, SC.closed, SC.b, n5, h])

theorem oddDistance_zero_lt_five : oddDistance 0 < 5 := by
  simp [oddDistance]

theorem oddDistance_succ_not_lt_five (m : Nat) : ¬ oddDistance (m + 1) < 5 := by
  simp [oddDistance]
  omega

/-- Public syntactic view of `codeSubstTerm Surface.code.body`.

After the generic `recUnfold` rule, generated-row proofs must reason about the
visible Surface body.  This lemma performs only syntactic unfolding of the now
public `codeSubstAt`, using the public mirror of `Surface.code.body`; it is not
a semantic or evaluator fact. -/
theorem surfaceCodeSubstBody_eq {arity : Nat} (dT kT : Term arity .nat) :
    codeSubstTerm Surface.code.body dT kT =
      .ite (.ltNat dT (n5 : Term arity .nat))
        (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.baseEntry))
        (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)) := by
  rw [SurfaceASTPublic.code_body_eq_public]
  simp [SurfaceASTPublic.body, codeSubstTerm, codeSubstAt, n5]

/-- Object-logic proof that a one-step-unfolded Surface row selects the base
entry branch when the distance guard is true. -/
def surfaceCodeSubstBodyBase {arity fuel : Nat}
    (n : STerm arity .nat) (dT kT : Term arity .nat)
    (hGuard :
      PureFamilyDerivA Surface.code.body fuel
        (.eqBool (SC.closed (.ltNat dT (n5 : Term arity .nat))) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqStabUpTo n
        (SC.closed (codeSubstTerm Surface.code.body dT kT))
        (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.baseEntry)))) := by
  have hSel := PureFamilyDerivA.iteSelectThen n
    (.ltNat dT (n5 : Term arity .nat))
    (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.baseEntry))
    (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry))
    hGuard
  simpa [surfaceCodeSubstBody_eq dT kT] using hSel

/-- Object-logic proof that a one-step-unfolded Surface row selects the
recursive-entry branch when the distance guard is false. -/
def surfaceCodeSubstBodyRecursive {arity fuel : Nat}
    (n : STerm arity .nat) (dT kT : Term arity .nat)
    (hGuard :
      PureFamilyDerivA Surface.code.body fuel
        (.eqBool (SC.closed (.ltNat dT (n5 : Term arity .nat))) (SC.b false))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqStabUpTo n
        (SC.closed (codeSubstTerm Surface.code.body dT kT))
        (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))) := by
  have hSel := PureFamilyDerivA.iteSelectElse n
    (.ltNat dT (n5 : Term arity .nat))
    (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.baseEntry))
    (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry))
    hGuard
  simpa [surfaceCodeSubstBody_eq dT kT] using hSel

def surfaceCodeRowSelectBase {arity fuel : Nat}
    (n : STerm arity .nat) (dT kT : Term arity .nat)
    (hdPure : SFormula.PureNatTerm dT) (hkPure : SFormula.PureNatTerm kT)
    (hGuard :
      PureFamilyDerivA Surface.code.body fuel
        (.eqBool (SC.closed (.ltNat dT (n5 : Term arity .nat))) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqStabUpTo n
        (SC.closed (.recCall dT kT))
        (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.baseEntry)))) :=
  pureEqStabTrans n
    (SC.closed (.recCall dT kT))
    (SC.closed (codeSubstTerm Surface.code.body dT kT))
    (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.baseEntry)))
    (surfaceCodeRowUnfold n dT kT hdPure hkPure)
    (surfaceCodeSubstBodyBase n dT kT hGuard)

def surfaceCodeRowSelectRecursive {arity fuel : Nat}
    (n : STerm arity .nat) (dT kT : Term arity .nat)
    (hdPure : SFormula.PureNatTerm dT) (hkPure : SFormula.PureNatTerm kT)
    (hGuard :
      PureFamilyDerivA Surface.code.body fuel
        (.eqBool (SC.closed (.ltNat dT (n5 : Term arity .nat))) (SC.b false))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqStabUpTo n
        (SC.closed (.recCall dT kT))
        (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))) :=
  pureEqStabTrans n
    (SC.closed (.recCall dT kT))
    (SC.closed (codeSubstTerm Surface.code.body dT kT))
    (SC.closed (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)))
    (surfaceCodeRowUnfold n dT kT hdPure hkPure)
    (surfaceCodeSubstBodyRecursive n dT kT hGuard)

def surfaceCodeBaseEntryAt {arity fuel : Nat}
    (n : STerm arity .nat) (dT kT qT : Term arity .nat)
    (hdPure : SFormula.PureNatTerm dT) (hkPure : SFormula.PureNatTerm kT)
    (hGuard :
      PureFamilyDerivA Surface.code.body fuel
        (.eqBool (SC.closed (.ltNat dT (n5 : Term arity .nat))) (SC.b true))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.recCall dT kT)) (SC.closed qT))
        (SC.closed (.stabAt
          (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.baseEntry)) qT))) := by
  let baseStab : Term arity .stab :=
    .stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.baseEntry)
  let hRow := surfaceCodeRowSelectBase n dT kT hdPure hkPure hGuard
  let hProj := PureFamilyDerivA.eqPauliProj n
    (SC.closed (.recCall dT kT)) (SC.closed baseStab) (SC.closed qT) hRow
  let hSplit :
      PureFamilyDerivA Surface.code.body fuel
        (.eqPauli (SC.closed (.stabAt baseStab qT))
          (.stabAt (SC.closed baseStab) (SC.closed qT))) :=
    PureFamilyDerivA.closedStabAtSplit (cb := Surface.code.body) (fuel := fuel) baseStab qT
  exact PureFamilyDerivA.eqPauliTrans
    (.stabAt (SC.closed (.recCall dT kT)) (SC.closed qT))
    (.stabAt (SC.closed baseStab) (SC.closed qT))
    (SC.closed (.stabAt baseStab qT))
    hProj
    (PureFamilyDerivA.eqPauliSymm
      (SC.closed (.stabAt baseStab qT))
      (.stabAt (SC.closed baseStab) (SC.closed qT))
      hSplit)

def surfaceCodeRecursiveEntryAt {arity fuel : Nat}
    (n : STerm arity .nat) (dT kT qT : Term arity .nat)
    (hdPure : SFormula.PureNatTerm dT) (hkPure : SFormula.PureNatTerm kT)
    (hGuard :
      PureFamilyDerivA Surface.code.body fuel
        (.eqBool (SC.closed (.ltNat dT (n5 : Term arity .nat))) (SC.b false))) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt (SC.closed (.recCall dT kT)) (SC.closed qT))
      (SC.closed (.stabAt
          (.stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)) qT))) := by
  let recStab : Term arity .stab :=
    .stabLam (codeSubstAt dT kT 1 SurfaceASTPublic.recursiveEntry)
  let hRow := surfaceCodeRowSelectRecursive n dT kT hdPure hkPure hGuard
  let hProj := PureFamilyDerivA.eqPauliProj n
    (SC.closed (.recCall dT kT)) (SC.closed recStab) (SC.closed qT) hRow
  let hSplit :
      PureFamilyDerivA Surface.code.body fuel
        (.eqPauli (SC.closed (.stabAt recStab qT))
          (.stabAt (SC.closed recStab) (SC.closed qT))) :=
    PureFamilyDerivA.closedStabAtSplit (cb := Surface.code.body) (fuel := fuel) recStab qT
  exact PureFamilyDerivA.eqPauliTrans
    (.stabAt (SC.closed (.recCall dT kT)) (SC.closed qT))
    (.stabAt (SC.closed recStab) (SC.closed qT))
    (SC.closed (.stabAt recStab qT))
    hProj
    (PureFamilyDerivA.eqPauliSymm
      (SC.closed (.stabAt recStab qT))
      (.stabAt (SC.closed recStab) (SC.closed qT))
      hSplit)

/-- Base odd distance (`d = 3`) exposes the direct `baseEntry` row body. -/
def surfaceCodeD3BaseEntryAt {fuel : Nat}
    (n : STerm 0 .nat) (k q : Nat) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt
          (SC.closed (Formula.codeRow (.natLit (arity := 0) (oddDistance 0))
            (.natLit (arity := 0) k)))
          (SC.n (arity := 0) q))
        (SC.closed (.stabAt
          (.stabLam (codeSubstAt (.natLit (arity := 0) (oddDistance 0))
            (.natLit (arity := 0) k) 1
            SurfaceASTPublic.baseEntry))
          (.natLit (arity := 0) q)))) := by
  simpa [Formula.codeRow, SC.n] using
    surfaceCodeBaseEntryAt n
      (.natLit (arity := 0) (oddDistance 0)) (.natLit (arity := 0) k)
      (.natLit (arity := 0) q)
      (SFormula.PureNatTerm.nat (oddDistance 0))
      (SFormula.PureNatTerm.nat k)
      (closedLtFiveTrue (fuel := fuel) oddDistance_zero_lt_five)

/-- Successor odd distances (`d >= 5`) expose the recursive shell body. -/
def surfaceCodeSuccRecursiveEntryAt {fuel : Nat}
    (m : Nat) (n : STerm 0 .nat) (k q : Nat) :
    PureFamilyDerivA Surface.code.body fuel
      (.eqPauli
        (.stabAt
          (SC.closed (Formula.codeRow (.natLit (arity := 0) (oddDistance (m + 1)))
            (.natLit (arity := 0) k)))
          (SC.n (arity := 0) q))
        (SC.closed (.stabAt
          (.stabLam (codeSubstAt (.natLit (arity := 0) (oddDistance (m + 1)))
            (.natLit (arity := 0) k) 1
            SurfaceASTPublic.recursiveEntry))
          (.natLit (arity := 0) q)))) := by
  simpa [Formula.codeRow, SC.n] using
    surfaceCodeRecursiveEntryAt n
      (.natLit (arity := 0) (oddDistance (m + 1))) (.natLit (arity := 0) k)
      (.natLit (arity := 0) q)
      (SFormula.PureNatTerm.nat (oddDistance (m + 1)))
      (SFormula.PureNatTerm.nat k)
      (closedLtFiveFalse (fuel := fuel) (oddDistance_succ_not_lt_five m))

end QHL.CodeLang.Surface.Verify
