import QStab.QHL.CodeRules

/-! # Syntactic derivations for code-level formulas

This module adds a proof-object language for `CodeLang.Formula`.  The proof
language is deliberately small:

* atomic leaves are executable checks of existing atomic formulas;
* boolean connectives have explicit proof rules;
* bounded universal formulas have explicit proof lists, one child per checked
  index, or a prefix plus the first failing child.

There is no five-qubit-specific primitive here.
-/

namespace QHL.CodeLang

namespace Formula

/-- Atomic formulas are the only direct checked leaves.  Compound formulas must
be proved with logical rule constructors. -/
inductive Atomic : {arity : Nat} -> Formula arity -> Type where
  | eqNat {arity : Nat} (a b : Term arity .nat) :
      Atomic (.eqNat a b)
  | eqBool {arity : Nat} (a b : Term arity .bool) :
      Atomic (.eqBool a b)
  | eqPauli {arity : Nat} (a b : Term arity .pauli) :
      Atomic (.eqPauli a b)
  | eqStabUpTo {arity : Nat}
      (n : Term arity .nat) (a b : Term arity .stab) :
      Atomic (.eqStabUpTo n a b)
  | commutesUpTo {arity : Nat}
      (n : Term arity .nat) (a b : Term arity .stab) :
      Atomic (.commutesUpTo n a b)
  | weightLe {arity : Nat}
      (n : Term arity .nat) (a : Term arity .stab) (w : Term arity .nat) :
      Atomic (.weightLe n a w)

mutual

/-- Syntactic derivations of a formula's Boolean value.

`Deriv A true` proves `A`; `Deriv A false` proves that `A` evaluates to false.
The false judgment is needed for implication and for finding the first failing
case of a bounded universal. -/
inductive Deriv : {arity : Nat} -> Formula arity -> Bool -> Type where
  | top : Deriv .top true
  | bot : Deriv .bot false
  | atom {arity : Nat} {A : Formula arity} (kind : Atomic A) (b : Bool) :
      Deriv A b
  | andTrue {arity : Nat} {A B : Formula arity} :
      Deriv A true -> Deriv B true -> Deriv (.and A B) true
  | andFalseLeft {arity : Nat} {A B : Formula arity} :
      Deriv A false -> Deriv (.and A B) false
  | andFalseRight {arity : Nat} {A B : Formula arity} :
      Deriv A true -> Deriv B false -> Deriv (.and A B) false
  | andElimLeft {arity : Nat} {A B : Formula arity} :
      Deriv (.and A B) true -> Deriv A true
  | andElimRight {arity : Nat} {A B : Formula arity} :
      Deriv (.and A B) true -> Deriv B true
  | orTrueLeft {arity : Nat} {A B : Formula arity} :
      Deriv A true -> Deriv (.or A B) true
  | orTrueRight {arity : Nat} {A B : Formula arity} :
      Deriv A false -> Deriv B true -> Deriv (.or A B) true
  | orFalse {arity : Nat} {A B : Formula arity} :
      Deriv A false -> Deriv B false -> Deriv (.or A B) false
  | notTrue {arity : Nat} {A : Formula arity} :
      Deriv A false -> Deriv (.not A) true
  | notFalse {arity : Nat} {A : Formula arity} :
      Deriv A true -> Deriv (.not A) false
  | impTrueByFalse {arity : Nat} {A B : Formula arity} :
      Deriv A false -> Deriv (.imp A B) true
  | impTrue {arity : Nat} {A B : Formula arity} :
      Deriv A true -> Deriv B true -> Deriv (.imp A B) true
  | impFalse {arity : Nat} {A B : Formula arity} :
      Deriv A true -> Deriv B false -> Deriv (.imp A B) false
  | mp {arity : Nat} {A B : Formula arity} :
      Deriv (.imp A B) true -> Deriv A true -> Deriv B true
  | applyNat {arity : Nat} {A : Formula (arity + 1)} {b : Bool}
      (witness : Term arity .nat) :
      Deriv A b -> Deriv (.applyNat witness A) b
  | allNatLtTrue {arity : Nat}
      (n : Term arity .nat) (A : Formula (arity + 1))
      (children : DerivList A true) :
      Deriv (.allNatLt n A) true
  | allNatLtFalse {arity : Nat}
      (n : Term arity .nat) (A : Formula (arity + 1))
      (goodPrefix : DerivList A true) (bad : Deriv A false) :
      Deriv (.allNatLt n A) false

/-- First-class lists of derivations.  This avoids Lean's nested-inductive
restriction for `List (Deriv A b)` in the `Deriv` constructors. -/
inductive DerivList : {arity : Nat} -> Formula arity -> Bool -> Type where
  | nil {arity : Nat} {A : Formula arity} {b : Bool} : DerivList A b
  | cons {arity : Nat} {A : Formula arity} {b : Bool} :
      Deriv A b -> DerivList A b -> DerivList A b

end

namespace DerivList

def length {arity : Nat} {A : Formula (arity + 1)} {b : Bool} :
    DerivList A b -> Nat
  | .nil => 0
  | .cons _ rest => rest.length + 1

def snoc {arity : Nat} {A : Formula (arity + 1)} {b : Bool}
    (xs : DerivList A b) (x : Deriv A b) : DerivList A b :=
  match xs with
  | .nil => .cons x .nil
  | .cons y ys => .cons y (ys.snoc x)

end DerivList

namespace Deriv

mutual

def checkList {arity : Nat} {A : Formula (arity + 1)} {b : Bool}
    (codeBody : Term 2 .stab) (fuel : Nat) (rho : Env arity)
    (xs : DerivList A b) (start : Nat) : Bool :=
  match xs with
  | .nil => true
  | .cons D rest =>
      D.check codeBody fuel (Env.cons start rho) &&
        checkList codeBody fuel rho rest (start + 1)

/-- Executable verifier for a syntactic derivation tree. -/
def check {arity : Nat} {A : Formula arity} {b : Bool}
    (D : Deriv A b) (codeBody : Term 2 .stab) (fuel : Nat)
    (rho : Env arity) : Bool :=
  match D with
  | .top => true
  | .bot => true
  | .atom _ expected =>
      match A.eval codeBody fuel rho with
      | some actual => decide (actual = expected)
      | none => false
  | .andTrue left right =>
      left.check codeBody fuel rho && right.check codeBody fuel rho
  | .andFalseLeft left =>
      left.check codeBody fuel rho
  | .andFalseRight left right =>
      left.check codeBody fuel rho && right.check codeBody fuel rho
  | .andElimLeft child =>
      child.check codeBody fuel rho
  | .andElimRight child =>
      child.check codeBody fuel rho
  | .orTrueLeft left =>
      left.check codeBody fuel rho
  | .orTrueRight left right =>
      left.check codeBody fuel rho && right.check codeBody fuel rho
  | .orFalse left right =>
      left.check codeBody fuel rho && right.check codeBody fuel rho
  | .notTrue child =>
      child.check codeBody fuel rho
  | .notFalse child =>
      child.check codeBody fuel rho
  | .impTrueByFalse antecedent =>
      antecedent.check codeBody fuel rho
  | .impTrue antecedent consequent =>
      antecedent.check codeBody fuel rho && consequent.check codeBody fuel rho
  | .impFalse antecedent consequent =>
      antecedent.check codeBody fuel rho && consequent.check codeBody fuel rho
  | .mp implication antecedent =>
      implication.check codeBody fuel rho && antecedent.check codeBody fuel rho
  | .applyNat witness child =>
      match Term.eval codeBody fuel witness rho with
      | some wv => child.check codeBody fuel (Env.cons wv rho)
      | none => false
  | .allNatLtTrue n _ children =>
      match Term.eval codeBody fuel n rho with
      | some bound =>
          decide (children.length = bound) &&
            checkList codeBody fuel rho children 0
      | none => false
  | .allNatLtFalse n _ goodPrefix bad =>
      match Term.eval codeBody fuel n rho with
      | some bound =>
          decide (goodPrefix.length < bound) &&
            checkList codeBody fuel rho goodPrefix 0 &&
            bad.check codeBody fuel (Env.cons goodPrefix.length rho)
      | none => false

end

mutual

def sizeList {arity : Nat} {A : Formula (arity + 1)} {b : Bool} :
    DerivList A b -> Nat
  | .nil => 0
  | .cons D rest => size D + sizeList rest

/-- Size of the derivation tree. -/
def size : {arity : Nat} -> {A : Formula arity} -> {b : Bool} ->
    Deriv A b -> Nat
  | _, _, _, .top => 1
  | _, _, _, .bot => 1
  | _, _, _, .atom _ _ => 1
  | _, _, _, .andTrue left right => 1 + size left + size right
  | _, _, _, .andFalseLeft left => 1 + size left
  | _, _, _, .andFalseRight left right => 1 + size left + size right
  | _, _, _, .andElimLeft child => 1 + size child
  | _, _, _, .andElimRight child => 1 + size child
  | _, _, _, .orTrueLeft left => 1 + size left
  | _, _, _, .orTrueRight left right => 1 + size left + size right
  | _, _, _, .orFalse left right => 1 + size left + size right
  | _, _, _, .notTrue child => 1 + size child
  | _, _, _, .notFalse child => 1 + size child
  | _, _, _, .impTrueByFalse antecedent => 1 + size antecedent
  | _, _, _, .impTrue antecedent consequent => 1 + size antecedent + size consequent
  | _, _, _, .impFalse antecedent consequent => 1 + size antecedent + size consequent
  | _, _, _, .mp implication antecedent => 1 + size implication + size antecedent
  | _, _, _, .applyNat _ child => 1 + size child
  | _, _, _, .allNatLtTrue _ _ children => 1 + sizeList children
  | _, _, _, .allNatLtFalse _ _ goodPrefix bad => 1 + sizeList goodPrefix + size bad

end

end Deriv

/-- Result type for building a bounded universal derivation. -/
inductive AllNatLtBuildResult {arity : Nat} (A : Formula (arity + 1)) where
  | allTrue (children : DerivList A true) : AllNatLtBuildResult A
  | firstFalse (goodPrefix : DerivList A true) (bad : Deriv A false) :
      AllNatLtBuildResult A

namespace AllNatLtBuildResult

def toDeriv {arity : Nat} {n : Term arity .nat} {A : Formula (arity + 1)} :
    AllNatLtBuildResult A -> Sigma (fun b : Bool => Deriv (.allNatLt n A) b)
  | .allTrue children => ⟨true, .allNatLtTrue n A children⟩
  | .firstFalse goodPrefix bad => ⟨false, .allNatLtFalse n A goodPrefix bad⟩

end AllNatLtBuildResult

mutual

/-- Small proof search for the syntactic derivation language.

The returned tree is not trusted by construction; clients must run
`Deriv.check` to verify every rule and atomic leaf. -/
partial def derive? {arity : Nat} (codeBody : Term 2 .stab) (fuel : Nat)
    (rho : Env arity) : (A : Formula arity) ->
      Option (Sigma (fun b : Bool => Deriv A b))
  | .top => some ⟨true, .top⟩
  | .bot => some ⟨false, .bot⟩
  | .eqNat a b =>
      match Formula.eval codeBody fuel (.eqNat a b) rho with
      | some expected => some ⟨expected, .atom (.eqNat a b) expected⟩
      | none => none
  | .eqBool a b =>
      match Formula.eval codeBody fuel (.eqBool a b) rho with
      | some expected => some ⟨expected, .atom (.eqBool a b) expected⟩
      | none => none
  | .eqPauli a b =>
      match Formula.eval codeBody fuel (.eqPauli a b) rho with
      | some expected => some ⟨expected, .atom (.eqPauli a b) expected⟩
      | none => none
  | .eqStabUpTo n a b =>
      match Formula.eval codeBody fuel (.eqStabUpTo n a b) rho with
      | some expected => some ⟨expected, .atom (.eqStabUpTo n a b) expected⟩
      | none => none
  | .commutesUpTo n a b =>
      match Formula.eval codeBody fuel (.commutesUpTo n a b) rho with
      | some expected => some ⟨expected, .atom (.commutesUpTo n a b) expected⟩
      | none => none
  | .weightLe n a w =>
      match Formula.eval codeBody fuel (.weightLe n a w) rho with
      | some expected => some ⟨expected, .atom (.weightLe n a w) expected⟩
      | none => none
  | .and A B => do
      let ⟨a, DA⟩ <- derive? codeBody fuel rho A
      match a with
      | false => some ⟨false, .andFalseLeft DA⟩
      | true =>
          let ⟨b, DB⟩ <- derive? codeBody fuel rho B
          match b with
          | true => some ⟨true, .andTrue DA DB⟩
          | false => some ⟨false, .andFalseRight DA DB⟩
  | .or A B => do
      let ⟨a, DA⟩ <- derive? codeBody fuel rho A
      match a with
      | true => some ⟨true, .orTrueLeft DA⟩
      | false =>
          let ⟨b, DB⟩ <- derive? codeBody fuel rho B
          match b with
          | true => some ⟨true, .orTrueRight DA DB⟩
          | false => some ⟨false, .orFalse DA DB⟩
  | .not A => do
      let ⟨a, DA⟩ <- derive? codeBody fuel rho A
      match a with
      | true => some ⟨false, .notFalse DA⟩
      | false => some ⟨true, .notTrue DA⟩
  | .imp A B => do
      let ⟨a, DA⟩ <- derive? codeBody fuel rho A
      match a with
      | false => some ⟨true, .impTrueByFalse DA⟩
      | true =>
          let ⟨b, DB⟩ <- derive? codeBody fuel rho B
          match b with
          | true => some ⟨true, .impTrue DA DB⟩
          | false => some ⟨false, .impFalse DA DB⟩
  | .applyNat witness A => do
      let wv <- Term.eval codeBody fuel witness rho
      let ⟨b, D⟩ <- derive? codeBody fuel (Env.cons wv rho) A
      some ⟨b, .applyNat witness D⟩
  | .allNatLt n A =>
      match Term.eval codeBody fuel n rho with
      | none => none
      | some bound => do
          let result <- deriveAllNatLt? codeBody fuel rho A bound
          some (AllNatLtBuildResult.toDeriv (n := n) result)
  | .existsNatLt _ _ =>
      none

/-- Build the derivation of a bounded universal in the same order as
`allNatLt`: first all smaller entries, then the last entry. -/
partial def deriveAllNatLt? {arity : Nat} (codeBody : Term 2 .stab)
    (fuel : Nat) (rho : Env arity) (A : Formula (arity + 1)) :
    Nat -> Option (AllNatLtBuildResult A)
  | 0 => some (.allTrue .nil)
  | bound + 1 => do
      let previous <- deriveAllNatLt? codeBody fuel rho A bound
      match previous with
      | .firstFalse goodPrefix bad => some (.firstFalse goodPrefix bad)
      | .allTrue goodPrefix =>
          let ⟨b, D⟩ <- derive? codeBody fuel (Env.cons bound rho) A
          match b with
          | true => some (.allTrue (goodPrefix.snoc D))
          | false => some (.firstFalse goodPrefix D)

end

/-- Extract a true derivation from proof search. -/
def deriveTrue? {arity : Nat} (codeBody : Term 2 .stab) (fuel : Nat)
    (rho : Env arity) (A : Formula arity) : Option (Deriv A true) := do
  let ⟨b, D⟩ <- derive? codeBody fuel rho A
  match b with
  | true => some D
  | false => none

/-! ## Object-level induction schemas -/

/-- Standard natural-number induction from `1`.

The step consumes the already-built object-language derivation of `P(n)` and
returns an object-language derivation of `P(n+1)`.  This is the usual induction
rule as proof data; Lean is not asked to prove `forall n, P n` directly, and
the step is not a closed semantic implication discharged elsewhere.
-/
structure NatOneInductionDerivation (motive : Nat -> Formula 0) where
  base : Deriv (motive 1) true
  step : (n : Nat) -> Deriv (motive n) true -> Option (Deriv (motive (n + 1)) true)

namespace NatOneInductionDerivation

/-- Instantiate an induction derivation at distance `offset + 1`. -/
def instantiate? {motive : Nat -> Formula 0}
    (D : NatOneInductionDerivation motive) :
    (offset : Nat) -> Option (Deriv (motive (offset + 1)) true)
  | 0 => some D.base
  | offset + 1 => do
      let prev <- D.instantiate? offset
      D.step (offset + 1) prev

def checkAt {motive : Nat -> Formula 0}
    (D : NatOneInductionDerivation motive)
    (codeBody : Term 2 .stab) (fuel offset : Nat) : Bool :=
  match D.instantiate? offset with
  | some proof => proof.check codeBody fuel Env.empty
  | none => false

def instantiatedSize? {motive : Nat -> Formula 0}
    (D : NatOneInductionDerivation motive) (offset : Nat) : Option Nat :=
  match D.instantiate? offset with
  | some proof => some proof.size
  | none => none

end NatOneInductionDerivation

/-- Standard natural-number induction from `0`.

This is useful for parametric families whose first nontrivial member is
encoded by an index, e.g. odd Surface distances `d = 2*m + 3`.
-/
structure NatZeroInductionDerivation (motive : Nat -> Formula 0) where
  base : Deriv (motive 0) true
  step : (n : Nat) -> Deriv (motive n) true -> Option (Deriv (motive (n + 1)) true)

namespace NatZeroInductionDerivation

/-- Instantiate a zero-based induction derivation at index `target`. -/
def instantiate? {motive : Nat -> Formula 0}
    (D : NatZeroInductionDerivation motive) :
    (target : Nat) -> Option (Deriv (motive target) true)
  | 0 => some D.base
  | target + 1 => do
      let prev <- D.instantiate? target
      D.step target prev

def checkAt {motive : Nat -> Formula 0}
    (D : NatZeroInductionDerivation motive)
    (codeBody : Term 2 .stab) (fuel target : Nat) : Bool :=
  match D.instantiate? target with
  | some proof => proof.check codeBody fuel Env.empty
  | none => false

def instantiatedSize? {motive : Nat -> Formula 0}
    (D : NatZeroInductionDerivation motive) (target : Nat) : Option Nat :=
  match D.instantiate? target with
  | some proof => some proof.size
  | none => none

end NatZeroInductionDerivation

end Formula

#print axioms Formula.Deriv.check
#print axioms Formula.deriveTrue?
#print axioms Formula.NatOneInductionDerivation.instantiate?
#print axioms Formula.NatZeroInductionDerivation.instantiate?

end QHL.CodeLang
