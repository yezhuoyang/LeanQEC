import QStab.PauliOps

/-! # A small functional language for QEC code families

This module is the code-level language below QStab.  It has no states, no
faults, and no measurement commands.  It is just a typed, OCaml-style expression
language for indexed Pauli strings.

The raw evaluator is deliberately partial: recursive calls consume explicit
fuel, and fuel exhaustion returns `none`.  There is no identity fallback.  A
total stabilizer can be extracted only with a proof that every queried Pauli
entry evaluates to `some p`.
-/

namespace QHL.CodeLang

/-- A stabilizer/Pauli string before choosing a finite block length. -/
abbrev Stabilizer := Nat -> Pauli

/-- A partial stabilizer produced by the raw evaluator. -/
abbrev PartialStabilizer := Nat -> Option Pauli

def identityStabilizer : Stabilizer := fun _ => Pauli.I

def partialIdentityStabilizer : PartialStabilizer := fun _ => some Pauli.I

def partialStabilizerMul (A B : PartialStabilizer) : PartialStabilizer :=
  fun q => do
    let av <- A q
    let bv <- B q
    some (Pauli.mul av bv)

def partialStabilizerFold : Nat -> (Nat -> PartialStabilizer) -> PartialStabilizer
  | 0, _ => partialIdentityStabilizer
  | n + 1, body => partialStabilizerMul (partialStabilizerFold n body) (body n)

/-- The small value language.  Higher-level QEC notions are derived from these
    sorts, not added as primitives. -/
inductive Ty where
  | nat
  | bool
  | pauli
  | stab
  deriving DecidableEq, Repr

namespace Ty

/-- Total mathematical denotation. -/
abbrev denote : Ty -> Type
  | .nat => Nat
  | .bool => Bool
  | .pauli => Pauli
  | .stab => Stabilizer

/-- Raw executable denotation.  Stabilizers are partial until termination is
    established for every queried entry. -/
abbrev partialDenote : Ty -> Type
  | .nat => Nat
  | .bool => Bool
  | .pauli => Pauli
  | .stab => PartialStabilizer

end Ty

/-- A first-order environment of natural-number variables. -/
abbrev Env (arity : Nat) := Fin arity -> Nat

namespace Env

def empty : Env 0 := fun i => nomatch i

def cons {arity : Nat} (x : Nat) (rho : Env arity) : Env (arity + 1)
  | ⟨0, _⟩ => x
  | ⟨n + 1, h⟩ => rho ⟨n, Nat.lt_of_succ_lt_succ h⟩

/-- Code-function environment: variable 0 is `k`, variable 1 is `d`. -/
def code (d k : Nat) : Env 2 :=
  cons k (cons d empty)

end Env

/-- Terms of the tiny functional language.

`recCall d k` is the only recursive-code primitive.  It denotes the same code
family at parameters `(d,k)`, returning a partial stabilizer closure. -/
inductive Term : Nat -> Ty -> Type where
  | var {arity : Nat} : Fin arity -> Term arity .nat
  | natLit {arity : Nat} : Nat -> Term arity .nat
  | boolLit {arity : Nat} : Bool -> Term arity .bool
  | pauliLit {arity : Nat} : Pauli -> Term arity .pauli
  | add {arity : Nat} : Term arity .nat -> Term arity .nat -> Term arity .nat
  | sub {arity : Nat} : Term arity .nat -> Term arity .nat -> Term arity .nat
  | mul {arity : Nat} : Term arity .nat -> Term arity .nat -> Term arity .nat
  | div {arity : Nat} : Term arity .nat -> Term arity .nat -> Term arity .nat
  | mod {arity : Nat} : Term arity .nat -> Term arity .nat -> Term arity .nat
  | eqNat {arity : Nat} : Term arity .nat -> Term arity .nat -> Term arity .bool
  | ltNat {arity : Nat} : Term arity .nat -> Term arity .nat -> Term arity .bool
  | leNat {arity : Nat} : Term arity .nat -> Term arity .nat -> Term arity .bool
  | not {arity : Nat} : Term arity .bool -> Term arity .bool
  | and {arity : Nat} : Term arity .bool -> Term arity .bool -> Term arity .bool
  | or {arity : Nat} : Term arity .bool -> Term arity .bool -> Term arity .bool
  | ite {arity : Nat} : Term arity .bool -> Term arity ty -> Term arity ty ->
      Term arity ty
  | pauliMul {arity : Nat} : Term arity .pauli -> Term arity .pauli ->
      Term arity .pauli
  | anticommutes {arity : Nat} : Term arity .pauli -> Term arity .pauli ->
      Term arity .bool
  | stabLam {arity : Nat} : Term (arity + 1) .pauli -> Term arity .stab
  | stabAt {arity : Nat} : Term arity .stab -> Term arity .nat -> Term arity .pauli
  | stabFold {arity : Nat} : Term arity .nat -> Term (arity + 1) .stab ->
      Term arity .stab
  | recCall {arity : Nat} : Term arity .nat -> Term arity .nat -> Term arity .stab

namespace Term

def sizeOfTerm {arity : Nat} {ty : Ty} : Term arity ty -> Nat
  | .var _ => 1
  | .natLit _ => 1
  | .boolLit _ => 1
  | .pauliLit _ => 1
  | .add a b => 1 + sizeOfTerm a + sizeOfTerm b
  | .sub a b => 1 + sizeOfTerm a + sizeOfTerm b
  | .mul a b => 1 + sizeOfTerm a + sizeOfTerm b
  | .div a b => 1 + sizeOfTerm a + sizeOfTerm b
  | .mod a b => 1 + sizeOfTerm a + sizeOfTerm b
  | .eqNat a b => 1 + sizeOfTerm a + sizeOfTerm b
  | .ltNat a b => 1 + sizeOfTerm a + sizeOfTerm b
  | .leNat a b => 1 + sizeOfTerm a + sizeOfTerm b
  | .not a => 1 + sizeOfTerm a
  | .and a b => 1 + sizeOfTerm a + sizeOfTerm b
  | .or a b => 1 + sizeOfTerm a + sizeOfTerm b
  | .ite c t e => 1 + sizeOfTerm c + sizeOfTerm t + sizeOfTerm e
  | .pauliMul a b => 1 + sizeOfTerm a + sizeOfTerm b
  | .anticommutes a b => 1 + sizeOfTerm a + sizeOfTerm b
  | .stabLam entry => 1 + sizeOfTerm entry
  | .stabAt s q => 1 + sizeOfTerm s + sizeOfTerm q
  | .stabFold n body => 1 + sizeOfTerm n + sizeOfTerm body
  | .recCall d k => 1 + sizeOfTerm d + sizeOfTerm k

/-- Executable big-step semantics with explicit recursion fuel. -/
def eval (codeBody : Term 2 .stab) :
    (fuel : Nat) -> {arity : Nat} -> {ty : Ty} ->
      Term arity ty -> Env arity -> Option ty.partialDenote
  | _, _, _, .var v, rho => some (rho v)
  | _, _, _, .natLit n, _ => some n
  | _, _, _, .boolLit b, _ => some b
  | _, _, _, .pauliLit p, _ => some p
  | fuel, _, _, .add a b, rho => do
      let av <- eval codeBody fuel a rho
      let bv <- eval codeBody fuel b rho
      some (av + bv)
  | fuel, _, _, .sub a b, rho => do
      let av <- eval codeBody fuel a rho
      let bv <- eval codeBody fuel b rho
      some (av - bv)
  | fuel, _, _, .mul a b, rho => do
      let av <- eval codeBody fuel a rho
      let bv <- eval codeBody fuel b rho
      some (av * bv)
  | fuel, _, _, .div a b, rho => do
      let av <- eval codeBody fuel a rho
      let bv <- eval codeBody fuel b rho
      some (av / bv)
  | fuel, _, _, .mod a b, rho => do
      let av <- eval codeBody fuel a rho
      let bv <- eval codeBody fuel b rho
      some (av % bv)
  | fuel, _, _, .eqNat a b, rho => do
      let av <- eval codeBody fuel a rho
      let bv <- eval codeBody fuel b rho
      some (decide (av = bv))
  | fuel, _, _, .ltNat a b, rho => do
      let av <- eval codeBody fuel a rho
      let bv <- eval codeBody fuel b rho
      some (decide (av < bv))
  | fuel, _, _, .leNat a b, rho => do
      let av <- eval codeBody fuel a rho
      let bv <- eval codeBody fuel b rho
      some (decide (av <= bv))
  | fuel, _, _, .not a, rho => do
      let av <- eval codeBody fuel a rho
      some (!av)
  | fuel, _, _, .and a b, rho => do
      let av <- eval codeBody fuel a rho
      if av then eval codeBody fuel b rho else some false
  | fuel, _, _, .or a b, rho => do
      let av <- eval codeBody fuel a rho
      if av then some true else eval codeBody fuel b rho
  | fuel, _, _, .ite c t e, rho => do
      let cv <- eval codeBody fuel c rho
      if cv then eval codeBody fuel t rho else eval codeBody fuel e rho
  | fuel, _, _, .pauliMul a b, rho => do
      let av <- eval codeBody fuel a rho
      let bv <- eval codeBody fuel b rho
      some (Pauli.mul av bv)
  | fuel, _, _, .anticommutes a b, rho => do
      let av <- eval codeBody fuel a rho
      let bv <- eval codeBody fuel b rho
      some (ErrorVec.Pauli.anticommutes av bv)
  | fuel, _, _, .stabLam entry, rho =>
      some (fun q => eval codeBody fuel entry (Env.cons q rho))
  | fuel, _, _, .stabAt s q, rho => do
      let sv <- eval codeBody fuel s rho
      let qv <- eval codeBody fuel q rho
      sv qv
  | fuel, _, _, .stabFold n body, rho => do
      let nv <- eval codeBody fuel n rho
      some <| partialStabilizerFold nv fun i =>
        match eval codeBody fuel body (Env.cons i rho) with
        | some row => row
        | none => fun _ => none
  | 0, _, _, .recCall _ _, _ =>
      none
  | fuel + 1, _, _, .recCall d k, rho => do
      let dv <- eval codeBody fuel d rho
      let kv <- eval codeBody fuel k rho
      eval codeBody fuel codeBody (Env.code dv kv)
termination_by fuel _ _ term _ => (fuel, sizeOfTerm term)
decreasing_by
  all_goals
    simp_wf
    simp [sizeOfTerm]
    omega

end Term

namespace C

abbrev N (arity : Nat) := Term arity .nat
abbrev B (arity : Nat) := Term arity .bool
abbrev P (arity : Nat) := Term arity .pauli
abbrev S (arity : Nat) := Term arity .stab

def n {arity : Nat} (x : Nat) : N arity := .natLit x
def b {arity : Nat} (x : Bool) : B arity := .boolLit x
def p {arity : Nat} (x : Pauli) : P arity := .pauliLit x

def zero {arity : Nat} : N arity := n 0
def one {arity : Nat} : N arity := n 1
def two {arity : Nat} : N arity := n 2

def add {arity : Nat} : N arity -> N arity -> N arity := .add
def sub {arity : Nat} : N arity -> N arity -> N arity := .sub
def mul {arity : Nat} : N arity -> N arity -> N arity := .mul
def div {arity : Nat} : N arity -> N arity -> N arity := .div
def mod {arity : Nat} : N arity -> N arity -> N arity := .mod
def eq {arity : Nat} : N arity -> N arity -> B arity := .eqNat
def lt {arity : Nat} : N arity -> N arity -> B arity := .ltNat
def le {arity : Nat} : N arity -> N arity -> B arity := .leNat
def band {arity : Nat} : B arity -> B arity -> B arity := .and
def bor {arity : Nat} : B arity -> B arity -> B arity := .or
def bnot {arity : Nat} : B arity -> B arity := .not
def ite {arity : Nat} {ty : Ty} : B arity -> Term arity ty -> Term arity ty ->
    Term arity ty := .ite

namespace Code

/-- Inside a code body, variable 0 is `k` and variable 1 is `d`. -/
def k : N 2 := .var ⟨0, by decide⟩
def d : N 2 := .var ⟨1, by decide⟩

end Code

namespace Entry

/-- Inside a stabilizer lambda, variable 0 is `q`, variable 1 is `k`,
    and variable 2 is `d`. -/
def q : N 3 := .var ⟨0, by decide⟩
def k : N 3 := .var ⟨1, by decide⟩
def d : N 3 := .var ⟨2, by decide⟩

end Entry

end C

/-- A recursive code family of type `Nat -> Nat -> Stabilizer`. -/
structure CodeFn where
  body : Term 2 .stab

namespace CodeFn

def fuelForDistance (d : Nat) : Nat := d + 1

def evalStabilizer? (F : CodeFn) (fuel d k : Nat) : Option PartialStabilizer :=
  Term.eval F.body fuel F.body (Env.code d k)

def evalEntry? (F : CodeFn) (fuel d k q : Nat) : Option Pauli := do
  let row <- F.evalStabilizer? fuel d k
  row q

def evalAt? (F : CodeFn) (d k q : Nat) : Option Pauli :=
  F.evalEntry? (fuelForDistance d) d k q

def TerminatesEntry (F : CodeFn) (fuel d k q : Nat) : Prop :=
  exists p : Pauli, F.evalEntry? fuel d k q = some p

def TerminatesStabilizer (F : CodeFn) (fuel d k : Nat) : Prop :=
  forall q : Nat, F.TerminatesEntry fuel d k q

/-- A computational witness for one evaluated Pauli entry. -/
abbrev EntryResult (F : CodeFn) (fuel d k q : Nat) : Type :=
  {p : Pauli // F.evalEntry? fuel d k q = some p}

/-- A computational witness for a total evaluated stabilizer. -/
abbrev StabilizerResult (F : CodeFn) (fuel d k : Nat) : Type :=
  forall q : Nat, F.EntryResult fuel d k q

/-- Extract one total Pauli entry from the raw semantics. -/
def evalEntry (F : CodeFn) (fuel d k q : Nat)
    (h : F.EntryResult fuel d k q) : Pauli :=
  h.val

theorem evalEntry_spec (F : CodeFn) (fuel d k q : Nat)
    (h : F.EntryResult fuel d k q) :
    F.evalEntry? fuel d k q = some (F.evalEntry fuel d k q h) := by
  exact h.property

/-- Extract a total stabilizer from the raw semantics. -/
def evalStabilizer (F : CodeFn) (fuel d k : Nat)
    (h : F.StabilizerResult fuel d k) : Stabilizer :=
  fun q => F.evalEntry fuel d k q (h q)

theorem evalStabilizer_spec (F : CodeFn) (fuel d k q : Nat)
    (h : F.StabilizerResult fuel d k) :
    F.evalEntry? fuel d k q = some (F.evalStabilizer fuel d k h q) :=
  F.evalEntry_spec fuel d k q (h q)

end CodeFn

/-! ## Finite assertion formulas over code families -/

def allNatLt (n : Nat) (pred : Nat -> Option Bool) : Option Bool :=
  match n with
  | 0 => some true
  | m + 1 => do
      let ok <- allNatLt m pred
      if ok then pred m else some false

def existsNatLt (n : Nat) (pred : Nat -> Option Bool) : Option Bool :=
  match n with
  | 0 => some false
  | m + 1 => do
      let ok <- existsNatLt m pred
      if ok then some true else pred m

def stabEqUpTo : Nat -> PartialStabilizer -> PartialStabilizer -> Option Bool
  | 0, _, _ => some true
  | n + 1, a, b => do
      let ok <- stabEqUpTo n a b
      if ok then
        let av <- a n
        let bv <- b n
        some (decide (av = bv))
      else
        some false

def parityUpTo : Nat -> PartialStabilizer -> PartialStabilizer -> Option Bool
  | 0, _, _ => some false
  | n + 1, a, b => do
      let rest <- parityUpTo n a b
      let av <- a n
      let bv <- b n
      some (xor rest (ErrorVec.Pauli.anticommutes av bv))

def weightUpTo : Nat -> PartialStabilizer -> Option Nat
  | 0, _ => some 0
  | n + 1, a => do
      let rest <- weightUpTo n a
      let av <- a n
      some (if av = Pauli.I then rest else rest + 1)

/-- Boolean assertion language for finite code-level obligations. -/
inductive Formula : Nat -> Type where
  | top {arity : Nat} : Formula arity
  | bot {arity : Nat} : Formula arity
  | eqNat {arity : Nat} : Term arity .nat -> Term arity .nat -> Formula arity
  | eqBool {arity : Nat} : Term arity .bool -> Term arity .bool -> Formula arity
  | eqPauli {arity : Nat} : Term arity .pauli -> Term arity .pauli -> Formula arity
  | eqStabUpTo {arity : Nat} : Term arity .nat -> Term arity .stab -> Term arity .stab ->
      Formula arity
  | commutesUpTo {arity : Nat} : Term arity .nat -> Term arity .stab -> Term arity .stab ->
      Formula arity
  | weightLe {arity : Nat} : Term arity .nat -> Term arity .stab -> Term arity .nat ->
      Formula arity
  | and {arity : Nat} : Formula arity -> Formula arity -> Formula arity
  | or {arity : Nat} : Formula arity -> Formula arity -> Formula arity
  | not {arity : Nat} : Formula arity -> Formula arity
  | imp {arity : Nat} : Formula arity -> Formula arity -> Formula arity
  | applyNat {arity : Nat} : Term arity .nat -> Formula (arity + 1) -> Formula arity
  | allNatLt {arity : Nat} : Term arity .nat -> Formula (arity + 1) -> Formula arity
  | existsNatLt {arity : Nat} : Term arity .nat -> Formula (arity + 1) -> Formula arity

namespace Formula

/-- Executable semantics of code-level assertions.  A failed term evaluation
    makes the whole assertion fail with `none`, rather than silently succeeding. -/
def eval (codeBody : Term 2 .stab) (fuel : Nat) :
    {arity : Nat} -> Formula arity -> Env arity -> Option Bool
  | _, .top, _ => some true
  | _, .bot, _ => some false
  | _, .eqNat a b, rho => do
      let av <- Term.eval codeBody fuel a rho
      let bv <- Term.eval codeBody fuel b rho
      some (decide (av = bv))
  | _, .eqBool a b, rho => do
      let av <- Term.eval codeBody fuel a rho
      let bv <- Term.eval codeBody fuel b rho
      some (decide (av = bv))
  | _, .eqPauli a b, rho => do
      let av <- Term.eval codeBody fuel a rho
      let bv <- Term.eval codeBody fuel b rho
      some (decide (av = bv))
  | _, .eqStabUpTo n a b, rho => do
      let nv <- Term.eval codeBody fuel n rho
      let av <- Term.eval codeBody fuel a rho
      let bv <- Term.eval codeBody fuel b rho
      stabEqUpTo nv av bv
  | _, .commutesUpTo n a b, rho => do
      let nv <- Term.eval codeBody fuel n rho
      let av <- Term.eval codeBody fuel a rho
      let bv <- Term.eval codeBody fuel b rho
      let parity <- parityUpTo nv av bv
      some (!parity)
  | _, .weightLe n a w, rho => do
      let nv <- Term.eval codeBody fuel n rho
      let av <- Term.eval codeBody fuel a rho
      let wv <- Term.eval codeBody fuel w rho
      let weight <- weightUpTo nv av
      some (decide (weight <= wv))
  | _, .and A B, rho => do
      let av <- eval codeBody fuel A rho
      if av then eval codeBody fuel B rho else some false
  | _, .or A B, rho => do
      let av <- eval codeBody fuel A rho
      if av then some true else eval codeBody fuel B rho
  | _, .not A, rho => do
      let av <- eval codeBody fuel A rho
      some (!av)
  | _, .imp A B, rho => do
      let av <- eval codeBody fuel A rho
      if av then eval codeBody fuel B rho else some true
  | _, .applyNat witness A, rho => do
      let wv <- Term.eval codeBody fuel witness rho
      eval codeBody fuel A (Env.cons wv rho)
  | _, .allNatLt n A, rho => do
      let nv <- Term.eval codeBody fuel n rho
      QHL.CodeLang.allNatLt nv fun x => eval codeBody fuel A (Env.cons x rho)
  | _, .existsNatLt n A, rho => do
      let nv <- Term.eval codeBody fuel n rho
      QHL.CodeLang.existsNatLt nv fun x => eval codeBody fuel A (Env.cons x rho)

end Formula

/-! ## Smoke examples for the executable semantics -/

def identityCode : CodeFn where
  body := .stabLam (.pauliLit Pauli.I)

/-- info: some (Pauli.I) -/
#guard_msgs in
#eval identityCode.evalEntry? 0 7 11 5

/-- info: some (Pauli.I) -/
#guard_msgs in
#eval identityCode.evalEntry? 10 7 11 5

def oneQubitXCode : CodeFn where
  body := .stabLam <|
    .ite (.eqNat C.Entry.q C.zero) (.pauliLit Pauli.X) (.pauliLit Pauli.I)

/-- info: some (Pauli.X) -/
#guard_msgs in
#eval oneQubitXCode.evalEntry? 0 3 0 0

/-- info: some (Pauli.I) -/
#guard_msgs in
#eval oneQubitXCode.evalEntry? 0 3 0 1

def oneQubitCommutesFormula : Formula 0 :=
  let closedX : Term 0 .stab :=
    .stabLam <| .ite (.eqNat (.var ⟨0, by decide⟩) (.natLit 0))
      (.pauliLit Pauli.X) (.pauliLit Pauli.I)
  .commutesUpTo (.natLit 1)
    closedX
    closedX

/-- info: some true -/
#guard_msgs in
#eval oneQubitCommutesFormula.eval oneQubitXCode.body 0 Env.empty

#print axioms CodeFn.evalEntry?
#print axioms Formula.eval

end QHL.CodeLang
