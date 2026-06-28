import QStab.QHL.CodeNatArithmetic
import QStab.QHL.CodeDerivation

/-! # A generic stabilizer binder for code-level assertions

`CodeLang.Formula` can quantify over natural indices, but until this file it
could not bind an arbitrary stabilizer/error value.  That is too weak for code
distance: the lower-bound statement must range over all Pauli strings, not only
over the closed stabilizer terms that we happened to generate.

This module adds the minimal generic layer:

* `STerm` is the old term language plus one distinguished bound stabilizer
  variable `E`.
* `SFormula` is the old first-order formula language interpreted under that
  bound stabilizer.
* `ForallStabFormula` is the object-language binder
  `forall E : Stab[n], body(E)`.

No Surface-specific primitive is introduced here.  The binder is deliberately
finite: its semantics only accepts bound stabilizers that are total on the
declared prefix.
-/

namespace QHL.CodeLang

namespace StabBinder

/-- A finite stabilizer value is total on the first `n` qubits. -/
def TotalUpTo (n : Nat) (E : PartialStabilizer) : Prop :=
  forall q, q < n -> exists p, E q = some p

namespace Term

/-- Capture-avoiding substitution for one natural variable.

`instantiateNatAt cutoff x t` replaces the variable at de Bruijn index
`cutoff` in `t` by `x`, leaving variables below the cutoff alone and shifting
variables above the cutoff down by one.  Under stabilizer binders the cutoff is
incremented and the replacement term is weakened. -/
def instantiateNatAt (cutoff : Nat) {arity : Nat} (x : Term arity .nat)
    (hcut : cutoff <= arity) : {ty : Ty} -> Term (arity + 1) ty -> Term arity ty
  | _, .var v =>
      if hlt : v.val < cutoff then
        .var ⟨v.val, by omega⟩
      else if heq : v.val = cutoff then
        x
      else
        .var ⟨v.val - 1, by omega⟩
  | _, .natLit n => .natLit n
  | _, .boolLit b => .boolLit b
  | _, .pauliLit p => .pauliLit p
  | _, .add a b => .add (instantiateNatAt cutoff x hcut a) (instantiateNatAt cutoff x hcut b)
  | _, .sub a b => .sub (instantiateNatAt cutoff x hcut a) (instantiateNatAt cutoff x hcut b)
  | _, .mul a b => .mul (instantiateNatAt cutoff x hcut a) (instantiateNatAt cutoff x hcut b)
  | _, .div a b => .div (instantiateNatAt cutoff x hcut a) (instantiateNatAt cutoff x hcut b)
  | _, .mod a b => .mod (instantiateNatAt cutoff x hcut a) (instantiateNatAt cutoff x hcut b)
  | _, .eqNat a b =>
      .eqNat (instantiateNatAt cutoff x hcut a) (instantiateNatAt cutoff x hcut b)
  | _, .ltNat a b =>
      .ltNat (instantiateNatAt cutoff x hcut a) (instantiateNatAt cutoff x hcut b)
  | _, .leNat a b =>
      .leNat (instantiateNatAt cutoff x hcut a) (instantiateNatAt cutoff x hcut b)
  | _, .not a => .not (instantiateNatAt cutoff x hcut a)
  | _, .and a b => .and (instantiateNatAt cutoff x hcut a) (instantiateNatAt cutoff x hcut b)
  | _, .or a b => .or (instantiateNatAt cutoff x hcut a) (instantiateNatAt cutoff x hcut b)
  | _, .ite c t e =>
      .ite (instantiateNatAt cutoff x hcut c)
        (instantiateNatAt cutoff x hcut t)
        (instantiateNatAt cutoff x hcut e)
  | _, .pauliMul a b =>
      .pauliMul (instantiateNatAt cutoff x hcut a) (instantiateNatAt cutoff x hcut b)
  | _, .anticommutes a b =>
      .anticommutes (instantiateNatAt cutoff x hcut a) (instantiateNatAt cutoff x hcut b)
  | _, .stabLam entry =>
      .stabLam (instantiateNatAt (cutoff + 1) x.weaken (by omega) entry)
  | _, .stabAt s q =>
      .stabAt (instantiateNatAt cutoff x hcut s) (instantiateNatAt cutoff x hcut q)
  | _, .stabFold n body =>
      .stabFold (instantiateNatAt cutoff x hcut n)
        (instantiateNatAt (cutoff + 1) x.weaken (by omega) body)
  | _, .recCall d k =>
      .recCall (instantiateNatAt cutoff x hcut d) (instantiateNatAt cutoff x hcut k)

/-- Substitute the outermost natural variable. -/
def instantiateTopNat {arity : Nat} {ty : Ty} (x : Term arity .nat) :
    Term (arity + 1) ty -> Term arity ty :=
  instantiateNatAt 0 x (Nat.zero_le arity)

end Term

/-- Terms with one distinguished bound stabilizer variable.

All ordinary closed code expressions are embedded with `closed`.  The only new
variable is `boundStab`, which represents the stabilizer introduced by
`forallStab`.
-/
inductive STerm : Nat -> Ty -> Type where
  | closed {arity : Nat} {ty : Ty} : Term arity ty -> STerm arity ty
  | boundStab {arity : Nat} : STerm arity .stab
  | ite {arity : Nat} {ty : Ty} :
      STerm arity .bool -> STerm arity ty -> STerm arity ty -> STerm arity ty
  | pauliMul {arity : Nat} :
      STerm arity .pauli -> STerm arity .pauli -> STerm arity .pauli
  | anticommutes {arity : Nat} :
      STerm arity .pauli -> STerm arity .pauli -> STerm arity .bool
  | ltNat {arity : Nat} :
      STerm arity .nat -> STerm arity .nat -> STerm arity .bool
  | stabLam {arity : Nat} : STerm (arity + 1) .pauli -> STerm arity .stab
  | stabAt {arity : Nat} :
      STerm arity .stab -> STerm arity .nat -> STerm arity .pauli
  | stabFold {arity : Nat} :
      STerm arity .nat -> STerm (arity + 1) .stab -> STerm arity .stab
  | applyNat {arity : Nat} {ty : Ty} :
      STerm arity .nat -> STerm (arity + 1) ty -> STerm arity ty

namespace STerm

def sizeOfSTerm {arity : Nat} {ty : Ty} : STerm arity ty -> Nat
  | .closed _ => 1
  | .boundStab => 1
  | .ite c t e => 1 + sizeOfSTerm c + sizeOfSTerm t + sizeOfSTerm e
  | .pauliMul a b => 1 + sizeOfSTerm a + sizeOfSTerm b
  | .anticommutes a b => 1 + sizeOfSTerm a + sizeOfSTerm b
  | .ltNat a b => 1 + sizeOfSTerm a + sizeOfSTerm b
  | .stabLam entry => 1 + sizeOfSTerm entry
  | .stabAt s q => 1 + sizeOfSTerm s + sizeOfSTerm q
  | .stabFold n body => 1 + sizeOfSTerm n + sizeOfSTerm body
  | .applyNat witness body => 1 + sizeOfSTerm witness + sizeOfSTerm body

/-- Capture-avoiding weakening under one newly bound natural variable. -/
def lift (cutoff : Nat) {arity : Nat} {ty : Ty} :
    STerm arity ty -> STerm (arity + 1) ty
  | .closed t => .closed (t.lift cutoff)
  | .boundStab => .boundStab
  | .ite c t e => .ite (c.lift cutoff) (t.lift cutoff) (e.lift cutoff)
  | .pauliMul a b => .pauliMul (a.lift cutoff) (b.lift cutoff)
  | .anticommutes a b => .anticommutes (a.lift cutoff) (b.lift cutoff)
  | .ltNat a b => .ltNat (a.lift cutoff) (b.lift cutoff)
  | .stabLam entry => .stabLam (entry.lift (cutoff + 1))
  | .stabAt s q => .stabAt (s.lift cutoff) (q.lift cutoff)
  | .stabFold n body => .stabFold (n.lift cutoff) (body.lift (cutoff + 1))
  | .applyNat witness body => .applyNat (witness.lift cutoff) (body.lift (cutoff + 1))

def weaken {arity : Nat} {ty : Ty} (t : STerm arity ty) :
    STerm (arity + 1) ty :=
  t.lift 0

/-- Capture-avoiding application of a natural-indexed stabilizer body. -/
def instantiateNatAt (cutoff : Nat) {arity : Nat} (x : Term arity .nat)
    (hcut : cutoff <= arity) : {ty : Ty} -> STerm (arity + 1) ty -> STerm arity ty
  | _, .closed t => .closed (Term.instantiateNatAt cutoff x hcut t)
  | _, .boundStab => .boundStab
  | _, .ite c t e =>
      .ite (c.instantiateNatAt cutoff x hcut)
        (t.instantiateNatAt cutoff x hcut)
        (e.instantiateNatAt cutoff x hcut)
  | _, .pauliMul a b =>
      .pauliMul (a.instantiateNatAt cutoff x hcut) (b.instantiateNatAt cutoff x hcut)
  | _, .anticommutes a b =>
      .anticommutes (a.instantiateNatAt cutoff x hcut) (b.instantiateNatAt cutoff x hcut)
  | _, .ltNat a b =>
      .ltNat (a.instantiateNatAt cutoff x hcut) (b.instantiateNatAt cutoff x hcut)
  | _, .stabLam entry =>
      .stabLam (entry.instantiateNatAt (cutoff + 1) x.weaken (by omega))
  | _, .stabAt s q =>
      .stabAt (s.instantiateNatAt cutoff x hcut) (q.instantiateNatAt cutoff x hcut)
  | _, .stabFold n body =>
      .stabFold (n.instantiateNatAt cutoff x hcut)
        (body.instantiateNatAt (cutoff + 1) x.weaken (by omega))
  | _, .applyNat witness body =>
      .applyNat (witness.instantiateNatAt cutoff x hcut)
        (body.instantiateNatAt (cutoff + 1) x.weaken (by omega))

/-- Apply a one-index stabilizer body to a syntactic natural index. -/
def instantiateTopNat {arity : Nat} {ty : Ty} (x : Term arity .nat) :
    STerm (arity + 1) ty -> STerm arity ty :=
  instantiateNatAt 0 x (Nat.zero_le arity)

/-- Replace the bound stabilizer by a closed stabilizer expression. -/
def instantiate (E : Term arity .stab) : {ty : Ty} -> STerm arity ty -> Term arity ty
  | _, .closed t => t
  | _, .boundStab => E
  | _, .ite c t e => .ite (c.instantiate E) (t.instantiate E) (e.instantiate E)
  | _, .pauliMul a b => .pauliMul (a.instantiate E) (b.instantiate E)
  | _, .anticommutes a b => .anticommutes (a.instantiate E) (b.instantiate E)
  | _, .ltNat a b => .ltNat (a.instantiate E) (b.instantiate E)
  | _, .stabLam entry => .stabLam (entry.instantiate E.weaken)
  | _, .stabAt s q => .stabAt (s.instantiate E) (q.instantiate E)
  | _, .stabFold n body => .stabFold (n.instantiate E) (body.instantiate E.weaken)
  | _, .applyNat witness body =>
      Term.instantiateTopNat (witness.instantiate E) (body.instantiate E.weaken)

/-- Syntactic check that a term does not mention the distinguished stabilizer
    variable.  This is not semantic proof search; it is a structural predicate
    used by the family-indexed checker below. -/
def boundFree {arity : Nat} {ty : Ty} : STerm arity ty -> Bool
  | .closed _ => true
  | .boundStab => false
  | .ite c t e => c.boundFree && t.boundFree && e.boundFree
  | .pauliMul a b => a.boundFree && b.boundFree
  | .anticommutes a b => a.boundFree && b.boundFree
  | .ltNat a b => a.boundFree && b.boundFree
  | .stabLam entry => entry.boundFree
  | .stabAt s q => s.boundFree && q.boundFree
  | .stabFold n body => n.boundFree && body.boundFree
  | .applyNat _ _ => false

/-- Big-step semantics under a semantic bound stabilizer. -/
def eval (codeBody : Term 2 .stab) (fuel : Nat) :
    {arity : Nat} -> {ty : Ty} ->
      STerm arity ty -> Env arity -> PartialStabilizer -> Option ty.partialDenote
  | _, _, .closed t, rho, _ => Term.eval codeBody fuel t rho
  | _, _, .boundStab, _, E => some E
  | _, _, .ite c t e, rho, E => do
      let cv <- eval codeBody fuel c rho E
      if cv then eval codeBody fuel t rho E else eval codeBody fuel e rho E
  | _, _, .pauliMul a b, rho, E => do
      let av <- eval codeBody fuel a rho E
      let bv <- eval codeBody fuel b rho E
      some (Pauli.mul av bv)
  | _, _, .anticommutes a b, rho, E => do
      let av <- eval codeBody fuel a rho E
      let bv <- eval codeBody fuel b rho E
      some (ErrorVec.Pauli.anticommutes av bv)
  | _, _, .ltNat a b, rho, E => do
      let av <- eval codeBody fuel a rho E
      let bv <- eval codeBody fuel b rho E
      some (decide (av < bv))
  | _, _, .stabLam entry, rho, E =>
      some (fun q => eval codeBody fuel entry (Env.cons q rho) E)
  | _, _, .stabAt s q, rho, E => do
      let sv <- eval codeBody fuel s rho E
      let qv <- eval codeBody fuel q rho E
      sv qv
  | _, _, .stabFold n body, rho, E => do
      let nv <- eval codeBody fuel n rho E
      some <| partialStabilizerFold nv fun i =>
        match eval codeBody fuel body (Env.cons i rho) E with
        | some row => row
        | none => fun _ => none
  | _, _, .applyNat witness body, rho, E => do
      let wv <- eval codeBody fuel witness rho E
      eval codeBody fuel body (Env.cons wv rho) E
termination_by _ _ term _ _ => sizeOfSTerm term
decreasing_by
  all_goals
    simp [sizeOfSTerm]
    try omega

end STerm

namespace SC

abbrev N (arity : Nat) := STerm arity .nat
abbrev B (arity : Nat) := STerm arity .bool
abbrev P (arity : Nat) := STerm arity .pauli
abbrev S (arity : Nat) := STerm arity .stab

def closed {arity : Nat} {ty : Ty} (t : Term arity ty) : STerm arity ty :=
  .closed t

def n {arity : Nat} (x : Nat) : N arity := .closed (.natLit x)
def b {arity : Nat} (x : Bool) : B arity := .closed (.boolLit x)
def p {arity : Nat} (x : Pauli) : P arity := .closed (.pauliLit x)

def succClosed {arity : Nat} (x : Term arity .nat) : N arity :=
  .closed (.add x (.natLit 1))

def bound {arity : Nat} : S arity := .boundStab
def entry {arity : Nat} : S arity -> N arity -> P arity := .stabAt
def anticommutes {arity : Nat} : P arity -> P arity -> B arity := .anticommutes
def lt {arity : Nat} : N arity -> N arity -> B arity := .ltNat
def holds {arity : Nat} (x : B arity) : B arity := x

/-- The qubit variable bound by a surrounding stabilizer lambda. -/
def qVar {arity : Nat} : N (arity + 1) :=
  .closed (.var ⟨0, Nat.succ_pos arity⟩)

/-- Pointwise product of two stabilizer terms.  This is derived syntax:
    it expands to `stabLam`, `stabAt`, and `pauliMul`. -/
def stabMul {arity : Nat} (A B : S arity) : S arity :=
  .stabLam <|
    .pauliMul
      (.stabAt A.weaken qVar)
      (.stabAt B.weaken qVar)

/-- Identity stabilizer, as derived syntax. -/
def stabOne {arity : Nat} : S arity :=
  .stabLam (SC.p Pauli.I)

/-- Finite product of stabilizer terms, with the identity stabilizer as base. -/
def stabListProduct {arity : Nat} : List (S arity) -> S arity
  | [] => stabOne
  | A :: rest => stabMul A (stabListProduct rest)

/-- Bounded product over natural indices.  This is the parametric product form:
    the AST size is independent of the runtime bound. -/
def stabFold {arity : Nat} (n : N arity) (body : S (arity + 1)) : S arity :=
  .stabFold n body

def applyNat {arity : Nat} (x : Term arity .nat) (body : S (arity + 1)) : S arity :=
  .applyNat (.closed x) body

def gridIdx {arity : Nat} (dist row col : Term arity .nat) : Term arity .nat :=
  NatArithmetic.gridIdxLeft dist row col

def rowZCut {arity : Nat} (dist : Nat) (row : Term arity .nat) : S arity :=
  .closed <|
    .stabLam <|
      .ite (.eqNat (.div (.var ⟨0, Nat.succ_pos arity⟩) (.natLit dist)) row.weaken)
        (.pauliLit Pauli.Z)
        (.pauliLit Pauli.I)

def colXCut {arity : Nat} (dist : Nat) (col : Term arity .nat) : S arity :=
  .closed <|
    .stabLam <|
      .ite (.eqNat (.mod (.var ⟨0, Nat.succ_pos arity⟩) (.natLit dist)) col.weaken)
        (.pauliLit Pauli.X)
        (.pauliLit Pauli.I)

def rowZBridge {arity : Nat} (dist : Nat) (row : Term arity .nat) : S arity :=
  stabMul (rowZCut dist row) (rowZCut dist (.add row (.natLit 1)))

def colXBridge {arity : Nat} (dist : Nat) (col : Term arity .nat) : S arity :=
  stabMul (colXCut dist col) (colXCut dist (.add col (.natLit 1)))

end SC

/-- Formulas interpreted under one bound stabilizer. -/
inductive SFormula : Nat -> Type where
  | top {arity : Nat} : SFormula arity
  | bot {arity : Nat} : SFormula arity
  | eqNat {arity : Nat} : STerm arity .nat -> STerm arity .nat -> SFormula arity
  | eqBool {arity : Nat} : STerm arity .bool -> STerm arity .bool -> SFormula arity
  | eqPauli {arity : Nat} : STerm arity .pauli -> STerm arity .pauli -> SFormula arity
  | eqStabUpTo {arity : Nat} :
      STerm arity .nat -> STerm arity .stab -> STerm arity .stab -> SFormula arity
  | commutesUpTo {arity : Nat} :
      STerm arity .nat -> STerm arity .stab -> STerm arity .stab -> SFormula arity
  | weightLe {arity : Nat} :
      STerm arity .nat -> STerm arity .stab -> STerm arity .nat -> SFormula arity
  | and {arity : Nat} : SFormula arity -> SFormula arity -> SFormula arity
  | or {arity : Nat} : SFormula arity -> SFormula arity -> SFormula arity
  | not {arity : Nat} : SFormula arity -> SFormula arity
  | imp {arity : Nat} : SFormula arity -> SFormula arity -> SFormula arity
  | applyNat {arity : Nat} : STerm arity .nat -> SFormula (arity + 1) -> SFormula arity
  | allNatLt {arity : Nat} : STerm arity .nat -> SFormula (arity + 1) -> SFormula arity
  | existsNatLt {arity : Nat} : STerm arity .nat -> SFormula (arity + 1) -> SFormula arity

namespace SFormula

def sizeOfSFormula {arity : Nat} : SFormula arity -> Nat
  | .top => 1
  | .bot => 1
  | .eqNat a b => 1 + STerm.sizeOfSTerm a + STerm.sizeOfSTerm b
  | .eqBool a b => 1 + STerm.sizeOfSTerm a + STerm.sizeOfSTerm b
  | .eqPauli a b => 1 + STerm.sizeOfSTerm a + STerm.sizeOfSTerm b
  | .eqStabUpTo n a b =>
      1 + STerm.sizeOfSTerm n + STerm.sizeOfSTerm a + STerm.sizeOfSTerm b
  | .commutesUpTo n a b =>
      1 + STerm.sizeOfSTerm n + STerm.sizeOfSTerm a + STerm.sizeOfSTerm b
  | .weightLe n a w =>
      1 + STerm.sizeOfSTerm n + STerm.sizeOfSTerm a + STerm.sizeOfSTerm w
  | .and A B => 1 + sizeOfSFormula A + sizeOfSFormula B
  | .or A B => 1 + sizeOfSFormula A + sizeOfSFormula B
  | .not A => 1 + sizeOfSFormula A
  | .imp A B => 1 + sizeOfSFormula A + sizeOfSFormula B
  | .applyNat witness A => 1 + STerm.sizeOfSTerm witness + sizeOfSFormula A
  | .allNatLt n A => 1 + STerm.sizeOfSTerm n + sizeOfSFormula A
  | .existsNatLt n A => 1 + STerm.sizeOfSTerm n + sizeOfSFormula A

def lift (cutoff : Nat) {arity : Nat} : SFormula arity -> SFormula (arity + 1)
  | .top => .top
  | .bot => .bot
  | .eqNat a b => .eqNat (a.lift cutoff) (b.lift cutoff)
  | .eqBool a b => .eqBool (a.lift cutoff) (b.lift cutoff)
  | .eqPauli a b => .eqPauli (a.lift cutoff) (b.lift cutoff)
  | .eqStabUpTo n a b => .eqStabUpTo (n.lift cutoff) (a.lift cutoff) (b.lift cutoff)
  | .commutesUpTo n a b => .commutesUpTo (n.lift cutoff) (a.lift cutoff) (b.lift cutoff)
  | .weightLe n a w => .weightLe (n.lift cutoff) (a.lift cutoff) (w.lift cutoff)
  | .and A B => .and (A.lift cutoff) (B.lift cutoff)
  | .or A B => .or (A.lift cutoff) (B.lift cutoff)
  | .not A => .not (A.lift cutoff)
  | .imp A B => .imp (A.lift cutoff) (B.lift cutoff)
  | .applyNat witness A => .applyNat (witness.lift cutoff) (A.lift (cutoff + 1))
  | .allNatLt n A => .allNatLt (n.lift cutoff) (A.lift (cutoff + 1))
  | .existsNatLt n A => .existsNatLt (n.lift cutoff) (A.lift (cutoff + 1))

def weaken {arity : Nat} (A : SFormula arity) : SFormula (arity + 1) :=
  A.lift 0

/-- Capture-avoiding substitution for the nearest natural variable in a
    formula.  This is the formula-level counterpart of
    `STerm.instantiateNatAt`. -/
def instantiateNatAt (cutoff : Nat) {arity : Nat} (x : Term arity .nat)
    (hcut : cutoff <= arity) : SFormula (arity + 1) -> SFormula arity
  | .top => .top
  | .bot => .bot
  | .eqNat a b =>
      .eqNat (a.instantiateNatAt cutoff x hcut) (b.instantiateNatAt cutoff x hcut)
  | .eqBool a b =>
      .eqBool (a.instantiateNatAt cutoff x hcut) (b.instantiateNatAt cutoff x hcut)
  | .eqPauli a b =>
      .eqPauli (a.instantiateNatAt cutoff x hcut) (b.instantiateNatAt cutoff x hcut)
  | .eqStabUpTo n a b =>
      .eqStabUpTo
        (n.instantiateNatAt cutoff x hcut)
        (a.instantiateNatAt cutoff x hcut)
        (b.instantiateNatAt cutoff x hcut)
  | .commutesUpTo n a b =>
      .commutesUpTo
        (n.instantiateNatAt cutoff x hcut)
        (a.instantiateNatAt cutoff x hcut)
        (b.instantiateNatAt cutoff x hcut)
  | .weightLe n a w =>
      .weightLe
        (n.instantiateNatAt cutoff x hcut)
        (a.instantiateNatAt cutoff x hcut)
        (w.instantiateNatAt cutoff x hcut)
  | .and A B => .and (A.instantiateNatAt cutoff x hcut) (B.instantiateNatAt cutoff x hcut)
  | .or A B => .or (A.instantiateNatAt cutoff x hcut) (B.instantiateNatAt cutoff x hcut)
  | .not A => .not (A.instantiateNatAt cutoff x hcut)
  | .imp A B => .imp (A.instantiateNatAt cutoff x hcut) (B.instantiateNatAt cutoff x hcut)
  | .applyNat witness A =>
      .applyNat
        (witness.instantiateNatAt cutoff x hcut)
        (A.instantiateNatAt (cutoff + 1) x.weaken (by omega))
  | .allNatLt n A =>
      .allNatLt
        (n.instantiateNatAt cutoff x hcut)
        (A.instantiateNatAt (cutoff + 1) x.weaken (by omega))
  | .existsNatLt n A =>
      .existsNatLt
        (n.instantiateNatAt cutoff x hcut)
        (A.instantiateNatAt (cutoff + 1) x.weaken (by omega))

/-- Substitute the nearest natural variable in a formula. -/
def instantiateTopNat {arity : Nat} (x : Term arity .nat) :
    SFormula (arity + 1) -> SFormula arity :=
  instantiateNatAt 0 x (Nat.zero_le arity)

/-- Replace the distinguished stabilizer variable by a closed term and return
    an ordinary `CodeLang.Formula`. -/
def instantiate (E : Term arity .stab) : SFormula arity -> Formula arity
  | .top => .top
  | .bot => .bot
  | .eqNat a b => .eqNat (a.instantiate E) (b.instantiate E)
  | .eqBool a b => .eqBool (a.instantiate E) (b.instantiate E)
  | .eqPauli a b => .eqPauli (a.instantiate E) (b.instantiate E)
  | .eqStabUpTo n a b => .eqStabUpTo (n.instantiate E) (a.instantiate E) (b.instantiate E)
  | .commutesUpTo n a b => .commutesUpTo (n.instantiate E) (a.instantiate E) (b.instantiate E)
  | .weightLe n a w => .weightLe (n.instantiate E) (a.instantiate E) (w.instantiate E)
  | .and A B => .and (A.instantiate E) (B.instantiate E)
  | .or A B => .or (A.instantiate E) (B.instantiate E)
  | .not A => .not (A.instantiate E)
  | .imp A B => .imp (A.instantiate E) (B.instantiate E)
  | .applyNat witness A => .applyNat (witness.instantiate E) (A.instantiate E.weaken)
  | .allNatLt n A => .allNatLt (n.instantiate E) (A.instantiate E.weaken)
  | .existsNatLt n A => .existsNatLt (n.instantiate E) (A.instantiate E.weaken)

/-- Syntactic check that a formula does not mention the distinguished
    stabilizer variable.  Finite natural quantifiers are allowed; explicit
    `applyNat` is intentionally excluded because its beta reasoning belongs to
    the symbolic derivation layer. -/
def boundFree {arity : Nat} : SFormula arity -> Bool
  | .top => true
  | .bot => true
  | .eqNat a b => a.boundFree && b.boundFree
  | .eqBool a b => a.boundFree && b.boundFree
  | .eqPauli a b => a.boundFree && b.boundFree
  | .eqStabUpTo n a b => n.boundFree && a.boundFree && b.boundFree
  | .commutesUpTo n a b => n.boundFree && a.boundFree && b.boundFree
  | .weightLe n a w => n.boundFree && a.boundFree && w.boundFree
  | .and A B => A.boundFree && B.boundFree
  | .or A B => A.boundFree && B.boundFree
  | .not A => A.boundFree
  | .imp A B => A.boundFree && B.boundFree
  | .applyNat _ _ => false
  | .allNatLt n A => n.boundFree && A.boundFree
  | .existsNatLt n A => n.boundFree && A.boundFree

/-- Executable semantics under a semantic bound stabilizer. -/
def eval (codeBody : Term 2 .stab) (fuel : Nat) :
    {arity : Nat} -> SFormula arity -> Env arity -> PartialStabilizer -> Option Bool
  | _, .top, _, _ => some true
  | _, .bot, _, _ => some false
  | _, .eqNat a b, rho, E => do
      let av <- a.eval codeBody fuel rho E
      let bv <- b.eval codeBody fuel rho E
      some (decide (av = bv))
  | _, .eqBool a b, rho, E => do
      let av <- a.eval codeBody fuel rho E
      let bv <- b.eval codeBody fuel rho E
      some (decide (av = bv))
  | _, .eqPauli a b, rho, E => do
      let av <- a.eval codeBody fuel rho E
      let bv <- b.eval codeBody fuel rho E
      some (decide (av = bv))
  | _, .eqStabUpTo n a b, rho, E => do
      let nv <- n.eval codeBody fuel rho E
      let av <- a.eval codeBody fuel rho E
      let bv <- b.eval codeBody fuel rho E
      stabEqUpTo nv av bv
  | _, .commutesUpTo n a b, rho, E => do
      let nv <- n.eval codeBody fuel rho E
      let av <- a.eval codeBody fuel rho E
      let bv <- b.eval codeBody fuel rho E
      let parity <- parityUpTo nv av bv
      some (!parity)
  | _, .weightLe n a w, rho, E => do
      let nv <- n.eval codeBody fuel rho E
      let av <- a.eval codeBody fuel rho E
      let wv <- w.eval codeBody fuel rho E
      let weight <- weightUpTo nv av
      some (decide (weight <= wv))
  | _, .and A B, rho, E => do
      let av <- eval codeBody fuel A rho E
      if av then eval codeBody fuel B rho E else some false
  | _, .or A B, rho, E => do
      let av <- eval codeBody fuel A rho E
      if av then some true else eval codeBody fuel B rho E
  | _, .not A, rho, E => do
      let av <- eval codeBody fuel A rho E
      some (!av)
  | _, .imp A B, rho, E => do
      let av <- eval codeBody fuel A rho E
      if av then eval codeBody fuel B rho E else some true
  | _, .applyNat witness A, rho, E => do
      let wv <- witness.eval codeBody fuel rho E
      eval codeBody fuel A (Env.cons wv rho) E
  | _, .allNatLt n A, rho, E => do
      let nv <- n.eval codeBody fuel rho E
      QHL.CodeLang.allNatLt nv fun x => eval codeBody fuel A (Env.cons x rho) E
  | _, .existsNatLt n A, rho, E => do
      let nv <- n.eval codeBody fuel rho E
      QHL.CodeLang.existsNatLt nv fun x => eval codeBody fuel A (Env.cons x rho) E

end SFormula

private theorem partialStabilizerFold_congr {n : Nat}
    {body1 body2 : Nat -> PartialStabilizer}
    (h : forall i, body1 i = body2 i) :
    partialStabilizerFold n body1 = partialStabilizerFold n body2 := by
  induction n with
  | zero =>
      rfl
  | succ m ih =>
      simp [partialStabilizerFold, ih, h]

private theorem allNatLt_congr {n : Nat} {p q : Nat -> Option Bool}
    (h : forall i, p i = q i) :
    QHL.CodeLang.allNatLt n p = QHL.CodeLang.allNatLt n q := by
  induction n with
  | zero =>
      rfl
  | succ m ih =>
      simp [QHL.CodeLang.allNatLt, ih, h]

private theorem existsNatLt_congr {n : Nat} {p q : Nat -> Option Bool}
    (h : forall i, p i = q i) :
    QHL.CodeLang.existsNatLt n p = QHL.CodeLang.existsNatLt n q := by
  induction n with
  | zero =>
      rfl
  | succ m ih =>
      simp [QHL.CodeLang.existsNatLt, ih, h]

namespace STerm

theorem eval_boundFree_instantiate {arity : Nat} {ty : Ty}
    (t : STerm arity ty) (hfree : t.boundFree = true)
    (codeBody : Term 2 .stab) (fuel : Nat) (rho : Env arity)
    (bound : PartialStabilizer) (E : Term arity .stab) :
    t.eval codeBody fuel rho bound =
      Term.eval codeBody fuel (t.instantiate E) rho := by
  induction t generalizing codeBody fuel bound with
  | closed t =>
      simp [STerm.eval, STerm.instantiate, Term.eval]
  | boundStab =>
      simp [STerm.boundFree] at hfree
  | ite c t e ihc iht ihe =>
      simp [STerm.boundFree] at hfree
      simp [STerm.eval, STerm.instantiate, Term.eval,
        ihc hfree.1.1 codeBody fuel rho bound E,
        iht hfree.1.2 codeBody fuel rho bound E,
        ihe hfree.2 codeBody fuel rho bound E]
  | pauliMul a b iha ihb =>
      simp [STerm.boundFree] at hfree
      simp [STerm.eval, STerm.instantiate, Term.eval,
        iha hfree.1 codeBody fuel rho bound E,
        ihb hfree.2 codeBody fuel rho bound E]
  | anticommutes a b iha ihb =>
      simp [STerm.boundFree] at hfree
      simp [STerm.eval, STerm.instantiate, Term.eval,
        iha hfree.1 codeBody fuel rho bound E,
        ihb hfree.2 codeBody fuel rho bound E]
  | ltNat a b iha ihb =>
      simp [STerm.boundFree] at hfree
      simp [STerm.eval, STerm.instantiate, Term.eval,
        iha hfree.1 codeBody fuel rho bound E,
        ihb hfree.2 codeBody fuel rho bound E]
  | stabLam entry ih =>
      simp [STerm.boundFree] at hfree
      simp [STerm.eval, STerm.instantiate, Term.eval]
      funext q
      exact ih hfree codeBody fuel (Env.cons q rho) bound E.weaken
  | stabAt s q ihs ihq =>
      simp [STerm.boundFree] at hfree
      simp [STerm.eval, STerm.instantiate, Term.eval,
        ihs hfree.1 codeBody fuel rho bound E,
        ihq hfree.2 codeBody fuel rho bound E]
  | stabFold n body ihn ihbody =>
      simp [STerm.boundFree] at hfree
      have hn := ihn hfree.1 codeBody fuel rho bound E
      cases hnv : Term.eval codeBody fuel (n.instantiate E) rho with
      | none =>
          simp [STerm.eval, STerm.instantiate, Term.eval, hn, hnv]
      | some nv =>
          simp [STerm.eval, STerm.instantiate, Term.eval, hn, hnv]
          apply partialStabilizerFold_congr
          intro i
          have hb := ihbody hfree.2 codeBody fuel (Env.cons i rho) bound E.weaken
          rw [hb]
          rfl
  | applyNat witness body ihw ihbody =>
      simp [STerm.boundFree] at hfree

end STerm

namespace SFormula

theorem eval_boundFree_instantiate {arity : Nat}
    (A : SFormula arity) (hfree : A.boundFree = true)
    (codeBody : Term 2 .stab) (fuel : Nat) (rho : Env arity)
    (bound : PartialStabilizer) (E : Term arity .stab) :
    A.eval codeBody fuel rho bound =
      Formula.eval codeBody fuel (A.instantiate E) rho := by
  induction A generalizing codeBody fuel bound with
  | top =>
      rfl
  | bot =>
      rfl
  | eqNat a b =>
      simp [SFormula.boundFree] at hfree
      simp [SFormula.eval, SFormula.instantiate, Formula.eval,
        STerm.eval_boundFree_instantiate a hfree.1 codeBody fuel rho bound E,
        STerm.eval_boundFree_instantiate b hfree.2 codeBody fuel rho bound E]
  | eqBool a b =>
      simp [SFormula.boundFree] at hfree
      simp [SFormula.eval, SFormula.instantiate, Formula.eval,
        STerm.eval_boundFree_instantiate a hfree.1 codeBody fuel rho bound E,
        STerm.eval_boundFree_instantiate b hfree.2 codeBody fuel rho bound E]
  | eqPauli a b =>
      simp [SFormula.boundFree] at hfree
      simp [SFormula.eval, SFormula.instantiate, Formula.eval,
        STerm.eval_boundFree_instantiate a hfree.1 codeBody fuel rho bound E,
        STerm.eval_boundFree_instantiate b hfree.2 codeBody fuel rho bound E]
  | eqStabUpTo n a b =>
      simp [SFormula.boundFree] at hfree
      simp [SFormula.eval, SFormula.instantiate, Formula.eval,
        STerm.eval_boundFree_instantiate n hfree.1.1 codeBody fuel rho bound E,
        STerm.eval_boundFree_instantiate a hfree.1.2 codeBody fuel rho bound E,
        STerm.eval_boundFree_instantiate b hfree.2 codeBody fuel rho bound E]
  | commutesUpTo n a b =>
      simp [SFormula.boundFree] at hfree
      simp [SFormula.eval, SFormula.instantiate, Formula.eval,
        STerm.eval_boundFree_instantiate n hfree.1.1 codeBody fuel rho bound E,
        STerm.eval_boundFree_instantiate a hfree.1.2 codeBody fuel rho bound E,
        STerm.eval_boundFree_instantiate b hfree.2 codeBody fuel rho bound E]
  | weightLe n a w =>
      simp [SFormula.boundFree] at hfree
      simp [SFormula.eval, SFormula.instantiate, Formula.eval,
        STerm.eval_boundFree_instantiate n hfree.1.1 codeBody fuel rho bound E,
        STerm.eval_boundFree_instantiate a hfree.1.2 codeBody fuel rho bound E,
        STerm.eval_boundFree_instantiate w hfree.2 codeBody fuel rho bound E]
  | and A B ihA ihB =>
      simp [SFormula.boundFree] at hfree
      simp [SFormula.eval, SFormula.instantiate, Formula.eval,
        ihA hfree.1 codeBody fuel rho bound E,
        ihB hfree.2 codeBody fuel rho bound E]
  | or A B ihA ihB =>
      simp [SFormula.boundFree] at hfree
      simp [SFormula.eval, SFormula.instantiate, Formula.eval,
        ihA hfree.1 codeBody fuel rho bound E,
        ihB hfree.2 codeBody fuel rho bound E]
  | not A ihA =>
      simp [SFormula.boundFree] at hfree
      simp [SFormula.eval, SFormula.instantiate, Formula.eval,
        ihA hfree codeBody fuel rho bound E]
  | imp A B ihA ihB =>
      simp [SFormula.boundFree] at hfree
      simp [SFormula.eval, SFormula.instantiate, Formula.eval,
        ihA hfree.1 codeBody fuel rho bound E,
        ihB hfree.2 codeBody fuel rho bound E]
  | applyNat witness A ih =>
      simp [SFormula.boundFree] at hfree
  | allNatLt n A ih =>
      simp [SFormula.boundFree] at hfree
      have hn := STerm.eval_boundFree_instantiate n hfree.1 codeBody fuel rho bound E
      cases hnv : Term.eval codeBody fuel (n.instantiate E) rho with
      | none =>
          simp [SFormula.eval, SFormula.instantiate, Formula.eval, hn, hnv]
      | some nv =>
          simp [SFormula.eval, SFormula.instantiate, Formula.eval, hn, hnv]
          apply allNatLt_congr
          intro i
          exact ih hfree.2 codeBody fuel (Env.cons i rho) bound E.weaken
  | existsNatLt n A ih =>
      simp [SFormula.boundFree] at hfree
      have hn := STerm.eval_boundFree_instantiate n hfree.1 codeBody fuel rho bound E
      cases hnv : Term.eval codeBody fuel (n.instantiate E) rho with
      | none =>
          simp [SFormula.eval, SFormula.instantiate, Formula.eval, hn, hnv]
      | some nv =>
          simp [SFormula.eval, SFormula.instantiate, Formula.eval, hn, hnv]
          apply existsNatLt_congr
          intro i
          exact ih hfree.2 codeBody fuel (Env.cons i rho) bound E.weaken

/-- The natural variable introduced by the nearest surrounding finite binder. -/
def boundNat {arity : Nat} : STerm (arity + 1) .nat :=
  SC.closed (.var ⟨0, Nat.succ_pos arity⟩)

/-- Syntactic bounded-index side condition for `allNatLt` elimination:
    `(witness < bound) = true`. -/
def witnessLt {arity : Nat} (witness bound : STerm arity .nat) :
    SFormula arity :=
  .eqBool (.ltNat witness bound) (SC.b true)

/-- Side condition available inside the body of `forall i < n`. -/
def boundNatLt {arity : Nat} (n : STerm arity .nat) : SFormula (arity + 1) :=
  witnessLt boundNat n.weaken

def nonIAt {arity : Nat} (E : STerm arity .stab) (q : STerm arity .nat) :
    SFormula arity :=
  .not (.eqPauli (.stabAt E q) (SC.p Pauli.I))

def xSupportAt {arity : Nat} (E : STerm arity .stab) (q : Term arity .nat) :
    SFormula arity :=
  .eqBool (.anticommutes (.stabAt E (.closed q)) (SC.p Pauli.Z)) (SC.b true)

def zSupportAt {arity : Nat} (E : STerm arity .stab) (q : Term arity .nat) :
    SFormula arity :=
  .eqBool (.anticommutes (.stabAt E (.closed q)) (SC.p Pauli.X)) (SC.b true)

def gridRowNoX {arity : Nat} (dist : Nat)
    (E : STerm arity .stab) (row : Term arity .nat) : SFormula arity :=
  .allNatLt (SC.n dist) <|
    .not <| xSupportAt E.weaken
      (SC.gridIdx (.natLit dist) row.weaken (.var ⟨0, Nat.succ_pos arity⟩))

def gridColNoZ {arity : Nat} (dist : Nat)
    (E : STerm arity .stab) (col : Term arity .nat) : SFormula arity :=
  .allNatLt (SC.n dist) <|
    .not <| zSupportAt E.weaken
      (SC.gridIdx (.natLit dist) (.var ⟨0, Nat.succ_pos arity⟩) col.weaken)

def gridRowXOccupied {arity : Nat} (dist : Nat)
    (E : STerm arity .stab) (row : Term arity .nat) : SFormula arity :=
  .not (gridRowNoX dist E row)

def gridColZOccupied {arity : Nat} (dist : Nat)
    (E : STerm arity .stab) (col : Term arity .nat) : SFormula arity :=
  .not (gridColNoZ dist E col)

def gridStripWidth (dist : Nat) : Nat :=
  (dist - 1) / 2 + 1

def gridNumStab (dist : Nat) : Nat :=
  max 1 ((dist - 1) * (dist - 1) + 2 * (dist - 1))

def gridRowZStripIndex {arity : Nat} (dist : Nat)
    (row slot : Term arity .nat) : Term arity .nat :=
  let dm1 : Term arity .nat := .natLit (dist - 1)
  let bulkCount : Term arity .nat := .natLit ((dist - 1) * (dist - 1))
  let half : Term arity .nat := .natLit ((dist - 1) / 2)
  let two : Term arity .nat := .natLit 2
  let rowEven := .eqNat (.mod row two) (.natLit 0)
  let bulkCol := .ite rowEven (.mul two slot) (.add (.mul two slot) (.natLit 1))
  let bulk := .add (.mul row dm1) bulkCol
  let rightBoundary := .add bulkCount (.add half (.div row two))
  let leftBoundary := .add bulkCount (.add (.mul two half) (.div (.sub row (.natLit 1)) two))
  .ite (.ltNat slot half) bulk (.ite rowEven rightBoundary leftBoundary)

def gridColXStripIndex {arity : Nat} (dist : Nat)
    (col slot : Term arity .nat) : Term arity .nat :=
  let dm1 : Term arity .nat := .natLit (dist - 1)
  let bulkCount : Term arity .nat := .natLit ((dist - 1) * (dist - 1))
  let half : Term arity .nat := .natLit ((dist - 1) / 2)
  let two : Term arity .nat := .natLit 2
  let colEven := .eqNat (.mod col two) (.natLit 0)
  let bulkRow := .ite colEven (.add (.mul two slot) (.natLit 1)) (.mul two slot)
  let bulk := .add (.mul bulkRow dm1) col
  let topBoundary := .add bulkCount (.div col two)
  let bottomBoundary := .add bulkCount (.add (.mul (.natLit 3) half)
    (.div (.sub col (.natLit 1)) two))
  .ite (.ltNat slot half) bulk (.ite colEven topBoundary bottomBoundary)

/-- Local Pauli premise: the entries of two stabilizers commute at one qubit. -/
def localCommutesAt {arity : Nat}
    (A B : STerm arity .stab) (q : STerm arity .nat) : SFormula arity :=
  .not (.eqBool (.anticommutes (.stabAt A q) (.stabAt B q)) (SC.b true))

/-- Pointwise local commutation premise for two stabilizers on a finite prefix. -/
def pointwiseCommutesUpTo {arity : Nat}
    (n : STerm arity .nat) (A B : STerm arity .stab) : SFormula arity :=
  .allNatLt n (localCommutesAt A.weaken B.weaken boundNat)

/-- Body for the generic counting premise: the slot selected by the current
    finite index is in range and carries a non-identity Pauli. -/
def slotSupportBody {arity : Nat}
    (n : STerm arity .nat) (E : STerm arity .stab)
    (slot : STerm (arity + 1) .nat) : SFormula (arity + 1) :=
  .and (witnessLt slot n.weaken) (nonIAt E.weaken slot)

/-- Body for pairwise injectivity of a one-index slot function under two
    bounded binders.  In the nested body, `boundNat` is `j` and
    `boundNat.weaken` is `i`. -/
def slotInjectiveBody {arity : Nat}
    (slot : STerm (arity + 1) .nat) : SFormula (arity + 2) :=
  .imp (.eqNat slot.weaken (slot.lift 1))
    (.eqNat (boundNat (arity := arity + 1)) (boundNat (arity := arity).weaken))

def slotInjectiveF {arity : Nat}
    (k : STerm arity .nat) (slot : STerm (arity + 1) .nat) : SFormula arity :=
  .allNatLt k (.allNatLt k.weaken (slotInjectiveBody slot))

/-- Body for a generic finite counting premise.  Under the current bounded row
    index `i`, there is a support qubit `q < n` such that `rowOf(q) = i`.
    This is the relation-free form needed by geometric code-distance proofs:
    the term `rowOf` maps each occupied support location back to its row/column
    label. -/
def supportSurjectiveBody {arity : Nat}
    (n : STerm arity .nat) (E : STerm arity .stab)
    (rowOf : STerm (arity + 1) .nat) : SFormula (arity + 1) :=
  .existsNatLt n.weaken <|
    .and
      (nonIAt E.weaken.weaken (boundNat (arity := arity + 1)))
      (.eqNat (rowOf.lift 1) ((boundNat (arity := arity)).weaken))

def supportSurjectiveF {arity : Nat}
    (k n : STerm arity .nat) (E : STerm arity .stab)
    (rowOf : STerm (arity + 1) .nat) : SFormula arity :=
  .allNatLt k (supportSurjectiveBody n E rowOf)

end SFormula

namespace SFormula

/-! ## Symbolic derivations under the bound stabilizer

The old `Formula.Deriv` checks closed formulas by evaluation.  `SFormula.Deriv`
is the complementary symbolic layer: it has assumptions and logical rules, but
no semantic catch-all leaf.  Nontrivial algebraic facts must be added later as
named, sound rules.
-/

def ContextHolds {arity : Nat} (codeBody : Term 2 .stab) (fuel : Nat)
    (rho : Env arity) (E : PartialStabilizer)
    (Γ : List (SFormula arity)) : Prop :=
  forall A, A ∈ Γ -> A.eval codeBody fuel rho E = some true

/-- Semantic relation for one capture-avoiding natural-variable insertion.
    `rho'` is `rho` with one extra variable inserted at `cutoff`. -/
private def EnvLifted {arity : Nat} (cutoff : Nat)
    (rho : Env arity) (rho' : Env (arity + 1)) : Prop :=
  (forall v : Fin arity, v.val < cutoff ->
    rho' ⟨v.val, Nat.lt_trans v.isLt (Nat.lt_succ_self arity)⟩ = rho v) /\
  (forall v : Fin arity, cutoff <= v.val ->
    rho' ⟨v.val + 1, Nat.succ_lt_succ v.isLt⟩ = rho v)

private theorem EnvLifted.underBinder {arity cutoff : Nat}
    {rho : Env arity} {rho' : Env (arity + 1)}
    (h : EnvLifted cutoff rho rho') (x : Nat) :
    EnvLifted (cutoff + 1) (Env.cons x rho) (Env.cons x rho') := by
  constructor
  · intro v hv
    cases v using Fin.cases with
    | zero => rfl
    | succ v =>
        have hv' : v.val < cutoff := Nat.lt_of_succ_lt_succ hv
        simp [Env.cons]
        exact h.1 v hv'
  · intro v hv
    cases v using Fin.cases with
    | zero =>
        simp at hv
    | succ v =>
        have hv' : cutoff <= v.val := Nat.le_of_succ_le_succ hv
        simp [Env.cons]
        exact h.2 v hv'

private theorem EnvLifted.top {arity : Nat} (rho : Env arity) (x : Nat) :
    EnvLifted 0 rho (Env.cons x rho) := by
  constructor
  · intro v hv
    omega
  · intro v _
    simp [Env.cons]

private def envTail {arity : Nat} (rho : Env (arity + 1)) : Env arity :=
  fun v => rho ⟨v.val + 1, Nat.succ_lt_succ v.isLt⟩

private theorem EnvLifted.tail {arity : Nat} (rho : Env (arity + 1)) :
    EnvLifted 0 (envTail rho) rho := by
  constructor
  · intro v hv
    omega
  · intro v _
    rfl

private theorem env_cons_zero {arity : Nat} (x : Nat) (rho : Env arity) :
    (Env.cons x rho) ⟨0, Nat.succ_pos arity⟩ = x := by
  rfl

private def EnvInserted {arity : Nat} (cutoff xv : Nat)
    (rho : Env arity) (rho' : Env (arity + 1)) (hcut : cutoff <= arity) : Prop :=
  EnvLifted cutoff rho rho' /\
    rho' ⟨cutoff, Nat.lt_succ_of_le hcut⟩ = xv

private theorem EnvInserted.top {arity : Nat} (rho : Env arity) (xv : Nat) :
    EnvInserted 0 xv rho (Env.cons xv rho) (Nat.zero_le arity) := by
  constructor
  · exact EnvLifted.top rho xv
  · rfl

private theorem EnvInserted.underBinder {arity cutoff xv : Nat}
    {rho : Env arity} {rho' : Env (arity + 1)} {hcut : cutoff <= arity}
    (h : EnvInserted cutoff xv rho rho' hcut) (q : Nat) :
    EnvInserted (cutoff + 1) xv (Env.cons q rho) (Env.cons q rho') (by omega) := by
  constructor
  · exact EnvLifted.underBinder h.1 q
  · simpa [Env.cons] using h.2

private theorem Term.eval_lift_of_env {arity cutoff : Nat} {ty : Ty}
    (t : Term arity ty) {rho : Env arity} {rho' : Env (arity + 1)}
    (h : EnvLifted cutoff rho rho') (codeBody : Term 2 .stab) (fuel : Nat) :
    Term.eval codeBody fuel (t.lift cutoff) rho' =
      Term.eval codeBody fuel t rho := by
  induction t generalizing cutoff fuel with
  | var v =>
      unfold Term.lift Term.weakenVar
      by_cases hlt : v.val < cutoff
      · simp [Term.eval, hlt, h.1 v hlt]
      · have hge : cutoff <= v.val := by omega
        simp [Term.eval, hlt, h.2 v hge]
  | natLit _ => simp [Term.lift, Term.eval]
  | boolLit _ => simp [Term.lift, Term.eval]
  | pauliLit _ => simp [Term.lift, Term.eval]
  | add a b iha ihb =>
      simp [Term.lift, Term.eval, iha h fuel, ihb h fuel]
  | sub a b iha ihb =>
      simp [Term.lift, Term.eval, iha h fuel, ihb h fuel]
  | mul a b iha ihb =>
      simp [Term.lift, Term.eval, iha h fuel, ihb h fuel]
  | div a b iha ihb =>
      simp [Term.lift, Term.eval, iha h fuel, ihb h fuel]
  | mod a b iha ihb =>
      simp [Term.lift, Term.eval, iha h fuel, ihb h fuel]
  | eqNat a b iha ihb =>
      simp [Term.lift, Term.eval, iha h fuel, ihb h fuel]
  | ltNat a b iha ihb =>
      simp [Term.lift, Term.eval, iha h fuel, ihb h fuel]
  | leNat a b iha ihb =>
      simp [Term.lift, Term.eval, iha h fuel, ihb h fuel]
  | not a ih =>
      simp [Term.lift, Term.eval, ih h fuel]
  | and a b iha ihb =>
      simp [Term.lift, Term.eval, iha h fuel, ihb h fuel]
  | or a b iha ihb =>
      simp [Term.lift, Term.eval, iha h fuel, ihb h fuel]
  | ite c t e ihc iht ihe =>
      simp [Term.lift, Term.eval, ihc h fuel, iht h fuel, ihe h fuel]
  | pauliMul a b iha ihb =>
      simp [Term.lift, Term.eval, iha h fuel, ihb h fuel]
  | anticommutes a b iha ihb =>
      simp [Term.lift, Term.eval, iha h fuel, ihb h fuel]
  | stabLam entry ih =>
      simp [Term.lift, Term.eval]
      funext q
      exact ih (EnvLifted.underBinder h q) fuel
  | stabAt s q ihs ihq =>
      simp [Term.lift, Term.eval, ihs h fuel, ihq h fuel]
  | stabFold n body ihn ihbody =>
      simp [Term.lift, Term.eval, ihn h fuel]
      cases hn : Term.eval codeBody fuel n rho with
      | none =>
          simp
      | some nv =>
          simp
          congr
          funext i q
          have hbody := ihbody (EnvLifted.underBinder h i) fuel
          rw [hbody]
  | recCall d k ihd ihk =>
      cases fuel with
      | zero =>
          simp [Term.lift, Term.eval]
      | succ fuel =>
          simp [Term.lift, Term.eval, ihd h fuel, ihk h fuel]

private def Term.eval_instantiateNatAt {arity cutoff : Nat} {ty : Ty}
    (t : Term (arity + 1) ty) (x : Term arity .nat) (hcut : cutoff <= arity)
    (codeBody : Term 2 .stab) (fuel : Nat) {rho : Env arity}
    {rho' : Env (arity + 1)} {xv : Nat}
    (hxAll : forall fuel', Term.eval codeBody fuel' x rho = some xv)
    (hins : EnvInserted cutoff xv rho rho' hcut) :
    Term.eval codeBody fuel (Term.instantiateNatAt cutoff x hcut t) rho =
      Term.eval codeBody fuel t rho' :=
  match t with
  | .var v => by
      unfold Term.instantiateNatAt
      by_cases hlt : v.val < cutoff
      · simp [hlt, Term.eval]
        exact (hins.1.1 ⟨v.val, by omega⟩ hlt).symm
      · by_cases heq : v.val = cutoff
        · simp [hlt, heq, Term.eval, hxAll fuel]
          have hv : v = ⟨cutoff, Nat.lt_succ_of_le hcut⟩ := Fin.ext heq
          simpa [hv] using hins.2.symm
        · have hgt : cutoff < v.val := by omega
          have hgePred : cutoff <= v.val - 1 := by omega
          let pred : Fin arity := ⟨v.val - 1, by omega⟩
          have hshift :=
            hins.1.2 pred hgePred
          simp [hlt, heq, Term.eval]
          have hidx :
              (⟨pred.val + 1, Nat.succ_lt_succ pred.isLt⟩ : Fin (arity + 1)) = v := by
            apply Fin.ext
            dsimp [pred]
            omega
          simpa [pred, hidx] using hshift.symm
  | .natLit _ => by
      simp [Term.instantiateNatAt, Term.eval]
  | .boolLit _ => by
      simp [Term.instantiateNatAt, Term.eval]
  | .pauliLit _ => by
      simp [Term.instantiateNatAt, Term.eval]
  | .add a b => by
      simp [Term.instantiateNatAt, Term.eval,
        Term.eval_instantiateNatAt a x hcut codeBody fuel hxAll hins,
        Term.eval_instantiateNatAt b x hcut codeBody fuel hxAll hins]
  | .sub a b => by
      simp [Term.instantiateNatAt, Term.eval,
        Term.eval_instantiateNatAt a x hcut codeBody fuel hxAll hins,
        Term.eval_instantiateNatAt b x hcut codeBody fuel hxAll hins]
  | .mul a b => by
      simp [Term.instantiateNatAt, Term.eval,
        Term.eval_instantiateNatAt a x hcut codeBody fuel hxAll hins,
        Term.eval_instantiateNatAt b x hcut codeBody fuel hxAll hins]
  | .div a b => by
      simp [Term.instantiateNatAt, Term.eval,
        Term.eval_instantiateNatAt a x hcut codeBody fuel hxAll hins,
        Term.eval_instantiateNatAt b x hcut codeBody fuel hxAll hins]
  | .mod a b => by
      simp [Term.instantiateNatAt, Term.eval,
        Term.eval_instantiateNatAt a x hcut codeBody fuel hxAll hins,
        Term.eval_instantiateNatAt b x hcut codeBody fuel hxAll hins]
  | .eqNat a b => by
      simp [Term.instantiateNatAt, Term.eval,
        Term.eval_instantiateNatAt a x hcut codeBody fuel hxAll hins,
        Term.eval_instantiateNatAt b x hcut codeBody fuel hxAll hins]
  | .ltNat a b => by
      simp [Term.instantiateNatAt, Term.eval,
        Term.eval_instantiateNatAt a x hcut codeBody fuel hxAll hins,
        Term.eval_instantiateNatAt b x hcut codeBody fuel hxAll hins]
  | .leNat a b => by
      simp [Term.instantiateNatAt, Term.eval,
        Term.eval_instantiateNatAt a x hcut codeBody fuel hxAll hins,
        Term.eval_instantiateNatAt b x hcut codeBody fuel hxAll hins]
  | .not a => by
      simp [Term.instantiateNatAt, Term.eval,
        Term.eval_instantiateNatAt a x hcut codeBody fuel hxAll hins]
  | .and a b => by
      simp [Term.instantiateNatAt, Term.eval,
        Term.eval_instantiateNatAt a x hcut codeBody fuel hxAll hins,
        Term.eval_instantiateNatAt b x hcut codeBody fuel hxAll hins]
  | .or a b => by
      simp [Term.instantiateNatAt, Term.eval,
        Term.eval_instantiateNatAt a x hcut codeBody fuel hxAll hins,
        Term.eval_instantiateNatAt b x hcut codeBody fuel hxAll hins]
  | .ite c t e => by
      simp [Term.instantiateNatAt, Term.eval,
        Term.eval_instantiateNatAt c x hcut codeBody fuel hxAll hins,
        Term.eval_instantiateNatAt t x hcut codeBody fuel hxAll hins,
        Term.eval_instantiateNatAt e x hcut codeBody fuel hxAll hins]
  | .pauliMul a b => by
      simp [Term.instantiateNatAt, Term.eval,
        Term.eval_instantiateNatAt a x hcut codeBody fuel hxAll hins,
        Term.eval_instantiateNatAt b x hcut codeBody fuel hxAll hins]
  | .anticommutes a b => by
      simp [Term.instantiateNatAt, Term.eval,
        Term.eval_instantiateNatAt a x hcut codeBody fuel hxAll hins,
        Term.eval_instantiateNatAt b x hcut codeBody fuel hxAll hins]
  | .stabLam entry => by
      simp [Term.instantiateNatAt, Term.eval]
      funext q
      have hxweak :
          forall fuel', Term.eval codeBody fuel' x.weaken (Env.cons q rho) = some xv := by
        intro fuel'
        simpa [Term.weaken] using
          (Term.eval_lift_of_env x (EnvLifted.top rho q) codeBody fuel').trans (hxAll fuel')
      exact Term.eval_instantiateNatAt entry x.weaken (by omega) codeBody fuel hxweak
        (EnvInserted.underBinder hins q)
  | .stabAt s q => by
      simp [Term.instantiateNatAt, Term.eval,
        Term.eval_instantiateNatAt s x hcut codeBody fuel hxAll hins,
        Term.eval_instantiateNatAt q x hcut codeBody fuel hxAll hins]
  | .stabFold n body => by
      simp [Term.instantiateNatAt, Term.eval,
        Term.eval_instantiateNatAt n x hcut codeBody fuel hxAll hins]
      cases hn : Term.eval codeBody fuel n rho' with
      | none =>
          simp
      | some nv =>
          simp
          congr
          funext i q
          have hxweak :
              forall fuel', Term.eval codeBody fuel' x.weaken (Env.cons i rho) = some xv := by
            intro fuel'
            simpa [Term.weaken] using
              (Term.eval_lift_of_env x (EnvLifted.top rho i) codeBody fuel').trans
                (hxAll fuel')
          have hbody :=
            Term.eval_instantiateNatAt body x.weaken (by omega) codeBody fuel hxweak
              (EnvInserted.underBinder hins i)
          rw [hbody]
  | .recCall d k => by
      cases fuel with
      | zero =>
          simp [Term.instantiateNatAt, Term.eval]
      | succ fuel =>
          simp [Term.instantiateNatAt, Term.eval,
            Term.eval_instantiateNatAt d x hcut codeBody fuel hxAll hins,
            Term.eval_instantiateNatAt k x hcut codeBody fuel hxAll hins]
termination_by Term.sizeOfTerm t
decreasing_by
  all_goals
    simp_wf
    simp [Term.sizeOfTerm]
    try omega

/- Pure witnesses whose evaluation is independent of recursion fuel and the
   ambient code body.  This is the arithmetic/Boolean fragment of the object
   language; stabilizer observation and recursive calls are excluded from beta
   rules for `applyNat`. -/
inductive PureTerm : {arity : Nat} -> {ty : Ty} -> Term arity ty -> Type where
  | var {arity : Nat} (v : Fin arity) : PureTerm (.var v)
  | natLit {arity : Nat} (n : Nat) : PureTerm (Term.natLit (arity := arity) n)
  | boolLit {arity : Nat} (b : Bool) : PureTerm (Term.boolLit (arity := arity) b)
  | add {arity : Nat} {a b : Term arity .nat} :
      PureTerm a -> PureTerm b -> PureTerm (.add a b)
  | sub {arity : Nat} {a b : Term arity .nat} :
      PureTerm a -> PureTerm b -> PureTerm (.sub a b)
  | mul {arity : Nat} {a b : Term arity .nat} :
      PureTerm a -> PureTerm b -> PureTerm (.mul a b)
  | div {arity : Nat} {a b : Term arity .nat} :
      PureTerm a -> PureTerm b -> PureTerm (.div a b)
  | mod {arity : Nat} {a b : Term arity .nat} :
      PureTerm a -> PureTerm b -> PureTerm (.mod a b)
  | eqNat {arity : Nat} {a b : Term arity .nat} :
      PureTerm a -> PureTerm b -> PureTerm (.eqNat a b)
  | ltNat {arity : Nat} {a b : Term arity .nat} :
      PureTerm a -> PureTerm b -> PureTerm (.ltNat a b)
  | leNat {arity : Nat} {a b : Term arity .nat} :
      PureTerm a -> PureTerm b -> PureTerm (.leNat a b)
  | not {arity : Nat} {a : Term arity .bool} :
      PureTerm a -> PureTerm (.not a)
  | and {arity : Nat} {a b : Term arity .bool} :
      PureTerm a -> PureTerm b -> PureTerm (.and a b)
  | or {arity : Nat} {a b : Term arity .bool} :
      PureTerm a -> PureTerm b -> PureTerm (.or a b)
  | ite {arity : Nat} {ty : Ty} {c : Term arity .bool} {a b : Term arity ty} :
      PureTerm c -> PureTerm a -> PureTerm b -> PureTerm (.ite c a b)

abbrev PureNatTerm {arity : Nat} (x : Term arity .nat) : Type :=
  PureTerm x

abbrev PureBoolTerm {arity : Nat} (x : Term arity .bool) : Type :=
  PureTerm x

namespace PureTerm

theorem eval_stable {arity : Nat} {ty : Ty} {x : Term arity ty} (hx : PureTerm x)
    (codeBody codeBody' : Term 2 .stab) (fuel fuel' : Nat) (rho : Env arity) :
    Term.eval codeBody fuel x rho = Term.eval codeBody' fuel' x rho := by
  induction hx with
  | var v =>
      simp [Term.eval]
  | natLit n =>
      simp [Term.eval]
  | boolLit b =>
      simp [Term.eval]
  | add ha hb iha ihb =>
      simp [Term.eval, iha, ihb]
  | sub ha hb iha ihb =>
      simp [Term.eval, iha, ihb]
  | mul ha hb iha ihb =>
      simp [Term.eval, iha, ihb]
  | div ha hb iha ihb =>
      simp [Term.eval, iha, ihb]
  | mod ha hb iha ihb =>
      simp [Term.eval, iha, ihb]
  | eqNat ha hb iha ihb =>
      simp [Term.eval, iha, ihb]
  | ltNat ha hb iha ihb =>
      simp [Term.eval, iha, ihb]
  | leNat ha hb iha ihb =>
      simp [Term.eval, iha, ihb]
  | not ha iha =>
      simp [Term.eval, iha]
  | and ha hb iha ihb =>
      simp [Term.eval, iha, ihb]
  | or ha hb iha ihb =>
      simp [Term.eval, iha, ihb]
  | ite hc ha hb ihc iha ihb =>
      simp [Term.eval, ihc, iha, ihb]

theorem eval_total {arity : Nat} {ty : Ty} {x : Term arity ty} (hx : PureTerm x)
    (codeBody : Term 2 .stab) (fuel : Nat) (rho : Env arity) :
    exists xv, Term.eval codeBody fuel x rho = some xv := by
  induction hx with
  | var v =>
      exact ⟨rho v, by simp [Term.eval]⟩
  | natLit n =>
      exact ⟨n, by simp [Term.eval]⟩
  | boolLit b =>
      exact ⟨b, by simp [Term.eval]⟩
  | add ha hb iha ihb =>
      rcases iha with ⟨av, hav⟩
      rcases ihb with ⟨bv, hbv⟩
      exact ⟨av + bv, by simp [Term.eval, hav, hbv]⟩
  | sub ha hb iha ihb =>
      rcases iha with ⟨av, hav⟩
      rcases ihb with ⟨bv, hbv⟩
      exact ⟨av - bv, by simp [Term.eval, hav, hbv]⟩
  | mul ha hb iha ihb =>
      rcases iha with ⟨av, hav⟩
      rcases ihb with ⟨bv, hbv⟩
      exact ⟨av * bv, by simp [Term.eval, hav, hbv]⟩
  | div ha hb iha ihb =>
      rcases iha with ⟨av, hav⟩
      rcases ihb with ⟨bv, hbv⟩
      exact ⟨av / bv, by simp [Term.eval, hav, hbv]⟩
  | mod ha hb iha ihb =>
      rcases iha with ⟨av, hav⟩
      rcases ihb with ⟨bv, hbv⟩
      exact ⟨av % bv, by simp [Term.eval, hav, hbv]⟩
  | eqNat ha hb iha ihb =>
      rcases iha with ⟨av, hav⟩
      rcases ihb with ⟨bv, hbv⟩
      exact ⟨decide (av = bv), by simp [Term.eval, hav, hbv]⟩
  | ltNat ha hb iha ihb =>
      rcases iha with ⟨av, hav⟩
      rcases ihb with ⟨bv, hbv⟩
      exact ⟨decide (av < bv), by simp [Term.eval, hav, hbv]⟩
  | leNat ha hb iha ihb =>
      rcases iha with ⟨av, hav⟩
      rcases ihb with ⟨bv, hbv⟩
      exact ⟨decide (av <= bv), by simp [Term.eval, hav, hbv]⟩
  | not ha iha =>
      rcases iha with ⟨av, hav⟩
      exact ⟨!av, by simp [Term.eval, hav]⟩
  | and ha hb iha ihb =>
      rcases iha with ⟨av, hav⟩
      cases av
      · exact ⟨false, by simp [Term.eval, hav]⟩
      · rcases ihb with ⟨bv, hbv⟩
        exact ⟨bv, by simp [Term.eval, hav, hbv]⟩
  | or ha hb iha ihb =>
      rcases iha with ⟨av, hav⟩
      cases av
      · rcases ihb with ⟨bv, hbv⟩
        exact ⟨bv, by simp [Term.eval, hav, hbv]⟩
      · exact ⟨true, by simp [Term.eval, hav]⟩
  | ite hc ha hb ihc iha ihb =>
      rcases ihc with ⟨cv, hcv⟩
      cases cv
      · rcases ihb with ⟨bv, hbv⟩
        exact ⟨bv, by simp [Term.eval, hcv, hbv]⟩
      · rcases iha with ⟨av, hav⟩
        exact ⟨av, by simp [Term.eval, hcv, hav]⟩

end PureTerm

namespace PureNatTerm

def nat {arity : Nat} (n : Nat) :
    PureNatTerm (Term.natLit (arity := arity) n) :=
  PureTerm.natLit (arity := arity) n

def var {arity : Nat} (v : Fin arity) : PureNatTerm (.var v) :=
  PureTerm.var v

def natLit {arity : Nat} (n : Nat) : PureNatTerm (.natLit (arity := arity) n) :=
  PureTerm.natLit (arity := arity) n

def add {arity : Nat} {a b : Term arity .nat} :
    PureNatTerm a -> PureNatTerm b -> PureNatTerm (.add a b) :=
  PureTerm.add

def sub {arity : Nat} {a b : Term arity .nat} :
    PureNatTerm a -> PureNatTerm b -> PureNatTerm (.sub a b) :=
  PureTerm.sub

def mul {arity : Nat} {a b : Term arity .nat} :
    PureNatTerm a -> PureNatTerm b -> PureNatTerm (.mul a b) :=
  PureTerm.mul

def div {arity : Nat} {a b : Term arity .nat} :
    PureNatTerm a -> PureNatTerm b -> PureNatTerm (.div a b) :=
  PureTerm.div

def mod {arity : Nat} {a b : Term arity .nat} :
    PureNatTerm a -> PureNatTerm b -> PureNatTerm (.mod a b) :=
  PureTerm.mod

def ite {arity : Nat} {c : Term arity .bool} {a b : Term arity .nat} :
    PureBoolTerm c -> PureNatTerm a -> PureNatTerm b -> PureNatTerm (.ite c a b) :=
  PureTerm.ite

def gridIdxLeft {arity : Nat} {dist row col : Term arity .nat}
    (hd : PureNatTerm dist) (hr : PureNatTerm row) (hc : PureNatTerm col) :
    PureNatTerm (NatArithmetic.gridIdxLeft dist row col) :=
  .add (.mul hd hr) hc

def rowOf {arity : Nat} {idx dist : Term arity .nat}
    (hi : PureNatTerm idx) (hd : PureNatTerm dist) :
    PureNatTerm (NatArithmetic.rowOf idx dist) :=
  .div hi hd

def colOf {arity : Nat} {idx dist : Term arity .nat}
    (hi : PureNatTerm idx) (hd : PureNatTerm dist) :
    PureNatTerm (NatArithmetic.colOf idx dist) :=
  .mod hi hd

theorem eval_stable {arity : Nat} {x : Term arity .nat} (hx : PureNatTerm x)
    (codeBody codeBody' : Term 2 .stab) (fuel fuel' : Nat) (rho : Env arity) :
    Term.eval codeBody fuel x rho = Term.eval codeBody' fuel' x rho := by
  exact PureTerm.eval_stable hx codeBody codeBody' fuel fuel' rho

end PureNatTerm

namespace PureBoolTerm

def boolLit {arity : Nat} (b : Bool) : PureBoolTerm (.boolLit (arity := arity) b) :=
  PureTerm.boolLit (arity := arity) b

def eqNat {arity : Nat} {a b : Term arity .nat} :
    PureNatTerm a -> PureNatTerm b -> PureBoolTerm (.eqNat a b) :=
  PureTerm.eqNat

def ltNat {arity : Nat} {a b : Term arity .nat} :
    PureNatTerm a -> PureNatTerm b -> PureBoolTerm (.ltNat a b) :=
  PureTerm.ltNat

def leNat {arity : Nat} {a b : Term arity .nat} :
    PureNatTerm a -> PureNatTerm b -> PureBoolTerm (.leNat a b) :=
  PureTerm.leNat

def not {arity : Nat} {a : Term arity .bool} :
    PureBoolTerm a -> PureBoolTerm (.not a) :=
  PureTerm.not

def and {arity : Nat} {a b : Term arity .bool} :
    PureBoolTerm a -> PureBoolTerm b -> PureBoolTerm (.and a b) :=
  PureTerm.and

def or {arity : Nat} {a b : Term arity .bool} :
    PureBoolTerm a -> PureBoolTerm b -> PureBoolTerm (.or a b) :=
  PureTerm.or

theorem eval_stable {arity : Nat} {x : Term arity .bool} (hx : PureBoolTerm x)
    (codeBody codeBody' : Term 2 .stab) (fuel fuel' : Nat) (rho : Env arity) :
    Term.eval codeBody fuel x rho = Term.eval codeBody' fuel' x rho := by
  exact PureTerm.eval_stable hx codeBody codeBody' fuel fuel' rho

end PureBoolTerm

namespace PureNatTerm

theorem eval_total {arity : Nat} {x : Term arity .nat} (hx : PureNatTerm x)
    (codeBody : Term 2 .stab) (fuel : Nat) (rho : Env arity) :
    exists xv, Term.eval codeBody fuel x rho = some xv := by
  exact PureTerm.eval_total hx codeBody fuel rho

end PureNatTerm

namespace PureBoolTerm

theorem eval_total {arity : Nat} {x : Term arity .bool} (hx : PureBoolTerm x)
    (codeBody : Term 2 .stab) (fuel : Nat) (rho : Env arity) :
    exists xv, Term.eval codeBody fuel x rho = some xv := by
  exact PureTerm.eval_total hx codeBody fuel rho

end PureBoolTerm

namespace PureNatTerm

theorem eval_all_fuels {arity : Nat} {x : Term arity .nat} (hx : PureNatTerm x)
    {codeBody : Term 2 .stab} {fuel : Nat} {rho : Env arity} {xv : Nat}
    (hbase : Term.eval codeBody fuel x rho = some xv) :
    forall fuel', Term.eval codeBody fuel' x rho = some xv := by
  intro fuel'
  have hstable := hx.eval_stable codeBody codeBody fuel' fuel rho
  exact hstable.trans hbase

end PureNatTerm

private theorem STerm.eval_lift_of_env {arity cutoff : Nat} {ty : Ty}
    (t : STerm arity ty) {rho : Env arity} {rho' : Env (arity + 1)}
    (h : EnvLifted cutoff rho rho') (codeBody : Term 2 .stab) (fuel : Nat)
    (E : PartialStabilizer) :
    STerm.eval codeBody fuel (t.lift cutoff) rho' E =
      STerm.eval codeBody fuel t rho E := by
  induction t generalizing cutoff fuel with
  | closed t =>
      simp [STerm.lift, STerm.eval, Term.eval_lift_of_env t h codeBody fuel]
  | boundStab =>
      simp [STerm.lift, STerm.eval]
  | ite c t e ihc iht ihe =>
      simp [STerm.lift, STerm.eval, ihc h fuel, iht h fuel, ihe h fuel]
  | pauliMul a b iha ihb =>
      simp [STerm.lift, STerm.eval, iha h fuel, ihb h fuel]
  | anticommutes a b iha ihb =>
      simp [STerm.lift, STerm.eval, iha h fuel, ihb h fuel]
  | ltNat a b iha ihb =>
      simp [STerm.lift, STerm.eval, iha h fuel, ihb h fuel]
  | stabLam entry ih =>
      simp [STerm.lift, STerm.eval]
      funext q
      exact ih (EnvLifted.underBinder h q) fuel
  | stabAt s q ihs ihq =>
      simp [STerm.lift, STerm.eval, ihs h fuel, ihq h fuel]
  | stabFold n body ihn ihbody =>
      simp [STerm.lift, STerm.eval, ihn h fuel]
      cases hn : STerm.eval codeBody fuel n rho E with
      | none =>
          simp
      | some nv =>
          simp
          congr
          funext i q
          have hbody := ihbody (EnvLifted.underBinder h i) fuel
          rw [hbody]
  | applyNat witness body ihw ihbody =>
      simp [STerm.lift, STerm.eval, ihw h fuel]
      cases hw : STerm.eval codeBody fuel witness rho E with
      | none =>
          simp
      | some wv =>
          simp
          exact ihbody (EnvLifted.underBinder h wv) fuel

private def STerm.eval_instantiateNatAt {arity cutoff : Nat} {ty : Ty}
    (t : STerm (arity + 1) ty) (x : Term arity .nat) (hcut : cutoff <= arity)
    (codeBody : Term 2 .stab) (fuel : Nat) {rho : Env arity}
    {rho' : Env (arity + 1)} {xv : Nat} (E : PartialStabilizer)
    (hxAll : forall fuel', Term.eval codeBody fuel' x rho = some xv)
    (hins : EnvInserted cutoff xv rho rho' hcut) :
    STerm.eval codeBody fuel (t.instantiateNatAt cutoff x hcut) rho E =
      STerm.eval codeBody fuel t rho' E :=
  match t with
  | .closed t => by
      simp [STerm.instantiateNatAt, STerm.eval,
        Term.eval_instantiateNatAt t x hcut codeBody fuel hxAll hins]
  | .boundStab => by
      simp [STerm.instantiateNatAt, STerm.eval]
  | .ite c t e => by
      simp [STerm.instantiateNatAt, STerm.eval,
        STerm.eval_instantiateNatAt c x hcut codeBody fuel E hxAll hins,
        STerm.eval_instantiateNatAt t x hcut codeBody fuel E hxAll hins,
        STerm.eval_instantiateNatAt e x hcut codeBody fuel E hxAll hins]
  | .pauliMul a b => by
      simp [STerm.instantiateNatAt, STerm.eval,
        STerm.eval_instantiateNatAt a x hcut codeBody fuel E hxAll hins,
        STerm.eval_instantiateNatAt b x hcut codeBody fuel E hxAll hins]
  | .anticommutes a b => by
      simp [STerm.instantiateNatAt, STerm.eval,
        STerm.eval_instantiateNatAt a x hcut codeBody fuel E hxAll hins,
        STerm.eval_instantiateNatAt b x hcut codeBody fuel E hxAll hins]
  | .ltNat a b => by
      simp [STerm.instantiateNatAt, STerm.eval,
        STerm.eval_instantiateNatAt a x hcut codeBody fuel E hxAll hins,
        STerm.eval_instantiateNatAt b x hcut codeBody fuel E hxAll hins]
  | .stabLam entry => by
      simp [STerm.instantiateNatAt, STerm.eval]
      funext q
      have hxweak :
          forall fuel',
            Term.eval codeBody fuel' x.weaken (Env.cons q rho) = some xv := by
        intro fuel'
        simpa [Term.weaken] using
          (Term.eval_lift_of_env x (EnvLifted.top rho q) codeBody fuel').trans (hxAll fuel')
      exact STerm.eval_instantiateNatAt entry x.weaken (by omega) codeBody fuel E hxweak
        (EnvInserted.underBinder hins q)
  | .stabAt s q => by
      simp [STerm.instantiateNatAt, STerm.eval,
        STerm.eval_instantiateNatAt s x hcut codeBody fuel E hxAll hins,
        STerm.eval_instantiateNatAt q x hcut codeBody fuel E hxAll hins]
  | .stabFold n body => by
      simp [STerm.instantiateNatAt, STerm.eval,
        STerm.eval_instantiateNatAt n x hcut codeBody fuel E hxAll hins]
      cases hn : STerm.eval codeBody fuel n rho' E with
      | none =>
          simp
      | some nv =>
          simp
          congr
          funext i q
          have hxweak :
              forall fuel',
                Term.eval codeBody fuel' x.weaken (Env.cons i rho) = some xv := by
            intro fuel'
            simpa [Term.weaken] using
              (Term.eval_lift_of_env x (EnvLifted.top rho i) codeBody fuel').trans
                (hxAll fuel')
          have hbody :=
            STerm.eval_instantiateNatAt body x.weaken (by omega) codeBody fuel E hxweak
              (EnvInserted.underBinder hins i)
          rw [hbody]
  | .applyNat witness body => by
      simp [STerm.instantiateNatAt, STerm.eval,
        STerm.eval_instantiateNatAt witness x hcut codeBody fuel E hxAll hins]
      cases hw : STerm.eval codeBody fuel witness rho' E with
      | none =>
          simp
      | some wv =>
          simp
          have hxweak :
              forall fuel',
                Term.eval codeBody fuel' x.weaken (Env.cons wv rho) = some xv := by
            intro fuel'
            simpa [Term.weaken] using
              (Term.eval_lift_of_env x (EnvLifted.top rho wv) codeBody fuel').trans
                (hxAll fuel')
          exact STerm.eval_instantiateNatAt body x.weaken (by omega) codeBody fuel E hxweak
            (EnvInserted.underBinder hins wv)
termination_by STerm.sizeOfSTerm t
decreasing_by
  all_goals
    simp_wf
    simp [STerm.sizeOfSTerm]
    try omega

private theorem eval_lift_of_env {arity cutoff : Nat}
    (A : SFormula arity) {rho : Env arity} {rho' : Env (arity + 1)}
    (h : EnvLifted cutoff rho rho') (codeBody : Term 2 .stab) (fuel : Nat)
    (E : PartialStabilizer) :
    SFormula.eval codeBody fuel (A.lift cutoff) rho' E =
      SFormula.eval codeBody fuel A rho E := by
  induction A generalizing cutoff fuel with
  | top =>
      simp [SFormula.lift, SFormula.eval]
  | bot =>
      simp [SFormula.lift, SFormula.eval]
  | eqNat a b =>
      simp [SFormula.lift, SFormula.eval, STerm.eval_lift_of_env a h codeBody fuel E,
        STerm.eval_lift_of_env b h codeBody fuel E]
  | eqBool a b =>
      simp [SFormula.lift, SFormula.eval, STerm.eval_lift_of_env a h codeBody fuel E,
        STerm.eval_lift_of_env b h codeBody fuel E]
  | eqPauli a b =>
      simp [SFormula.lift, SFormula.eval, STerm.eval_lift_of_env a h codeBody fuel E,
        STerm.eval_lift_of_env b h codeBody fuel E]
  | eqStabUpTo n a b =>
      simp [SFormula.lift, SFormula.eval, STerm.eval_lift_of_env n h codeBody fuel E,
        STerm.eval_lift_of_env a h codeBody fuel E,
        STerm.eval_lift_of_env b h codeBody fuel E]
  | commutesUpTo n a b =>
      simp [SFormula.lift, SFormula.eval, STerm.eval_lift_of_env n h codeBody fuel E,
        STerm.eval_lift_of_env a h codeBody fuel E,
        STerm.eval_lift_of_env b h codeBody fuel E]
  | weightLe n a w =>
      simp [SFormula.lift, SFormula.eval, STerm.eval_lift_of_env n h codeBody fuel E,
        STerm.eval_lift_of_env a h codeBody fuel E,
        STerm.eval_lift_of_env w h codeBody fuel E]
  | and A B ihA ihB =>
      simp [SFormula.lift, SFormula.eval, ihA h fuel, ihB h fuel]
  | or A B ihA ihB =>
      simp [SFormula.lift, SFormula.eval, ihA h fuel, ihB h fuel]
  | not A ih =>
      simp [SFormula.lift, SFormula.eval, ih h fuel]
  | imp A B ihA ihB =>
      simp [SFormula.lift, SFormula.eval, ihA h fuel, ihB h fuel]
  | applyNat witness A ih =>
      simp [SFormula.lift, SFormula.eval, STerm.eval_lift_of_env witness h codeBody fuel E]
      cases hw : STerm.eval codeBody fuel witness rho E with
      | none => simp
      | some wv =>
          simp
          exact ih (EnvLifted.underBinder h wv) fuel
  | allNatLt n A ih =>
      simp [SFormula.lift, SFormula.eval, STerm.eval_lift_of_env n h codeBody fuel E]
      cases hn : STerm.eval codeBody fuel n rho E with
      | none => simp
      | some nv =>
          simp
          congr
          funext x
          exact ih (EnvLifted.underBinder h x) fuel
  | existsNatLt n A ih =>
      simp [SFormula.lift, SFormula.eval, STerm.eval_lift_of_env n h codeBody fuel E]
      cases hn : STerm.eval codeBody fuel n rho E with
      | none => simp
      | some nv =>
          simp
          congr
          funext x
          exact ih (EnvLifted.underBinder h x) fuel

private def eval_instantiateNatAt {arity cutoff : Nat}
    (A : SFormula (arity + 1)) (x : Term arity .nat) (hcut : cutoff <= arity)
    (codeBody : Term 2 .stab) (fuel : Nat) {rho : Env arity}
    {rho' : Env (arity + 1)} {xv : Nat} (E : PartialStabilizer)
    (hxAll : forall fuel', Term.eval codeBody fuel' x rho = some xv)
    (hins : EnvInserted cutoff xv rho rho' hcut) :
    SFormula.eval codeBody fuel (A.instantiateNatAt cutoff x hcut) rho E =
      SFormula.eval codeBody fuel A rho' E :=
  match A with
  | .top => by
      simp [SFormula.instantiateNatAt, SFormula.eval]
  | .bot => by
      simp [SFormula.instantiateNatAt, SFormula.eval]
  | .eqNat a b => by
      simp [SFormula.instantiateNatAt, SFormula.eval,
        STerm.eval_instantiateNatAt a x hcut codeBody fuel E hxAll hins,
        STerm.eval_instantiateNatAt b x hcut codeBody fuel E hxAll hins]
  | .eqBool a b => by
      simp [SFormula.instantiateNatAt, SFormula.eval,
        STerm.eval_instantiateNatAt a x hcut codeBody fuel E hxAll hins,
        STerm.eval_instantiateNatAt b x hcut codeBody fuel E hxAll hins]
  | .eqPauli a b => by
      simp [SFormula.instantiateNatAt, SFormula.eval,
        STerm.eval_instantiateNatAt a x hcut codeBody fuel E hxAll hins,
        STerm.eval_instantiateNatAt b x hcut codeBody fuel E hxAll hins]
  | .eqStabUpTo n a b => by
      simp [SFormula.instantiateNatAt, SFormula.eval,
        STerm.eval_instantiateNatAt n x hcut codeBody fuel E hxAll hins,
        STerm.eval_instantiateNatAt a x hcut codeBody fuel E hxAll hins,
        STerm.eval_instantiateNatAt b x hcut codeBody fuel E hxAll hins]
  | .commutesUpTo n a b => by
      simp [SFormula.instantiateNatAt, SFormula.eval,
        STerm.eval_instantiateNatAt n x hcut codeBody fuel E hxAll hins,
        STerm.eval_instantiateNatAt a x hcut codeBody fuel E hxAll hins,
        STerm.eval_instantiateNatAt b x hcut codeBody fuel E hxAll hins]
  | .weightLe n a w => by
      simp [SFormula.instantiateNatAt, SFormula.eval,
        STerm.eval_instantiateNatAt n x hcut codeBody fuel E hxAll hins,
        STerm.eval_instantiateNatAt a x hcut codeBody fuel E hxAll hins,
        STerm.eval_instantiateNatAt w x hcut codeBody fuel E hxAll hins]
  | .and A B => by
      simp [SFormula.instantiateNatAt, SFormula.eval,
        eval_instantiateNatAt A x hcut codeBody fuel E hxAll hins,
        eval_instantiateNatAt B x hcut codeBody fuel E hxAll hins]
  | .or A B => by
      simp [SFormula.instantiateNatAt, SFormula.eval,
        eval_instantiateNatAt A x hcut codeBody fuel E hxAll hins,
        eval_instantiateNatAt B x hcut codeBody fuel E hxAll hins]
  | .not A => by
      simp [SFormula.instantiateNatAt, SFormula.eval,
        eval_instantiateNatAt A x hcut codeBody fuel E hxAll hins]
  | .imp A B => by
      simp [SFormula.instantiateNatAt, SFormula.eval,
        eval_instantiateNatAt A x hcut codeBody fuel E hxAll hins,
        eval_instantiateNatAt B x hcut codeBody fuel E hxAll hins]
  | .applyNat witness A => by
      simp [SFormula.instantiateNatAt, SFormula.eval,
        STerm.eval_instantiateNatAt witness x hcut codeBody fuel E hxAll hins]
      cases hw : STerm.eval codeBody fuel witness rho' E with
      | none =>
          simp
      | some wv =>
          simp
          have hxweak :
              forall fuel',
                Term.eval codeBody fuel' x.weaken (Env.cons wv rho) = some xv := by
            intro fuel'
            simpa [Term.weaken] using
              (Term.eval_lift_of_env x (EnvLifted.top rho wv) codeBody fuel').trans
                (hxAll fuel')
          exact eval_instantiateNatAt A x.weaken (by omega) codeBody fuel E hxweak
            (EnvInserted.underBinder hins wv)
  | .allNatLt n A => by
      simp [SFormula.instantiateNatAt, SFormula.eval,
        STerm.eval_instantiateNatAt n x hcut codeBody fuel E hxAll hins]
      cases hn : STerm.eval codeBody fuel n rho' E with
      | none =>
          simp
      | some nv =>
          simp
          congr
          funext i
          have hxweak :
              forall fuel',
                Term.eval codeBody fuel' x.weaken (Env.cons i rho) = some xv := by
            intro fuel'
            simpa [Term.weaken] using
              (Term.eval_lift_of_env x (EnvLifted.top rho i) codeBody fuel').trans
                (hxAll fuel')
          exact eval_instantiateNatAt A x.weaken (by omega) codeBody fuel E hxweak
            (EnvInserted.underBinder hins i)
  | .existsNatLt n A => by
      simp [SFormula.instantiateNatAt, SFormula.eval,
        STerm.eval_instantiateNatAt n x hcut codeBody fuel E hxAll hins]
      cases hn : STerm.eval codeBody fuel n rho' E with
      | none =>
          simp
      | some nv =>
          simp
          congr
          funext i
          have hxweak :
              forall fuel',
                Term.eval codeBody fuel' x.weaken (Env.cons i rho) = some xv := by
            intro fuel'
            simpa [Term.weaken] using
              (Term.eval_lift_of_env x (EnvLifted.top rho i) codeBody fuel').trans
                (hxAll fuel')
          exact eval_instantiateNatAt A x.weaken (by omega) codeBody fuel E hxweak
            (EnvInserted.underBinder hins i)
termination_by SFormula.sizeOfSFormula A
decreasing_by
  all_goals
    simp_wf
    simp [SFormula.sizeOfSFormula]
    try omega

private theorem eval_applyNat_closed_instantiateTopNat {arity : Nat}
    (A : SFormula (arity + 1)) (x : Term arity .nat)
    (codeBody : Term 2 .stab) (fuel : Nat) (rho : Env arity)
    (E : PartialStabilizer) {xv : Nat}
    (hxAll : forall fuel', Term.eval codeBody fuel' x rho = some xv) :
    SFormula.eval codeBody fuel (A.instantiateTopNat x) rho E =
      SFormula.eval codeBody fuel (.applyNat (SC.closed x) A) rho E := by
  have hinst :=
    eval_instantiateNatAt A x (Nat.zero_le arity) codeBody fuel E hxAll
      (EnvInserted.top rho xv)
  simp [SFormula.instantiateTopNat, SFormula.eval, SC.closed, STerm.eval,
    hxAll fuel, hinst]

private theorem EnvLifted.duplicateTop {arity : Nat} (rho : Env (arity + 1)) :
    EnvLifted 1 rho (Env.cons (rho ⟨0, Nat.succ_pos arity⟩) rho) := by
  constructor
  · intro v hv
    cases v using Fin.cases with
    | zero => rfl
    | succ v =>
        simp at hv
  · intro v hv
    cases v using Fin.cases with
    | zero => simp at hv
    | succ v =>
        simp [Env.cons]
        apply congrArg rho
        exact Fin.ext rfl

private theorem eval_applyNat_boundNat_lift_self {arity : Nat}
    (A : SFormula (arity + 1)) (codeBody : Term 2 .stab) (fuel : Nat)
    (rho : Env (arity + 1)) (E : PartialStabilizer) :
    SFormula.eval codeBody fuel
        (.applyNat SFormula.boundNat (A.lift 1)) rho E =
      SFormula.eval codeBody fuel A rho E := by
  simp [SFormula.eval, SFormula.boundNat, SC.closed, STerm.eval, Term.eval]
  exact eval_lift_of_env A (EnvLifted.duplicateTop rho) codeBody fuel E

def nonIBool (E : PartialStabilizer) (q : Nat) : Bool :=
  match E q with
  | some p => decide (p ≠ Pauli.I)
  | none => false

def supportSet (n : Nat) (E : PartialStabilizer) : Finset Nat :=
  (Finset.range n).filter fun q => nonIBool E q = true

theorem weightUpTo_eq_supportSet_card {n : Nat} {E : PartialStabilizer}
    {w : Nat} :
    weightUpTo n E = some w -> w = (supportSet n E).card := by
  induction n generalizing w with
  | zero =>
      intro h
      simp [weightUpTo, supportSet] at h ⊢
      exact h.symm
  | succ m ih =>
      intro h
      simp [weightUpTo] at h
      cases hprev : weightUpTo m E with
      | none =>
          simp [hprev] at h
      | some rest =>
          cases hE : E m with
          | none =>
              simp [hprev, hE] at h
          | some p =>
              simp [hprev, hE] at h
              have hrest : rest = (supportSet m E).card := ih hprev
              rw [← h]
              rw [hrest]
              by_cases hp : p = Pauli.I
              · unfold supportSet
                rw [Finset.range_add_one, Finset.filter_insert]
                simp [nonIBool, hE, hp]
              · unfold supportSet
                rw [Finset.range_add_one, Finset.filter_insert]
                simp [nonIBool, hE, hp]

private theorem weight_not_le_of_injective_support {n k limit w : Nat}
    {E : PartialStabilizer} {slot : Nat -> Nat}
    (hslotLt : forall i, i < k -> slot i < n)
    (hnonI : forall i, i < k -> nonIBool E (slot i) = true)
    (hinj : forall i j, i < k -> j < k -> slot i = slot j -> i = j)
    (hlimit : limit < k)
    (hweight : weightUpTo n E = some w) :
    ¬ w <= limit := by
  have hweightEq : w = (supportSet n E).card := weightUpTo_eq_supportSet_card hweight
  let f : Fin k -> Nat := fun i => slot i.val
  have hinjF : Function.Injective f := by
    intro a b h
    apply Fin.ext
    exact hinj a.val b.val a.isLt b.isLt h
  have hsubset : Finset.image f (Finset.univ : Finset (Fin k)) ⊆ supportSet n E := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨i, _, rfl⟩
    simp [supportSet]
    exact ⟨hslotLt i.val i.isLt, hnonI i.val i.isLt⟩
  have hcardImage : (Finset.image f (Finset.univ : Finset (Fin k))).card = k := by
    rw [Finset.card_image_of_injective _ hinjF]
    simp
  have hkLeSupport : k <= (supportSet n E).card := by
    rw [← hcardImage]
    exact Finset.card_le_card hsubset
  intro hle
  rw [hweightEq] at hle
  omega

private theorem weight_not_le_of_surjective_support {n k limit w : Nat}
    {E : PartialStabilizer} {rowOf : Nat -> Nat}
    (hcover : forall i, i < k ->
      exists q, q < n /\ nonIBool E q = true /\ rowOf q = i)
    (hlimit : limit < k)
    (hweight : weightUpTo n E = some w) :
    ¬ w <= limit := by
  classical
  choose pick hpick using hcover
  let slot : Nat -> Nat := fun i =>
    if h : i < k then pick i h else 0
  have hslotLt : forall i, i < k -> slot i < n := by
    intro i hi
    exact (by simpa [slot, hi] using (hpick i hi).1)
  have hnonI : forall i, i < k -> nonIBool E (slot i) = true := by
    intro i hi
    exact (by simpa [slot, hi] using (hpick i hi).2.1)
  have hinj : forall i j, i < k -> j < k -> slot i = slot j -> i = j := by
    intro i j hi hj hslot
    have hirow : rowOf (slot i) = i := by
      simpa [slot, hi] using (hpick i hi).2.2
    have hjrow : rowOf (slot j) = j := by
      simpa [slot, hj] using (hpick j hj).2.2
    rw [hslot] at hirow
    exact hirow.symm.trans hjrow
  exact weight_not_le_of_injective_support hslotLt hnonI hinj hlimit hweight

private theorem EnvLifted.underTop {arity : Nat} (rho : Env arity) (x : Nat) :
    EnvLifted 0 rho (Env.cons x rho) := by
  constructor
  · intro v hv
    omega
  · intro v _hv
    simp [Env.cons]

private abbrev partialStabMul : PartialStabilizer -> PartialStabilizer -> PartialStabilizer :=
  partialStabilizerMul

private theorem pauli_anticommutes_symm (p q : Pauli) :
    ErrorVec.Pauli.anticommutes p q = ErrorVec.Pauli.anticommutes q p := by
  cases p <;> cases q <;> rfl

private theorem pauli_anticommutes_mul_left (a b c : Pauli) :
    ErrorVec.Pauli.anticommutes (Pauli.mul a b) c =
      xor (ErrorVec.Pauli.anticommutes a c) (ErrorVec.Pauli.anticommutes b c) := by
  cases a <;> cases b <;> cases c <;> rfl

private theorem pauli_mul_comm (a b : Pauli) :
    Pauli.mul a b = Pauli.mul b a := by
  cases a <;> cases b <;> rfl

private theorem pauli_mul_cancel_middle (a b c : Pauli) :
    Pauli.mul (Pauli.mul a b) (Pauli.mul b c) = Pauli.mul a c := by
  cases a <;> cases b <;> cases c <;> rfl

private theorem parityUpTo_symm {n : Nat} {A B : PartialStabilizer} :
    parityUpTo n A B = parityUpTo n B A := by
  induction n with
  | zero =>
      rfl
  | succ m ih =>
      unfold parityUpTo
      rw [ih]
      cases hA : A m <;> cases hB : B m <;>
        simp [pauli_anticommutes_symm]

private theorem parityUpTo_false_of_localCommutes {arity : Nat}
    {codeBody : Term 2 .stab} {fuel : Nat} {rho : Env arity}
    {E : PartialStabilizer} {A B : STerm arity .stab}
    {Av Bv : PartialStabilizer} {n : Nat}
    (hlocal : forall q, q < n ->
      SFormula.eval codeBody fuel
        (SFormula.localCommutesAt A.weaken B.weaken SFormula.boundNat)
        (Env.cons q rho) E = some true)
    (hA : A.eval codeBody fuel rho E = some Av)
    (hB : B.eval codeBody fuel rho E = some Bv) :
    parityUpTo n Av Bv = some false := by
  induction n with
  | zero =>
      rfl
  | succ m ih =>
      unfold parityUpTo
      have hprev : parityUpTo m Av Bv = some false :=
        ih (fun q hq => hlocal q (by omega))
      have hm := hlocal m (Nat.lt_succ_self m)
      have hAweak :
          A.weaken.eval codeBody fuel (Env.cons m rho) E = some Av := by
        simpa [STerm.weaken] using
          STerm.eval_lift_of_env A (EnvLifted.underTop rho m) codeBody fuel E ▸ hA
      have hBweak :
          B.weaken.eval codeBody fuel (Env.cons m rho) E = some Bv := by
        simpa [STerm.weaken] using
          STerm.eval_lift_of_env B (EnvLifted.underTop rho m) codeBody fuel E ▸ hB
      have hBound :
          SFormula.boundNat.eval codeBody fuel (Env.cons m rho) E = some m := by
        unfold SFormula.boundNat SC.closed STerm.eval Term.eval
        change some ((Env.cons m rho) ⟨0, Nat.succ_pos arity⟩) = some m
        rfl
      simp [SFormula.localCommutesAt, SFormula.eval, STerm.eval, hAweak, hBweak, hBound,
        SC.b, Term.eval] at hm
      cases hAv : Av m with
      | none =>
          simp [hAv] at hm
      | some av =>
          cases hBv : Bv m with
          | none =>
              simp [hAv, hBv] at hm
          | some bv =>
              have hAnti : ErrorVec.Pauli.anticommutes av bv = false := by
                simpa [hAv, hBv] using hm
              simp [hprev, hAnti]

private theorem parityUpTo_false_of_pointwiseCommutes {arity : Nat}
    {codeBody : Term 2 .stab} {fuel : Nat} {rho : Env arity}
    {E : PartialStabilizer} {nTerm : STerm arity .nat} {A B : STerm arity .stab}
    {nv : Nat} {Av Bv : PartialStabilizer}
    (hPoint :
      SFormula.eval codeBody fuel (SFormula.pointwiseCommutesUpTo nTerm A B) rho E =
        some true)
    (hN : nTerm.eval codeBody fuel rho E = some nv)
    (hA : A.eval codeBody fuel rho E = some Av)
    (hB : B.eval codeBody fuel rho E = some Bv) :
    parityUpTo nv Av Bv = some false := by
  simp [SFormula.pointwiseCommutesUpTo, SFormula.eval, hN] at hPoint
  exact parityUpTo_false_of_localCommutes
    (fun q hq => allNatLt_sound hPoint q hq) hA hB

/-- Parity is odd (`some true`) when there is a UNIQUE anticommuting slot.

    This is the sound semantic core of `Deriv.noncommutesOfSingleAnti`.  The
    conclusion genuinely requires all three hypotheses:
    * `hq0` : the distinguished slot `q0` is in range;
    * `hanti` : the two stabilizers anticommute at `q0`;
    * `hrest` : the two stabilizers commute at every OTHER in-range slot.
    Dropping `hrest` is unsound — two anticommuting slots cancel to even
    parity (cf. the `X⊗Z` vs `Z⊗X` example, which commute). -/
private theorem parityUpTo_single_anti {n q0 : Nat} {A B : PartialStabilizer}
    (hq0 : q0 < n)
    (hdef : ∀ q, q < n → (∃ p, A q = some p) ∧ (∃ p, B q = some p))
    (hanti : ∀ pa pb, A q0 = some pa → B q0 = some pb →
        ErrorVec.Pauli.anticommutes pa pb = true)
    (hrest : ∀ q, q < n → q ≠ q0 → ∀ pa pb, A q = some pa → B q = some pb →
        ErrorVec.Pauli.anticommutes pa pb = false) :
    parityUpTo n A B = some true := by
  -- Stronger invariant: `parityUpTo m A B = some (decide (q0 < m))`.
  suffices h : ∀ m, m ≤ n → parityUpTo m A B = some (decide (q0 < m)) by
    have := h n (le_refl n)
    rw [this]
    simp [hq0]
  intro m
  induction m with
  | zero =>
      intro _
      simp [parityUpTo]
  | succ k ih =>
      intro hk
      have hkLe : k ≤ n := Nat.le_of_lt hk
      have hkLt : k < n := hk
      have hprev := ih hkLe
      unfold parityUpTo
      rw [hprev]
      obtain ⟨⟨pa, hpa⟩, ⟨pb, hpb⟩⟩ := hdef k hkLt
      rw [hpa, hpb]
      simp only [bind, Option.bind]
      by_cases hkq0 : k = q0
      · subst hkq0
        rw [hanti pa pb hpa hpb]
        have h1 : decide (k < k) = false := by simp
        have h2 : decide (k < k + 1) = true := by simp
        rw [h1, h2]
        rfl
      · rw [hrest k hkLt hkq0 pa pb hpa hpb]
        have heq : decide (q0 < k) = decide (q0 < k + 1) := by
          by_cases hq0k : q0 < k
          · simp [hq0k, Nat.lt_succ_of_lt hq0k]
          · have : ¬ q0 < k + 1 := by omega
            simp [hq0k, this]
        rw [heq]
        simp

/-- Local commutation at a slot supplies both definedness and the
    `anticommutes = false` fact for that slot. -/
private theorem localCommutes_defined_and_false {arity : Nat}
    {codeBody : Term 2 .stab} {fuel : Nat} {rho : Env arity}
    {E : PartialStabilizer} {A B : STerm arity .stab}
    {Av Bv : PartialStabilizer} {m : Nat}
    (hlocal :
      SFormula.eval codeBody fuel
        (SFormula.localCommutesAt A.weaken B.weaken SFormula.boundNat)
        (Env.cons m rho) E = some true)
    (hA : A.eval codeBody fuel rho E = some Av)
    (hB : B.eval codeBody fuel rho E = some Bv) :
    (∃ pa, Av m = some pa) ∧ (∃ pb, Bv m = some pb) ∧
      ∀ pa pb, Av m = some pa → Bv m = some pb →
        ErrorVec.Pauli.anticommutes pa pb = false := by
  have hAweak :
      A.weaken.eval codeBody fuel (Env.cons m rho) E = some Av := by
    simpa [STerm.weaken] using
      STerm.eval_lift_of_env A (EnvLifted.underTop rho m) codeBody fuel E ▸ hA
  have hBweak :
      B.weaken.eval codeBody fuel (Env.cons m rho) E = some Bv := by
    simpa [STerm.weaken] using
      STerm.eval_lift_of_env B (EnvLifted.underTop rho m) codeBody fuel E ▸ hB
  have hBound :
      SFormula.boundNat.eval codeBody fuel (Env.cons m rho) E = some m := by
    unfold SFormula.boundNat SC.closed STerm.eval Term.eval
    change some ((Env.cons m rho) ⟨0, Nat.succ_pos arity⟩) = some m
    rfl
  simp [SFormula.localCommutesAt, SFormula.eval, STerm.eval, hAweak, hBweak, hBound,
    SC.b, Term.eval] at hlocal
  cases hAv : Av m with
  | none => simp [hAv] at hlocal
  | some av =>
      cases hBv : Bv m with
      | none => simp [hAv, hBv] at hlocal
      | some bv =>
          have hAnti : ErrorVec.Pauli.anticommutes av bv = false := by
            simpa [hAv, hBv] using hlocal
          refine ⟨⟨av, rfl⟩, ⟨bv, rfl⟩, ?_⟩
          intro pa pb hpa hpb
          have hpaeq : pa = av := (Option.some.inj hpa).symm
          have hpbeq : pb = bv := (Option.some.inj hpb).symm
          rw [hpaeq, hpbeq]
          exact hAnti

/-- Eval-level assembly for `noncommutesOfSingleAnti`: odd parity from
    one anticommuting slot `q0` together with all-others-commute.  The three
    inputs mirror the rule's three premises after their soundness has been
    invoked. -/
private theorem parityUpTo_true_of_singleAntiPremises {arity : Nat}
    {codeBody : Term 2 .stab} {fuel : Nat} {rho : Env arity}
    {E : PartialStabilizer} {A B : STerm arity .stab} {q0 : STerm arity .nat}
    {nv q0v : Nat} {Av Bv : PartialStabilizer}
    (hq0Lt : q0v < nv)
    (hq0 : q0.eval codeBody fuel rho E = some q0v)
    (hA : A.eval codeBody fuel rho E = some Av)
    (hB : B.eval codeBody fuel rho E = some Bv)
    (hAnti :
      SFormula.eval codeBody fuel
        (.eqBool (.anticommutes (.stabAt A q0) (.stabAt B q0)) (SC.b true)) rho E =
        some true)
    (hImp :
      ∀ q, q < nv →
        SFormula.eval codeBody fuel
          (.imp (.not (.eqNat SFormula.boundNat q0.weaken))
            (SFormula.localCommutesAt A.weaken B.weaken SFormula.boundNat))
          (Env.cons q rho) E = some true) :
    parityUpTo nv Av Bv = some true := by
  -- `q0.weaken` evaluates to `q0v` under any extended environment.
  have hq0weak : ∀ m, q0.weaken.eval codeBody fuel (Env.cons m rho) E = some q0v := by
    intro m
    simpa [STerm.weaken] using
      STerm.eval_lift_of_env q0 (EnvLifted.underTop rho m) codeBody fuel E ▸ hq0
  -- `boundNat` evaluates to the current index.
  have hBound : ∀ m,
      SFormula.boundNat.eval codeBody fuel (Env.cons m rho) E = some m := by
    intro m
    unfold SFormula.boundNat SC.closed STerm.eval Term.eval
    change some ((Env.cons m rho) ⟨0, Nat.succ_pos arity⟩) = some m
    rfl
  -- Premise 2: anti at q0v, plus definedness at q0v.
  have hAntiPt :
      ∀ pa pb, Av q0v = some pa → Bv q0v = some pb →
        ErrorVec.Pauli.anticommutes pa pb = true := by
    intro pa pb hpa hpb
    simp [SFormula.eval, STerm.eval, hA, hB, hq0, hpa, hpb, SC.b, Term.eval] at hAnti
    exact hAnti
  have hq0Def : (∃ pa, Av q0v = some pa) ∧ (∃ pb, Bv q0v = some pb) := by
    -- if either side is undefined, premise 2 cannot evaluate to `some true`.
    have hAnti' := hAnti
    simp [SFormula.eval, STerm.eval, hA, hB, hq0, SC.b, Term.eval] at hAnti'
    cases hAv : Av q0v with
    | none => simp [hAv] at hAnti'
    | some pa =>
        cases hBv : Bv q0v with
        | none => simp [hAv, hBv] at hAnti'
        | some pb => exact ⟨⟨pa, rfl⟩, ⟨pb, rfl⟩⟩
  -- Premise 3: at every other in-range slot, the slots commute (and are defined).
  have hrestFull :
      ∀ q, q < nv → q ≠ q0v →
        ((∃ pa, Av q = some pa) ∧ (∃ pb, Bv q = some pb) ∧
          ∀ pa pb, Av q = some pa → Bv q = some pb →
            ErrorVec.Pauli.anticommutes pa pb = false) := by
    intro q hq hne
    have hbody := hImp q hq
    -- discharge the `imp` guard `q ≠ q0v` to reach `localCommutesAt`.
    have hlocal :
        SFormula.eval codeBody fuel
          (SFormula.localCommutesAt A.weaken B.weaken SFormula.boundNat)
          (Env.cons q rho) E = some true := by
      simp [SFormula.eval, hBound q, hq0weak q, hne] at hbody
      exact hbody
    exact localCommutes_defined_and_false hlocal hA hB
  -- Assemble definedness everywhere below `nv`.
  have hdef : ∀ q, q < nv → (∃ p, Av q = some p) ∧ (∃ p, Bv q = some p) := by
    intro q hq
    by_cases hqq0 : q = q0v
    · subst hqq0; exact hq0Def
    · exact ⟨(hrestFull q hq hqq0).1, (hrestFull q hq hqq0).2.1⟩
  -- The all-others-commute fact.
  have hrest : ∀ q, q < nv → q ≠ q0v → ∀ pa pb, Av q = some pa → Bv q = some pb →
      ErrorVec.Pauli.anticommutes pa pb = false := by
    intro q hq hne pa pb hpa hpb
    exact (hrestFull q hq hne).2.2 pa pb hpa hpb
  exact parityUpTo_single_anti hq0Lt hdef hAntiPt hrest

/-- Parity is even (`some false`) when there are exactly TWO DISTINCT
    anticommuting slots `q0 ≠ q1` and every other in-range slot commutes.

    This is the sound semantic core of `Deriv.commutesOfTwoAnti`.  All four
    structural hypotheses are required:
    * `hq0`, `hq1` : the two distinguished slots are in range;
    * `hne` : the two slots are DISTINCT — without it `q0 = q1` would give a
      single anticommuting slot (odd parity), so the conclusion would be
      unsound;
    * `hanti0`, `hanti1` : the two stabilizers anticommute at `q0` and at `q1`;
    * `hrest` : the two stabilizers commute at every OTHER in-range slot.
    Two anticommuting slots contribute `true` twice; `xor` cancels them, so the
    block parity is even and the stabilizers commute. -/
private theorem parityUpTo_two_anti {n q0 q1 : Nat} {A B : PartialStabilizer}
    (hq0 : q0 < n) (hq1 : q1 < n) (hne : q0 ≠ q1)
    (hdef : ∀ q, q < n → (∃ p, A q = some p) ∧ (∃ p, B q = some p))
    (hanti0 : ∀ pa pb, A q0 = some pa → B q0 = some pb →
        ErrorVec.Pauli.anticommutes pa pb = true)
    (hanti1 : ∀ pa pb, A q1 = some pa → B q1 = some pb →
        ErrorVec.Pauli.anticommutes pa pb = true)
    (hrest : ∀ q, q < n → q ≠ q0 → q ≠ q1 → ∀ pa pb, A q = some pa → B q = some pb →
        ErrorVec.Pauli.anticommutes pa pb = false) :
    parityUpTo n A B = some false := by
  -- Stronger invariant: parity after `m` slots is `xor (q0 < m) (q1 < m)`.
  -- The two distinguished slots each flip the running parity exactly once, so
  -- once both are passed (`m = n`) the parity is `xor true true = false`.
  suffices h : ∀ m, m ≤ n →
      parityUpTo m A B = some (xor (decide (q0 < m)) (decide (q1 < m))) by
    have := h n (le_refl n)
    rw [this]
    simp [hq0, hq1]
  intro m
  induction m with
  | zero =>
      intro _
      simp [parityUpTo]
  | succ k ih =>
      intro hk
      have hkLe : k ≤ n := Nat.le_of_lt hk
      have hkLt : k < n := hk
      have hprev := ih hkLe
      unfold parityUpTo
      rw [hprev]
      obtain ⟨⟨pa, hpa⟩, ⟨pb, hpb⟩⟩ := hdef k hkLt
      rw [hpa, hpb]
      simp only [bind, Option.bind]
      by_cases hkq0 : k = q0
      · -- slot k = q0: contributes `true`; q0 enters range, q1 unchanged.
        subst hkq0
        rw [hanti0 pa pb hpa hpb]
        have e0a : decide (k < k) = false := by simp
        have e0b : decide (k < k + 1) = true := by simp
        have e1 : decide (q1 < k) = decide (q1 < k + 1) := by
          by_cases h : q1 < k
          · simp [h, Nat.lt_succ_of_lt h]
          · have : ¬ q1 < k + 1 := by omega
            simp [h, this]
        rw [e0a, e0b, e1]
        cases decide (q1 < k + 1) <;> rfl
      · by_cases hkq1 : k = q1
        · -- slot k = q1: contributes `true`; q1 enters range, q0 unchanged.
          subst hkq1
          rw [hanti1 pa pb hpa hpb]
          have e1a : decide (k < k) = false := by simp
          have e1b : decide (k < k + 1) = true := by simp
          have e0 : decide (q0 < k) = decide (q0 < k + 1) := by
            by_cases h : q0 < k
            · simp [h, Nat.lt_succ_of_lt h]
            · have : ¬ q0 < k + 1 := by omega
              simp [h, this]
          rw [e1a, e1b, e0]
          cases decide (q0 < k + 1) <;> rfl
        · -- slot k is neither distinguished slot: contributes `false`.
          rw [hrest k hkLt hkq0 hkq1 pa pb hpa hpb]
          have e0 : decide (q0 < k) = decide (q0 < k + 1) := by
            by_cases h : q0 < k
            · simp [h, Nat.lt_succ_of_lt h]
            · have : ¬ q0 < k + 1 := by omega
              simp [h, this]
          have e1 : decide (q1 < k) = decide (q1 < k + 1) := by
            by_cases h : q1 < k
            · simp [h, Nat.lt_succ_of_lt h]
            · have : ¬ q1 < k + 1 := by omega
              simp [h, this]
          rw [e0, e1]
          cases decide (q0 < k + 1) <;> cases decide (q1 < k + 1) <;> rfl

/-- Eval-level assembly for `commutesOfTwoAnti`: even parity from two DISTINCT
    anticommuting slots `q0`, `q1` together with all-others-commute.  The five
    inputs mirror the rule's five premises after their soundness has been
    invoked. -/
private theorem parityUpTo_false_of_twoAntiPremises {arity : Nat}
    {codeBody : Term 2 .stab} {fuel : Nat} {rho : Env arity}
    {E : PartialStabilizer} {A B : STerm arity .stab} {q0 q1 : STerm arity .nat}
    {nv q0v q1v : Nat} {Av Bv : PartialStabilizer}
    (hq0Lt : q0v < nv) (hq1Lt : q1v < nv) (hneVal : q0v ≠ q1v)
    (hq0 : q0.eval codeBody fuel rho E = some q0v)
    (hq1 : q1.eval codeBody fuel rho E = some q1v)
    (hA : A.eval codeBody fuel rho E = some Av)
    (hB : B.eval codeBody fuel rho E = some Bv)
    (hAnti0 :
      SFormula.eval codeBody fuel
        (.eqBool (.anticommutes (.stabAt A q0) (.stabAt B q0)) (SC.b true)) rho E =
        some true)
    (hAnti1 :
      SFormula.eval codeBody fuel
        (.eqBool (.anticommutes (.stabAt A q1) (.stabAt B q1)) (SC.b true)) rho E =
        some true)
    (hImp :
      ∀ q, q < nv →
        SFormula.eval codeBody fuel
          (.imp (.not (.eqNat SFormula.boundNat q0.weaken))
            (.imp (.not (.eqNat SFormula.boundNat q1.weaken))
              (SFormula.localCommutesAt A.weaken B.weaken SFormula.boundNat)))
          (Env.cons q rho) E = some true) :
    parityUpTo nv Av Bv = some false := by
  -- `q0.weaken`/`q1.weaken` evaluate to `q0v`/`q1v` under any extended env.
  have hq0weak : ∀ m, q0.weaken.eval codeBody fuel (Env.cons m rho) E = some q0v := by
    intro m
    simpa [STerm.weaken] using
      STerm.eval_lift_of_env q0 (EnvLifted.underTop rho m) codeBody fuel E ▸ hq0
  have hq1weak : ∀ m, q1.weaken.eval codeBody fuel (Env.cons m rho) E = some q1v := by
    intro m
    simpa [STerm.weaken] using
      STerm.eval_lift_of_env q1 (EnvLifted.underTop rho m) codeBody fuel E ▸ hq1
  -- `boundNat` evaluates to the current index.
  have hBound : ∀ m,
      SFormula.boundNat.eval codeBody fuel (Env.cons m rho) E = some m := by
    intro m
    unfold SFormula.boundNat SC.closed STerm.eval Term.eval
    change some ((Env.cons m rho) ⟨0, Nat.succ_pos arity⟩) = some m
    rfl
  -- Premise: anti at q0v, plus definedness at q0v.
  have hAnti0Pt :
      ∀ pa pb, Av q0v = some pa → Bv q0v = some pb →
        ErrorVec.Pauli.anticommutes pa pb = true := by
    intro pa pb hpa hpb
    simp [SFormula.eval, STerm.eval, hA, hB, hq0, hpa, hpb, SC.b, Term.eval] at hAnti0
    exact hAnti0
  have hq0Def : (∃ pa, Av q0v = some pa) ∧ (∃ pb, Bv q0v = some pb) := by
    have hAnti0' := hAnti0
    simp [SFormula.eval, STerm.eval, hA, hB, hq0, SC.b, Term.eval] at hAnti0'
    cases hAv : Av q0v with
    | none => simp [hAv] at hAnti0'
    | some pa =>
        cases hBv : Bv q0v with
        | none => simp [hAv, hBv] at hAnti0'
        | some pb => exact ⟨⟨pa, rfl⟩, ⟨pb, rfl⟩⟩
  -- Premise: anti at q1v, plus definedness at q1v.
  have hAnti1Pt :
      ∀ pa pb, Av q1v = some pa → Bv q1v = some pb →
        ErrorVec.Pauli.anticommutes pa pb = true := by
    intro pa pb hpa hpb
    simp [SFormula.eval, STerm.eval, hA, hB, hq1, hpa, hpb, SC.b, Term.eval] at hAnti1
    exact hAnti1
  have hq1Def : (∃ pa, Av q1v = some pa) ∧ (∃ pb, Bv q1v = some pb) := by
    have hAnti1' := hAnti1
    simp [SFormula.eval, STerm.eval, hA, hB, hq1, SC.b, Term.eval] at hAnti1'
    cases hAv : Av q1v with
    | none => simp [hAv] at hAnti1'
    | some pa =>
        cases hBv : Bv q1v with
        | none => simp [hAv, hBv] at hAnti1'
        | some pb => exact ⟨⟨pa, rfl⟩, ⟨pb, rfl⟩⟩
  -- Premise: at every slot DISTINCT from both q0v and q1v, the slots commute
  -- (and are defined).  Discharge both `imp` guards using the distinctness.
  have hrestFull :
      ∀ q, q < nv → q ≠ q0v → q ≠ q1v →
        ((∃ pa, Av q = some pa) ∧ (∃ pb, Bv q = some pb) ∧
          ∀ pa pb, Av q = some pa → Bv q = some pb →
            ErrorVec.Pauli.anticommutes pa pb = false) := by
    intro q hq hne0 hne1
    have hbody := hImp q hq
    have hlocal :
        SFormula.eval codeBody fuel
          (SFormula.localCommutesAt A.weaken B.weaken SFormula.boundNat)
          (Env.cons q rho) E = some true := by
      simp [SFormula.eval, hBound q, hq0weak q, hq1weak q, hne0, hne1] at hbody
      exact hbody
    exact localCommutes_defined_and_false hlocal hA hB
  -- Definedness everywhere below `nv` (q0v / q1v from anti, else from rest).
  have hdef : ∀ q, q < nv → (∃ p, Av q = some p) ∧ (∃ p, Bv q = some p) := by
    intro q hq
    by_cases hqq0 : q = q0v
    · subst hqq0; exact hq0Def
    · by_cases hqq1 : q = q1v
      · subst hqq1; exact hq1Def
      · exact ⟨(hrestFull q hq hqq0 hqq1).1, (hrestFull q hq hqq0 hqq1).2.1⟩
  have hrest : ∀ q, q < nv → q ≠ q0v → q ≠ q1v →
      ∀ pa pb, Av q = some pa → Bv q = some pb →
        ErrorVec.Pauli.anticommutes pa pb = false := by
    intro q hq hne0 hne1 pa pb hpa hpb
    exact (hrestFull q hq hne0 hne1).2.2 pa pb hpa hpb
  exact parityUpTo_two_anti hq0Lt hq1Lt hneVal hdef hAnti0Pt hAnti1Pt hrest

theorem parityUpTo_right_entry_defined {n q : Nat}
    {A B : PartialStabilizer} {b : Bool} :
    parityUpTo n A B = some b -> q < n -> exists p, B q = some p := by
  induction n generalizing q b with
  | zero =>
      intro _ hq
      omega
  | succ m ih =>
      intro h hq
      unfold parityUpTo at h
      cases hPrev : parityUpTo m A B with
      | none =>
          simp [hPrev] at h
      | some prev =>
          cases hA : A m with
          | none =>
              simp [hPrev, hA] at h
          | some av =>
              cases hB : B m with
              | none =>
                  simp [hPrev, hA, hB] at h
              | some bv =>
                  by_cases hqm : q < m
                  · exact ih hPrev hqm
                  · have hqeq : q = m := by omega
                    subst q
                    exact ⟨bv, hB⟩

theorem stabEqUpTo_self_of_defined {n : Nat} {A : PartialStabilizer} {b : Bool} :
    stabEqUpTo n A A = some b -> b = true := by
  induction n generalizing b with
  | zero =>
      intro h
      simp [stabEqUpTo] at h
      exact h
  | succ m ih =>
      intro h
      unfold stabEqUpTo at h
      cases hprev : stabEqUpTo m A A with
      | none =>
          simp [hprev] at h
      | some prev =>
          have hprevTrue : prev = true := ih hprev
          cases hA : A m <;> simp [hprev, hprevTrue, hA] at h
          exact h

private theorem stabEqUpTo_symm_true {n : Nat} {A B : PartialStabilizer} :
    stabEqUpTo n A B = some true -> stabEqUpTo n B A = some true := by
  intro h
  exact stabEqUpTo_complete fun q hq =>
    let ⟨p, hA, hB⟩ := stabEqUpTo_sound h q hq
    ⟨p, hB, hA⟩

private theorem stabEqUpTo_trans_true {n : Nat} {A B C : PartialStabilizer} :
    stabEqUpTo n A B = some true ->
      stabEqUpTo n B C = some true ->
        stabEqUpTo n A C = some true := by
  intro hAB hBC
  exact stabEqUpTo_complete fun q hq =>
    let ⟨p, hA, hB⟩ := stabEqUpTo_sound hAB q hq
    let ⟨r, hB', hC⟩ := stabEqUpTo_sound hBC q hq
    have hpr : p = r := by
      rw [hB] at hB'
      exact Option.some.inj hB'
    ⟨p, hA, by simpa [hpr] using hC⟩

private theorem parityUpTo_congr_left {n : Nat} {A B C : PartialStabilizer} :
    stabEqUpTo n A B = some true -> parityUpTo n A C = parityUpTo n B C := by
  induction n with
  | zero =>
      intro _
      rfl
  | succ m ih =>
      intro hEq
      unfold stabEqUpTo at hEq
      cases hprev : stabEqUpTo m A B with
      | none =>
          simp [hprev] at hEq
      | some prev =>
          cases prev
          · simp [hprev] at hEq
          · cases hA : A m with
            | none =>
                simp [hprev, hA] at hEq
            | some av =>
                cases hB : B m with
                | none =>
                    simp [hprev, hA, hB] at hEq
                | some bv =>
                    have hab : av = bv := by
                      simp [hprev, hA, hB] at hEq
                      exact hEq
                    unfold parityUpTo
                    rw [ih hprev]
                    cases hC : C m <;> simp [hA, hB, hab]

private theorem parityUpTo_congr_right {n : Nat} {A B C : PartialStabilizer} :
    stabEqUpTo n B C = some true -> parityUpTo n A B = parityUpTo n A C := by
  intro hEq
  rw [parityUpTo_symm (A := A) (B := B)]
  rw [parityUpTo_congr_left hEq]
  rw [parityUpTo_symm (A := C) (B := A)]

private theorem parityUpTo_mul_left {n : Nat} {A B C : PartialStabilizer} :
    parityUpTo n (partialStabilizerMul A B) C =
      match parityUpTo n A C, parityUpTo n B C with
      | some pa, some pb => some (xor pa pb)
      | _, _ => none := by
  induction n with
  | zero =>
      rfl
  | succ m ih =>
      unfold parityUpTo
      rw [ih]
      cases hAC : parityUpTo m A C <;> cases hBC : parityUpTo m B C <;>
        simp [partialStabilizerMul]
      rename_i restAC restBC
      cases hA : A m <;> cases hB : B m <;> cases hC : C m <;>
        simp [partialStabilizerMul, hA, hB, hC]
      rename_i av bv cv
      cases restAC <;> cases restBC <;> cases av <;> cases bv <;> cases cv <;>
        simp [pauli_anticommutes_mul_left]

theorem parityUpTo_identity_defined_false {n : Nat} {C : PartialStabilizer}
    {b : Bool} :
    parityUpTo n partialIdentityStabilizer C = some b -> b = false := by
  induction n generalizing b with
  | zero =>
      intro h
      simp [parityUpTo] at h
      exact h
  | succ m ih =>
      intro h
      unfold parityUpTo at h
      cases hprev : parityUpTo m partialIdentityStabilizer C with
      | none =>
          simp [hprev] at h
      | some prev =>
          have hprevFalse : prev = false := ih hprev
          cases hC : C m with
          | none =>
              simp [partialIdentityStabilizer, hprev, hprevFalse, hC] at h
          | some val =>
              cases val <;> cases b <;>
                simp [partialIdentityStabilizer, ErrorVec.Pauli.anticommutes,
                  hprev, hprevFalse, hC] at h ⊢

theorem parityUpTo_fold_left_defined {n k : Nat}
    {body : Nat -> PartialStabilizer} {C : PartialStabilizer} {b : Bool}
    (hcomm : forall i, i < k -> parityUpTo n (body i) C = some false) :
    parityUpTo n (partialStabilizerFold k body) C = some b ->
      b = false := by
  induction k generalizing b with
  | zero =>
      intro h
      simpa [partialStabilizerFold] using parityUpTo_identity_defined_false h
  | succ m ih =>
      intro h
      simp [partialStabilizerFold] at h
      rw [parityUpTo_mul_left] at h
      cases hPrev : parityUpTo n (partialStabilizerFold m body) C with
      | none =>
          simp [hPrev] at h
      | some prev =>
          cases hBody : parityUpTo n (body m) C with
          | none =>
              simp [hPrev, hBody] at h
          | some bodyParity =>
              have hPrevFalse : prev = false := ih (fun i hi => hcomm i (by omega)) hPrev
              have hBodyFalse : bodyParity = false := by
                rw [hcomm m (Nat.lt_succ_self m)] at hBody
                exact (Option.some.inj hBody).symm
              subst prev
              subst bodyParity
              simp [hPrev, hBody] at h
              exact h

private theorem partialStabilizerMul_assoc (A B C : PartialStabilizer) :
    partialStabilizerMul (partialStabilizerMul A B) C =
      partialStabilizerMul A (partialStabilizerMul B C) := by
  funext q
  cases hA : A q <;> cases hB : B q <;> cases hC : C q <;>
    simp [partialStabilizerMul, hA, hB, hC, Pauli.mul_assoc]

private theorem partialStabilizerMul_comm (A B : PartialStabilizer) :
    partialStabilizerMul A B = partialStabilizerMul B A := by
  funext q
  cases hA : A q <;> cases hB : B q <;>
    simp [partialStabilizerMul, hA, hB, pauli_mul_comm]

private theorem pauli_adjacent_fold_telescopes (cut : Nat -> Pauli) (k q : Nat) :
    partialStabilizerFold k (fun i _ => some (Pauli.mul (cut i) (cut (i + 1)))) q =
      some (Pauli.mul (cut 0) (cut k)) := by
  induction k with
  | zero =>
      simp [partialStabilizerFold, partialIdentityStabilizer, Pauli.mul_self]
  | succ m ih =>
      simp [partialStabilizerFold, partialStabilizerMul, ih, pauli_mul_cancel_middle]

private theorem partialStabilizerFold_adjacent_telescopes
    (cut : Nat -> Nat -> Pauli) (k q : Nat) :
    partialStabilizerFold k (fun i q => some (Pauli.mul (cut i q) (cut (i + 1) q))) q =
      some (Pauli.mul (cut 0 q) (cut k q)) := by
  induction k with
  | zero =>
      simp [partialStabilizerFold, partialIdentityStabilizer, Pauli.mul_self]
  | succ m ih =>
      simp [partialStabilizerFold, partialStabilizerMul, ih, pauli_mul_cancel_middle]

private def rowZCutPauli (dist row q : Nat) : Pauli :=
  if q / dist = row then Pauli.Z else Pauli.I

private def colXCutPauli (dist col q : Nat) : Pauli :=
  if q % dist = col then Pauli.X else Pauli.I

private theorem eval_rowZCut {arity : Nat} {codeBody : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer} {row : Term arity .nat} {rv dist : Nat}
    (hrow : Term.eval codeBody fuel row rho = some rv) :
    (SC.rowZCut dist row).eval codeBody fuel rho E =
      some (fun q => some (rowZCutPauli dist rv q)) := by
  simp [SC.rowZCut, STerm.eval, Term.eval]
  funext q
  have hrowW : Term.eval codeBody fuel row.weaken (Env.cons q rho) = some rv := by
    exact (Term.eval_lift_of_env row (EnvLifted.underTop rho q) codeBody fuel).trans hrow
  simp [Term.eval, Env.cons, rowZCutPauli, hrowW]
  change (if q / dist = rv then some Pauli.Z else some Pauli.I) =
    some (if q / dist = rv then Pauli.Z else Pauli.I)
  by_cases hq : q / dist = rv <;> simp [hq]

private theorem eval_colXCut {arity : Nat} {codeBody : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer} {col : Term arity .nat} {cv dist : Nat}
    (hcol : Term.eval codeBody fuel col rho = some cv) :
    (SC.colXCut dist col).eval codeBody fuel rho E =
      some (fun q => some (colXCutPauli dist cv q)) := by
  simp [SC.colXCut, STerm.eval, Term.eval]
  funext q
  have hcolW : Term.eval codeBody fuel col.weaken (Env.cons q rho) = some cv := by
    exact (Term.eval_lift_of_env col (EnvLifted.underTop rho q) codeBody fuel).trans hcol
  simp [Term.eval, Env.cons, colXCutPauli, hcolW]
  change (if q % dist = cv then some Pauli.X else some Pauli.I) =
    some (if q % dist = cv then Pauli.X else Pauli.I)
  by_cases hq : q % dist = cv <;> simp [hq]

private theorem stabEqUpTo_mul_congr_true {n : Nat}
    {A A' B B' : PartialStabilizer} :
    stabEqUpTo n A A' = some true ->
      stabEqUpTo n B B' = some true ->
        stabEqUpTo n (partialStabilizerMul A B) (partialStabilizerMul A' B') = some true := by
  intro hA hB
  exact stabEqUpTo_complete fun q hq =>
    let ⟨pa, hAq, hAq'⟩ := stabEqUpTo_sound hA q hq
    let ⟨pb, hBq, hBq'⟩ := stabEqUpTo_sound hB q hq
    ⟨Pauli.mul pa pb, by simp [partialStabilizerMul, hAq, hBq],
      by simp [partialStabilizerMul, hAq', hBq']⟩

theorem stabEqUpTo_mul_self_identity_of_defined {n : Nat}
    {A : PartialStabilizer} {b : Bool} :
    stabEqUpTo n (partialStabilizerMul A A) partialIdentityStabilizer = some b ->
      b = true := by
  induction n generalizing b with
  | zero =>
      intro h
      simp [stabEqUpTo] at h
      exact h
  | succ m ih =>
      intro h
      unfold stabEqUpTo at h
      cases hprev : stabEqUpTo m (partialStabilizerMul A A) partialIdentityStabilizer with
      | none =>
          simp [hprev] at h
      | some prev =>
          have hprevTrue : prev = true := ih hprev
          cases hA : A m with
          | none =>
              simp [partialStabilizerMul, partialIdentityStabilizer, hprev, hprevTrue, hA] at h
          | some av =>
              cases b <;>
                simp [partialStabilizerMul, partialIdentityStabilizer, hprev, hprevTrue, hA,
                  Pauli.mul_self] at h ⊢

theorem stabEqUpTo_one_mul_of_defined {n : Nat}
    {A : PartialStabilizer} {b : Bool} :
    stabEqUpTo n (partialStabilizerMul partialIdentityStabilizer A) A = some b ->
      b = true := by
  induction n generalizing b with
  | zero =>
      intro h
      simp [stabEqUpTo] at h
      exact h
  | succ m ih =>
      intro h
      unfold stabEqUpTo at h
      cases hprev : stabEqUpTo m (partialStabilizerMul partialIdentityStabilizer A) A with
      | none =>
          simp [hprev] at h
      | some prev =>
          have hprevTrue : prev = true := ih hprev
          cases hA : A m with
          | none =>
              simp [partialStabilizerMul, partialIdentityStabilizer, hprev, hprevTrue, hA] at h
          | some av =>
              cases b <;>
                simp [partialStabilizerMul, partialIdentityStabilizer, hprev, hprevTrue, hA,
                  Pauli.I_mul] at h ⊢

theorem stabEqUpTo_mul_one_of_defined {n : Nat}
    {A : PartialStabilizer} {b : Bool} :
    stabEqUpTo n (partialStabilizerMul A partialIdentityStabilizer) A = some b ->
      b = true := by
  induction n generalizing b with
  | zero =>
      intro h
      simp [stabEqUpTo] at h
      exact h
  | succ m ih =>
      intro h
      unfold stabEqUpTo at h
      cases hprev : stabEqUpTo m (partialStabilizerMul A partialIdentityStabilizer) A with
      | none =>
          simp [hprev] at h
      | some prev =>
          have hprevTrue : prev = true := ih hprev
          cases hA : A m with
          | none =>
              simp [partialStabilizerMul, partialIdentityStabilizer, hprev, hprevTrue, hA] at h
          | some av =>
              cases b <;>
                simp [partialStabilizerMul, partialIdentityStabilizer, hprev, hprevTrue, hA,
                  Pauli.mul_I] at h ⊢

private theorem eval_stabMul_of_eval {arity : Nat} {codeBody : Term 2 .stab}
    {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    {A B : STerm arity .stab} {Av Bv : PartialStabilizer}
    (hA : A.eval codeBody fuel rho E = some Av)
    (hB : B.eval codeBody fuel rho E = some Bv) :
    (SC.stabMul A B).eval codeBody fuel rho E = some (partialStabMul Av Bv) := by
  simp [SC.stabMul, STerm.eval]
  funext q
  have hAlift :
      A.weaken.eval codeBody fuel (Env.cons q rho) E = some Av := by
    simpa [STerm.weaken] using
      STerm.eval_lift_of_env A (EnvLifted.underTop rho q) codeBody fuel E ▸ hA
  have hBlift :
      B.weaken.eval codeBody fuel (Env.cons q rho) E = some Bv := by
    simpa [STerm.weaken] using
      STerm.eval_lift_of_env B (EnvLifted.underTop rho q) codeBody fuel E ▸ hB
  simp [SC.qVar, STerm.eval, Term.eval, Env.cons, hAlift, hBlift, partialStabMul]
  change (Av q).bind (fun av => (Bv q).bind fun bv => some (Pauli.mul av bv)) =
    (Av q).bind (fun av => (Bv q).bind fun bv => some (Pauli.mul av bv))
  rfl

private theorem eval_rowZBridge {arity : Nat} {codeBody : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer} {row : Term arity .nat} {rv dist : Nat}
    (hrow : Term.eval codeBody fuel row rho = some rv) :
    (SC.rowZBridge dist row).eval codeBody fuel rho E =
      some (fun q =>
        some (Pauli.mul (rowZCutPauli dist rv q) (rowZCutPauli dist (rv + 1) q))) := by
  have hcut := eval_rowZCut (E := E) (dist := dist) hrow
  have hsucc : Term.eval codeBody fuel (.add row (.natLit 1)) rho = some (rv + 1) := by
    simp [Term.eval, hrow]
  have hcutSucc := eval_rowZCut (E := E) (dist := dist) hsucc
  simpa [SC.rowZBridge, partialStabMul, partialStabilizerMul] using
    eval_stabMul_of_eval (A := SC.rowZCut dist row)
      (B := SC.rowZCut dist (.add row (.natLit 1))) hcut hcutSucc

private theorem eval_colXBridge {arity : Nat} {codeBody : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer} {col : Term arity .nat} {cv dist : Nat}
    (hcol : Term.eval codeBody fuel col rho = some cv) :
    (SC.colXBridge dist col).eval codeBody fuel rho E =
      some (fun q =>
        some (Pauli.mul (colXCutPauli dist cv q) (colXCutPauli dist (cv + 1) q))) := by
  have hcut := eval_colXCut (E := E) (dist := dist) hcol
  have hsucc : Term.eval codeBody fuel (.add col (.natLit 1)) rho = some (cv + 1) := by
    simp [Term.eval, hcol]
  have hcutSucc := eval_colXCut (E := E) (dist := dist) hsucc
  simpa [SC.colXBridge, partialStabMul, partialStabilizerMul] using
    eval_stabMul_of_eval (A := SC.colXCut dist col)
      (B := SC.colXCut dist (.add col (.natLit 1))) hcut hcutSucc

private theorem eval_stabOne {arity : Nat} {codeBody : Term 2 .stab}
    {fuel : Nat} {rho : Env arity} {E : PartialStabilizer} :
    (SC.stabOne (arity := arity)).eval codeBody fuel rho E =
      some partialIdentityStabilizer := by
  simp [SC.stabOne, STerm.eval]
  funext q
  simp [SC.p, STerm.eval, Term.eval, partialIdentityStabilizer]

private theorem eqStabUpTo_eval_of_eval_eq {arity : Nat} {codeBody : Term 2 .stab}
    {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    {n : STerm arity .nat} {A B : STerm arity .stab}
    (hEq : A.eval codeBody fuel rho E = B.eval codeBody fuel rho E) :
    (exists b, SFormula.eval codeBody fuel (.eqStabUpTo n A B) rho E = some b) ->
      SFormula.eval codeBody fuel (.eqStabUpTo n A B) rho E = some true := by
  intro hdef
  rcases hdef with ⟨_, hTarget⟩
  simp [SFormula.eval] at hTarget ⊢
  rw [hEq] at hTarget ⊢
  cases hn : n.eval codeBody fuel rho E with
  | none =>
      simp [hn] at hTarget
  | some nv =>
      cases hB : B.eval codeBody fuel rho E with
      | none =>
          simp [hn, hB] at hTarget
      | some Bv =>
          simp [hn, hB] at hTarget ⊢
          cases hEqSelf : stabEqUpTo nv Bv Bv with
          | none =>
              simp [hEqSelf] at hTarget
          | some eqv =>
              have heqv : eqv = true := stabEqUpTo_self_of_defined hEqSelf
              simp [hEqSelf, heqv]

inductive Deriv : {arity : Nat} -> List (SFormula arity) -> SFormula arity -> Type where
  | hyp {Γ : List (SFormula arity)} {A : SFormula arity} : A ∈ Γ -> Deriv Γ A
  | contextWeakening {Γ Δ : List (SFormula arity)} {A : SFormula arity} :
      (forall C, C ∈ Γ -> C ∈ Δ) -> Deriv Γ A -> Deriv Δ A
  | weakenFresh {Γ : List (SFormula arity)} {A : SFormula arity} :
      Deriv Γ A -> Deriv (Γ.map (fun G => G.weaken)) A.weaken
  | top {Γ : List (SFormula arity)} : Deriv Γ .top
  | botElim {Γ : List (SFormula arity)} {A : SFormula arity} :
      Deriv Γ .bot -> Deriv Γ A
  | andIntro {Γ : List (SFormula arity)} {A B : SFormula arity} :
      Deriv Γ A -> Deriv Γ B -> Deriv Γ (.and A B)
  | andElimLeft {Γ : List (SFormula arity)} {A B : SFormula arity} :
      Deriv Γ (.and A B) -> Deriv Γ A
  | andElimRight {Γ : List (SFormula arity)} {A B : SFormula arity} :
      Deriv Γ (.and A B) -> Deriv Γ B
  | orIntroLeft {Γ : List (SFormula arity)} {A B : SFormula arity} :
      Deriv Γ A -> Deriv Γ (.or A B)
  | orIntroRight {Γ : List (SFormula arity)} {A B : SFormula arity} :
      Deriv Γ B -> Deriv Γ (.or A B)
  | orElim {Γ : List (SFormula arity)} {A B C : SFormula arity} :
      Deriv Γ (.or A B) -> Deriv (A :: Γ) C -> Deriv (B :: Γ) C -> Deriv Γ C
  | notIntro {Γ : List (SFormula arity)} {A : SFormula arity} :
      Deriv (A :: Γ) .bot -> Deriv Γ (.not A)
  | notElim {Γ : List (SFormula arity)} {A : SFormula arity} :
      Deriv Γ A -> Deriv Γ (.not A) -> Deriv Γ .bot
  | impIntro {Γ : List (SFormula arity)} {A B : SFormula arity} :
      Deriv (A :: Γ) B -> Deriv Γ (.imp A B)
  | mp {Γ : List (SFormula arity)} {A B : SFormula arity} :
      Deriv Γ (.imp A B) -> Deriv Γ A -> Deriv Γ B
  | boolCases {Γ : List (SFormula arity)} (b : STerm arity .bool)
      (C : SFormula arity) :
      Deriv (.eqBool b (SC.b true) :: Γ) C ->
        Deriv (.eqBool b (SC.b false) :: Γ) C ->
          Deriv Γ C
  | allNatLtIntro {Γ : List (SFormula arity)}
      (n : STerm arity .nat) (A : SFormula (arity + 1)) :
      Deriv (Γ.map (fun G => G.weaken)) A -> Deriv Γ (.allNatLt n A)
  | allNatLtIntroBounded {Γ : List (SFormula arity)}
      (n : STerm arity .nat) (A : SFormula (arity + 1)) :
      Deriv (SFormula.boundNatLt n :: Γ.map (fun G => G.weaken)) A ->
        Deriv Γ (.allNatLt n A)
  | allNatLtElim {Γ : List (SFormula arity)}
      (n : STerm arity .nat) (A : SFormula (arity + 1))
      (witness : STerm arity .nat) :
      Deriv Γ (.allNatLt n A) ->
        Deriv Γ (SFormula.witnessLt witness n) ->
          Deriv Γ (.applyNat witness A)
  | applyNatBoundNatBeta {base : Nat} {Γ : List (SFormula (base + 1))}
      (A : SFormula (base + 1)) :
      Deriv Γ (.applyNat (SFormula.boundNat (arity := base)) (A.lift 1)) -> Deriv Γ A
  | applyNatSubstitutionBeta {Γ : List (SFormula arity)}
      (x : Term arity .nat) (A : SFormula (arity + 1)) :
      PureNatTerm x -> Deriv Γ (A.instantiateTopNat x) ->
        Deriv Γ (.applyNat (SC.closed x) A)
  | applyNatSubstitutionBetaElim {Γ : List (SFormula arity)}
      (x : Term arity .nat) (A : SFormula (arity + 1)) :
      PureNatTerm x -> Deriv Γ (.applyNat (SC.closed x) A) ->
        Deriv Γ (A.instantiateTopNat x)
  | closedNatLt {Γ : List (SFormula arity)} (a b : Nat) (h : decide (a < b) = true) :
      Deriv Γ (SFormula.witnessLt (SC.n (arity := arity) a) (SC.n (arity := arity) b))
  | divLtOfLtSquare {Γ : List (SFormula arity)}
      (dist : Nat) (q : Term arity .nat) :
      Deriv Γ (SFormula.witnessLt (SC.closed q) (SC.n (dist * dist))) ->
        Deriv Γ (SFormula.witnessLt
          (SC.closed (NatArithmetic.rowOf q (.natLit dist))) (SC.n dist))
  | modLtOfLtSquare {Γ : List (SFormula arity)}
      (dist : Nat) (q : Term arity .nat) :
      Deriv Γ (SFormula.witnessLt (SC.closed q) (SC.n (dist * dist))) ->
        Deriv Γ (SFormula.witnessLt
          (SC.closed (NatArithmetic.colOf q (.natLit dist))) (SC.n dist))
  | gridIdxLeftLtSquare {Γ : List (SFormula arity)}
      (dist : Nat) (row col : Term arity .nat) :
      Deriv Γ (SFormula.witnessLt (SC.closed row) (SC.n dist)) ->
        Deriv Γ (SFormula.witnessLt (SC.closed col) (SC.n dist)) ->
          Deriv Γ (SFormula.witnessLt
            (SC.closed (NatArithmetic.gridIdxLeft (.natLit dist) row col))
            (SC.n (dist * dist)))
  | gridIdxLeftDivEq {Γ : List (SFormula arity)}
      (dist : Nat) (row col : Term arity .nat) :
      Deriv Γ (SFormula.witnessLt (SC.closed row) (SC.n dist)) ->
        Deriv Γ (SFormula.witnessLt (SC.closed col) (SC.n dist)) ->
          Deriv Γ (.eqNat
            (SC.closed (NatArithmetic.rowOf
              (NatArithmetic.gridIdxLeft (.natLit dist) row col) (.natLit dist)))
            (SC.closed row))
  | gridIdxLeftModEq {Γ : List (SFormula arity)}
      (dist : Nat) (row col : Term arity .nat) :
      Deriv Γ (SFormula.witnessLt (SC.closed row) (SC.n dist)) ->
        Deriv Γ (SFormula.witnessLt (SC.closed col) (SC.n dist)) ->
        Deriv Γ (.eqNat
          (SC.closed (NatArithmetic.colOf
            (NatArithmetic.gridIdxLeft (.natLit dist) row col) (.natLit dist)))
          (SC.closed col))
  | gridIdxLeftDivModEqOfRow {Γ : List (SFormula arity)}
      (dist : Nat) (row q : Term arity .nat) :
      Deriv Γ (SFormula.witnessLt (SC.closed q) (SC.n (dist * dist))) ->
        Deriv Γ (.eqBool
          (SC.closed (.eqNat (NatArithmetic.rowOf q (.natLit dist)) row))
          (SC.b true)) ->
          Deriv Γ (.eqNat
            (SC.closed (NatArithmetic.gridIdxLeft (.natLit dist) row
              (NatArithmetic.colOf q (.natLit dist))))
            (SC.closed q))
  | gridIdxLeftDivModEqOfCol {Γ : List (SFormula arity)}
      (dist : Nat) (col q : Term arity .nat) :
      Deriv Γ (SFormula.witnessLt (SC.closed q) (SC.n (dist * dist))) ->
        Deriv Γ (.eqBool
          (SC.closed (.eqNat (NatArithmetic.colOf q (.natLit dist)) col))
          (SC.b true)) ->
          Deriv Γ (.eqNat
            (SC.closed (NatArithmetic.gridIdxLeft (.natLit dist)
              (NatArithmetic.rowOf q (.natLit dist)) col))
            (SC.closed q))
  | ltOfLtLtClosedPred {Γ : List (SFormula arity)}
      (limit : Nat) (x y : STerm arity .nat) :
      Deriv Γ (SFormula.witnessLt x y) ->
        Deriv Γ (SFormula.witnessLt y (SC.n limit)) ->
          Deriv Γ (SFormula.witnessLt x (SC.n (limit - 1)))
  | eqStabRefl {Γ : List (SFormula arity)}
      (n : STerm arity .nat) (A : STerm arity .stab) :
      Deriv Γ (.eqStabUpTo n A A)
  | eqStabSymm {Γ : List (SFormula arity)}
      (n : STerm arity .nat) (A B : STerm arity .stab) :
      Deriv Γ (.eqStabUpTo n A B) -> Deriv Γ (.eqStabUpTo n B A)
  | eqStabTrans {Γ : List (SFormula arity)}
      (n : STerm arity .nat) (A B C : STerm arity .stab) :
      Deriv Γ (.eqStabUpTo n A B) ->
        Deriv Γ (.eqStabUpTo n B C) ->
          Deriv Γ (.eqStabUpTo n A C)
  | eqPauliSymm {Γ : List (SFormula arity)} (a b : STerm arity .pauli) :
      Deriv Γ (.eqPauli a b) -> Deriv Γ (.eqPauli b a)
  | eqPauliTrans {Γ : List (SFormula arity)} (a b c : STerm arity .pauli) :
      Deriv Γ (.eqPauli a b) -> Deriv Γ (.eqPauli b c) -> Deriv Γ (.eqPauli a c)
  | eqNatBoolTrue {Γ : List (SFormula arity)} (a b : Term arity .nat) :
      Deriv Γ (.eqNat (SC.closed a) (SC.closed b)) ->
        Deriv Γ (.eqBool (SC.closed (.eqNat a b)) (SC.b true))
  | eqBoolFalseNotTrue {Γ : List (SFormula arity)} (b : STerm arity .bool) :
      Deriv Γ (.eqBool b (SC.b false)) ->
        Deriv Γ (.not (.eqBool b (SC.b true)))
  | eqBoolTrueNotFalse {Γ : List (SFormula arity)} (b : STerm arity .bool) :
      Deriv Γ (.eqBool b (SC.b true)) ->
        Deriv Γ (.not (.eqBool b (SC.b false)))
  | eqStabMulCongr {Γ : List (SFormula arity)}
      (n : STerm arity .nat) (A A' B B' : STerm arity .stab) :
      Deriv Γ (.eqStabUpTo n A A') ->
        Deriv Γ (.eqStabUpTo n B B') ->
          Deriv Γ (.eqStabUpTo n (SC.stabMul A B) (SC.stabMul A' B'))
  | eqStabMulAssoc {Γ : List (SFormula arity)}
      (n : STerm arity .nat) (A B C : STerm arity .stab) :
      Deriv Γ (.eqStabUpTo n A A) ->
        Deriv Γ (.eqStabUpTo n B B) ->
          Deriv Γ (.eqStabUpTo n C C) ->
            Deriv Γ (.eqStabUpTo n
              (SC.stabMul (SC.stabMul A B) C)
              (SC.stabMul A (SC.stabMul B C)))
  | eqStabMulComm {Γ : List (SFormula arity)}
      (n : STerm arity .nat) (A B : STerm arity .stab) :
      Deriv Γ (.eqStabUpTo n A A) ->
        Deriv Γ (.eqStabUpTo n B B) ->
          Deriv Γ (.eqStabUpTo n (SC.stabMul A B) (SC.stabMul B A))
  | eqStabMulSelf {Γ : List (SFormula arity)}
      (n : STerm arity .nat) (A : STerm arity .stab) :
      Deriv Γ (.eqStabUpTo n A A) ->
        Deriv Γ (.eqStabUpTo n (SC.stabMul A A) SC.stabOne)
  | eqStabMulOneLeft {Γ : List (SFormula arity)}
      (n : STerm arity .nat) (A : STerm arity .stab) :
      Deriv Γ (.eqStabUpTo n A A) ->
        Deriv Γ (.eqStabUpTo n (SC.stabMul SC.stabOne A) A)
  | eqStabMulOneRight {Γ : List (SFormula arity)}
      (n : STerm arity .nat) (A : STerm arity .stab) :
      Deriv Γ (.eqStabUpTo n A A) ->
        Deriv Γ (.eqStabUpTo n (SC.stabMul A SC.stabOne) A)
  | eqStabFoldZero {Γ : List (SFormula arity)}
      (n : STerm arity .nat) (body : STerm (arity + 1) .stab) :
      Deriv Γ (.eqStabUpTo n (SC.stabFold (SC.n 0) body) SC.stabOne)
  | eqStabFoldSucc {Γ : List (SFormula arity)}
      (n : STerm arity .nat) (bound : Term arity .nat)
      (body : STerm (arity + 1) .stab) :
      Deriv Γ (.eqStabUpTo n
        (SC.stabFold (SC.succClosed bound) body)
        (SC.stabMul (SC.stabFold (SC.closed bound) body) (SC.applyNat bound body)))
  | commutesSymm {Γ : List (SFormula arity)}
      (n : STerm arity .nat) (A B : STerm arity .stab) :
      Deriv Γ (.commutesUpTo n A B) -> Deriv Γ (.commutesUpTo n B A)
  | noncommutesSymm {Γ : List (SFormula arity)}
      (n : STerm arity .nat) (A B : STerm arity .stab) :
      Deriv Γ (.not (.commutesUpTo n A B)) -> Deriv Γ (.not (.commutesUpTo n B A))
  | commutesOfEqLeft {Γ : List (SFormula arity)}
      (n : STerm arity .nat) (A B C : STerm arity .stab) :
      Deriv Γ (.eqStabUpTo n A B) ->
        Deriv Γ (.commutesUpTo n A C) ->
          Deriv Γ (.commutesUpTo n B C)
  | commutesOfEqRight {Γ : List (SFormula arity)}
      (n : STerm arity .nat) (A B C : STerm arity .stab) :
      Deriv Γ (.eqStabUpTo n B C) ->
        Deriv Γ (.commutesUpTo n A B) ->
          Deriv Γ (.commutesUpTo n A C)
  | noncommutesOfEqLeft {Γ : List (SFormula arity)}
      (n : STerm arity .nat) (A B C : STerm arity .stab) :
      Deriv Γ (.eqStabUpTo n A B) ->
        Deriv Γ (.not (.commutesUpTo n A C)) ->
          Deriv Γ (.not (.commutesUpTo n B C))
  | noncommutesOfEqRight {Γ : List (SFormula arity)}
      (n : STerm arity .nat) (A B C : STerm arity .stab) :
      Deriv Γ (.eqStabUpTo n B C) ->
        Deriv Γ (.not (.commutesUpTo n A B)) ->
          Deriv Γ (.not (.commutesUpTo n A C))
  | commutesStabMulLeft {Γ : List (SFormula arity)}
      (n : STerm arity .nat) (A B C : STerm arity .stab) :
      Deriv Γ (.commutesUpTo n A C) ->
        Deriv Γ (.commutesUpTo n B C) ->
          Deriv Γ (.commutesUpTo n (SC.stabMul A B) C)
  | noncommutesStabMulLeft {Γ : List (SFormula arity)}
      (n : STerm arity .nat) (A B C : STerm arity .stab) :
      Deriv Γ (.commutesUpTo n A C) ->
        Deriv Γ (.not (.commutesUpTo n B C)) ->
          Deriv Γ (.not (.commutesUpTo n (SC.stabMul A B) C))
  | noncommutesStabMulRight {Γ : List (SFormula arity)}
      (n : STerm arity .nat) (A B C : STerm arity .stab) :
      Deriv Γ (.not (.commutesUpTo n A C)) ->
        Deriv Γ (.commutesUpTo n B C) ->
          Deriv Γ (.not (.commutesUpTo n (SC.stabMul A B) C))
  | commutesStabFoldLeft {Γ : List (SFormula arity)}
      (n bound : STerm arity .nat) (body : STerm (arity + 1) .stab)
      (C : STerm arity .stab) :
      Deriv Γ (.allNatLt bound (.commutesUpTo n.weaken body C.weaken)) ->
        Deriv Γ (.commutesUpTo n (SC.stabFold bound body) C)
  | commutesOfPointwise {Γ : List (SFormula arity)}
      (n : STerm arity .nat) (A B : STerm arity .stab) :
      Deriv Γ (SFormula.pointwiseCommutesUpTo n A B) -> Deriv Γ (.commutesUpTo n A B)
  /-- Sound base introduction for non-commutation by a PARITY argument: two
      stabilizers fail to commute when `q0` is the UNIQUE anticommuting slot.
      All three premises are required for soundness — the third (all OTHER
      in-range slots commute) is what makes the anticommutation count odd.
      Dropping it is unsound (two anticommuting slots cancel). -/
  | noncommutesOfSingleAnti {Γ : List (SFormula arity)}
      (n : STerm arity .nat) (A B : STerm arity .stab) (q0 : STerm arity .nat) :
      Deriv Γ (SFormula.witnessLt q0 n) ->
        Deriv Γ (.eqBool (.anticommutes (.stabAt A q0) (.stabAt B q0)) (SC.b true)) ->
          Deriv Γ (.allNatLt n
            (.imp (.not (.eqNat SFormula.boundNat q0.weaken))
              (SFormula.localCommutesAt A.weaken B.weaken SFormula.boundNat))) ->
            Deriv Γ (.not (.commutesUpTo n A B))
  /-- Sound base introduction for COMMUTATION by a PARITY argument: two
      stabilizers commute when there are exactly TWO DISTINCT anticommuting
      slots `q0 ≠ q1`, and every other in-range slot commutes.  The premise
      `q0 ≠ q1` is LOAD-BEARING — dropping it allows `q0 = q1` (one
      anticommuting slot = odd parity = NOT commute), making the rule unsound.
      The all-others-commute premise is likewise required: a third
      anticommuting slot would make the parity odd again. -/
  | commutesOfTwoAnti {Γ : List (SFormula arity)}
      (n : STerm arity .nat) (A B : STerm arity .stab) (q0 q1 : STerm arity .nat) :
      Deriv Γ (SFormula.witnessLt q0 n) ->
        Deriv Γ (SFormula.witnessLt q1 n) ->
          Deriv Γ (.not (.eqNat q0 q1)) ->
            Deriv Γ (.eqBool (.anticommutes (.stabAt A q0) (.stabAt B q0)) (SC.b true)) ->
              Deriv Γ (.eqBool (.anticommutes (.stabAt A q1) (.stabAt B q1)) (SC.b true)) ->
                Deriv Γ (.allNatLt n
                  (.imp (.not (.eqNat SFormula.boundNat q0.weaken))
                    (.imp (.not (.eqNat SFormula.boundNat q1.weaken))
                      (SFormula.localCommutesAt A.weaken B.weaken SFormula.boundNat)))) ->
                  Deriv Γ (.commutesUpTo n A B)
  | stabAtClosedIteLamEqThen {Γ : List (SFormula arity)}
      (cond : Term (arity + 1) .bool) (thenP elseP : Term (arity + 1) .pauli)
      (q : Term arity .nat) :
      PureNatTerm q ->
        Deriv Γ (.eqBool (SC.closed (Term.instantiateTopNat q cond)) (SC.b true)) ->
          Deriv Γ (.eqPauli
            (.stabAt (SC.closed (.stabLam (.ite cond thenP elseP))) (SC.closed q))
            (SC.closed (Term.instantiateTopNat q thenP)))
  | stabAtClosedIteLamEqElse {Γ : List (SFormula arity)}
      (cond : Term (arity + 1) .bool) (thenP elseP : Term (arity + 1) .pauli)
      (q : Term arity .nat) :
      PureNatTerm q ->
        Deriv Γ (.eqBool (SC.closed (Term.instantiateTopNat q cond)) (SC.b false)) ->
          Deriv Γ (.eqPauli
            (.stabAt (SC.closed (.stabLam (.ite cond thenP elseP))) (SC.closed q))
            (SC.closed (Term.instantiateTopNat q elseP)))
  /-- Context-aware bare-Pauli `ite` selection: when the guard `cond` is known
      to be `true` (possibly via a context hypothesis), the closed Pauli term
      `ite cond p1 p2` selects the `then` branch `p1`.  This is the
      `SFormula.Deriv` analogue of `PureFamilyDerivA.pauliIteSelectThen`. -/
  | pauliIteSelectThen {Γ : List (SFormula arity)}
      (cond : Term arity .bool) (p1 p2 : Term arity .pauli) :
      Deriv Γ (.eqBool (SC.closed cond) (SC.b true)) ->
        Deriv Γ (.eqPauli (SC.closed (.ite cond p1 p2)) (SC.closed p1))
  /-- Context-aware bare-Pauli `ite` selection: when the guard `cond` is known
      to be `false`, the closed Pauli term `ite cond p1 p2` selects the `else`
      branch `p2`.  Analogue of `PureFamilyDerivA.pauliIteSelectElse`. -/
  | pauliIteSelectElse {Γ : List (SFormula arity)}
      (cond : Term arity .bool) (p1 p2 : Term arity .pauli) :
      Deriv Γ (.eqBool (SC.closed cond) (SC.b false)) ->
        Deriv Γ (.eqPauli (SC.closed (.ite cond p1 p2)) (SC.closed p2))
  | localCommutesOfLeftI {Γ : List (SFormula arity)}
      (A B : STerm arity .stab) (q : STerm arity .nat) :
      Deriv Γ (.eqPauli (.stabAt A q) (SC.p Pauli.I)) ->
        Deriv Γ (SFormula.localCommutesAt A B q)
  | localCommutesOfLeftEqNoAntiRight {Γ : List (SFormula arity)}
      (A B : STerm arity .stab) (q : STerm arity .nat) (p : STerm arity .pauli) :
      Deriv Γ (.eqPauli (.stabAt A q) p) ->
        Deriv Γ (.not (.eqBool (.anticommutes (.stabAt B q) p) (SC.b true))) ->
          Deriv Γ (SFormula.localCommutesAt A B q)
  | localCommutesOfRightI {Γ : List (SFormula arity)}
      (A B : STerm arity .stab) (q : STerm arity .nat) :
      Deriv Γ (.eqPauli (.stabAt B q) (SC.p Pauli.I)) ->
        Deriv Γ (SFormula.localCommutesAt A B q)
  | anticommutesTransport {Γ : List (SFormula arity)}
      (a a' b b' : STerm arity .pauli) (rhs : STerm arity .bool) :
      Deriv Γ (.eqPauli a a') ->
        Deriv Γ (.eqPauli b b') ->
          Deriv Γ (.eqBool (.anticommutes a' b') rhs) ->
            Deriv Γ (.eqBool (.anticommutes a b) rhs)
  | noAntiAtSubst {Γ : List (SFormula arity)}
      (E : STerm arity .stab) (p : STerm arity .pauli)
      (q₁ q₂ : Term arity .nat) :
      PureNatTerm q₁ -> PureNatTerm q₂ ->
        Deriv Γ (.eqNat (SC.closed q₁) (SC.closed q₂)) ->
          Deriv Γ (.not (.eqBool (.anticommutes (.stabAt E (SC.closed q₁)) p)
            (SC.b true))) ->
            Deriv Γ (.not (.eqBool (.anticommutes (.stabAt E (SC.closed q₂)) p)
              (SC.b true)))
  | pauliAnticommutesNonI {Γ : List (SFormula arity)}
      (p a : STerm arity .pauli) :
      Deriv Γ (.eqBool (.anticommutes p a) (SC.b true)) ->
        Deriv Γ (.not (.eqPauli p (SC.p Pauli.I)))
  | pauliAnticommutesLit {Γ : List (SFormula arity)} (p q : Pauli) :
      Deriv Γ (.eqBool
        (.anticommutes (SC.p (arity := arity) p) (SC.p (arity := arity) q))
        (SC.b (ErrorVec.Pauli.anticommutes p q)))
  | pauliMulLit {Γ : List (SFormula arity)} (p q : Pauli) :
      Deriv Γ (.eqPauli
        (.pauliMul (SC.p (arity := arity) p) (SC.p (arity := arity) q))
        (SC.p (Pauli.mul p q)))
  | pauliEqLit {Γ : List (SFormula arity)} (p : Pauli) :
      Deriv Γ (.eqPauli (SC.p (arity := arity) p) (SC.p p))
  | pauliNeqLit {Γ : List (SFormula arity)} (p q : Pauli)
      (h : decide (p = q) = false) :
      Deriv Γ (.not (.eqPauli (SC.p (arity := arity) p) (SC.p q)))
  | finiteInjectiveWeightLower {Γ : List (SFormula arity)}
      (n : STerm arity .nat) (E : STerm arity .stab)
      (limit k : STerm arity .nat) (slot : STerm (arity + 1) .nat) :
      Deriv Γ (.allNatLt k (SFormula.slotSupportBody n E slot)) ->
        Deriv Γ (SFormula.slotInjectiveF k slot) ->
          Deriv Γ (SFormula.witnessLt limit k) ->
            Deriv Γ (.not (.weightLe n E limit))
  | finiteSurjectiveWeightLower {Γ : List (SFormula arity)}
      (n : STerm arity .nat) (E : STerm arity .stab)
      (limit k : STerm arity .nat) (rowOf : STerm (arity + 1) .nat) :
      Deriv Γ (SFormula.supportSurjectiveF k n E rowOf) ->
        Deriv Γ (SFormula.witnessLt limit k) ->
          Deriv Γ (.not (.weightLe n E limit))
  | finiteDeMorgan {Γ : List (SFormula arity)}
      (n : STerm arity .nat) (A : SFormula (arity + 1)) :
      Deriv Γ (.not (.allNatLt n (.not A))) -> Deriv Γ (.existsNatLt n A)
  | existsNatLtIntro {Γ : List (SFormula arity)}
      (n : STerm arity .nat) (A : SFormula (arity + 1)) (witness : Nat) :
      Deriv (Γ.map (fun G => G.weaken)) A -> Deriv Γ (.existsNatLt n A)
  | existsNatLtIntroTerm {Γ : List (SFormula arity)}
      (n : STerm arity .nat) (A : SFormula (arity + 1))
      (witness : STerm arity .nat) :
      Deriv Γ (SFormula.witnessLt witness n) ->
        Deriv Γ (.applyNat witness A) ->
          Deriv Γ (.existsNatLt n A)
  | existsNatLtElim {Γ : List (SFormula arity)}
      (n : STerm arity .nat) (A : SFormula (arity + 1)) (C : SFormula arity) :
      Deriv Γ (.existsNatLt n A) ->
        Deriv (A :: SFormula.boundNatLt n :: Γ.map (fun G => G.weaken)) C.weaken ->
          Deriv Γ C

namespace Deriv

def assumption {arity : Nat} {Γ : List (SFormula arity)} {A : SFormula arity} :
    Deriv (A :: Γ) A :=
  .hyp (by simp)

private def weakenByCore {arity : Nat} :
    {Γ : List (SFormula arity)} -> {A : SFormula arity} ->
    Deriv Γ A -> {Δ : List (SFormula arity)} ->
    (forall C, C ∈ Γ -> C ∈ Δ) -> Deriv Δ A
  | _, _, .hyp h, _, hsub => .hyp (hsub _ h)
  | _, _, .contextWeakening hweak child, _, hsub =>
      .contextWeakening (fun C hC => hsub C (hweak C hC)) child
  | _, _, .weakenFresh child, _, hsub =>
      .contextWeakening hsub (.weakenFresh child)
  | _, _, .top, _, _ => .top
  | _, _, .botElim child, _, hsub => .botElim (weakenByCore child hsub)
  | _, _, .andIntro left right, _, hsub =>
      .andIntro (weakenByCore left hsub) (weakenByCore right hsub)
  | _, _, .andElimLeft child, _, hsub => .andElimLeft (weakenByCore child hsub)
  | _, _, .andElimRight child, _, hsub => .andElimRight (weakenByCore child hsub)
  | _, _, .orIntroLeft child, _, hsub => .orIntroLeft (weakenByCore child hsub)
  | _, _, .orIntroRight child, _, hsub => .orIntroRight (weakenByCore child hsub)
  | _, _, .orElim disj left right, _, hsub =>
      .orElim (weakenByCore disj hsub)
        (weakenByCore left fun C hmem => by
          cases hmem with
          | head => simp
          | tail _ htail => exact List.mem_cons_of_mem _ (hsub C htail))
        (weakenByCore right fun C hmem => by
          cases hmem with
          | head => simp
          | tail _ htail => exact List.mem_cons_of_mem _ (hsub C htail))
  | _, _, .notIntro child, _, hsub =>
      .notIntro <| weakenByCore child fun C hmem => by
        cases hmem with
        | head => simp
        | tail _ htail => exact List.mem_cons_of_mem _ (hsub C htail)
  | _, _, .notElim positive negative, _, hsub =>
      .notElim (weakenByCore positive hsub) (weakenByCore negative hsub)
  | _, _, .impIntro child, _, hsub =>
      .impIntro <| weakenByCore child fun C hmem => by
        cases hmem with
        | head => simp
        | tail _ htail => exact List.mem_cons_of_mem _ (hsub C htail)
  | _, _, .mp implication antecedent, _, hsub =>
      .mp (weakenByCore implication hsub) (weakenByCore antecedent hsub)
  | _, _, .boolCases b C left right, _, hsub =>
      .boolCases b C
        (weakenByCore left fun G hmem => by
          cases hmem with
          | head => simp
          | tail _ htail => exact List.mem_cons_of_mem _ (hsub G htail))
        (weakenByCore right fun G hmem => by
          cases hmem with
          | head => simp
          | tail _ htail => exact List.mem_cons_of_mem _ (hsub G htail))
  | _, _, .allNatLtIntro n A child, _, hsub =>
      .allNatLtIntro n A <| weakenByCore child fun C hmem => by
        simp at hmem ⊢
        rcases hmem with ⟨G, hG, rfl⟩
        exact ⟨G, hsub G hG, rfl⟩
  | _, _, .allNatLtIntroBounded n A child, _, hsub =>
      .allNatLtIntroBounded n A <| weakenByCore child fun C hmem => by
        simp at hmem ⊢
        rcases hmem with hbound | ⟨G, hG, rfl⟩
        · exact Or.inl hbound
        · exact Or.inr ⟨G, hsub G hG, rfl⟩
  | _, _, .allNatLtElim n A witness forallD ltD, _, hsub =>
      .allNatLtElim n A witness (weakenByCore forallD hsub) (weakenByCore ltD hsub)
  | _, _, .applyNatBoundNatBeta A child, _, hsub =>
      .applyNatBoundNatBeta A (weakenByCore child hsub)
  | _, _, .applyNatSubstitutionBeta x A hx child, _, hsub =>
      .applyNatSubstitutionBeta x A hx (weakenByCore child hsub)
  | _, _, .applyNatSubstitutionBetaElim x A hx child, _, hsub =>
      .applyNatSubstitutionBetaElim x A hx (weakenByCore child hsub)
  | _, _, .closedNatLt a b h, _, _ =>
      .closedNatLt a b h
  | _, _, .divLtOfLtSquare dist q child, _, hsub =>
      .divLtOfLtSquare dist q (weakenByCore child hsub)
  | _, _, .modLtOfLtSquare dist q child, _, hsub =>
      .modLtOfLtSquare dist q (weakenByCore child hsub)
  | _, _, .gridIdxLeftLtSquare dist row col rowLt colLt, _, hsub =>
      .gridIdxLeftLtSquare dist row col
        (weakenByCore rowLt hsub) (weakenByCore colLt hsub)
  | _, _, .gridIdxLeftDivEq dist row col rowLt colLt, _, hsub =>
      .gridIdxLeftDivEq dist row col
        (weakenByCore rowLt hsub) (weakenByCore colLt hsub)
  | _, _, .gridIdxLeftModEq dist row col rowLt colLt, _, hsub =>
      .gridIdxLeftModEq dist row col
        (weakenByCore rowLt hsub) (weakenByCore colLt hsub)
  | _, _, .gridIdxLeftDivModEqOfRow dist row q qLt rowEq, _, hsub =>
      .gridIdxLeftDivModEqOfRow dist row q
        (weakenByCore qLt hsub) (weakenByCore rowEq hsub)
  | _, _, .gridIdxLeftDivModEqOfCol dist col q qLt colEq, _, hsub =>
      .gridIdxLeftDivModEqOfCol dist col q
        (weakenByCore qLt hsub) (weakenByCore colEq hsub)
  | _, _, .ltOfLtLtClosedPred limit x y xy ylimit, _, hsub =>
      .ltOfLtLtClosedPred limit x y
        (weakenByCore xy hsub) (weakenByCore ylimit hsub)
  | _, _, .eqStabRefl n A, _, _ =>
      .eqStabRefl n A
  | _, _, .eqStabSymm n A B child, _, hsub =>
      .eqStabSymm n A B (weakenByCore child hsub)
  | _, _, .eqStabTrans n A B C left right, _, hsub =>
      .eqStabTrans n A B C (weakenByCore left hsub) (weakenByCore right hsub)
  | _, _, .eqPauliSymm a b child, _, hsub =>
      .eqPauliSymm a b (weakenByCore child hsub)
  | _, _, .eqPauliTrans a b c left right, _, hsub =>
      .eqPauliTrans a b c (weakenByCore left hsub) (weakenByCore right hsub)
  | _, _, .eqNatBoolTrue a b child, _, hsub =>
      .eqNatBoolTrue a b (weakenByCore child hsub)
  | _, _, .eqBoolFalseNotTrue b child, _, hsub =>
      .eqBoolFalseNotTrue b (weakenByCore child hsub)
  | _, _, .eqBoolTrueNotFalse b child, _, hsub =>
      .eqBoolTrueNotFalse b (weakenByCore child hsub)
  | _, _, .eqStabMulCongr n A A' B B' left right, _, hsub =>
      .eqStabMulCongr n A A' B B' (weakenByCore left hsub) (weakenByCore right hsub)
  | _, _, .eqStabMulAssoc n A B C hA hB hC, _, hsub =>
      .eqStabMulAssoc n A B C
        (weakenByCore hA hsub) (weakenByCore hB hsub) (weakenByCore hC hsub)
  | _, _, .eqStabMulComm n A B hA hB, _, hsub =>
      .eqStabMulComm n A B (weakenByCore hA hsub) (weakenByCore hB hsub)
  | _, _, .eqStabMulSelf n A child, _, hsub =>
      .eqStabMulSelf n A (weakenByCore child hsub)
  | _, _, .eqStabMulOneLeft n A child, _, hsub =>
      .eqStabMulOneLeft n A (weakenByCore child hsub)
  | _, _, .eqStabMulOneRight n A child, _, hsub =>
      .eqStabMulOneRight n A (weakenByCore child hsub)
  | _, _, .eqStabFoldZero n body, _, _ =>
      .eqStabFoldZero n body
  | _, _, .eqStabFoldSucc n bound body, _, _ =>
      .eqStabFoldSucc n bound body
  | _, _, .commutesSymm n A B child, _, hsub =>
      .commutesSymm n A B (weakenByCore child hsub)
  | _, _, .noncommutesSymm n A B child, _, hsub =>
      .noncommutesSymm n A B (weakenByCore child hsub)
  | _, _, .commutesOfEqLeft n A B C eqD commD, _, hsub =>
      .commutesOfEqLeft n A B C (weakenByCore eqD hsub) (weakenByCore commD hsub)
  | _, _, .commutesOfEqRight n A B C eqD commD, _, hsub =>
      .commutesOfEqRight n A B C (weakenByCore eqD hsub) (weakenByCore commD hsub)
  | _, _, .noncommutesOfEqLeft n A B C eqD noncommD, _, hsub =>
      .noncommutesOfEqLeft n A B C
        (weakenByCore eqD hsub) (weakenByCore noncommD hsub)
  | _, _, .noncommutesOfEqRight n A B C eqD noncommD, _, hsub =>
      .noncommutesOfEqRight n A B C
        (weakenByCore eqD hsub) (weakenByCore noncommD hsub)
  | _, _, .commutesStabMulLeft n A B C left right, _, hsub =>
      .commutesStabMulLeft n A B C (weakenByCore left hsub) (weakenByCore right hsub)
  | _, _, .noncommutesStabMulLeft n A B C left right, _, hsub =>
      .noncommutesStabMulLeft n A B C (weakenByCore left hsub) (weakenByCore right hsub)
  | _, _, .noncommutesStabMulRight n A B C left right, _, hsub =>
      .noncommutesStabMulRight n A B C (weakenByCore left hsub) (weakenByCore right hsub)
  | _, _, .commutesStabFoldLeft n bound body C child, _, hsub =>
      .commutesStabFoldLeft n bound body C (weakenByCore child hsub)
  | _, _, .commutesOfPointwise n A B child, _, hsub =>
      .commutesOfPointwise n A B (weakenByCore child hsub)
  | _, _, .noncommutesOfSingleAnti n A B q0 ltD antiD restD, _, hsub =>
      .noncommutesOfSingleAnti n A B q0
        (weakenByCore ltD hsub) (weakenByCore antiD hsub) (weakenByCore restD hsub)
  | _, _, .commutesOfTwoAnti n A B q0 q1 lt0D lt1D neD anti0D anti1D restD, _, hsub =>
      .commutesOfTwoAnti n A B q0 q1
        (weakenByCore lt0D hsub) (weakenByCore lt1D hsub) (weakenByCore neD hsub)
        (weakenByCore anti0D hsub) (weakenByCore anti1D hsub) (weakenByCore restD hsub)
  | _, _, .stabAtClosedIteLamEqThen cond thenP elseP q hq child, _, hsub =>
      .stabAtClosedIteLamEqThen cond thenP elseP q hq (weakenByCore child hsub)
  | _, _, .stabAtClosedIteLamEqElse cond thenP elseP q hq child, _, hsub =>
      .stabAtClosedIteLamEqElse cond thenP elseP q hq (weakenByCore child hsub)
  | _, _, .pauliIteSelectThen cond p1 p2 child, _, hsub =>
      .pauliIteSelectThen cond p1 p2 (weakenByCore child hsub)
  | _, _, .pauliIteSelectElse cond p1 p2 child, _, hsub =>
      .pauliIteSelectElse cond p1 p2 (weakenByCore child hsub)
  | _, _, .localCommutesOfLeftI A B q child, _, hsub =>
      .localCommutesOfLeftI A B q (weakenByCore child hsub)
  | _, _, .localCommutesOfLeftEqNoAntiRight A B q p eqD noAntiD, _, hsub =>
      .localCommutesOfLeftEqNoAntiRight A B q p
        (weakenByCore eqD hsub) (weakenByCore noAntiD hsub)
  | _, _, .localCommutesOfRightI A B q child, _, hsub =>
      .localCommutesOfRightI A B q (weakenByCore child hsub)
  | _, _, .anticommutesTransport a a' b b' rhs eqAD eqBD antiD, _, hsub =>
      .anticommutesTransport a a' b b' rhs
        (weakenByCore eqAD hsub) (weakenByCore eqBD hsub) (weakenByCore antiD hsub)
  | _, _, .noAntiAtSubst E p q₁ q₂ hq₁ hq₂ eqD noAntiD, _, hsub =>
      .noAntiAtSubst E p q₁ q₂ hq₁ hq₂
        (weakenByCore eqD hsub) (weakenByCore noAntiD hsub)
  | _, _, .pauliAnticommutesNonI p a child, _, hsub =>
      .pauliAnticommutesNonI p a (weakenByCore child hsub)
  | _, _, .pauliAnticommutesLit p q, _, _ =>
      .pauliAnticommutesLit p q
  | _, _, .pauliMulLit p q, _, _ =>
      .pauliMulLit p q
  | _, _, .pauliEqLit p, _, _ =>
      .pauliEqLit p
  | _, _, .pauliNeqLit p q h, _, _ =>
      .pauliNeqLit p q h
  | _, _, .finiteInjectiveWeightLower n E limit k slot support inj lt, _, hsub =>
      .finiteInjectiveWeightLower n E limit k slot
        (weakenByCore support hsub) (weakenByCore inj hsub) (weakenByCore lt hsub)
  | _, _, .finiteSurjectiveWeightLower n E limit k rowOf cover lt, _, hsub =>
      .finiteSurjectiveWeightLower n E limit k rowOf
        (weakenByCore cover hsub) (weakenByCore lt hsub)
  | _, _, .finiteDeMorgan n A child, _, hsub =>
      .finiteDeMorgan n A (weakenByCore child hsub)
  | _, _, .existsNatLtIntro n A witness child, _, hsub =>
      .existsNatLtIntro n A witness <| weakenByCore child fun C hmem => by
        simp at hmem ⊢
        rcases hmem with ⟨G, hG, rfl⟩
        exact ⟨G, hsub G hG, rfl⟩
  | _, _, .existsNatLtIntroTerm n A witness ltD bodyD, _, hsub =>
      .existsNatLtIntroTerm n A witness
        (weakenByCore ltD hsub)
        (weakenByCore bodyD hsub)
  | _, _, .existsNatLtElim n A C existsD bodyD, _, hsub =>
      .existsNatLtElim n A C (weakenByCore existsD hsub) <|
        weakenByCore bodyD fun F hmem => by
          simp at hmem ⊢
          rcases hmem with hA | hbound | ⟨G, hG, rfl⟩
          · exact Or.inl hA
          · exact Or.inr (Or.inl hbound)
          · exact Or.inr (Or.inr ⟨G, hsub G hG, rfl⟩)

def weakenBy {arity : Nat} {Γ Δ : List (SFormula arity)} {A : SFormula arity}
    (hsub : forall C, C ∈ Γ -> C ∈ Δ) (D : Deriv Γ A) : Deriv Δ A :=
  .contextWeakening hsub D

def weakenContext {arity : Nat} {Γ : List (SFormula arity)} {A B : SFormula arity} :
    Deriv Γ A -> Deriv (B :: Γ) A :=
  weakenBy (fun _ h => List.mem_cons_of_mem _ h)

def check {arity : Nat} {Γ : List (SFormula arity)} {A : SFormula arity} :
    Deriv Γ A -> Bool
  | .hyp _ => true
  | .contextWeakening _ child => child.check
  | .weakenFresh child => child.check
  | .top => true
  | .botElim child => child.check
  | .andIntro left right => left.check && right.check
  | .andElimLeft child => child.check
  | .andElimRight child => child.check
  | .orIntroLeft child => child.check
  | .orIntroRight child => child.check
  | .orElim disj left right => disj.check && left.check && right.check
  | .notIntro child => child.check
  | .notElim positive negative => positive.check && negative.check
  | .impIntro child => child.check
  | .mp implication antecedent => implication.check && antecedent.check
  | .boolCases _ _ left right => left.check && right.check
  | .allNatLtIntro _ _ child => child.check
  | .allNatLtIntroBounded _ _ child => child.check
  | .allNatLtElim _ _ _ forallD ltD => forallD.check && ltD.check
  | .applyNatBoundNatBeta _ child => child.check
  | .applyNatSubstitutionBeta _ _ _ child => child.check
  | .applyNatSubstitutionBetaElim _ _ _ child => child.check
  | .closedNatLt _ _ _ => true
  | .divLtOfLtSquare _ _ child => child.check
  | .modLtOfLtSquare _ _ child => child.check
  | .gridIdxLeftLtSquare _ _ _ rowLt colLt => rowLt.check && colLt.check
  | .gridIdxLeftDivEq _ _ _ rowLt colLt => rowLt.check && colLt.check
  | .gridIdxLeftModEq _ _ _ rowLt colLt => rowLt.check && colLt.check
  | .gridIdxLeftDivModEqOfRow _ _ _ qLt rowEq => qLt.check && rowEq.check
  | .gridIdxLeftDivModEqOfCol _ _ _ qLt colEq => qLt.check && colEq.check
  | .ltOfLtLtClosedPred _ _ _ xy ylimit => xy.check && ylimit.check
  | .eqStabRefl _ _ => true
  | .eqStabSymm _ _ _ child => child.check
  | .eqStabTrans _ _ _ _ left right => left.check && right.check
  | .eqPauliSymm _ _ child => child.check
  | .eqPauliTrans _ _ _ left right => left.check && right.check
  | .eqNatBoolTrue _ _ child => child.check
  | .eqBoolFalseNotTrue _ child => child.check
  | .eqBoolTrueNotFalse _ child => child.check
  | .eqStabMulCongr _ _ _ _ _ left right => left.check && right.check
  | .eqStabMulAssoc _ _ _ _ hA hB hC => hA.check && hB.check && hC.check
  | .eqStabMulComm _ _ _ hA hB => hA.check && hB.check
  | .eqStabMulSelf _ _ child => child.check
  | .eqStabMulOneLeft _ _ child => child.check
  | .eqStabMulOneRight _ _ child => child.check
  | .eqStabFoldZero _ _ => true
  | .eqStabFoldSucc _ _ _ => true
  | .commutesSymm _ _ _ child => child.check
  | .noncommutesSymm _ _ _ child => child.check
  | .commutesOfEqLeft _ _ _ _ eqD commD => eqD.check && commD.check
  | .commutesOfEqRight _ _ _ _ eqD commD => eqD.check && commD.check
  | .noncommutesOfEqLeft _ _ _ _ eqD noncommD => eqD.check && noncommD.check
  | .noncommutesOfEqRight _ _ _ _ eqD noncommD => eqD.check && noncommD.check
  | .commutesStabMulLeft _ _ _ _ left right => left.check && right.check
  | .noncommutesStabMulLeft _ _ _ _ left right => left.check && right.check
  | .noncommutesStabMulRight _ _ _ _ left right => left.check && right.check
  | .commutesStabFoldLeft _ _ _ _ child => child.check
  | .commutesOfPointwise _ _ _ child => child.check
  | .noncommutesOfSingleAnti _ _ _ _ ltD antiD restD =>
      ltD.check && antiD.check && restD.check
  | .commutesOfTwoAnti _ _ _ _ _ lt0D lt1D neD anti0D anti1D restD =>
      lt0D.check && lt1D.check && neD.check && anti0D.check && anti1D.check && restD.check
  | .stabAtClosedIteLamEqThen _ _ _ _ _ child => child.check
  | .stabAtClosedIteLamEqElse _ _ _ _ _ child => child.check
  | .pauliIteSelectThen _ _ _ child => child.check
  | .pauliIteSelectElse _ _ _ child => child.check
  | .localCommutesOfLeftI _ _ _ child => child.check
  | .localCommutesOfLeftEqNoAntiRight _ _ _ _ eqD noAntiD =>
      eqD.check && noAntiD.check
  | .localCommutesOfRightI _ _ _ child => child.check
  | .anticommutesTransport _ _ _ _ _ eqAD eqBD antiD =>
      eqAD.check && eqBD.check && antiD.check
  | .noAntiAtSubst _ _ _ _ _ _ eqD noAntiD => eqD.check && noAntiD.check
  | .pauliAnticommutesNonI _ _ child => child.check
  | .pauliAnticommutesLit _ _ => true
  | .pauliMulLit _ _ => true
  | .pauliEqLit _ => true
  | .pauliNeqLit _ _ _ => true
  | .finiteInjectiveWeightLower _ _ _ _ _ support inj lt =>
      support.check && inj.check && lt.check
  | .finiteSurjectiveWeightLower _ _ _ _ _ cover lt =>
      cover.check && lt.check
  | .finiteDeMorgan _ _ child => child.check
  | .existsNatLtIntro _ _ _ child => child.check
  | .existsNatLtIntroTerm _ _ _ ltD bodyD => ltD.check && bodyD.check
  | .existsNatLtElim _ _ _ existsD bodyD => existsD.check && bodyD.check

def size {arity : Nat} {Γ : List (SFormula arity)} {A : SFormula arity} :
    Deriv Γ A -> Nat
  | .hyp _ => 1
  | .contextWeakening _ child => 1 + child.size
  | .weakenFresh child => 1 + child.size
  | .top => 1
  | .botElim child => 1 + child.size
  | .andIntro left right => 1 + left.size + right.size
  | .andElimLeft child => 1 + child.size
  | .andElimRight child => 1 + child.size
  | .orIntroLeft child => 1 + child.size
  | .orIntroRight child => 1 + child.size
  | .orElim disj left right => 1 + disj.size + left.size + right.size
  | .notIntro child => 1 + child.size
  | .notElim positive negative => 1 + positive.size + negative.size
  | .impIntro child => 1 + child.size
  | .mp implication antecedent => 1 + implication.size + antecedent.size
  | .boolCases _ _ left right => 1 + left.size + right.size
  | .allNatLtIntro _ _ child => 1 + child.size
  | .allNatLtIntroBounded _ _ child => 1 + child.size
  | .allNatLtElim _ _ _ forallD ltD => 1 + forallD.size + ltD.size
  | .applyNatBoundNatBeta _ child => 1 + child.size
  | .applyNatSubstitutionBeta _ _ _ child => 1 + child.size
  | .applyNatSubstitutionBetaElim _ _ _ child => 1 + child.size
  | .closedNatLt _ _ _ => 1
  | .divLtOfLtSquare _ _ child => 1 + child.size
  | .modLtOfLtSquare _ _ child => 1 + child.size
  | .gridIdxLeftLtSquare _ _ _ rowLt colLt => 1 + rowLt.size + colLt.size
  | .gridIdxLeftDivEq _ _ _ rowLt colLt => 1 + rowLt.size + colLt.size
  | .gridIdxLeftModEq _ _ _ rowLt colLt => 1 + rowLt.size + colLt.size
  | .gridIdxLeftDivModEqOfRow _ _ _ qLt rowEq => 1 + qLt.size + rowEq.size
  | .gridIdxLeftDivModEqOfCol _ _ _ qLt colEq => 1 + qLt.size + colEq.size
  | .ltOfLtLtClosedPred _ _ _ xy ylimit => 1 + xy.size + ylimit.size
  | .eqStabRefl _ _ => 1
  | .eqStabSymm _ _ _ child => 1 + child.size
  | .eqStabTrans _ _ _ _ left right => 1 + left.size + right.size
  | .eqPauliSymm _ _ child => 1 + child.size
  | .eqPauliTrans _ _ _ left right => 1 + left.size + right.size
  | .eqNatBoolTrue _ _ child => 1 + child.size
  | .eqBoolFalseNotTrue _ child => 1 + child.size
  | .eqBoolTrueNotFalse _ child => 1 + child.size
  | .eqStabMulCongr _ _ _ _ _ left right => 1 + left.size + right.size
  | .eqStabMulAssoc _ _ _ _ hA hB hC => 1 + hA.size + hB.size + hC.size
  | .eqStabMulComm _ _ _ hA hB => 1 + hA.size + hB.size
  | .eqStabMulSelf _ _ child => 1 + child.size
  | .eqStabMulOneLeft _ _ child => 1 + child.size
  | .eqStabMulOneRight _ _ child => 1 + child.size
  | .eqStabFoldZero _ _ => 1
  | .eqStabFoldSucc _ _ _ => 1
  | .commutesSymm _ _ _ child => 1 + child.size
  | .noncommutesSymm _ _ _ child => 1 + child.size
  | .commutesOfEqLeft _ _ _ _ eqD commD => 1 + eqD.size + commD.size
  | .commutesOfEqRight _ _ _ _ eqD commD => 1 + eqD.size + commD.size
  | .noncommutesOfEqLeft _ _ _ _ eqD noncommD => 1 + eqD.size + noncommD.size
  | .noncommutesOfEqRight _ _ _ _ eqD noncommD => 1 + eqD.size + noncommD.size
  | .commutesStabMulLeft _ _ _ _ left right => 1 + left.size + right.size
  | .noncommutesStabMulLeft _ _ _ _ left right => 1 + left.size + right.size
  | .noncommutesStabMulRight _ _ _ _ left right => 1 + left.size + right.size
  | .commutesStabFoldLeft _ _ _ _ child => 1 + child.size
  | .commutesOfPointwise _ _ _ child => 1 + child.size
  | .noncommutesOfSingleAnti _ _ _ _ ltD antiD restD =>
      1 + ltD.size + antiD.size + restD.size
  | .commutesOfTwoAnti _ _ _ _ _ lt0D lt1D neD anti0D anti1D restD =>
      1 + lt0D.size + lt1D.size + neD.size + anti0D.size + anti1D.size + restD.size
  | .stabAtClosedIteLamEqThen _ _ _ _ _ child => 1 + child.size
  | .stabAtClosedIteLamEqElse _ _ _ _ _ child => 1 + child.size
  | .pauliIteSelectThen _ _ _ child => 1 + child.size
  | .pauliIteSelectElse _ _ _ child => 1 + child.size
  | .localCommutesOfLeftI _ _ _ child => 1 + child.size
  | .localCommutesOfLeftEqNoAntiRight _ _ _ _ eqD noAntiD =>
      1 + eqD.size + noAntiD.size
  | .localCommutesOfRightI _ _ _ child => 1 + child.size
  | .anticommutesTransport _ _ _ _ _ eqAD eqBD antiD =>
      1 + eqAD.size + eqBD.size + antiD.size
  | .noAntiAtSubst _ _ _ _ _ _ eqD noAntiD => 1 + eqD.size + noAntiD.size
  | .pauliAnticommutesNonI _ _ child => 1 + child.size
  | .pauliAnticommutesLit _ _ => 1
  | .pauliMulLit _ _ => 1
  | .pauliEqLit _ => 1
  | .pauliNeqLit _ _ _ => 1
  | .finiteInjectiveWeightLower _ _ _ _ _ support inj lt =>
      1 + support.size + inj.size + lt.size
  | .finiteSurjectiveWeightLower _ _ _ _ _ cover lt =>
      1 + cover.size + lt.size
  | .finiteDeMorgan _ _ child => 1 + child.size
  | .existsNatLtIntro _ _ _ child => 1 + child.size
  | .existsNatLtIntroTerm _ _ _ ltD bodyD => 1 + ltD.size + bodyD.size
  | .existsNatLtElim _ _ _ existsD bodyD => 1 + existsD.size + bodyD.size

def FormulaDefined {arity : Nat} (codeBody : Term 2 .stab) (fuel : Nat)
    (rho : Env arity) (E : PartialStabilizer) (A : SFormula arity) : Prop :=
  exists b, A.eval codeBody fuel rho E = some b

def DefinedObligations {arity : Nat} {Γ : List (SFormula arity)} {A : SFormula arity}
    (D : Deriv Γ A) (codeBody : Term 2 .stab) (fuel : Nat)
    (rho : Env arity) (E : PartialStabilizer) : Prop :=
  match D with
  | .hyp _ => True
  | .contextWeakening _ child =>
      child.DefinedObligations codeBody fuel rho E
  | .weakenFresh child =>
      child.DefinedObligations codeBody fuel (envTail rho) E
  | .top => True
  | .botElim child => child.DefinedObligations codeBody fuel rho E
  | .andIntro left right =>
      left.DefinedObligations codeBody fuel rho E /\
        right.DefinedObligations codeBody fuel rho E
  | .andElimLeft child => child.DefinedObligations codeBody fuel rho E
  | .andElimRight child => child.DefinedObligations codeBody fuel rho E
  | .orIntroLeft child => child.DefinedObligations codeBody fuel rho E
  | .orIntroRight (A := A) child =>
      FormulaDefined codeBody fuel rho E A /\
        child.DefinedObligations codeBody fuel rho E
  | .orElim disj left right =>
      disj.DefinedObligations codeBody fuel rho E /\
        left.DefinedObligations codeBody fuel rho E /\
          right.DefinedObligations codeBody fuel rho E
  | .notIntro (A := A) child =>
      FormulaDefined codeBody fuel rho E A /\
        child.DefinedObligations codeBody fuel rho E
  | .notElim positive negative =>
      positive.DefinedObligations codeBody fuel rho E /\
        negative.DefinedObligations codeBody fuel rho E
  | .impIntro (A := A) child =>
      FormulaDefined codeBody fuel rho E A /\
        child.DefinedObligations codeBody fuel rho E
  | .mp implication antecedent =>
      implication.DefinedObligations codeBody fuel rho E /\
        antecedent.DefinedObligations codeBody fuel rho E
  | .boolCases b _ left right =>
      (exists bv, b.eval codeBody fuel rho E = some bv) /\
        (b.eval codeBody fuel rho E = some true -> left.DefinedObligations codeBody fuel rho E) /\
          (b.eval codeBody fuel rho E = some false -> right.DefinedObligations codeBody fuel rho E)
  | .allNatLtIntro (Γ := Γ) n _ child =>
      exists bound, n.eval codeBody fuel rho E = some bound /\
        forall x, x < bound ->
          child.DefinedObligations codeBody fuel (Env.cons x rho) E /\
            ContextHolds codeBody fuel (Env.cons x rho) E
              (Γ.map (fun G => G.weaken))
  | .allNatLtIntroBounded (Γ := Γ) n _ child =>
      exists bound, n.eval codeBody fuel rho E = some bound /\
        forall x, x < bound ->
          child.DefinedObligations codeBody fuel (Env.cons x rho) E /\
            ContextHolds codeBody fuel (Env.cons x rho) E
              (SFormula.boundNatLt n :: Γ.map (fun G => G.weaken))
  | .allNatLtElim _ _ _ forallD ltD =>
      forallD.DefinedObligations codeBody fuel rho E /\
        ltD.DefinedObligations codeBody fuel rho E
  | .applyNatBoundNatBeta _ child =>
      child.DefinedObligations codeBody fuel rho E
  | .applyNatSubstitutionBeta _ _ _ child =>
      child.DefinedObligations codeBody fuel rho E
  | .applyNatSubstitutionBetaElim _ _ _ child =>
      child.DefinedObligations codeBody fuel rho E
  | .closedNatLt _ _ _ => True
  | .divLtOfLtSquare _ _ child =>
      child.DefinedObligations codeBody fuel rho E
  | .modLtOfLtSquare _ _ child =>
      child.DefinedObligations codeBody fuel rho E
  | .gridIdxLeftLtSquare _ _ _ rowLt colLt =>
      rowLt.DefinedObligations codeBody fuel rho E /\
        colLt.DefinedObligations codeBody fuel rho E
  | .gridIdxLeftDivEq _ _ _ rowLt colLt =>
      rowLt.DefinedObligations codeBody fuel rho E /\
        colLt.DefinedObligations codeBody fuel rho E
  | .gridIdxLeftModEq _ _ _ rowLt colLt =>
      rowLt.DefinedObligations codeBody fuel rho E /\
        colLt.DefinedObligations codeBody fuel rho E
  | .gridIdxLeftDivModEqOfRow _ _ _ qLt rowEq =>
      qLt.DefinedObligations codeBody fuel rho E /\
        rowEq.DefinedObligations codeBody fuel rho E
  | .gridIdxLeftDivModEqOfCol _ _ _ qLt colEq =>
      qLt.DefinedObligations codeBody fuel rho E /\
        colEq.DefinedObligations codeBody fuel rho E
  | .ltOfLtLtClosedPred _ _ _ xy ylimit =>
      xy.DefinedObligations codeBody fuel rho E /\
        ylimit.DefinedObligations codeBody fuel rho E
  | .eqStabRefl n A =>
      FormulaDefined codeBody fuel rho E (.eqStabUpTo n A A)
  | .eqStabSymm _ _ _ child =>
      child.DefinedObligations codeBody fuel rho E
  | .eqStabTrans _ _ _ _ left right =>
      left.DefinedObligations codeBody fuel rho E /\
        right.DefinedObligations codeBody fuel rho E
  | .eqPauliSymm _ _ child =>
      child.DefinedObligations codeBody fuel rho E
  | .eqPauliTrans _ _ _ left right =>
      left.DefinedObligations codeBody fuel rho E /\
        right.DefinedObligations codeBody fuel rho E
  | .eqNatBoolTrue _ _ child =>
      child.DefinedObligations codeBody fuel rho E
  | .eqBoolFalseNotTrue _ child =>
      child.DefinedObligations codeBody fuel rho E
  | .eqBoolTrueNotFalse _ child =>
      child.DefinedObligations codeBody fuel rho E
  | .eqStabMulCongr _ _ _ _ _ left right =>
      left.DefinedObligations codeBody fuel rho E /\
        right.DefinedObligations codeBody fuel rho E
  | .eqStabMulAssoc _ _ _ _ hA hB hC =>
      hA.DefinedObligations codeBody fuel rho E /\
        hB.DefinedObligations codeBody fuel rho E /\
          hC.DefinedObligations codeBody fuel rho E
  | .eqStabMulComm _ _ _ hA hB =>
      hA.DefinedObligations codeBody fuel rho E /\
        hB.DefinedObligations codeBody fuel rho E
  | .eqStabMulSelf _ _ child =>
      child.DefinedObligations codeBody fuel rho E
  | .eqStabMulOneLeft _ _ child =>
      child.DefinedObligations codeBody fuel rho E
  | .eqStabMulOneRight _ _ child =>
      child.DefinedObligations codeBody fuel rho E
  | .eqStabFoldZero n body =>
      FormulaDefined codeBody fuel rho E (.eqStabUpTo n (SC.stabFold (SC.n 0) body) SC.stabOne)
  | .eqStabFoldSucc n bound body =>
      FormulaDefined codeBody fuel rho E (.eqStabUpTo n
        (SC.stabFold (SC.succClosed bound) body)
        (SC.stabMul (SC.stabFold (SC.closed bound) body) (SC.applyNat bound body)))
  | .commutesSymm _ _ _ child =>
      child.DefinedObligations codeBody fuel rho E
  | .noncommutesSymm _ _ _ child =>
      child.DefinedObligations codeBody fuel rho E
  | .commutesOfEqLeft _ _ _ _ eqD commD =>
      eqD.DefinedObligations codeBody fuel rho E /\
        commD.DefinedObligations codeBody fuel rho E
  | .commutesOfEqRight _ _ _ _ eqD commD =>
      eqD.DefinedObligations codeBody fuel rho E /\
        commD.DefinedObligations codeBody fuel rho E
  | .noncommutesOfEqLeft _ _ _ _ eqD noncommD =>
      eqD.DefinedObligations codeBody fuel rho E /\
        noncommD.DefinedObligations codeBody fuel rho E
  | .noncommutesOfEqRight _ _ _ _ eqD noncommD =>
      eqD.DefinedObligations codeBody fuel rho E /\
        noncommD.DefinedObligations codeBody fuel rho E
  | .commutesStabMulLeft _ _ _ _ left right =>
      left.DefinedObligations codeBody fuel rho E /\
        right.DefinedObligations codeBody fuel rho E
  | .noncommutesStabMulLeft _ _ _ _ left right =>
      left.DefinedObligations codeBody fuel rho E /\
        right.DefinedObligations codeBody fuel rho E
  | .noncommutesStabMulRight _ _ _ _ left right =>
      left.DefinedObligations codeBody fuel rho E /\
        right.DefinedObligations codeBody fuel rho E
  | .commutesStabFoldLeft n bound body C child =>
      child.DefinedObligations codeBody fuel rho E /\
        FormulaDefined codeBody fuel rho E (.commutesUpTo n (SC.stabFold bound body) C)
  | .commutesOfPointwise n A B child =>
      child.DefinedObligations codeBody fuel rho E /\
        FormulaDefined codeBody fuel rho E (.commutesUpTo n A B)
  | .noncommutesOfSingleAnti _ _ _ _ ltD antiD restD =>
      ltD.DefinedObligations codeBody fuel rho E /\
        antiD.DefinedObligations codeBody fuel rho E /\
          restD.DefinedObligations codeBody fuel rho E
  | .commutesOfTwoAnti _ _ _ _ _ lt0D lt1D neD anti0D anti1D restD =>
      lt0D.DefinedObligations codeBody fuel rho E /\
        lt1D.DefinedObligations codeBody fuel rho E /\
          neD.DefinedObligations codeBody fuel rho E /\
            anti0D.DefinedObligations codeBody fuel rho E /\
              anti1D.DefinedObligations codeBody fuel rho E /\
                restD.DefinedObligations codeBody fuel rho E
  | .stabAtClosedIteLamEqThen cond thenP elseP q _ child =>
      child.DefinedObligations codeBody fuel rho E /\
        FormulaDefined codeBody fuel rho E
          (.eqPauli
            (.stabAt (SC.closed (.stabLam (.ite cond thenP elseP))) (SC.closed q))
            (SC.closed (Term.instantiateTopNat q thenP)))
  | .stabAtClosedIteLamEqElse cond thenP elseP q _ child =>
      child.DefinedObligations codeBody fuel rho E /\
        FormulaDefined codeBody fuel rho E
          (.eqPauli
            (.stabAt (SC.closed (.stabLam (.ite cond thenP elseP))) (SC.closed q))
            (SC.closed (Term.instantiateTopNat q elseP)))
  | .pauliIteSelectThen cond p1 p2 child =>
      child.DefinedObligations codeBody fuel rho E /\
        FormulaDefined codeBody fuel rho E
          (.eqPauli (SC.closed (.ite cond p1 p2)) (SC.closed p1))
  | .pauliIteSelectElse cond p1 p2 child =>
      child.DefinedObligations codeBody fuel rho E /\
        FormulaDefined codeBody fuel rho E
          (.eqPauli (SC.closed (.ite cond p1 p2)) (SC.closed p2))
  | .localCommutesOfLeftI A B q child =>
      child.DefinedObligations codeBody fuel rho E /\
        FormulaDefined codeBody fuel rho E (SFormula.localCommutesAt A B q)
  | .localCommutesOfLeftEqNoAntiRight A B q p eqD noAntiD =>
      eqD.DefinedObligations codeBody fuel rho E /\
        noAntiD.DefinedObligations codeBody fuel rho E /\
          FormulaDefined codeBody fuel rho E (SFormula.localCommutesAt A B q)
  | .localCommutesOfRightI A B q child =>
      child.DefinedObligations codeBody fuel rho E /\
        FormulaDefined codeBody fuel rho E (SFormula.localCommutesAt A B q)
  | .anticommutesTransport a b _ _ rhs eqAD eqBD antiD =>
      eqAD.DefinedObligations codeBody fuel rho E /\
        eqBD.DefinedObligations codeBody fuel rho E /\
          antiD.DefinedObligations codeBody fuel rho E /\
            FormulaDefined codeBody fuel rho E
              (.eqBool (.anticommutes a b) rhs)
  | .noAntiAtSubst Eterm p _ q₂ _ _ eqD noAntiD =>
      eqD.DefinedObligations codeBody fuel rho E /\
        noAntiD.DefinedObligations codeBody fuel rho E /\
          FormulaDefined codeBody fuel rho E
            (.not (.eqBool (.anticommutes (.stabAt Eterm (SC.closed q₂)) p)
              (SC.b true)))
  | .pauliAnticommutesNonI _ _ child =>
      child.DefinedObligations codeBody fuel rho E
  | .pauliAnticommutesLit _ _ => True
  | .pauliMulLit _ _ => True
  | .pauliEqLit _ => True
  | .pauliNeqLit _ _ _ => True
  | .finiteInjectiveWeightLower n Eterm limit _ _ support inj lt =>
      support.DefinedObligations codeBody fuel rho E /\
        inj.DefinedObligations codeBody fuel rho E /\
          lt.DefinedObligations codeBody fuel rho E /\
            FormulaDefined codeBody fuel rho E (.weightLe n Eterm limit)
  | .finiteSurjectiveWeightLower n Eterm limit _ _ cover lt =>
      cover.DefinedObligations codeBody fuel rho E /\
        lt.DefinedObligations codeBody fuel rho E /\
          FormulaDefined codeBody fuel rho E (.weightLe n Eterm limit)
  | .finiteDeMorgan n A child =>
      child.DefinedObligations codeBody fuel rho E /\
        exists bound, n.eval codeBody fuel rho E = some bound /\
          forall x, x < bound -> FormulaDefined codeBody fuel (Env.cons x rho) E A
  | .existsNatLtIntro (Γ := Γ) n A witness child =>
      exists bound, n.eval codeBody fuel rho E = some bound /\
        witness < bound /\
          (forall x, x < bound ->
            FormulaDefined codeBody fuel (Env.cons x rho) E A) /\
            child.DefinedObligations codeBody fuel (Env.cons witness rho) E /\
              ContextHolds codeBody fuel (Env.cons witness rho) E
                (Γ.map (fun G => G.weaken))
  | .existsNatLtIntroTerm n A _ ltD bodyD =>
      ltD.DefinedObligations codeBody fuel rho E /\
        bodyD.DefinedObligations codeBody fuel rho E /\
          exists bound, n.eval codeBody fuel rho E = some bound /\
            forall x, x < bound -> FormulaDefined codeBody fuel (Env.cons x rho) E A
  | .existsNatLtElim (Γ := Γ) n A _ existsD bodyD =>
      existsD.DefinedObligations codeBody fuel rho E /\
        exists bound, n.eval codeBody fuel rho E = some bound /\
          forall x, x < bound ->
            A.eval codeBody fuel (Env.cons x rho) E = some true ->
              bodyD.DefinedObligations codeBody fuel (Env.cons x rho) E /\
                ContextHolds codeBody fuel (Env.cons x rho) E
                  (A :: SFormula.boundNatLt n :: Γ.map (fun G => G.weaken))

private theorem and_eval_true_left {arity : Nat} {codeBody : Term 2 .stab}
    {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    {A B : SFormula arity} :
    SFormula.eval codeBody fuel (.and A B) rho E = some true ->
      SFormula.eval codeBody fuel A rho E = some true := by
  intro h
  simp [SFormula.eval] at h
  cases hA : SFormula.eval codeBody fuel A rho E with
  | none =>
      simp [hA] at h
  | some av =>
      cases av <;> simp [hA] at h ⊢

private theorem and_eval_true_right {arity : Nat} {codeBody : Term 2 .stab}
    {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    {A B : SFormula arity} :
    SFormula.eval codeBody fuel (.and A B) rho E = some true ->
      SFormula.eval codeBody fuel B rho E = some true := by
  intro h
  simp [SFormula.eval] at h
  cases hA : SFormula.eval codeBody fuel A rho E with
  | none =>
      simp [hA] at h
  | some av =>
      cases av <;> simp [hA] at h
      exact h

private theorem imp_eval_true_apply {arity : Nat} {codeBody : Term 2 .stab}
    {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    {A B : SFormula arity} :
    SFormula.eval codeBody fuel (.imp A B) rho E = some true ->
      SFormula.eval codeBody fuel A rho E = some true ->
        SFormula.eval codeBody fuel B rho E = some true := by
  intro himp hA
  simp [SFormula.eval, hA] at himp
  exact himp

private theorem or_eval_true_cases {arity : Nat} {codeBody : Term 2 .stab}
    {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    {A B : SFormula arity} :
    SFormula.eval codeBody fuel (.or A B) rho E = some true ->
      SFormula.eval codeBody fuel A rho E = some true \/
        SFormula.eval codeBody fuel B rho E = some true := by
  intro hor
  simp [SFormula.eval] at hor
  cases hA : SFormula.eval codeBody fuel A rho E with
  | none =>
      simp [hA] at hor
  | some av =>
      cases av
      · simp [hA] at hor ⊢
        exact hor
      · simp

private theorem not_eval_true_false {arity : Nat} {codeBody : Term 2 .stab}
    {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    {A : SFormula arity} :
    SFormula.eval codeBody fuel (.not A) rho E = some true ->
      SFormula.eval codeBody fuel A rho E = some false := by
  intro hnot
  simp [SFormula.eval] at hnot
  cases hA : SFormula.eval codeBody fuel A rho E with
  | none =>
      simp [hA] at hnot
  | some av =>
      cases av <;> simp [hA] at hnot ⊢

private theorem witnessLt_eval_true {arity : Nat} {codeBody : Term 2 .stab}
    {fuel : Nat} {rho : Env arity} {E : PartialStabilizer}
    {witness n : STerm arity .nat} :
    SFormula.eval codeBody fuel (SFormula.witnessLt witness n) rho E = some true ->
      exists wv bound,
        witness.eval codeBody fuel rho E = some wv /\
          n.eval codeBody fuel rho E = some bound /\
            wv < bound := by
  intro h
  simp [SFormula.witnessLt, SFormula.eval, STerm.eval, Term.eval, SC.b] at h
  cases hw : witness.eval codeBody fuel rho E with
  | none =>
      simp [hw] at h
  | some wv =>
      simp [hw] at h
      cases hn : n.eval codeBody fuel rho E with
      | none =>
          simp [hn] at h
      | some bound =>
          simp [hn] at h
          exact ⟨wv, bound, rfl, rfl, h⟩

private theorem slotSupportBody_eval_true {arity : Nat} {codeBody : Term 2 .stab}
    {fuel : Nat} {rho : Env arity} {Ebound : PartialStabilizer}
    {n : STerm arity .nat} {Eterm : STerm arity .stab}
    {slot : STerm (arity + 1) .nat} {i nv : Nat} {Ev : PartialStabilizer} :
    SFormula.eval codeBody fuel (SFormula.slotSupportBody n Eterm slot)
        (Env.cons i rho) Ebound = some true ->
      n.eval codeBody fuel rho Ebound = some nv ->
        Eterm.eval codeBody fuel rho Ebound = some Ev ->
          exists q,
            slot.eval codeBody fuel (Env.cons i rho) Ebound = some q /\
              q < nv /\ nonIBool Ev q = true := by
  intro h hN hE
  have hLt := and_eval_true_left h
  have hNonI := and_eval_true_right h
  rcases witnessLt_eval_true hLt with ⟨q, bound, hSlot, hNweak, hqLt⟩
  have hNweaken :
      n.weaken.eval codeBody fuel (Env.cons i rho) Ebound = some nv := by
    simpa [STerm.weaken] using
      STerm.eval_lift_of_env n (EnvLifted.underTop rho i) codeBody fuel Ebound ▸ hN
  have hbound : bound = nv := by
    rw [hNweaken] at hNweak
    exact Option.some.inj hNweak.symm
  subst hbound
  have hEweaken :
      Eterm.weaken.eval codeBody fuel (Env.cons i rho) Ebound = some Ev := by
    simpa [STerm.weaken] using
      STerm.eval_lift_of_env Eterm (EnvLifted.underTop rho i) codeBody fuel Ebound ▸ hE
  have hEqFalse := not_eval_true_false hNonI
  simp [SFormula.eval, hEweaken, hSlot, SC.p, STerm.eval, Term.eval] at hEqFalse
  cases hEvq : Ev q with
  | none =>
      simp [hEvq] at hEqFalse
  | some p =>
      simp [hEvq] at hEqFalse
      have hpNe : p ≠ Pauli.I := by
        intro hp
        simp [hp] at hEqFalse
      exact ⟨q, hSlot, hqLt, by simp [nonIBool, hEvq, hpNe]⟩

private theorem slotInjectiveF_eval_true {arity : Nat} {codeBody : Term 2 .stab}
    {fuel : Nat} {rho : Env arity} {Ebound : PartialStabilizer}
    {k : STerm arity .nat} {slot : STerm (arity + 1) .nat} {kv : Nat} :
    SFormula.eval codeBody fuel (SFormula.slotInjectiveF k slot) rho Ebound = some true ->
      k.eval codeBody fuel rho Ebound = some kv ->
        forall i j qi qj,
          i < kv -> j < kv ->
            slot.eval codeBody fuel (Env.cons i rho) Ebound = some qi ->
              slot.eval codeBody fuel (Env.cons j rho) Ebound = some qj ->
                qi = qj -> i = j := by
  intro h hK i j qi qj hi hj hSlotI hSlotJ hEq
  simp [SFormula.slotInjectiveF, SFormula.eval, hK] at h
  have hI := allNatLt_sound h i hi
  have hKweaken :
      k.weaken.eval codeBody fuel (Env.cons i rho) Ebound = some kv := by
    simpa [STerm.weaken] using
      STerm.eval_lift_of_env k (EnvLifted.underTop rho i) codeBody fuel Ebound ▸ hK
  simp [hKweaken] at hI
  have hJ := allNatLt_sound hI j hj
  have hSlotIweaken :
      slot.weaken.eval codeBody fuel (Env.cons j (Env.cons i rho)) Ebound = some qi := by
    simpa [STerm.weaken] using
      STerm.eval_lift_of_env slot (EnvLifted.underTop (Env.cons i rho) j)
        codeBody fuel Ebound ▸ hSlotI
  have hBaseLift : EnvLifted 1 (Env.cons j rho) (Env.cons j (Env.cons i rho)) :=
    EnvLifted.underBinder (EnvLifted.underTop rho i) j
  have hSlotJlift :
      (slot.lift 1).eval codeBody fuel (Env.cons j (Env.cons i rho)) Ebound =
        some qj := by
    simpa using
      STerm.eval_lift_of_env slot hBaseLift codeBody fuel Ebound ▸ hSlotJ
  have hAnte :
      SFormula.eval codeBody fuel
        (.eqNat slot.weaken (slot.lift 1)) (Env.cons j (Env.cons i rho)) Ebound =
          some true := by
    simp [SFormula.eval, hSlotIweaken, hSlotJlift, hEq]
  have hCons := imp_eval_true_apply hJ hAnte
  simp [SFormula.eval, SFormula.boundNat, STerm.weaken, STerm.lift, STerm.eval,
    Term.lift, Term.weakenVar, Term.eval, SC.closed, Env.cons] at hCons
  exact hCons.symm

private theorem supportSurjectiveBody_eval_true {arity : Nat} {codeBody : Term 2 .stab}
    {fuel : Nat} {rho : Env arity} {Ebound : PartialStabilizer}
    {n : STerm arity .nat} {Eterm : STerm arity .stab}
    {rowOf : STerm (arity + 1) .nat} {i nv : Nat} {Ev : PartialStabilizer} :
    SFormula.eval codeBody fuel (SFormula.supportSurjectiveBody n Eterm rowOf)
        (Env.cons i rho) Ebound = some true ->
      n.eval codeBody fuel rho Ebound = some nv ->
        Eterm.eval codeBody fuel rho Ebound = some Ev ->
          exists q,
            q < nv /\
              nonIBool Ev q = true /\
                rowOf.eval codeBody fuel (Env.cons q rho) Ebound = some i := by
  intro h hN hE
  have hNweaken :
      n.weaken.eval codeBody fuel (Env.cons i rho) Ebound = some nv := by
    simpa [STerm.weaken] using
      STerm.eval_lift_of_env n (EnvLifted.underTop rho i) codeBody fuel Ebound ▸ hN
  simp [SFormula.supportSurjectiveBody, SFormula.eval, hNweaken] at h
  rcases existsNatLt_sound h with ⟨q, hqLt, hBody⟩
  change SFormula.eval codeBody fuel
      (.and
        (SFormula.nonIAt Eterm.weaken.weaken (SFormula.boundNat (arity := arity + 1)))
        (.eqNat (rowOf.lift 1) ((SFormula.boundNat (arity := arity)).weaken)))
      (Env.cons q (Env.cons i rho)) Ebound = some true at hBody
  have hNonI := and_eval_true_left hBody
  have hRowEq := and_eval_true_right hBody
  have hEweaken1 :
      Eterm.weaken.eval codeBody fuel (Env.cons i rho) Ebound = some Ev := by
    simpa [STerm.weaken] using
      STerm.eval_lift_of_env Eterm (EnvLifted.underTop rho i) codeBody fuel Ebound ▸ hE
  have hEweaken2 :
      Eterm.weaken.weaken.eval codeBody fuel (Env.cons q (Env.cons i rho)) Ebound =
        some Ev := by
    simpa [STerm.weaken] using
      STerm.eval_lift_of_env Eterm.weaken
        (EnvLifted.underTop (Env.cons i rho) q) codeBody fuel Ebound ▸ hEweaken1
  have hEqFalse := not_eval_true_false hNonI
  have hQIndex :
      (SFormula.boundNat (arity := arity + 1)).eval codeBody fuel
        (Env.cons q (Env.cons i rho)) Ebound = some q := by
      simp [SFormula.boundNat, SC.closed, STerm.eval, Term.eval, Env.cons]
      rfl
  simp [SFormula.eval, hEweaken2, hQIndex, SC.p, STerm.eval, Term.eval] at hEqFalse
  have hNonIBool : nonIBool Ev q = true := by
    cases hEvq : Ev q with
    | none =>
        simp [hEvq] at hEqFalse
    | some p =>
        simp [hEvq] at hEqFalse
        have hpNe : p ≠ Pauli.I := by
          intro hp
          simp [hp] at hEqFalse
        simp [nonIBool, hEvq, hpNe]
  have hBaseLift : EnvLifted 1 (Env.cons q rho) (Env.cons q (Env.cons i rho)) :=
    EnvLifted.underBinder (EnvLifted.underTop rho i) q
  have hRowOfLift :
      (rowOf.lift 1).eval codeBody fuel (Env.cons q (Env.cons i rho)) Ebound =
        rowOf.eval codeBody fuel (Env.cons q rho) Ebound := by
    exact STerm.eval_lift_of_env rowOf hBaseLift codeBody fuel Ebound
  have hRow :
      rowOf.eval codeBody fuel (Env.cons q rho) Ebound = some i := by
    have hRowIndex :
        (SFormula.boundNat (arity := arity)).weaken.eval codeBody fuel
          (Env.cons q (Env.cons i rho)) Ebound = some i := by
      have hBase :
          (SFormula.boundNat (arity := arity)).eval codeBody fuel
            (Env.cons i rho) Ebound = some i := by
        simp [SFormula.boundNat, SC.closed, STerm.eval, Term.eval, Env.cons]
        rfl
      simpa [STerm.weaken] using
        STerm.eval_lift_of_env (SFormula.boundNat (arity := arity))
          (EnvLifted.underTop (Env.cons i rho) q) codeBody fuel Ebound ▸ hBase
    simp [SFormula.eval, hRowOfLift, hRowIndex] at hRowEq
    cases hRowOf : rowOf.eval codeBody fuel (Env.cons q rho) Ebound with
    | none =>
        simp [hRowOf] at hRowEq
    | some r =>
        simp [hRowOf] at hRowEq
        have hri : r = i := hRowEq
        simp [hri]
  exact ⟨q, hqLt, hNonIBool, hRow⟩

private theorem finite_not_all_not_to_exists {n : Nat} {pred : Nat -> Option Bool} :
    (forall i, i < n -> exists b, pred i = some b) ->
      QHL.CodeLang.allNatLt n
          (fun i => do
            let b <- pred i
            some (!b)) = some false ->
        QHL.CodeLang.existsNatLt n pred = some true := by
  have allNatLt_defined :
      forall {n : Nat} {pred : Nat -> Option Bool},
        (forall i, i < n -> exists b, pred i = some b) ->
          exists b, QHL.CodeLang.allNatLt n pred = some b := by
    intro n pred htotal
    induction n with
    | zero =>
        exact ⟨true, rfl⟩
    | succ m ih =>
        obtain ⟨prev, hprev⟩ := ih (fun i hi => htotal i (by omega))
        cases prev
        · exact ⟨false, by simp [QHL.CodeLang.allNatLt, hprev]⟩
        · obtain ⟨last, hlast⟩ := htotal m (Nat.lt_succ_self m)
          cases last
          · exact ⟨false, by simp [QHL.CodeLang.allNatLt, hprev, hlast]⟩
          · exact ⟨true, by simp [QHL.CodeLang.allNatLt, hprev, hlast]⟩
  induction n with
  | zero =>
      intro _ h
      simp [QHL.CodeLang.allNatLt] at h
  | succ m ih =>
      intro htotal h
      unfold QHL.CodeLang.allNatLt at h
      have hprevTotal :
          forall i, i < m ->
            exists b,
              (do
                let b <- pred i
                some (!b)) = some b := by
        intro i hi
        obtain ⟨b, hb⟩ := htotal i (by omega)
        cases b <;> simp [hb]
      obtain ⟨prevDefined, hprevDefined⟩ := allNatLt_defined hprevTotal
      cases hprev :
          QHL.CodeLang.allNatLt m
            (fun i => do
              let b <- pred i
              some (!b)) with
      | none =>
          rw [hprev] at hprevDefined
          contradiction
      | some prev =>
          cases prev
          · have hexPrev : QHL.CodeLang.existsNatLt m pred = some true :=
              ih (fun i hi => htotal i (by omega)) hprev
            simp [QHL.CodeLang.existsNatLt, hexPrev]
          · rw [hprev] at h
            simp at h
            obtain ⟨last, hlast⟩ := htotal m (Nat.lt_succ_self m)
            cases last
            · simp [hlast] at h
            · have hpred : pred m = some true := hlast
              cases hexPrev : QHL.CodeLang.existsNatLt m pred with
              | none =>
                  obtain ⟨prevExistsDefined, hPrevExistsDefined⟩ :=
                    existsNatLt_defined (n := m) (pred := pred)
                      (fun i hi => htotal i (by omega))
                  rw [hexPrev] at hPrevExistsDefined
                  contradiction
              | some ok =>
                  cases ok <;> simp [QHL.CodeLang.existsNatLt, hexPrev, hpred]

theorem sound {arity : Nat} {codeBody : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {E : PartialStabilizer}
    {Γ : List (SFormula arity)} {A : SFormula arity}
    (D : Deriv Γ A) :
    D.DefinedObligations codeBody fuel rho E ->
    ContextHolds codeBody fuel rho E Γ ->
      A.eval codeBody fuel rho E = some true := by
  induction D with
  | hyp h =>
      intro _ hctx
      exact hctx _ h
  | contextWeakening hweak child ih =>
      intro hdef hctx
      exact ih hdef fun C hC => hctx C (hweak C hC)
  | weakenFresh child ih =>
      rename_i arity0 Γ0 A0
      intro hdef hctx
      let rho0 := envTail rho
      have hlift : EnvLifted 0 rho0 rho := EnvLifted.tail rho
      have hctx0 : ContextHolds codeBody fuel rho0 E Γ0 := by
        intro C hC
        have hWeak : C.weaken.eval codeBody fuel rho E = some true :=
          hctx C.weaken (List.mem_map.mpr ⟨C, hC, rfl⟩)
        simpa [SFormula.weaken] using
          (show C.eval codeBody fuel rho0 E = some true from by
            simpa [SFormula.weaken] using
              ((eval_lift_of_env C hlift codeBody fuel E).symm ▸ hWeak))
      have hChild := ih hdef hctx0
      simpa [SFormula.weaken] using
        (show (A0.lift 0).eval codeBody fuel rho E = some true from by
          rw [eval_lift_of_env A0 hlift codeBody fuel E]
          exact hChild)
  | top =>
      intro _ _
      rfl
  | botElim child ih =>
      intro hdef hctx
      have hbot := ih hdef hctx
      simp [SFormula.eval] at hbot
  | andIntro left right ihLeft ihRight =>
      intro hdef hctx
      exact
        let hLeft := ihLeft hdef.left hctx
        let hRight := ihRight hdef.right hctx
        by simp [SFormula.eval, hLeft, hRight]
  | andElimLeft child ih =>
      intro hdef hctx
      exact and_eval_true_left (ih hdef hctx)
  | andElimRight child ih =>
      intro hdef hctx
      exact and_eval_true_right (ih hdef hctx)
  | orIntroLeft child ih =>
      intro hdef hctx
      have hLeft := ih hdef hctx
      simp [SFormula.eval, hLeft]
  | orIntroRight child ih =>
      intro hdef hctx
      rcases hdef with ⟨⟨aVal, hA⟩, hChildDef⟩
      have hRight := ih hChildDef hctx
      cases aVal <;> simp [SFormula.eval, hA, hRight]
  | orElim disj left right ihDisj ihLeft ihRight =>
      intro hdef hctx
      rcases hdef with ⟨hDisjDef, hLeftDef, hRightDef⟩
      cases or_eval_true_cases (ihDisj hDisjDef hctx) with
      | inl hA =>
          exact ihLeft hLeftDef (fun C hC => by
            cases hC with
            | head => exact hA
            | tail _ htail => exact hctx C htail)
      | inr hB =>
          exact ihRight hRightDef (fun C hC => by
            cases hC with
            | head => exact hB
            | tail _ htail => exact hctx C htail)
  | notIntro child ih =>
      intro hdef hctx
      rcases hdef with ⟨⟨aVal, hA⟩, hChildDef⟩
      cases aVal
      · simp [SFormula.eval, hA]
      · have hbot := ih hChildDef (fun C hC => by
          cases hC with
          | head => exact hA
          | tail _ htail => exact hctx C htail)
        simp [SFormula.eval] at hbot
  | notElim positive negative ihPositive ihNegative =>
      intro hdef hctx
      have hPos := ihPositive hdef.left hctx
      have hNeg := not_eval_true_false (ihNegative hdef.right hctx)
      rw [hPos] at hNeg
      contradiction
  | impIntro child ih =>
      intro hdef hctx
      rcases hdef with ⟨⟨aVal, hA⟩, hChildDef⟩
      cases aVal
      · simp [SFormula.eval, hA]
      · simp [SFormula.eval, hA]
        exact ih hChildDef (fun C hC => by
          cases hC with
          | head => exact hA
          | tail _ htail => exact hctx C htail)
  | mp implication antecedent ihImp ihAntecedent =>
      intro hdef hctx
      exact imp_eval_true_apply (ihImp hdef.left hctx) (ihAntecedent hdef.right hctx)
  | boolCases b C left right ihLeft ihRight =>
      intro hdef hctx
      rcases hdef with ⟨⟨bv, hb⟩, hLeftDef, hRightDef⟩
      cases bv
      · exact ihRight (hRightDef hb) (fun F hF => by
          cases hF with
          | head =>
              simp [SFormula.eval, hb, SC.b, STerm.eval, Term.eval]
          | tail _ htail => exact hctx F htail)
      · exact ihLeft (hLeftDef hb) (fun F hF => by
          cases hF with
          | head =>
              simp [SFormula.eval, hb, SC.b, STerm.eval, Term.eval]
          | tail _ htail => exact hctx F htail)
  | allNatLtIntro n A child ih =>
      intro hdef _
      rcases hdef with ⟨bound, hbound, hbody⟩
      simp [SFormula.eval, hbound]
      exact allNatLt_complete (fun x hx => ih (hbody x hx).left (hbody x hx).right)
  | allNatLtIntroBounded n A child ih =>
      intro hdef _
      rcases hdef with ⟨bound, hbound, hbody⟩
      simp [SFormula.eval, hbound]
      exact allNatLt_complete (fun x hx => ih (hbody x hx).left (hbody x hx).right)
  | allNatLtElim n A witness forallD ltD ihForall ihLt =>
      intro hdef hctx
      rcases hdef with ⟨hForallDef, hLtDef⟩
      have hForall := ihForall hForallDef hctx
      have hLt := ihLt hLtDef hctx
      rcases witnessLt_eval_true hLt with ⟨wv, bound, hw, hbound, hwitness⟩
      simp [SFormula.eval, hbound] at hForall
      simp [SFormula.eval, hw]
      exact allNatLt_sound hForall wv hwitness
  | applyNatBoundNatBeta A child ih =>
      intro hdef hctx
      have hChild := ih hdef hctx
      rw [eval_applyNat_boundNat_lift_self A codeBody fuel rho E] at hChild
      exact hChild
  | applyNatSubstitutionBeta x A hx child ih =>
      intro hdef hctx
      obtain ⟨xv, hxv⟩ := hx.eval_total codeBody fuel rho
      have hxAll := hx.eval_all_fuels hxv
      have hChild := ih hdef hctx
      rw [eval_applyNat_closed_instantiateTopNat A x codeBody fuel rho E hxAll] at hChild
      exact hChild
  | applyNatSubstitutionBetaElim x A hx child ih =>
      intro hdef hctx
      obtain ⟨xv, hxv⟩ := hx.eval_total codeBody fuel rho
      have hxAll := hx.eval_all_fuels hxv
      have hChild := ih hdef hctx
      rw [eval_applyNat_closed_instantiateTopNat A x codeBody fuel rho E hxAll]
      exact hChild
  | closedNatLt a b h =>
      intro _ _
      have hlt : a < b := of_decide_eq_true h
      simp [SFormula.witnessLt, SFormula.eval, STerm.eval, Term.eval, SC.n, SC.b, hlt]
  | divLtOfLtSquare dist q child ih =>
      intro hdef hctx
      have hQ := ih hdef hctx
      rcases witnessLt_eval_true hQ with ⟨qv, bound, hq, hbound, hqLt⟩
      have hboundEq : bound = dist * dist := by
        have h : (some (dist * dist) : Option Nat) = some bound := by
          simpa [SC.n, SC.closed, STerm.eval, Term.eval] using hbound
        exact (Option.some.inj h).symm
      subst bound
      have hrowLt : qv / dist < dist := by
        by_cases hdist : dist = 0
        · subst dist
          simpa using hqLt
        · exact Nat.div_lt_of_lt_mul hqLt
      have hqEval : Term.eval codeBody fuel q rho = some qv := by
        simpa [SC.closed, STerm.eval] using hq
      simpa [SFormula.witnessLt, SFormula.eval, STerm.eval, Term.eval, SC.closed,
        SC.n, SC.b, NatArithmetic.rowOf, hqEval, hrowLt]
  | modLtOfLtSquare dist q child ih =>
      intro hdef hctx
      have hQ := ih hdef hctx
      rcases witnessLt_eval_true hQ with ⟨qv, bound, hq, hbound, hqLt⟩
      have hboundEq : bound = dist * dist := by
        have h : (some (dist * dist) : Option Nat) = some bound := by
          simpa [SC.n, SC.closed, STerm.eval, Term.eval] using hbound
        exact (Option.some.inj h).symm
      subst bound
      have hdistPos : 0 < dist := by
        by_cases hdist : dist = 0
        · subst dist
          simpa using hqLt
        · exact Nat.pos_of_ne_zero hdist
      have hmodLt : qv % dist < dist := Nat.mod_lt qv hdistPos
      have hqEval : Term.eval codeBody fuel q rho = some qv := by
        simpa [SC.closed, STerm.eval] using hq
      simpa [SFormula.witnessLt, SFormula.eval, STerm.eval, Term.eval, SC.closed,
        SC.n, SC.b, NatArithmetic.colOf, hqEval, hmodLt]
  | gridIdxLeftLtSquare dist row col rowLt colLt ihRow ihCol =>
      intro hdef hctx
      rcases hdef with ⟨hRowDef, hColDef⟩
      have hRow := ihRow hRowDef hctx
      have hCol := ihCol hColDef hctx
      rcases witnessLt_eval_true hRow with ⟨rv, dv, hrow, hdistRow, hrowLt⟩
      rcases witnessLt_eval_true hCol with ⟨cv, dv', hcol, hdistCol, hcolLt'⟩
      have hdv : dv = dist := by
        have h : (some dist : Option Nat) = some dv := by
          simpa [SC.n, SC.closed, STerm.eval, Term.eval] using hdistRow
        exact (Option.some.inj h).symm
      have hdv' : dv' = dist := by
        have h : (some dist : Option Nat) = some dv' := by
          simpa [SC.n, SC.closed, STerm.eval, Term.eval] using hdistCol
        exact (Option.some.inj h).symm
      subst dv
      subst dv'
      have hrowEval : Term.eval codeBody fuel row rho = some rv := by
        simpa [SC.closed, STerm.eval] using hrow
      have hcolEval : Term.eval codeBody fuel col rho = some cv := by
        simpa [SC.closed, STerm.eval] using hcol
      have hlt : dist * rv + cv < dist * dist :=
        NatArithmetic.gridIdxLeft_lt_square hrowLt hcolLt'
      simp [SFormula.witnessLt, SFormula.eval, STerm.eval, Term.eval, SC.closed, SC.b,
        SC.n, NatArithmetic.gridIdxLeft, hrowEval, hcolEval, hlt]
  | gridIdxLeftDivEq dist row col rowLt colLt ihRow ihCol =>
      intro hdef hctx
      rcases hdef with ⟨hRowDef, hColDef⟩
      have hRow := ihRow hRowDef hctx
      have hCol := ihCol hColDef hctx
      rcases witnessLt_eval_true hRow with ⟨rv, dv, hrow, hdistRow, _hrowLt⟩
      rcases witnessLt_eval_true hCol with ⟨cv, dv', hcol, hdistCol, hcolLt'⟩
      have hdv : dv = dist := by
        have h : (some dist : Option Nat) = some dv := by
          simpa [SC.n, SC.closed, STerm.eval, Term.eval] using hdistRow
        exact (Option.some.inj h).symm
      have hdv' : dv' = dist := by
        have h : (some dist : Option Nat) = some dv' := by
          simpa [SC.n, SC.closed, STerm.eval, Term.eval] using hdistCol
        exact (Option.some.inj h).symm
      subst dv
      subst dv'
      have hrowEval : Term.eval codeBody fuel row rho = some rv := by
        simpa [SC.closed, STerm.eval] using hrow
      have hcolEval : Term.eval codeBody fuel col rho = some cv := by
        simpa [SC.closed, STerm.eval] using hcol
      have hdiv : (dist * rv + cv) / dist = rv :=
        NatArithmetic.gridIdxLeft_div hcolLt'
      simp [SFormula.eval, STerm.eval, Term.eval, SC.closed, NatArithmetic.rowOf,
        NatArithmetic.gridIdxLeft, hrowEval, hcolEval, hdiv]
  | gridIdxLeftModEq dist row col rowLt colLt ihRow ihCol =>
      intro hdef hctx
      rcases hdef with ⟨hRowDef, hColDef⟩
      have hRow := ihRow hRowDef hctx
      have hCol := ihCol hColDef hctx
      rcases witnessLt_eval_true hRow with ⟨rv, dv, hrow, hdistRow, _hrowLt⟩
      rcases witnessLt_eval_true hCol with ⟨cv, dv', hcol, hdistCol, hcolLt'⟩
      have hdv : dv = dist := by
        have h : (some dist : Option Nat) = some dv := by
          simpa [SC.n, SC.closed, STerm.eval, Term.eval] using hdistRow
        exact (Option.some.inj h).symm
      have hdv' : dv' = dist := by
        have h : (some dist : Option Nat) = some dv' := by
          simpa [SC.n, SC.closed, STerm.eval, Term.eval] using hdistCol
        exact (Option.some.inj h).symm
      subst dv
      subst dv'
      have hrowEval : Term.eval codeBody fuel row rho = some rv := by
        simpa [SC.closed, STerm.eval] using hrow
      have hcolEval : Term.eval codeBody fuel col rho = some cv := by
        simpa [SC.closed, STerm.eval] using hcol
      have hmod : (dist * rv + cv) % dist = cv :=
        NatArithmetic.gridIdxLeft_mod hcolLt'
      simp [SFormula.eval, STerm.eval, Term.eval, SC.closed, NatArithmetic.colOf,
        NatArithmetic.gridIdxLeft, hrowEval, hcolEval, hmod]
  | gridIdxLeftDivModEqOfRow dist row q qLt rowEq ihQ ihRowEq =>
      intro hdef hctx
      rcases hdef with ⟨hQDef, hRowEqDef⟩
      have hQ := ihQ hQDef hctx
      have hRowEq := ihRowEq hRowEqDef hctx
      rcases witnessLt_eval_true hQ with ⟨qv, bound, hq, hbound, hqLt⟩
      have hboundEq : bound = dist * dist := by
        have h : (some (dist * dist) : Option Nat) = some bound := by
          simpa [SC.n, SC.closed, STerm.eval, Term.eval] using hbound
        exact (Option.some.inj h).symm
      subst bound
      have hqEval : Term.eval codeBody fuel q rho = some qv := by
        simpa [SC.closed, STerm.eval] using hq
      simp [SFormula.eval, STerm.eval, Term.eval, SC.closed, SC.b,
        NatArithmetic.rowOf] at hRowEq
      cases hrowEval : Term.eval codeBody fuel row rho with
      | none =>
          simp [hqEval, hrowEval] at hRowEq
      | some rv =>
          simp [hqEval, hrowEval] at hRowEq
          cases hdec : decide (qv / dist = rv) with
          | false =>
              have hdecTrue : decide (qv / dist = rv) = true := decide_eq_true hRowEq
              simp [hdec] at hdecTrue
          | true =>
              have hrow : qv / dist = rv := of_decide_eq_true hdec
              have hidx : dist * rv + qv % dist = qv := by
                rw [← hrow]
                simpa [Nat.mul_comm] using Nat.div_add_mod qv dist
              simp [SFormula.eval, STerm.eval, Term.eval, SC.closed,
                NatArithmetic.gridIdxLeft, NatArithmetic.colOf, hqEval, hrowEval, hidx]
  | gridIdxLeftDivModEqOfCol dist col q qLt colEq ihQ ihColEq =>
      intro hdef hctx
      rcases hdef with ⟨hQDef, hColEqDef⟩
      have hQ := ihQ hQDef hctx
      have hColEq := ihColEq hColEqDef hctx
      rcases witnessLt_eval_true hQ with ⟨qv, bound, hq, hbound, hqLt⟩
      have hboundEq : bound = dist * dist := by
        have h : (some (dist * dist) : Option Nat) = some bound := by
          simpa [SC.n, SC.closed, STerm.eval, Term.eval] using hbound
        exact (Option.some.inj h).symm
      subst bound
      have hqEval : Term.eval codeBody fuel q rho = some qv := by
        simpa [SC.closed, STerm.eval] using hq
      simp [SFormula.eval, STerm.eval, Term.eval, SC.closed, SC.b,
        NatArithmetic.colOf] at hColEq
      cases hcolEval : Term.eval codeBody fuel col rho with
      | none =>
          simp [hqEval, hcolEval] at hColEq
      | some cv =>
          simp [hqEval, hcolEval] at hColEq
          cases hdec : decide (qv % dist = cv) with
          | false =>
              have hdecTrue : decide (qv % dist = cv) = true := decide_eq_true hColEq
              simp [hdec] at hdecTrue
          | true =>
              have hcol : qv % dist = cv := of_decide_eq_true hdec
              have hidx : dist * (qv / dist) + cv = qv := by
                rw [← hcol]
                simpa [Nat.mul_comm] using Nat.div_add_mod qv dist
              simp [SFormula.eval, STerm.eval, Term.eval, SC.closed,
                NatArithmetic.gridIdxLeft, NatArithmetic.rowOf, hqEval, hcolEval, hidx]
  | ltOfLtLtClosedPred limit x y xy ylimit ihXY ihYLimit =>
      intro hdef hctx
      have hXY := ihXY hdef.left hctx
      have hYLimit := ihYLimit hdef.right hctx
      rcases witnessLt_eval_true hXY with ⟨xv, yv, hx, hy, hxy⟩
      rcases witnessLt_eval_true hYLimit with ⟨yv', limit', hy', hlimit, hyLimit⟩
      have hlimitEq : limit' = limit := by
        have h : limit = limit' := by
          simpa [SC.n, STerm.eval, Term.eval] using hlimit
        exact h.symm
      subst limit'
      have hyEq : yv = yv' := by
        rw [hy] at hy'
        exact Option.some.inj hy'
      have hyLimit' : yv < limit := by
        exact hyEq ▸ hyLimit
      subst yv'
      have hxLimit : xv < limit - 1 := by
        apply Nat.lt_sub_iff_add_lt.mpr
        exact Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hxy) hyLimit'
      simp [SFormula.witnessLt, SFormula.eval, STerm.eval, Term.eval, SC.n, SC.b,
        hx, hxLimit]
  | eqStabRefl n A =>
      intro hdef _
      rcases hdef with ⟨b, hEval⟩
      simp [SFormula.eval] at hEval ⊢
      cases hn : n.eval codeBody fuel rho E with
      | none =>
          simp [hn] at hEval
      | some nv =>
          cases hA : A.eval codeBody fuel rho E with
          | none =>
              simp [hn, hA] at hEval
          | some Av =>
              cases hEq : stabEqUpTo nv Av Av with
              | none =>
                  simp [hn, hA, hEq] at hEval
              | some eqv =>
                  have heqv : eqv = true := stabEqUpTo_self_of_defined hEq
                  simp [hEq, heqv]
  | eqStabSymm n A B child ih =>
      intro hdef hctx
      have hChild := ih hdef hctx
      simp [SFormula.eval] at hChild ⊢
      cases hn : n.eval codeBody fuel rho E with
      | none =>
          simp [hn] at hChild
      | some nv =>
          cases hA : A.eval codeBody fuel rho E with
          | none =>
              simp [hn, hA] at hChild
          | some Av =>
              cases hB : B.eval codeBody fuel rho E with
              | none =>
                  simp [hn, hA, hB] at hChild
              | some Bv =>
                  simp [hn, hA, hB] at hChild ⊢
                  exact stabEqUpTo_symm_true hChild
  | eqStabTrans n A B C left right ihLeft ihRight =>
      intro hdef hctx
      have hLeft := ihLeft hdef.left hctx
      have hRight := ihRight hdef.right hctx
      simp [SFormula.eval] at hLeft hRight ⊢
      cases hn : n.eval codeBody fuel rho E with
      | none =>
          simp [hn] at hLeft
      | some nv =>
          cases hA : A.eval codeBody fuel rho E with
          | none =>
              simp [hn, hA] at hLeft
          | some Av =>
              cases hB : B.eval codeBody fuel rho E with
              | none =>
                  simp [hn, hA, hB] at hLeft
              | some Bv =>
                  cases hC : C.eval codeBody fuel rho E with
                  | none =>
                      simp [hn, hB, hC] at hRight
                  | some Cv =>
                      simp [hn, hA, hB] at hLeft
                      simp [hn, hB, hC] at hRight
                      simp
                      exact stabEqUpTo_trans_true hLeft hRight
  | eqPauliSymm a b child ih =>
      intro hdef hctx
      have hChild := ih hdef hctx
      simp only [SFormula.eval, bind, Option.bind] at hChild ⊢
      cases ha : a.eval codeBody fuel rho E with
      | none => simp [ha] at hChild
      | some av =>
          cases hb : b.eval codeBody fuel rho E with
          | none => simp [ha, hb] at hChild
          | some bv =>
              simp only [ha, hb] at hChild ⊢
              have e : av = bv := by simpa using hChild
              subst e
              simp
  | eqPauliTrans a b c left right ihLeft ihRight =>
      intro hdef hctx
      have hLeft := ihLeft hdef.left hctx
      have hRight := ihRight hdef.right hctx
      simp only [SFormula.eval, bind, Option.bind] at hLeft hRight ⊢
      cases ha : a.eval codeBody fuel rho E with
      | none => simp [ha] at hLeft
      | some av =>
          cases hb : b.eval codeBody fuel rho E with
          | none => simp [ha, hb] at hLeft
          | some bv =>
              cases hc : c.eval codeBody fuel rho E with
              | none => simp [hb, hc] at hRight
              | some cv =>
                  simp only [ha, hb] at hLeft
                  simp only [hb, hc] at hRight
                  have e1 : av = bv := by simpa using hLeft
                  have e2 : bv = cv := by simpa using hRight
                  subst e1; subst e2; simp
  | eqNatBoolTrue a b child ih =>
      intro hdef hctx
      have hChild := ih hdef hctx
      simp only [SFormula.eval, SC.closed, SC.b, STerm.eval, Term.eval,
        bind, Option.bind] at hChild ⊢
      cases ha : Term.eval codeBody fuel a rho with
      | none => simp [ha] at hChild
      | some av =>
          cases hb : Term.eval codeBody fuel b rho with
          | none => simp [ha, hb] at hChild
          | some bv =>
              simp only [ha, hb] at hChild ⊢
              have e : av = bv := by simpa using hChild
              subst e
              simp
  | eqBoolFalseNotTrue b child ih =>
      intro hdef hctx
      have hChild := ih hdef hctx
      cases hb : STerm.eval codeBody fuel b rho E with
      | none =>
          simp [SFormula.eval, hb, SC.b, STerm.eval, Term.eval] at hChild
      | some bv =>
          have e : bv = false := by
            simp only [SFormula.eval, hb, SC.b, STerm.eval, Term.eval,
              bind, Option.bind, Option.some.injEq, decide_eq_true_eq] at hChild
            exact hChild
          subst e
          simp [SFormula.eval, hb, SC.b, STerm.eval, Term.eval]
  | eqBoolTrueNotFalse b child ih =>
      intro hdef hctx
      have hChild := ih hdef hctx
      cases hb : STerm.eval codeBody fuel b rho E with
      | none =>
          simp [SFormula.eval, hb, SC.b, STerm.eval, Term.eval] at hChild
      | some bv =>
          have e : bv = true := by
            simp only [SFormula.eval, hb, SC.b, STerm.eval, Term.eval,
              bind, Option.bind, Option.some.injEq, decide_eq_true_eq] at hChild
            exact hChild
          subst e
          simp [SFormula.eval, hb, SC.b, STerm.eval, Term.eval]
  | eqStabMulCongr n A A' B B' left right ihLeft ihRight =>
      intro hdef hctx
      have hLeft := ihLeft hdef.left hctx
      have hRight := ihRight hdef.right hctx
      simp [SFormula.eval] at hLeft hRight ⊢
      cases hn : n.eval codeBody fuel rho E with
      | none =>
          simp [hn] at hLeft
      | some nv =>
          cases hA : A.eval codeBody fuel rho E with
          | none =>
              simp [hn, hA] at hLeft
          | some Av =>
              cases hA' : A'.eval codeBody fuel rho E with
              | none =>
                  simp [hn, hA, hA'] at hLeft
              | some A'v =>
                  cases hB : B.eval codeBody fuel rho E with
                  | none =>
                      simp [hn, hB] at hRight
                  | some Bv =>
                      cases hB' : B'.eval codeBody fuel rho E with
                      | none =>
                          simp [hn, hB, hB'] at hRight
                      | some B'v =>
                          simp [hn, hA, hA'] at hLeft
                          simp [hn, hB, hB'] at hRight
                          have hMulLeft := eval_stabMul_of_eval (A := A) (B := B) hA hB
                          have hMulRight :=
                            eval_stabMul_of_eval (A := A') (B := B') hA' hB'
                          simp [hMulLeft, hMulRight]
                          exact stabEqUpTo_mul_congr_true hLeft hRight
  | eqStabMulAssoc n A B C hA hB hC ihA ihB ihC =>
      intro hdef hctx
      rcases hdef with ⟨hAdef, hBdef, hCdef⟩
      have hAself := ihA hAdef hctx
      have hBself := ihB hBdef hctx
      have hCself := ihC hCdef hctx
      simp [SFormula.eval] at hAself hBself hCself ⊢
      cases hn : n.eval codeBody fuel rho E with
      | none =>
          simp [hn] at hAself
      | some nv =>
          cases hAe : A.eval codeBody fuel rho E with
          | none =>
              simp [hn, hAe] at hAself
          | some Av =>
              cases hBe : B.eval codeBody fuel rho E with
              | none =>
                  simp [hn, hBe] at hBself
              | some Bv =>
                  cases hCe : C.eval codeBody fuel rho E with
                  | none =>
                      simp [hn, hCe] at hCself
                  | some Cv =>
                      simp [hn, hAe] at hAself
                      simp [hn, hBe] at hBself
                      simp [hn, hCe] at hCself
                      have hAB := eval_stabMul_of_eval (A := A) (B := B) hAe hBe
                      have hBC := eval_stabMul_of_eval (A := B) (B := C) hBe hCe
                      have hLeft :=
                        eval_stabMul_of_eval (A := SC.stabMul A B) (B := C) hAB hCe
                      have hRight :=
                        eval_stabMul_of_eval (A := A) (B := SC.stabMul B C) hAe hBC
                      have hBCself := stabEqUpTo_mul_congr_true hBself hCself
                      have hRightSelf := stabEqUpTo_mul_congr_true hAself hBCself
                      simpa [SFormula.eval, hn, hLeft, hRight, partialStabilizerMul_assoc]
                        using hRightSelf
  | eqStabMulComm n A B hA hB ihA ihB =>
      intro hdef hctx
      rcases hdef with ⟨hAdef, hBdef⟩
      have hAself := ihA hAdef hctx
      have hBself := ihB hBdef hctx
      simp [SFormula.eval] at hAself hBself ⊢
      cases hn : n.eval codeBody fuel rho E with
      | none =>
          simp [hn] at hAself
      | some nv =>
          cases hAe : A.eval codeBody fuel rho E with
          | none =>
              simp [hn, hAe] at hAself
          | some Av =>
              cases hBe : B.eval codeBody fuel rho E with
              | none =>
                  simp [hn, hBe] at hBself
              | some Bv =>
                  simp [hn, hAe] at hAself
                  simp [hn, hBe] at hBself
                  have hLeft := eval_stabMul_of_eval (A := A) (B := B) hAe hBe
                  have hRight := eval_stabMul_of_eval (A := B) (B := A) hBe hAe
                  have hBAself := stabEqUpTo_mul_congr_true hBself hAself
                  simpa [SFormula.eval, hn, hLeft, hRight, partialStabilizerMul_comm]
                    using hBAself
  | eqStabMulSelf n A child ih =>
      intro hdef hctx
      have hAself := ih hdef hctx
      simp [SFormula.eval] at hAself ⊢
      cases hn : n.eval codeBody fuel rho E with
      | none =>
          simp [hn] at hAself
      | some nv =>
          cases hAe : A.eval codeBody fuel rho E with
          | none =>
              simp [hn, hAe] at hAself
          | some Av =>
              simp [hn, hAe] at hAself
              have hMul := eval_stabMul_of_eval (A := A) (B := A) hAe hAe
              have hOne := eval_stabOne (codeBody := codeBody) (fuel := fuel) (rho := rho) (E := E)
              simp [SFormula.eval, hn, hMul, hOne]
              exact stabEqUpTo_complete fun q hq =>
                let ⟨p, hAv, _⟩ := stabEqUpTo_sound hAself q hq
                ⟨Pauli.I, by simp [partialStabilizerMul, hAv, Pauli.mul_self],
                  by simp [partialIdentityStabilizer]⟩
  | eqStabMulOneLeft n A child ih =>
      intro hdef hctx
      have hAself := ih hdef hctx
      simp [SFormula.eval] at hAself ⊢
      cases hn : n.eval codeBody fuel rho E with
      | none =>
          simp [hn] at hAself
      | some nv =>
          cases hAe : A.eval codeBody fuel rho E with
          | none =>
              simp [hn, hAe] at hAself
          | some Av =>
              simp [hn, hAe] at hAself
              have hOne := eval_stabOne (codeBody := codeBody) (fuel := fuel) (rho := rho) (E := E)
              have hMul := eval_stabMul_of_eval (A := SC.stabOne) (B := A) hOne hAe
              simp [SFormula.eval, hn, hMul]
              exact stabEqUpTo_complete fun q hq =>
                let ⟨p, hAv, _⟩ := stabEqUpTo_sound hAself q hq
                ⟨p, by
                  cases p <;> simp [partialStabilizerMul, partialIdentityStabilizer, hAv,
                    Pauli.mul],
                  hAv⟩
  | eqStabMulOneRight n A child ih =>
      intro hdef hctx
      have hAself := ih hdef hctx
      simp [SFormula.eval] at hAself ⊢
      cases hn : n.eval codeBody fuel rho E with
      | none =>
          simp [hn] at hAself
      | some nv =>
          cases hAe : A.eval codeBody fuel rho E with
          | none =>
              simp [hn, hAe] at hAself
          | some Av =>
              simp [hn, hAe] at hAself
              have hOne := eval_stabOne (codeBody := codeBody) (fuel := fuel) (rho := rho) (E := E)
              have hMul := eval_stabMul_of_eval (A := A) (B := SC.stabOne) hAe hOne
              simp [SFormula.eval, hn, hMul]
              exact stabEqUpTo_complete fun q hq =>
                let ⟨p, hAv, _⟩ := stabEqUpTo_sound hAself q hq
                ⟨p, by
                  cases p <;> simp [partialStabilizerMul, partialIdentityStabilizer, hAv,
                    Pauli.mul],
                  hAv⟩
  | eqStabFoldZero n body =>
      intro hdef _hctx
      apply eqStabUpTo_eval_of_eval_eq
      · have hFold :
            (SC.stabFold (SC.n 0) body).eval codeBody fuel rho E =
              some partialIdentityStabilizer := by
          simp [SC.stabFold, SC.n, STerm.eval, Term.eval, partialStabilizerFold]
        have hOne := eval_stabOne (codeBody := codeBody) (fuel := fuel) (rho := rho) (E := E)
        rw [hFold, hOne]
      · exact hdef
  | eqStabFoldSucc n bound body =>
      intro hdef _hctx
      cases hBound : Term.eval codeBody fuel bound rho with
      | none =>
          rcases hdef with ⟨b, hTarget⟩
          simp [SFormula.eval, SC.stabFold, SC.succClosed, STerm.eval, Term.eval, hBound]
            at hTarget
      | some bv =>
          let bodyFn : Nat -> PartialStabilizer := fun i =>
            match body.eval codeBody fuel (Env.cons i rho) E with
            | some row => row
            | none => fun _ => none
          have hLeft :
              (SC.stabFold (SC.succClosed bound) body).eval codeBody fuel rho E =
                some (partialStabilizerFold (bv + 1) bodyFn) := by
            simp [SC.stabFold, SC.succClosed, STerm.eval, Term.eval, hBound, bodyFn]
          have hRight :
              (SC.stabMul (SC.stabFold (SC.closed bound) body) (SC.applyNat bound body)).eval
                  codeBody fuel rho E =
                some (partialStabilizerMul (partialStabilizerFold bv bodyFn) (bodyFn bv)) := by
            have hFoldBase :
                (SC.stabFold (SC.closed bound) body).eval codeBody fuel rho E =
                  some (partialStabilizerFold bv bodyFn) := by
              simp [SC.stabFold, SC.closed, STerm.eval, Term.eval, hBound, bodyFn]
            have hAppBase :
                (SC.applyNat bound body).eval codeBody fuel rho E =
                  body.eval codeBody fuel (Env.cons bv rho) E := by
              simp [SC.applyNat, STerm.eval, hBound]
            simp [SC.stabMul, STerm.eval]
            funext q
            have hFoldWeak :
                (SC.stabFold (SC.closed bound) body).weaken.eval codeBody fuel
                    (Env.cons q rho) E =
                  some (partialStabilizerFold bv bodyFn) := by
              exact (STerm.eval_lift_of_env (SC.stabFold (SC.closed bound) body)
                (EnvLifted.underTop rho q) codeBody fuel E).trans hFoldBase
            have hAppWeak :
                (SC.applyNat bound body).weaken.eval codeBody fuel (Env.cons q rho) E =
                  body.eval codeBody fuel (Env.cons bv rho) E := by
              exact (STerm.eval_lift_of_env (SC.applyNat bound body)
                (EnvLifted.underTop rho q) codeBody fuel E).trans hAppBase
            have hQ :
                SC.qVar.eval codeBody fuel (Env.cons q rho) E = some q := by
              simp [SC.qVar, STerm.eval, Term.eval, Env.cons]
              rfl
            simp [hFoldWeak, hAppWeak, hQ, partialStabilizerMul]
            cases hBody : body.eval codeBody fuel (Env.cons bv rho) E with
            | none =>
                simp [hBody, bodyFn]
            | some row =>
                simp [hBody, bodyFn]
          apply eqStabUpTo_eval_of_eval_eq
          · rw [hLeft, hRight]
            simp [partialStabilizerFold]
          · exact hdef
  | commutesSymm n A B child ih =>
      intro hdef hctx
      have hChild := ih hdef hctx
      simp [SFormula.eval] at hChild ⊢
      cases hn : n.eval codeBody fuel rho E with
      | none =>
          simp [hn] at hChild
      | some nv =>
          cases hA : A.eval codeBody fuel rho E with
          | none =>
              simp [hn, hA] at hChild
          | some Av =>
              cases hB : B.eval codeBody fuel rho E with
              | none =>
                  simp [hn, hA, hB] at hChild
              | some Bv =>
                  simp [hn, hA, hB] at hChild ⊢
                  rw [parityUpTo_symm (A := Bv) (B := Av)]
                  exact hChild
  | noncommutesSymm n A B child ih =>
      intro hdef hctx
      have hChildNot := ih hdef hctx
      have hChild := not_eval_true_false hChildNot
      simp [SFormula.eval] at hChild ⊢
      cases hn : n.eval codeBody fuel rho E with
      | none =>
          simp [hn] at hChild
      | some nv =>
          cases hA : A.eval codeBody fuel rho E with
          | none =>
              simp [hn, hA] at hChild
          | some Av =>
              cases hB : B.eval codeBody fuel rho E with
              | none =>
                  simp [hn, hA, hB] at hChild
              | some Bv =>
                  simp [hn, hA, hB] at hChild
                  have hAB : parityUpTo nv Av Bv = some true := by
                    cases hParity : parityUpTo nv Av Bv with
                    | none =>
                        simp [hParity] at hChild
                    | some parity =>
                        cases parity <;> simp [hParity] at hChild ⊢
                  have hBA : parityUpTo nv Bv Av = some true := by
                    rw [parityUpTo_symm (A := Bv) (B := Av)]
                    exact hAB
                  simp [SFormula.eval, hn, hB, hA, hBA]
  | commutesOfEqLeft n A B C eqD commD ihEq ihComm =>
      intro hdef hctx
      have hEq := ihEq hdef.left hctx
      have hComm := ihComm hdef.right hctx
      simp [SFormula.eval] at hEq hComm ⊢
      cases hn : n.eval codeBody fuel rho E with
      | none =>
          simp [hn] at hEq
      | some nv =>
          cases hA : A.eval codeBody fuel rho E with
          | none =>
              simp [hn, hA] at hEq
          | some Av =>
              cases hB : B.eval codeBody fuel rho E with
              | none =>
                  simp [hn, hA, hB] at hEq
              | some Bv =>
                  cases hC : C.eval codeBody fuel rho E with
                  | none =>
                      simp [hn, hA, hC] at hComm
                  | some Cv =>
                      simp [hn, hA, hB] at hEq
                      simp [hn, hA, hC] at hComm
                      simp
                      rw [← parityUpTo_congr_left (C := Cv) hEq]
                      exact hComm
  | commutesOfEqRight n A B C eqD commD ihEq ihComm =>
      intro hdef hctx
      have hEq := ihEq hdef.left hctx
      have hComm := ihComm hdef.right hctx
      simp [SFormula.eval] at hEq hComm ⊢
      cases hn : n.eval codeBody fuel rho E with
      | none =>
          simp [hn] at hEq
      | some nv =>
          cases hA : A.eval codeBody fuel rho E with
          | none =>
              simp [hn, hA] at hComm
          | some Av =>
              cases hB : B.eval codeBody fuel rho E with
              | none =>
                  simp [hn, hA, hB] at hComm
              | some Bv =>
                  cases hC : C.eval codeBody fuel rho E with
                  | none =>
                      simp [hn, hB, hC] at hEq
                  | some Cv =>
                      simp [hn, hB, hC] at hEq
                      simp [hn, hA, hB] at hComm
                      simp
                      rw [← parityUpTo_congr_right (A := Av) hEq]
                      exact hComm
  | noncommutesOfEqLeft n A B C eqD noncommD ihEq ihNoncomm =>
      intro hdef hctx
      have hEq := ihEq hdef.left hctx
      have hNoncomm := not_eval_true_false (ihNoncomm hdef.right hctx)
      simp [SFormula.eval] at hEq hNoncomm ⊢
      cases hn : n.eval codeBody fuel rho E with
      | none =>
          simp [hn] at hEq
      | some nv =>
          cases hA : A.eval codeBody fuel rho E with
          | none =>
              simp [hn, hA] at hEq
          | some Av =>
              cases hB : B.eval codeBody fuel rho E with
              | none =>
                  simp [hn, hA, hB] at hEq
              | some Bv =>
                  cases hC : C.eval codeBody fuel rho E with
                  | none =>
                      simp [hn, hA, hC] at hNoncomm
                  | some Cv =>
                      simp [hn, hA, hB] at hEq
                      simp [hn, hA, hC] at hNoncomm
                      have hAC : parityUpTo nv Av Cv = some true := by
                        cases hParity : parityUpTo nv Av Cv with
                        | none =>
                            simp [hParity] at hNoncomm
                        | some parity =>
                            cases parity <;> simp [hParity] at hNoncomm ⊢
                      have hBC : parityUpTo nv Bv Cv = some true := by
                        rw [← parityUpTo_congr_left (C := Cv) hEq]
                        exact hAC
                      simp [SFormula.eval, hn, hB, hC, hBC]
  | noncommutesOfEqRight n A B C eqD noncommD ihEq ihNoncomm =>
      intro hdef hctx
      have hEq := ihEq hdef.left hctx
      have hNoncomm := not_eval_true_false (ihNoncomm hdef.right hctx)
      simp [SFormula.eval] at hEq hNoncomm ⊢
      cases hn : n.eval codeBody fuel rho E with
      | none =>
          simp [hn] at hEq
      | some nv =>
          cases hA : A.eval codeBody fuel rho E with
          | none =>
              simp [hn, hA] at hNoncomm
          | some Av =>
              cases hB : B.eval codeBody fuel rho E with
              | none =>
                  simp [hn, hA, hB] at hNoncomm
              | some Bv =>
                  cases hC : C.eval codeBody fuel rho E with
                  | none =>
                      simp [hn, hB, hC] at hEq
                  | some Cv =>
                      simp [hn, hB, hC] at hEq
                      simp [hn, hA, hB] at hNoncomm
                      have hAB : parityUpTo nv Av Bv = some true := by
                        cases hParity : parityUpTo nv Av Bv with
                        | none =>
                            simp [hParity] at hNoncomm
                        | some parity =>
                            cases parity <;> simp [hParity] at hNoncomm ⊢
                      have hAC : parityUpTo nv Av Cv = some true := by
                        rw [← parityUpTo_congr_right (A := Av) hEq]
                        exact hAB
                      simp [SFormula.eval, hn, hA, hC, hAC]
  | commutesStabMulLeft n A B C left right ihLeft ihRight =>
      intro hdef hctx
      have hLeft := ihLeft hdef.left hctx
      have hRight := ihRight hdef.right hctx
      simp [SFormula.eval] at hLeft hRight ⊢
      cases hn : n.eval codeBody fuel rho E with
      | none =>
          simp [hn] at hLeft
      | some nv =>
          cases hA : A.eval codeBody fuel rho E with
          | none =>
              simp [hn, hA] at hLeft
          | some Av =>
              cases hB : B.eval codeBody fuel rho E with
              | none =>
                  simp [hn, hB] at hRight
              | some Bv =>
                  cases hC : C.eval codeBody fuel rho E with
                  | none =>
                      simp [hn, hA, hC] at hLeft
                  | some Cv =>
                      simp [hn, hA, hC] at hLeft
                      simp [hn, hB, hC] at hRight
                      have hAC : parityUpTo nv Av Cv = some false := by
                        cases hParity : parityUpTo nv Av Cv with
                        | none =>
                            simp [hParity] at hLeft
                        | some parity =>
                            cases parity <;> simp [hParity] at hLeft ⊢
                      have hBC : parityUpTo nv Bv Cv = some false := by
                        cases hParity : parityUpTo nv Bv Cv with
                        | none =>
                            simp [hParity] at hRight
                        | some parity =>
                            cases parity <;> simp [hParity] at hRight ⊢
                      have hMul := eval_stabMul_of_eval (A := A) (B := B) hA hB
                      simp [hMul, parityUpTo_mul_left, hAC, hBC]
  | noncommutesStabMulLeft n A B C left right ihLeft ihRight =>
      intro hdef hctx
      have hLeft := ihLeft hdef.left hctx
      have hRightNot := ihRight hdef.right hctx
      have hRight := not_eval_true_false hRightNot
      simp [SFormula.eval] at hLeft hRight ⊢
      cases hn : n.eval codeBody fuel rho E with
      | none =>
          simp [hn] at hLeft
      | some nv =>
          cases hA : A.eval codeBody fuel rho E with
          | none =>
              simp [hn, hA] at hLeft
          | some Av =>
              cases hB : B.eval codeBody fuel rho E with
              | none =>
                  simp [hn, hB] at hRight
              | some Bv =>
                  cases hC : C.eval codeBody fuel rho E with
                  | none =>
                      simp [hn, hA, hC] at hLeft
                  | some Cv =>
                      simp [hn, hA, hC] at hLeft
                      simp [hn, hB, hC] at hRight
                      have hAC : parityUpTo nv Av Cv = some false := by
                        cases hParity : parityUpTo nv Av Cv with
                        | none =>
                            simp [hParity] at hLeft
                        | some parity =>
                            cases parity <;> simp [hParity] at hLeft ⊢
                      have hBC : parityUpTo nv Bv Cv = some true := by
                        cases hParity : parityUpTo nv Bv Cv with
                        | none =>
                            simp [hParity] at hRight
                        | some parity =>
                            cases parity <;> simp [hParity] at hRight ⊢
                      have hMul := eval_stabMul_of_eval (A := A) (B := B) hA hB
                      simp [SFormula.eval, hn, hMul, hC, parityUpTo_mul_left, hAC, hBC]
  | noncommutesStabMulRight n A B C left right ihLeft ihRight =>
      intro hdef hctx
      have hLeftNot := ihLeft hdef.left hctx
      have hLeft := not_eval_true_false hLeftNot
      have hRight := ihRight hdef.right hctx
      simp [SFormula.eval] at hLeft hRight ⊢
      cases hn : n.eval codeBody fuel rho E with
      | none =>
          simp [hn] at hLeft
      | some nv =>
          cases hA : A.eval codeBody fuel rho E with
          | none =>
              simp [hn, hA] at hLeft
          | some Av =>
              cases hB : B.eval codeBody fuel rho E with
              | none =>
                  simp [hn, hB] at hRight
              | some Bv =>
                  cases hC : C.eval codeBody fuel rho E with
                  | none =>
                      simp [hn, hA, hC] at hLeft
                  | some Cv =>
                      simp [hn, hA, hC] at hLeft
                      simp [hn, hB, hC] at hRight
                      have hAC : parityUpTo nv Av Cv = some true := by
                        cases hParity : parityUpTo nv Av Cv with
                        | none =>
                            simp [hParity] at hLeft
                        | some parity =>
                            cases parity <;> simp [hParity] at hLeft ⊢
                      have hBC : parityUpTo nv Bv Cv = some false := by
                        cases hParity : parityUpTo nv Bv Cv with
                        | none =>
                            simp [hParity] at hRight
                        | some parity =>
                            cases parity <;> simp [hParity] at hRight ⊢
                      have hMul := eval_stabMul_of_eval (A := A) (B := B) hA hB
                      simp [SFormula.eval, hn, hMul, hC, parityUpTo_mul_left, hAC, hBC]
  | commutesStabFoldLeft n bound body C child ih =>
      intro hdef hctx
      rcases hdef with ⟨hChildDef, hTargetDefined⟩
      have hAll := ih hChildDef hctx
      simp [SFormula.eval] at hAll ⊢
      cases hN : n.eval codeBody fuel rho E with
      | none =>
          rcases hTargetDefined with ⟨_, hTarget⟩
          simp [SFormula.eval, hN] at hTarget
      | some nv =>
          cases hBound : bound.eval codeBody fuel rho E with
          | none =>
              rcases hTargetDefined with ⟨_, hTarget⟩
              simp [SFormula.eval, SC.stabFold, STerm.eval, hN, hBound] at hTarget
          | some bv =>
              cases hC : C.eval codeBody fuel rho E with
              | none =>
                  rcases hTargetDefined with ⟨_, hTarget⟩
                  simp [SFormula.eval, hN, hBound, hC] at hTarget
              | some Cv =>
                  simp [hBound] at hAll
                  let bodyFn : Nat -> PartialStabilizer := fun i =>
                    match body.eval codeBody fuel (Env.cons i rho) E with
                    | some row => row
                    | none => fun _ => none
                  have hFold :
                      (SC.stabFold bound body).eval codeBody fuel rho E =
                        some (partialStabilizerFold bv bodyFn) := by
                    simp [SC.stabFold, STerm.eval, hBound, bodyFn]
                  rcases hTargetDefined with ⟨targetValue, hTarget⟩
                  simp [SFormula.eval, hN, hFold, hC] at hTarget
                  have hcomm :
                      forall i, i < bv -> parityUpTo nv (bodyFn i) Cv = some false := by
                    intro i hi
                    have hBody := allNatLt_sound hAll i hi
                    have hNweaken :
                        n.weaken.eval codeBody fuel (Env.cons i rho) E = some nv := by
                      simpa [STerm.weaken] using
                        STerm.eval_lift_of_env n (EnvLifted.underTop rho i)
                          codeBody fuel E ▸ hN
                    have hCweaken :
                        C.weaken.eval codeBody fuel (Env.cons i rho) E = some Cv := by
                      simpa [STerm.weaken] using
                        STerm.eval_lift_of_env C (EnvLifted.underTop rho i)
                          codeBody fuel E ▸ hC
                    simp [SFormula.eval, hNweaken, hCweaken, bodyFn] at hBody
                    cases hBodyEval : body.eval codeBody fuel (Env.cons i rho) E with
                    | none =>
                        simp [hBodyEval] at hBody
                    | some row =>
                        simp [hBodyEval] at hBody
                        cases hParity : parityUpTo nv row Cv with
                        | none =>
                            simp [hParity] at hBody
                        | some parity =>
                            cases parity
                            · simpa [bodyFn, hBodyEval] using hParity
                            · simp [hParity] at hBody
                  cases hFoldParity :
                      parityUpTo nv (partialStabilizerFold bv bodyFn) Cv with
                  | none =>
                      simp [hFoldParity] at hTarget
                  | some parity =>
                      have hParityFalse : parity = false :=
                        parityUpTo_fold_left_defined hcomm hFoldParity
                      simp [SFormula.eval, hN, hFold, hC, hFoldParity, hParityFalse]
  | commutesOfPointwise n A B child ih =>
      intro hdef hctx
      rcases hdef with ⟨hChildDef, hTargetDefined⟩
      have hPoint := ih hChildDef hctx
      rcases hTargetDefined with ⟨_, hTarget⟩
      simp [SFormula.eval] at hTarget ⊢
      cases hN : n.eval codeBody fuel rho E with
      | none =>
          simp [hN] at hTarget
      | some nv =>
          cases hA : A.eval codeBody fuel rho E with
          | none =>
              simp [hN, hA] at hTarget
          | some Av =>
              cases hB : B.eval codeBody fuel rho E with
              | none =>
                  simp [hN, hA, hB] at hTarget
              | some Bv =>
                  have hParity :
                      parityUpTo nv Av Bv = some false :=
                    parityUpTo_false_of_pointwiseCommutes hPoint hN hA hB
                  simp [hN, hA, hB, hParity]
  | noncommutesOfSingleAnti n A B q0 ltD antiD restD ihLt ihAnti ihRest =>
      intro hdef hctx
      have hLt := ihLt hdef.left hctx
      have hAnti := ihAnti hdef.right.left hctx
      have hRest := ihRest hdef.right.right hctx
      -- Premise 1 supplies `q0v < nv`, with `q0` and `n` defined.
      rcases witnessLt_eval_true hLt with ⟨q0v, nv, hq0, hN, hq0Lt⟩
      -- Premise 2 forces `A` and `B` to be defined.
      have hABdef : (∃ Av, A.eval codeBody fuel rho E = some Av) ∧
          (∃ Bv, B.eval codeBody fuel rho E = some Bv) := by
        have hAnti' := hAnti
        simp [SFormula.eval, STerm.eval, SC.b, Term.eval] at hAnti'
        cases hA : A.eval codeBody fuel rho E with
        | none => simp [hA] at hAnti'
        | some Av =>
            cases hB : B.eval codeBody fuel rho E with
            | none => simp [hA, hB] at hAnti'
            | some Bv => exact ⟨⟨Av, rfl⟩, ⟨Bv, rfl⟩⟩
      obtain ⟨⟨Av, hA⟩, ⟨Bv, hB⟩⟩ := hABdef
      -- Premise 3 supplies the per-slot imp body via `allNatLt_sound`.
      have hImp : ∀ q, q < nv →
          SFormula.eval codeBody fuel
            (.imp (.not (.eqNat SFormula.boundNat q0.weaken))
              (SFormula.localCommutesAt A.weaken B.weaken SFormula.boundNat))
            (Env.cons q rho) E = some true := by
        have hRest' := hRest
        simp [SFormula.eval, hN] at hRest'
        exact fun q hq => allNatLt_sound hRest' q hq
      have hParity : parityUpTo nv Av Bv = some true :=
        parityUpTo_true_of_singleAntiPremises hq0Lt hq0 hA hB hAnti hImp
      simp [SFormula.eval, hN, hA, hB, hParity]
  | commutesOfTwoAnti n A B q0 q1 lt0D lt1D neD anti0D anti1D restD
      ihLt0 ihLt1 ihNe ihAnti0 ihAnti1 ihRest =>
      intro hdef hctx
      have hLt0 := ihLt0 hdef.left hctx
      have hLt1 := ihLt1 hdef.right.left hctx
      have hNe := ihNe hdef.right.right.left hctx
      have hAnti0 := ihAnti0 hdef.right.right.right.left hctx
      have hAnti1 := ihAnti1 hdef.right.right.right.right.left hctx
      have hRest := ihRest hdef.right.right.right.right.right hctx
      -- Premise 1/2 supply `q0v < nv`, `q1v < nv`, with `q0`, `q1`, `n` defined.
      rcases witnessLt_eval_true hLt0 with ⟨q0v, nv, hq0, hN, hq0Lt⟩
      rcases witnessLt_eval_true hLt1 with ⟨q1v, nv', hq1, hN', hq1Lt⟩
      -- The bound `n` is the same term, so its two evaluated values agree.
      have hNNeq : nv = nv' := by
        have : some nv = some nv' := by rw [← hN, ← hN']
        exact Option.some.inj this
      subst hNNeq
      -- Premise 3 supplies `q0v ≠ q1v` from `not (eqNat q0 q1) = some true`.
      have hneVal : q0v ≠ q1v := by
        have hNe' := hNe
        simp [SFormula.eval, hq0, hq1] at hNe'
        exact hNe'
      -- Premises 4/5 force `A` and `B` to be defined.
      have hABdef : (∃ Av, A.eval codeBody fuel rho E = some Av) ∧
          (∃ Bv, B.eval codeBody fuel rho E = some Bv) := by
        have hAnti0' := hAnti0
        simp [SFormula.eval, STerm.eval, SC.b, Term.eval] at hAnti0'
        cases hA : A.eval codeBody fuel rho E with
        | none => simp [hA] at hAnti0'
        | some Av =>
            cases hB : B.eval codeBody fuel rho E with
            | none => simp [hA, hB] at hAnti0'
            | some Bv => exact ⟨⟨Av, rfl⟩, ⟨Bv, rfl⟩⟩
      obtain ⟨⟨Av, hA⟩, ⟨Bv, hB⟩⟩ := hABdef
      -- Premise 6 supplies the per-slot doubly-guarded imp body.
      have hImp : ∀ q, q < nv →
          SFormula.eval codeBody fuel
            (.imp (.not (.eqNat SFormula.boundNat q0.weaken))
              (.imp (.not (.eqNat SFormula.boundNat q1.weaken))
                (SFormula.localCommutesAt A.weaken B.weaken SFormula.boundNat)))
            (Env.cons q rho) E = some true := by
        have hRest' := hRest
        simp [SFormula.eval, hN] at hRest'
        exact fun q hq => allNatLt_sound hRest' q hq
      have hParity : parityUpTo nv Av Bv = some false :=
        parityUpTo_false_of_twoAntiPremises hq0Lt hq1Lt hneVal hq0 hq1 hA hB
          hAnti0 hAnti1 hImp
      simp [SFormula.eval, hN, hA, hB, hParity]
  | stabAtClosedIteLamEqThen cond thenP elseP q hq child ih =>
      intro hdef hctx
      rcases hdef with ⟨hChildDef, hTargetDefined⟩
      have hCondTrue := ih hChildDef hctx
      obtain ⟨qv, hqv⟩ := hq.eval_total codeBody fuel rho
      have hqAll := hq.eval_all_fuels hqv
      have hCondSub :
          Term.eval codeBody fuel (Term.instantiateTopNat q cond) rho =
            Term.eval codeBody fuel cond (Env.cons qv rho) :=
        Term.eval_instantiateNatAt cond q (Nat.zero_le _) codeBody fuel hqAll
          (EnvInserted.top rho qv)
      have hThenSub :
          Term.eval codeBody fuel (Term.instantiateTopNat q thenP) rho =
            Term.eval codeBody fuel thenP (Env.cons qv rho) :=
        Term.eval_instantiateNatAt thenP q (Nat.zero_le _) codeBody fuel hqAll
          (EnvInserted.top rho qv)
      simp [SFormula.eval, STerm.eval, Term.eval, SC.closed, SC.b, hCondSub] at hCondTrue
      cases hCondEval : Term.eval codeBody fuel cond (Env.cons qv rho) with
      | none =>
          simp [hCondEval] at hCondTrue
      | some bv =>
          simp [hCondEval] at hCondTrue
          have hbv : bv = true := hCondTrue
          subst bv
          rcases hTargetDefined with ⟨_, hTarget⟩
          simp [SFormula.eval, STerm.eval, Term.eval, SC.closed, hqv, hCondEval,
            hThenSub] at hTarget ⊢
          cases hThenEval : Term.eval codeBody fuel thenP (Env.cons qv rho) with
          | none =>
              simp [hThenEval] at hTarget
          | some tv =>
              simp [hThenEval]
  | stabAtClosedIteLamEqElse cond thenP elseP q hq child ih =>
      intro hdef hctx
      rcases hdef with ⟨hChildDef, hTargetDefined⟩
      have hCondFalse := ih hChildDef hctx
      obtain ⟨qv, hqv⟩ := hq.eval_total codeBody fuel rho
      have hqAll := hq.eval_all_fuels hqv
      have hCondSub :
          Term.eval codeBody fuel (Term.instantiateTopNat q cond) rho =
            Term.eval codeBody fuel cond (Env.cons qv rho) :=
        Term.eval_instantiateNatAt cond q (Nat.zero_le _) codeBody fuel hqAll
          (EnvInserted.top rho qv)
      have hElseSub :
          Term.eval codeBody fuel (Term.instantiateTopNat q elseP) rho =
            Term.eval codeBody fuel elseP (Env.cons qv rho) :=
        Term.eval_instantiateNatAt elseP q (Nat.zero_le _) codeBody fuel hqAll
          (EnvInserted.top rho qv)
      simp [SFormula.eval, STerm.eval, Term.eval, SC.closed, SC.b, hCondSub] at hCondFalse
      cases hCondEval : Term.eval codeBody fuel cond (Env.cons qv rho) with
      | none =>
          simp [hCondEval] at hCondFalse
      | some bv =>
          simp [hCondEval] at hCondFalse
          have hbv : bv = false := hCondFalse
          subst bv
          rcases hTargetDefined with ⟨_, hTarget⟩
          simp [SFormula.eval, STerm.eval, Term.eval, SC.closed, hqv, hCondEval,
            hElseSub] at hTarget ⊢
          cases hElseEval : Term.eval codeBody fuel elseP (Env.cons qv rho) with
          | none =>
              simp [hElseEval] at hTarget
          | some tv =>
              simp [hElseEval]
  | pauliIteSelectThen cond p1 p2 child ih =>
      intro hdef hctx
      rcases hdef with ⟨hChildDef, hTargetDefined⟩
      have hChildEval := ih hChildDef hctx
      have hcond : Term.eval codeBody fuel cond rho = some true := by
        simp only [SFormula.eval, SC.closed, SC.b, STerm.eval, Term.eval, bind,
          Option.bind] at hChildEval
        cases hc : Term.eval codeBody fuel cond rho with
        | none => simp [hc] at hChildEval
        | some cv =>
            simp [hc] at hChildEval
            rw [hChildEval]
      rcases hTargetDefined with ⟨_, hTarget⟩
      simp [SFormula.eval, SC.closed, STerm.eval, Term.eval, hcond] at hTarget ⊢
      cases hp1 : Term.eval codeBody fuel p1 rho with
      | none => simp [hp1] at hTarget
      | some p1v => simp [hp1]
  | pauliIteSelectElse cond p1 p2 child ih =>
      intro hdef hctx
      rcases hdef with ⟨hChildDef, hTargetDefined⟩
      have hChildEval := ih hChildDef hctx
      have hcond : Term.eval codeBody fuel cond rho = some false := by
        simp only [SFormula.eval, SC.closed, SC.b, STerm.eval, Term.eval, bind,
          Option.bind] at hChildEval
        cases hc : Term.eval codeBody fuel cond rho with
        | none => simp [hc] at hChildEval
        | some cv =>
            simp [hc] at hChildEval
            rw [hChildEval]
      rcases hTargetDefined with ⟨_, hTarget⟩
      simp [SFormula.eval, SC.closed, STerm.eval, Term.eval, hcond] at hTarget ⊢
      cases hp2 : Term.eval codeBody fuel p2 rho with
      | none => simp [hp2] at hTarget
      | some p2v => simp [hp2]
  | localCommutesOfLeftI A B q child ih =>
      intro hdef hctx
      rcases hdef with ⟨hChildDef, hTargetDefined⟩
      have hEq := ih hChildDef hctx
      rcases hTargetDefined with ⟨_, hTarget⟩
      simp [SFormula.localCommutesAt, SFormula.eval, STerm.eval, Term.eval, SC.p,
        SC.b] at hEq hTarget ⊢
      cases hA : A.eval codeBody fuel rho E with
      | none =>
          simp [hA] at hEq
      | some Av =>
          cases hqEval : q.eval codeBody fuel rho E with
          | none =>
              simp [hA, hqEval] at hEq
          | some qv =>
              cases hAv : Av qv with
              | none =>
                  simp [hA, hqEval, hAv] at hEq
              | some av =>
                  simp [hA, hqEval, hAv] at hEq
                  have hav : av = Pauli.I := hEq
                  subst av
                  cases hB : B.eval codeBody fuel rho E with
                  | none =>
                      simp [hA, hqEval, hAv, hB] at hTarget
                  | some Bv =>
                      cases hBv : Bv qv with
                      | none =>
                          simp [hA, hqEval, hAv, hB, hBv] at hTarget
                      | some bv =>
                          cases bv <;>
                            simp [hA, hqEval, hAv, hB, hBv,
                              ErrorVec.Pauli.anticommutes]
  | localCommutesOfLeftEqNoAntiRight A B q p eqD noAntiD ihEq ihNoAnti =>
      intro hdef hctx
      rcases hdef with ⟨hEqDef, hNoAntiDef, hTargetDefined⟩
      have hEq := ihEq hEqDef hctx
      have hNoAnti := ihNoAnti hNoAntiDef hctx
      rcases hTargetDefined with ⟨_, hTarget⟩
      simp [SFormula.eval, STerm.eval] at hEq
      simp [SFormula.localCommutesAt, SFormula.eval, STerm.eval, SC.b] at hNoAnti hTarget
      cases hA : A.eval codeBody fuel rho E with
      | none =>
          simp [hA] at hEq
      | some Av =>
          cases hqEval : q.eval codeBody fuel rho E with
          | none =>
              simp [hA, hqEval] at hEq
          | some qv =>
              cases hAv : Av qv with
              | none =>
                  simp [hA, hqEval, hAv] at hEq
              | some av =>
                  cases hp : p.eval codeBody fuel rho E with
                  | none =>
                      simp [hA, hqEval, hAv, hp] at hEq
                  | some pv =>
                      simp [hA, hqEval, hAv, hp] at hEq
                      have hav : av = pv := hEq
                      subst av
                      cases hB : B.eval codeBody fuel rho E with
                      | none =>
                          simp [hB] at hNoAnti
                      | some Bv =>
                          cases hBv : Bv qv with
                          | none =>
                              simp [hB, hqEval, hBv, hp] at hNoAnti
                          | some bv =>
                              simp [hB, hqEval, hBv, hp] at hNoAnti
                              have hAntiFalse :
                                  ErrorVec.Pauli.anticommutes bv pv = false := by
                                cases hAnti : ErrorVec.Pauli.anticommutes bv pv with
                                | false => rfl
                                | true =>
                                    simp [hAnti, Term.eval] at hNoAnti
                              have hAntiTarget :
                                  ErrorVec.Pauli.anticommutes pv bv = false := by
                                simpa [pauli_anticommutes_symm] using hAntiFalse
                              simp [SFormula.localCommutesAt, SFormula.eval, STerm.eval,
                                Term.eval, SC.b, hA, hqEval, hAv, hB, hBv, hAntiTarget]
  | localCommutesOfRightI A B q child ih =>
      intro hdef hctx
      rcases hdef with ⟨hChildDef, hTargetDefined⟩
      have hEq := ih hChildDef hctx
      rcases hTargetDefined with ⟨_, hTarget⟩
      simp [SFormula.localCommutesAt, SFormula.eval, STerm.eval, Term.eval, SC.p,
        SC.b] at hEq hTarget ⊢
      cases hB : B.eval codeBody fuel rho E with
      | none =>
          simp [hB] at hEq
      | some Bv =>
          cases hqEval : q.eval codeBody fuel rho E with
          | none =>
              simp [hB, hqEval] at hEq
          | some qv =>
              cases hBv : Bv qv with
              | none =>
                  simp [hB, hqEval, hBv] at hEq
              | some bv =>
                  simp [hB, hqEval, hBv] at hEq
                  have hbv : bv = Pauli.I := hEq
                  subst bv
                  cases hA : A.eval codeBody fuel rho E with
                  | none =>
                      simp [hA, hqEval, hB, hBv] at hTarget
                  | some Av =>
                      cases hAv : Av qv with
                      | none =>
                          simp [hA, hqEval, hAv, hB, hBv] at hTarget
                      | some av =>
                          cases av <;>
                            simp [hAv, hBv,
                              ErrorVec.Pauli.anticommutes]
  | anticommutesTransport a a' b b' rhs eqAD eqBD antiD ihEqA ihEqB ihAnti =>
      intro hdef hctx
      rcases hdef with ⟨hEqADef, hEqBDef, hAntiDef, hTargetDefined⟩
      have hEqA := ihEqA hEqADef hctx
      have hEqB := ihEqB hEqBDef hctx
      have hAnti := ihAnti hAntiDef hctx
      rcases hTargetDefined with ⟨_, hTarget⟩
      simp [SFormula.eval, STerm.eval] at hEqA hEqB hAnti ⊢
      cases ha : a.eval codeBody fuel rho E with
      | none =>
          simp [ha] at hEqA
      | some av =>
          cases ha' : a'.eval codeBody fuel rho E with
          | none =>
              simp [ha, ha'] at hEqA
          | some av' =>
              simp [ha, ha'] at hEqA
              have havEq : av = av' := hEqA
              subst av'
              cases hb : b.eval codeBody fuel rho E with
              | none =>
                  simp [hb] at hEqB
              | some bv =>
                  cases hb' : b'.eval codeBody fuel rho E with
                  | none =>
                      simp [hb, hb'] at hEqB
                  | some bv' =>
                      simp [hb, hb'] at hEqB
                      have hbvEq : bv = bv' := hEqB
                      subst bv'
                      cases hr : rhs.eval codeBody fuel rho E with
                      | none =>
                          simp [ha', hb', hr] at hAnti
                      | some rv =>
                          simp [ha', hb', hr] at hAnti
                          have hAntiRhs :
                              ErrorVec.Pauli.anticommutes av bv = rv := hAnti
                          simp [hAntiRhs]
  | noAntiAtSubst Eterm p q1 q2 hq1 hq2 eqD noAntiD ihEq ihNoAnti =>
      intro hdef hctx
      rcases hdef with ⟨hEqDef, hNoAntiDef, hTargetDefined⟩
      have hEq := ihEq hEqDef hctx
      have hNoAnti := ihNoAnti hNoAntiDef hctx
      obtain ⟨qv1, hqv1⟩ := hq1.eval_total codeBody fuel rho
      obtain ⟨qv2, hqv2⟩ := hq2.eval_total codeBody fuel rho
      simp [SFormula.eval, STerm.eval, Term.eval, SC.closed, SC.b, hqv1, hqv2] at hEq
      have hqEq : qv1 = qv2 := hEq
      subst qv2
      rcases hTargetDefined with ⟨_, hTarget⟩
      simp [SFormula.eval, STerm.eval, Term.eval, SC.closed, SC.b, hqv1] at hNoAnti
      simp [SFormula.eval, STerm.eval, Term.eval, SC.closed, SC.b, hqv1] at hTarget
      cases hE : Eterm.eval codeBody fuel rho E with
      | none =>
          simp [hE] at hNoAnti
      | some Ev =>
          cases hEv : Ev qv1 with
          | none =>
              simp [hE, hEv] at hNoAnti
          | some ev =>
              cases hp : p.eval codeBody fuel rho E with
              | none =>
                  simp [hE, hEv, hp] at hNoAnti
              | some pv =>
                  simp [hE, hEv, hp] at hNoAnti
                  cases hAnti : ErrorVec.Pauli.anticommutes ev pv with
                  | false =>
                      simp [SFormula.eval, STerm.eval, Term.eval, SC.closed, SC.b,
                        hqv1, hqv2, hE, hEv, hp, hAnti]
                  | true =>
                      simp [hAnti, Term.eval] at hNoAnti
  | pauliAnticommutesNonI p a child ih =>
      intro hdef hctx
      have hAnti := ih hdef hctx
      simp [SFormula.eval, SC.b, SC.p, STerm.eval, Term.eval] at hAnti ⊢
      cases hp : p.eval codeBody fuel rho E with
      | none =>
          simp [hp] at hAnti
      | some pv =>
          cases ha : a.eval codeBody fuel rho E with
          | none =>
              simp [hp, ha] at hAnti
          | some av =>
              simp [hp, ha] at hAnti
              have hpNe : pv ≠ Pauli.I := by
                cases pv <;> cases av <;> simp [ErrorVec.Pauli.anticommutes] at hAnti ⊢
              simp [hpNe]
  | pauliAnticommutesLit p q =>
      intro _ _
      cases p <;> cases q <;>
        simp [SFormula.eval, STerm.eval, Term.eval, SC.p, SC.b, ErrorVec.Pauli.anticommutes]
  | pauliMulLit p q =>
      intro _ _
      cases p <;> cases q <;>
        simp [SFormula.eval, STerm.eval, Term.eval, SC.p, Pauli.mul]
  | pauliEqLit p =>
      intro _ _
      cases p <;> simp [SFormula.eval, STerm.eval, Term.eval, SC.p]
  | pauliNeqLit p q h =>
      intro _ _
      cases p <;> cases q <;>
        simp [SFormula.eval, STerm.eval, Term.eval, SC.p] at h ⊢
  | finiteInjectiveWeightLower n Eterm limit k slot support inj lt
      ihSupport ihInj ihLt =>
      intro hdef hctx
      rcases hdef with ⟨hSupportDef, hInjDef, hLtDef, hWeightDefined⟩
      have hSupport := ihSupport hSupportDef hctx
      have hInj := ihInj hInjDef hctx
      have hLt := ihLt hLtDef hctx
      rcases witnessLt_eval_true hLt with ⟨limitv, kv, hLimit, hK, hLimitLt⟩
      rcases hWeightDefined with ⟨_, hWeightEval⟩
      cases hN : n.eval codeBody fuel rho E with
      | none =>
          simp [SFormula.eval, hN] at hWeightEval
      | some nv =>
          cases hEterm : Eterm.eval codeBody fuel rho E with
          | none =>
              simp [SFormula.eval, hN, hEterm] at hWeightEval
          | some Ev =>
              cases hWeight : weightUpTo nv Ev with
              | none =>
                  simp [SFormula.eval, hN, hEterm, hLimit, hWeight] at hWeightEval
              | some w =>
                  simp [SFormula.eval, hK] at hSupport
                  let slotFn : Nat -> Nat := fun i =>
                    match slot.eval codeBody fuel (Env.cons i rho) E with
                    | some q => q
                    | none => 0
                  have hslotLt : forall i, i < kv -> slotFn i < nv := by
                    intro i hi
                    have hBody := allNatLt_sound hSupport i hi
                    rcases slotSupportBody_eval_true hBody hN hEterm with
                      ⟨q, hSlot, hqLt, _⟩
                    simp [slotFn, hSlot, hqLt]
                  have hnonI : forall i, i < kv -> nonIBool Ev (slotFn i) = true := by
                    intro i hi
                    have hBody := allNatLt_sound hSupport i hi
                    rcases slotSupportBody_eval_true hBody hN hEterm with
                      ⟨q, hSlot, _, hNonI⟩
                    simp [slotFn, hSlot, hNonI]
                  have hinj :
                      forall i j, i < kv -> j < kv -> slotFn i = slotFn j -> i = j := by
                    intro i j hi hj hEq
                    have hBodyI := allNatLt_sound hSupport i hi
                    have hBodyJ := allNatLt_sound hSupport j hj
                    rcases slotSupportBody_eval_true hBodyI hN hEterm with
                      ⟨qi, hSlotI, _, _⟩
                    rcases slotSupportBody_eval_true hBodyJ hN hEterm with
                      ⟨qj, hSlotJ, _, _⟩
                    have hSlotFnI : slotFn i = qi := by simp [slotFn, hSlotI]
                    have hSlotFnJ : slotFn j = qj := by simp [slotFn, hSlotJ]
                    have hq : qi = qj := by
                      exact hSlotFnI.symm.trans (hEq.trans hSlotFnJ)
                    exact slotInjectiveF_eval_true hInj hK i j qi qj hi hj hSlotI hSlotJ hq
                  have hNotLe : ¬ w <= limitv :=
                    weight_not_le_of_injective_support hslotLt hnonI hinj hLimitLt hWeight
                  simp [SFormula.eval, hN, hEterm, hLimit, hWeight, hNotLe]
  | finiteSurjectiveWeightLower n Eterm limit k rowOf cover lt ihCover ihLt =>
      intro hdef hctx
      rcases hdef with ⟨hCoverDef, hLtDef, hWeightDefined⟩
      have hCover := ihCover hCoverDef hctx
      have hLt := ihLt hLtDef hctx
      rcases witnessLt_eval_true hLt with ⟨limitv, kv, hLimit, hK, hLimitLt⟩
      rcases hWeightDefined with ⟨_, hWeightEval⟩
      cases hN : n.eval codeBody fuel rho E with
      | none =>
          simp [SFormula.eval, hN] at hWeightEval
      | some nv =>
          cases hEterm : Eterm.eval codeBody fuel rho E with
          | none =>
              simp [SFormula.eval, hN, hEterm] at hWeightEval
          | some Ev =>
              cases hWeight : weightUpTo nv Ev with
              | none =>
                  simp [SFormula.eval, hN, hEterm, hLimit, hWeight] at hWeightEval
              | some w =>
                  simp [SFormula.supportSurjectiveF, SFormula.eval, hK] at hCover
                  let rowOfFn : Nat -> Nat := fun q =>
                    match rowOf.eval codeBody fuel (Env.cons q rho) E with
                    | some r => r
                    | none => 0
                  have hcover :
                      forall i, i < kv ->
                        exists q, q < nv /\ nonIBool Ev q = true /\ rowOfFn q = i := by
                    intro i hi
                    have hBody := allNatLt_sound hCover i hi
                    rcases supportSurjectiveBody_eval_true hBody hN hEterm with
                      ⟨q, hqLt, hNonI, hRow⟩
                    exact ⟨q, hqLt, hNonI, by simp [rowOfFn, hRow]⟩
                  have hNotLe : ¬ w <= limitv :=
                    weight_not_le_of_surjective_support hcover hLimitLt hWeight
                  simp [SFormula.eval, hN, hEterm, hLimit, hWeight, hNotLe]
  | finiteDeMorgan n A child ih =>
      intro hdef hctx
      rcases hdef with ⟨hChildDef, bound, hbound, htotal⟩
      have hChild := ih hChildDef hctx
      simp [SFormula.eval, hbound] at hChild ⊢
      let notPred := fun x => do
        let av <- SFormula.eval codeBody fuel A (Env.cons x rho) E
        some (!av)
      change (QHL.CodeLang.allNatLt bound notPred).bind (fun av => some (!av)) =
        some true at hChild
      change QHL.CodeLang.existsNatLt bound
        (fun x => SFormula.eval codeBody fuel A (Env.cons x rho) E) = some true
      cases hall : QHL.CodeLang.allNatLt bound notPred with
      | none =>
          rw [hall] at hChild
          simp at hChild
      | some allOk =>
          cases allOk
          · exact finite_not_all_not_to_exists htotal hall
          · rw [hall] at hChild
            simp at hChild
  | existsNatLtIntro n A witness child ih =>
      intro hdef _
      rcases hdef with ⟨bound, hbound, hwitness, htotal, hChildDef, hChildCtx⟩
      simp [SFormula.eval, hbound]
      exact existsNatLt_complete htotal ⟨witness, hwitness, ih hChildDef hChildCtx⟩
  | existsNatLtIntroTerm n A witness ltD bodyD ihLt ihBody =>
      intro hdef hctx
      rcases hdef with ⟨hLtDef, hBodyDef, bound, hbound, htotal⟩
      have hLt := ihLt hLtDef hctx
      have hBody := ihBody hBodyDef hctx
      rcases witnessLt_eval_true hLt with ⟨wv, bound', hw, hbound', hwitness⟩
      have hboundEq : bound = bound' := by
        rw [hbound] at hbound'
        exact Option.some.inj hbound'
      have hwitness' : wv < bound := by
        simpa [hboundEq] using hwitness
      simp [SFormula.eval, hbound]
      simp [SFormula.eval, hw] at hBody
      exact existsNatLt_complete htotal ⟨wv, hwitness', hBody⟩
  | existsNatLtElim n A C existsD bodyD ihExists ihBody =>
      intro hdef hctx
      rcases hdef with ⟨hExistsDef, bound, hbound, hbodyDef⟩
      have hExists := ihExists hExistsDef hctx
      simp [SFormula.eval, hbound] at hExists
      rcases existsNatLt_sound hExists with ⟨witness, hwitness, hA⟩
      rcases hbodyDef witness hwitness hA with ⟨hBodyDef, hBodyCtx⟩
      have hWeakened := ihBody hBodyDef hBodyCtx
      have hCweaken :
          SFormula.eval codeBody fuel C.weaken (Env.cons witness rho) E =
            SFormula.eval codeBody fuel C rho E := by
        simpa [SFormula.weaken] using
          eval_lift_of_env C (EnvLifted.underTop rho witness) codeBody fuel E
      rw [hCweaken] at hWeakened
      exact hWeakened

end Deriv

end SFormula

/-- Object-language finite stabilizer quantification.

Semantically, `body` must hold for every stabilizer value total on the first
`width` slots.  This is intentionally not implemented by enumeration.
-/
structure ForallStabFormula (arity : Nat) where
  width : STerm arity .nat
  body : SFormula arity

namespace ForallStabFormula

def instantiate (Q : ForallStabFormula arity) (E : Term arity .stab) :
    Formula arity :=
  Q.body.instantiate E

def evalOn (codeBody : Term 2 .stab) (fuel : Nat) (Q : ForallStabFormula arity)
    (rho : Env arity) (E : PartialStabilizer) : Option Bool :=
  Q.body.eval codeBody fuel rho E

def holds (codeBody : Term 2 .stab) (fuel : Nat) (Q : ForallStabFormula arity)
    (rho : Env arity) : Prop :=
  forall E n,
    Q.width.eval codeBody fuel rho E = some n ->
      TotalUpTo n E ->
        Q.evalOn codeBody fuel rho E = some true

/-- A concrete instance checker for the universal formula.  This is the rule
    used by examples and tests: instantiate the bound stabilizer with a closed
    stabilizer program and check the resulting old `Formula` derivation. -/
def checkClosedInstance (Q : ForallStabFormula 0) (codeBody : Term 2 .stab)
    (fuel : Nat) (E : Term 0 .stab) (D : Formula.Deriv (Q.instantiate E) true) : Bool :=
  D.check codeBody fuel Env.empty

end ForallStabFormula

/-- A derivation of `forall E : Stab[n], body(E)`.

The intro rule is the usual universal-introduction rule: prove the body with a
fresh symbolic stabilizer and no assumptions about which concrete stabilizer it
is.  Future algebraic/geometric rules may use the binder width and totality
premise; this logical core does not add such leaves.
-/
inductive ForallStabDeriv {arity : Nat} : ForallStabFormula arity -> Type where
  | intro {Q : ForallStabFormula arity} :
      SFormula.Deriv [] Q.body -> ForallStabDeriv Q

namespace ForallStabDeriv

def check {arity : Nat} {Q : ForallStabFormula arity} :
    ForallStabDeriv Q -> Bool
  | .intro body => body.check

def size {arity : Nat} {Q : ForallStabFormula arity} :
    ForallStabDeriv Q -> Nat
  | .intro body => 1 + body.size

def DefinedObligations {arity : Nat} {Q : ForallStabFormula arity}
    (D : ForallStabDeriv Q) (codeBody : Term 2 .stab) (fuel : Nat)
    (rho : Env arity) (E : PartialStabilizer) : Prop :=
  match D with
  | .intro body => body.DefinedObligations codeBody fuel rho E

theorem sound {arity : Nat} {codeBody : Term 2 .stab} {fuel : Nat}
    {rho : Env arity} {Q : ForallStabFormula arity}
    (D : ForallStabDeriv Q) :
    (forall E n,
      Q.width.eval codeBody fuel rho E = some n ->
        TotalUpTo n E ->
          D.DefinedObligations codeBody fuel rho E) ->
    Q.holds codeBody fuel rho := by
  intro hdef E n hWidth hTotal
  cases D with
  | intro body =>
      exact body.sound (hdef E n hWidth hTotal) (fun A hmem => by cases hmem)

end ForallStabDeriv

/-- A harmless closed stabilizer used only to instantiate formulas that have
    first been syntactically checked not to mention the bound stabilizer. -/
def dummyClosedStabilizer : Term 0 .stab :=
  Formula.closedStabilizer (.pauliLit Pauli.I)

/-! ### Code-family-indexed closed derivations

`SFormula.Deriv` is intentionally code-family-polymorphic.  Some generated
equalities, however, are closed with respect to the stabilizer binder and are
only true for the particular recursive code AST being verified.  The following
wrapper is the generic bridge: it may use ordinary symbolic derivations, or it
may check a bound-free formula by executable evaluation under a fixed
`codeBody` and `fuel`.

There is no Surface-specific constructor here.
-/

inductive FamilyDeriv (codeBody : Term 2 .stab) (fuel : Nat) :
    SFormula 0 -> Type where
  | core {A : SFormula 0} :
      SFormula.Deriv [] A -> FamilyDeriv codeBody fuel A
  | checkedBoundFree (A : SFormula 0) : FamilyDeriv codeBody fuel A
  | cut1 {A B : SFormula 0} :
      SFormula.Deriv [A] B ->
        FamilyDeriv codeBody fuel A ->
          FamilyDeriv codeBody fuel B
  | cut2 {A B C : SFormula 0} :
      SFormula.Deriv [A, B] C ->
        FamilyDeriv codeBody fuel A ->
          FamilyDeriv codeBody fuel B ->
            FamilyDeriv codeBody fuel C
  | cut3 {A B C D : SFormula 0} :
      SFormula.Deriv [A, B, C] D ->
        FamilyDeriv codeBody fuel A ->
          FamilyDeriv codeBody fuel B ->
            FamilyDeriv codeBody fuel C ->
              FamilyDeriv codeBody fuel D
  | cut4 {A B C D E : SFormula 0} :
      SFormula.Deriv [A, B, C, D] E ->
        FamilyDeriv codeBody fuel A ->
          FamilyDeriv codeBody fuel B ->
            FamilyDeriv codeBody fuel C ->
              FamilyDeriv codeBody fuel D ->
                FamilyDeriv codeBody fuel E

namespace FamilyDeriv

def checkedBoundFreeCheck (codeBody : Term 2 .stab) (fuel : Nat)
    (A : SFormula 0) : Bool :=
  A.boundFree && Formula.check codeBody fuel (A.instantiate dummyClosedStabilizer) Env.empty

def check {codeBody : Term 2 .stab} {fuel : Nat}
    {A : SFormula 0} :
    FamilyDeriv codeBody fuel A -> Bool
  | .core D => D.check
  | .checkedBoundFree A => checkedBoundFreeCheck codeBody fuel A
  | .cut1 D hA => D.check && check hA
  | .cut2 D hA hB => D.check && check hA && check hB
  | .cut3 D hA hB hC => D.check && check hA && check hB && check hC
  | .cut4 D hA hB hC hD => D.check && check hA && check hB && check hC && check hD

def size {codeBody : Term 2 .stab} {fuel : Nat}
    {A : SFormula 0} :
    FamilyDeriv codeBody fuel A -> Nat
  | .core D => 1 + D.size
  | .checkedBoundFree _ => 1
  | .cut1 D hA => 1 + D.size + size hA
  | .cut2 D hA hB => 1 + D.size + size hA + size hB
  | .cut3 D hA hB hC => 1 + D.size + size hA + size hB + size hC
  | .cut4 D hA hB hC hD => 1 + D.size + size hA + size hB + size hC + size hD

def DefinedObligations {codeBody : Term 2 .stab} {fuel : Nat}
    {A : SFormula 0}
    (D : FamilyDeriv codeBody fuel A) (E : PartialStabilizer) : Prop :=
  match D with
  | .core Dcore => Dcore.DefinedObligations codeBody fuel Env.empty E
  | .checkedBoundFree _ => True
  | .cut1 Dcore hA =>
      Dcore.DefinedObligations codeBody fuel Env.empty E /\
        DefinedObligations hA E
  | .cut2 Dcore hA hB =>
      Dcore.DefinedObligations codeBody fuel Env.empty E /\
        DefinedObligations hA E /\ DefinedObligations hB E
  | .cut3 Dcore hA hB hC =>
      Dcore.DefinedObligations codeBody fuel Env.empty E /\
        DefinedObligations hA E /\ DefinedObligations hB E /\ DefinedObligations hC E
  | .cut4 Dcore hA hB hC hD =>
      Dcore.DefinedObligations codeBody fuel Env.empty E /\
        DefinedObligations hA E /\ DefinedObligations hB E /\
          DefinedObligations hC E /\ DefinedObligations hD E

theorem sound {codeBody : Term 2 .stab} {fuel : Nat} {A : SFormula 0}
    (D : FamilyDeriv codeBody fuel A) (E : PartialStabilizer) :
    check D = true ->
      DefinedObligations D E ->
        A.eval codeBody fuel Env.empty E = some true := by
  intro hcheck hdef
  induction D with
  | core Dcore =>
      simp [DefinedObligations] at hdef
      exact Dcore.sound hdef (fun B hmem => by cases hmem)
  | checkedBoundFree A =>
      simp [check, checkedBoundFreeCheck, Bool.and_eq_true] at hcheck
      rcases hcheck with ⟨hfree, hchecked⟩
      have hFormula :
          Formula.eval codeBody fuel (A.instantiate dummyClosedStabilizer) Env.empty =
            some true :=
        Formula.check_sound (A := A.instantiate dummyClosedStabilizer) hchecked
      have hEval :=
        SFormula.eval_boundFree_instantiate A hfree codeBody fuel Env.empty E
          dummyClosedStabilizer
      rwa [hEval]
  | cut1 Dcore hA ihA =>
      simp [check, DefinedObligations, Bool.and_eq_true] at hcheck hdef
      rcases hcheck with ⟨hcoreCheck, hACheck⟩
      rcases hdef with ⟨hcoreDef, hADef⟩
      exact Dcore.sound hcoreDef
        (fun B hmem => by
          cases hmem with
          | head => exact ihA hACheck hADef
          | tail _ htail => cases htail)
  | cut2 Dcore hA hB ihA ihB =>
      simp [check, DefinedObligations, Bool.and_eq_true] at hcheck hdef
      rcases hcheck with ⟨⟨hcoreCheck, hACheck⟩, hBCheck⟩
      rcases hdef with ⟨hcoreDef, hADef, hBDef⟩
      exact Dcore.sound hcoreDef
        (fun X hmem => by
          cases hmem with
          | head => exact ihA hACheck hADef
          | tail _ htail =>
              cases htail with
              | head => exact ihB hBCheck hBDef
              | tail _ hnil => cases hnil)
  | cut3 Dcore hA hB hC ihA ihB ihC =>
      simp [check, DefinedObligations, Bool.and_eq_true] at hcheck hdef
      rcases hcheck with ⟨⟨⟨hcoreCheck, hACheck⟩, hBCheck⟩, hCCheck⟩
      rcases hdef with ⟨hcoreDef, hADef, hBDef, hCDef⟩
      exact Dcore.sound hcoreDef
        (fun X hmem => by
          cases hmem with
          | head => exact ihA hACheck hADef
          | tail _ htail =>
              cases htail with
              | head => exact ihB hBCheck hBDef
              | tail _ htail2 =>
                  cases htail2 with
                  | head => exact ihC hCCheck hCDef
                  | tail _ hnil => cases hnil)
  | cut4 Dcore hA hB hC hD ihA ihB ihC ihD =>
      simp [check, DefinedObligations, Bool.and_eq_true] at hcheck hdef
      rcases hcheck with
        ⟨⟨⟨⟨hcoreCheck, hACheck⟩, hBCheck⟩, hCCheck⟩, hDCheck⟩
      rcases hdef with ⟨hcoreDef, hADef, hBDef, hCDef, hDDef⟩
      exact Dcore.sound hcoreDef
        (fun X hmem => by
          cases hmem with
          | head => exact ihA hACheck hADef
          | tail _ htail =>
              cases htail with
              | head => exact ihB hBCheck hBDef
              | tail _ htail2 =>
                  cases htail2 with
                  | head => exact ihC hCCheck hCDef
                  | tail _ htail3 =>
                      cases htail3 with
                      | head => exact ihD hDCheck hDDef
                      | tail _ hnil => cases hnil)

end FamilyDeriv

/-- Universal stabilizer derivations whose closed auxiliary facts are checked
    against one concrete code family. -/
inductive ForallStabFamilyDeriv (codeBody : Term 2 .stab) (fuel : Nat) :
    ForallStabFormula 0 -> Type where
  | intro {Q : ForallStabFormula 0} :
      FamilyDeriv codeBody fuel Q.body ->
        ForallStabFamilyDeriv codeBody fuel Q

namespace ForallStabFamilyDeriv

def check {codeBody : Term 2 .stab} {fuel : Nat} {Q : ForallStabFormula 0} :
    ForallStabFamilyDeriv codeBody fuel Q -> Bool
  | .intro body => FamilyDeriv.check body

def size {codeBody : Term 2 .stab} {fuel : Nat} {Q : ForallStabFormula 0} :
    ForallStabFamilyDeriv codeBody fuel Q -> Nat
  | .intro body => 1 + FamilyDeriv.size body

def DefinedObligations {codeBody : Term 2 .stab} {fuel : Nat}
    {Q : ForallStabFormula 0}
    (D : ForallStabFamilyDeriv codeBody fuel Q) (E : PartialStabilizer) : Prop :=
  match D with
  | .intro body => FamilyDeriv.DefinedObligations body E

theorem sound {codeBody : Term 2 .stab} {fuel : Nat} {Q : ForallStabFormula 0}
    (D : ForallStabFamilyDeriv codeBody fuel Q) :
    check D = true ->
      (forall E n,
        Q.width.eval codeBody fuel Env.empty E = some n ->
          TotalUpTo n E ->
            D.DefinedObligations E) ->
        Q.holds codeBody fuel Env.empty := by
  intro hcheck hdef E n hWidth hTotal
  cases D with
  | intro body =>
      exact FamilyDeriv.sound body E hcheck (hdef E n hWidth hTotal)

end ForallStabFamilyDeriv

/-! ## Small closed smoke tests -/

def oneSlotWidth : STerm 0 .nat := SC.n 1
def boundSelfCommutesBody : SFormula 0 :=
  .commutesUpTo oneSlotWidth SC.bound SC.bound

def forallBoundSelfCommutes : ForallStabFormula 0 where
  width := oneSlotWidth
  body := boundSelfCommutesBody

def forallImpSelf : ForallStabFormula 0 where
  width := oneSlotWidth
  body := .imp boundSelfCommutesBody boundSelfCommutesBody

def forallImpSelfDeriv : ForallStabDeriv forallImpSelf :=
  .intro (.impIntro .assumption)

def boundedTopF : SFormula 0 :=
  .allNatLt (SC.n (arity := 0) 2) (SFormula.top (arity := 1))

def boundedTopDeriv : SFormula.Deriv [] boundedTopF :=
  .allNatLtIntro (SC.n (arity := 0) 2) (SFormula.top (arity := 1)) .top

def boundedWitnessF : SFormula 0 :=
  .allNatLt (SC.n (arity := 0) 2)
    (SFormula.boundNatLt (SC.n (arity := 0) 2))

def boundedWitnessDeriv : SFormula.Deriv [] boundedWitnessF :=
  .allNatLtIntroBounded (SC.n (arity := 0) 2)
    (SFormula.boundNatLt (SC.n (arity := 0) 2))
    .assumption

def boundedTopWitnessLt : SFormula 0 :=
  SFormula.witnessLt (SC.n (arity := 0) 1) (SC.n (arity := 0) 2)

/-- Bounded universal elimination is a two-premise syntactic rule:
    the universal proof plus a proof of the object-language bound side
    condition.  This smoke proof deliberately supplies the side condition as
    an assumption in the derivation context. -/
def boundedTopElimDeriv :
    SFormula.Deriv [boundedTopWitnessLt]
      (.applyNat (SC.n (arity := 0) 1) (SFormula.top (arity := 1))) :=
  .allNatLtElim (SC.n (arity := 0) 2) (SFormula.top (arity := 1))
    (SC.n (arity := 0) 1)
    (boundedTopDeriv.weakenContext)
    .assumption

/-- Right disjunction introduction is a real checked rule. -/
def rightOrTopDeriv : SFormula.Deriv [] (.or (SFormula.bot (arity := 0)) .top) :=
  .orIntroRight .top

/-- Disjunction elimination composes two derivation branches syntactically. -/
def orElimTopDeriv : SFormula.Deriv [] (SFormula.top (arity := 0)) :=
  .orElim (A := SFormula.top) (B := SFormula.bot) (C := SFormula.top)
    (.orIntroLeft (B := SFormula.bot) .top)
    .top
    .top

def existsTopF : SFormula 0 :=
  .existsNatLt (SC.n (arity := 0) 3) (SFormula.top (arity := 1))

/-- Bounded existential introduction carries a concrete finite witness index. -/
def existsTopDeriv : SFormula.Deriv [] existsTopF :=
  .existsNatLtIntro (SC.n (arity := 0) 3) (SFormula.top (arity := 1)) 0 .top

def boundedTop3F : SFormula 0 :=
  .allNatLt (SC.n (arity := 0) 3) (SFormula.top (arity := 1))

def boundedTop3Deriv : SFormula.Deriv [] boundedTop3F :=
  .allNatLtIntro (SC.n (arity := 0) 3) (SFormula.top (arity := 1)) .top

def existsTopTermWitnessLt : SFormula 0 :=
  SFormula.witnessLt (SC.n (arity := 0) 1) (SC.n (arity := 0) 3)

def existsTopTermBodyDeriv :
    SFormula.Deriv [existsTopTermWitnessLt]
      (.applyNat (SC.n (arity := 0) 1) (SFormula.top (arity := 1))) :=
  .allNatLtElim (SC.n (arity := 0) 3) (SFormula.top (arity := 1))
    (SC.n (arity := 0) 1)
    (boundedTop3Deriv.weakenContext)
    .assumption

/-- Term-witness bounded existential introduction.  The witness proof is the
    object-language side condition `1 < 3`; the body proof is obtained by
    bounded universal elimination, not by evaluation. -/
def existsTopTermDeriv : SFormula.Deriv [existsTopTermWitnessLt] existsTopF :=
  .existsNatLtIntroTerm (SC.n (arity := 0) 3) (SFormula.top (arity := 1))
    (SC.n (arity := 0) 1)
    .assumption
    existsTopTermBodyDeriv

/-- Bounded existential elimination opens a fresh finite witness and proves the
    result from the body assumption plus the generated bound side condition. -/
def existsTopElimDeriv : SFormula.Deriv [existsTopF] (SFormula.top (arity := 0)) :=
  .existsNatLtElim (SC.n (arity := 0) 3) (SFormula.top (arity := 1))
    (SFormula.top (arity := 0))
    .assumption
    .top

def notAllNotTopF : SFormula 0 :=
  .not (.allNatLt (SC.n (arity := 0) 3) (.not (SFormula.top (arity := 1))))

def finiteDeMorganTopDeriv : SFormula.Deriv [notAllNotTopF] (.existsNatLt
    (SC.n (arity := 0) 3) (SFormula.top (arity := 1))) :=
  .finiteDeMorgan (SC.n (arity := 0) 3) (SFormula.top (arity := 1)) .assumption

def applyNatBetaTopAssumption : SFormula 1 :=
  .applyNat SFormula.boundNat ((SFormula.top (arity := 1)).lift 1)

def applyNatBetaTopDeriv :
    SFormula.Deriv [applyNatBetaTopAssumption] (SFormula.top (arity := 1)) :=
  .applyNatBoundNatBeta (SFormula.top (arity := 1)) .assumption

def xAnticommutesZTrueF : SFormula 0 :=
  .eqBool (.anticommutes (SC.p (arity := 0) Pauli.X) (SC.p (arity := 0) Pauli.Z))
    (SC.b true)

def xAnticommutesZNonIDeriv :
    SFormula.Deriv [xAnticommutesZTrueF]
      (.not (.eqPauli (SC.p (arity := 0) Pauli.X) (SC.p Pauli.I))) :=
  .pauliAnticommutesNonI (SC.p (arity := 0) Pauli.X) (SC.p (arity := 0) Pauli.Z)
    .assumption

def boundEqReflDeriv :
    SFormula.Deriv [] (.eqStabUpTo oneSlotWidth SC.bound SC.bound) :=
  .eqStabRefl oneSlotWidth SC.bound

def productSelfCommutesBody : SFormula 0 :=
  .commutesUpTo oneSlotWidth (SC.stabMul SC.bound SC.bound) SC.bound

def productSelfCommutesDeriv :
    SFormula.Deriv [boundSelfCommutesBody] productSelfCommutesBody :=
  .commutesStabMulLeft oneSlotWidth SC.bound SC.bound SC.bound .assumption .assumption

def stabOneEqReflDeriv :
    SFormula.Deriv [] (.eqStabUpTo oneSlotWidth SC.stabOne SC.stabOne) :=
  .eqStabRefl oneSlotWidth SC.stabOne

def productCongrBody : SFormula 0 :=
  .eqStabUpTo oneSlotWidth
    (SC.stabMul SC.bound SC.stabOne)
    (SC.stabMul SC.bound SC.stabOne)

def productCongrDeriv : SFormula.Deriv [] productCongrBody :=
  .eqStabMulCongr oneSlotWidth SC.bound SC.bound SC.stabOne SC.stabOne
    boundEqReflDeriv
    stabOneEqReflDeriv

def productAssocBody : SFormula 0 :=
  .eqStabUpTo oneSlotWidth
    (SC.stabMul (SC.stabMul SC.bound SC.bound) SC.bound)
    (SC.stabMul SC.bound (SC.stabMul SC.bound SC.bound))

def productAssocDeriv : SFormula.Deriv [] productAssocBody :=
  .eqStabMulAssoc oneSlotWidth SC.bound SC.bound SC.bound
    boundEqReflDeriv
    boundEqReflDeriv
    boundEqReflDeriv

def productCommBody : SFormula 0 :=
  .eqStabUpTo oneSlotWidth
    (SC.stabMul SC.bound SC.stabOne)
    (SC.stabMul SC.stabOne SC.bound)

def productCommDeriv : SFormula.Deriv [] productCommBody :=
  .eqStabMulComm oneSlotWidth SC.bound SC.stabOne
    boundEqReflDeriv
    stabOneEqReflDeriv

def productSelfCancelBody : SFormula 0 :=
  .eqStabUpTo oneSlotWidth (SC.stabMul SC.bound SC.bound) SC.stabOne

def productSelfCancelDeriv : SFormula.Deriv [] productSelfCancelBody :=
  .eqStabMulSelf oneSlotWidth SC.bound boundEqReflDeriv

def productOneLeftBody : SFormula 0 :=
  .eqStabUpTo oneSlotWidth (SC.stabMul SC.stabOne SC.bound) SC.bound

def productOneLeftDeriv : SFormula.Deriv [] productOneLeftBody :=
  .eqStabMulOneLeft oneSlotWidth SC.bound boundEqReflDeriv

def productOneRightBody : SFormula 0 :=
  .eqStabUpTo oneSlotWidth (SC.stabMul SC.bound SC.stabOne) SC.bound

def productOneRightDeriv : SFormula.Deriv [] productOneRightBody :=
  .eqStabMulOneRight oneSlotWidth SC.bound boundEqReflDeriv

def foldZeroBody : SFormula 0 :=
  .eqStabUpTo oneSlotWidth
    (SC.stabFold (SC.n 0) (SC.bound (arity := 1)))
    SC.stabOne

def foldZeroDeriv : SFormula.Deriv [] foldZeroBody :=
  .eqStabFoldZero oneSlotWidth (SC.bound (arity := 1))

def foldSuccBody : SFormula 0 :=
  .eqStabUpTo oneSlotWidth
    (SC.stabFold (SC.succClosed (.natLit 1)) (SC.bound (arity := 1)))
    (SC.stabMul
      (SC.stabFold (SC.closed (.natLit 1)) (SC.bound (arity := 1)))
      (SC.applyNat (.natLit 1) (SC.bound (arity := 1))))

def foldSuccDeriv : SFormula.Deriv [] foldSuccBody :=
  .eqStabFoldSucc oneSlotWidth (.natLit 1) (SC.bound (arity := 1))

def oneSlotSupportF : SFormula 0 :=
  .allNatLt (SC.n (arity := 0) 1) <|
    SFormula.slotSupportBody (SC.n (arity := 0) 1) SC.bound SFormula.boundNat

def oneSlotInjectiveF : SFormula 0 :=
  SFormula.slotInjectiveF (SC.n (arity := 0) 1) SFormula.boundNat

def oneSlotLimitLtF : SFormula 0 :=
  SFormula.witnessLt (SC.n (arity := 0) 0) (SC.n (arity := 0) 1)

def oneSlotCountingDeriv :
    SFormula.Deriv [oneSlotSupportF, oneSlotInjectiveF, oneSlotLimitLtF]
      (.not (.weightLe (SC.n (arity := 0) 1) SC.bound (SC.n (arity := 0) 0))) :=
  .finiteInjectiveWeightLower (SC.n (arity := 0) 1) SC.bound
    (SC.n (arity := 0) 0) (SC.n (arity := 0) 1) SFormula.boundNat
    (.hyp (by simp [oneSlotSupportF]))
    (.hyp (by simp [oneSlotInjectiveF]))
    (.hyp (by simp [oneSlotLimitLtF]))

def oneSupportSurjectiveF : SFormula 0 :=
  SFormula.supportSurjectiveF (SC.n (arity := 0) 1) (SC.n (arity := 0) 1)
    SC.bound SFormula.boundNat

def oneSupportCountingDeriv :
    SFormula.Deriv [oneSupportSurjectiveF, oneSlotLimitLtF]
      (.not (.weightLe (SC.n (arity := 0) 1) SC.bound (SC.n (arity := 0) 0))) :=
  .finiteSurjectiveWeightLower (SC.n (arity := 0) 1) SC.bound
    (SC.n (arity := 0) 0) (SC.n (arity := 0) 1) SFormula.boundNat
    (.hyp (by simp [oneSupportSurjectiveF]))
    (.hyp (by simp [oneSlotLimitLtF]))

def closedNatLtSmokeDeriv :
    SFormula.Deriv []
      (SFormula.witnessLt (SC.n (arity := 0) 0) (SC.n (arity := 0) 1)) :=
  .closedNatLt 0 1 rfl

def oneSlotPointwiseCommutesF : SFormula 0 :=
  SFormula.pointwiseCommutesUpTo (SC.n (arity := 0) 1) SC.bound SC.bound

def oneSlotPointwiseCommutesDeriv :
    SFormula.Deriv [oneSlotPointwiseCommutesF]
      (.commutesUpTo (SC.n (arity := 0) 1) SC.bound SC.bound) :=
  .commutesOfPointwise (SC.n (arity := 0) 1) SC.bound SC.bound .assumption

private def closedX0 : Term 0 .stab :=
  Formula.closedStabilizer <|
    .ite (.eqNat (.var ⟨0, by decide⟩) (.natLit 0))
      (.pauliLit Pauli.X)
      (.pauliLit Pauli.I)

/-- info: some true -/
#guard_msgs in
#eval (forallBoundSelfCommutes.instantiate closedX0).eval identityCode.body 0 Env.empty

/-- info: true -/
#guard_msgs in
#eval match Formula.deriveTrue? identityCode.body 0 Env.empty
    (forallBoundSelfCommutes.instantiate closedX0) with
  | some D => forallBoundSelfCommutes.checkClosedInstance identityCode.body 0 closedX0 D
  | none => false

/-- info: true -/
#guard_msgs in
#eval forallImpSelfDeriv.check

/-- info: 3 -/
#guard_msgs in
#eval forallImpSelfDeriv.size

/-- info: true -/
#guard_msgs in
#eval boundedTopDeriv.check

/-- info: true -/
#guard_msgs in
#eval boundedWitnessDeriv.check

/-- info: true -/
#guard_msgs in
#eval boundedTopElimDeriv.check

/-- info: true -/
#guard_msgs in
#eval rightOrTopDeriv.check

/-- info: true -/
#guard_msgs in
#eval orElimTopDeriv.check

/-- info: true -/
#guard_msgs in
#eval existsTopDeriv.check

/-- info: true -/
#guard_msgs in
#eval existsTopTermDeriv.check

/-- info: true -/
#guard_msgs in
#eval existsTopElimDeriv.check

/-- info: true -/
#guard_msgs in
#eval finiteDeMorganTopDeriv.check

/-- info: true -/
#guard_msgs in
#eval applyNatBetaTopDeriv.check

/-- info: true -/
#guard_msgs in
#eval xAnticommutesZNonIDeriv.check

/-- info: true -/
#guard_msgs in
#eval boundEqReflDeriv.check

/-- info: true -/
#guard_msgs in
#eval productSelfCommutesDeriv.check

/-- info: true -/
#guard_msgs in
#eval productCongrDeriv.check

/-- info: true -/
#guard_msgs in
#eval productAssocDeriv.check

/-- info: true -/
#guard_msgs in
#eval productCommDeriv.check

/-- info: true -/
#guard_msgs in
#eval productSelfCancelDeriv.check

/-- info: true -/
#guard_msgs in
#eval productOneLeftDeriv.check

/-- info: true -/
#guard_msgs in
#eval productOneRightDeriv.check

/-- info: true -/
#guard_msgs in
#eval foldZeroDeriv.check

/-- info: true -/
#guard_msgs in
#eval foldSuccDeriv.check

/-- info: true -/
#guard_msgs in
#eval oneSlotCountingDeriv.check

/-- info: true -/
#guard_msgs in
#eval oneSupportCountingDeriv.check

/-- info: true -/
#guard_msgs in
#eval closedNatLtSmokeDeriv.check

/-- info: true -/
#guard_msgs in
#eval oneSlotPointwiseCommutesDeriv.check

/-- info: 2 -/
#guard_msgs in
#eval boundedTopDeriv.size

/-- info: 2 -/
#guard_msgs in
#eval boundedWitnessDeriv.size

#print axioms STerm.eval
#print axioms SFormula.eval
#print axioms SFormula.Deriv.sound
#print axioms ForallStabFormula.holds
#print axioms ForallStabFormula.checkClosedInstance
#print axioms ForallStabDeriv.sound

end StabBinder

end QHL.CodeLang
