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

def weaken {arity : Nat} {ty : Ty} (t : STerm arity ty) :
    STerm (arity + 1) ty :=
  t.lift 0

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

def bound {arity : Nat} : S arity := .boundStab
def entry {arity : Nat} : S arity -> N arity -> P arity := .stabAt
def anticommutes {arity : Nat} : P arity -> P arity -> B arity := .anticommutes
def lt {arity : Nat} : N arity -> N arity -> B arity := .ltNat
def holds {arity : Nat} (x : B arity) : B arity := x

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

/-- Syntactic bounded-index side condition for `allNatLt` elimination:
    `(witness < bound) = true`. -/
def witnessLt {arity : Nat} (witness bound : STerm arity .nat) :
    SFormula arity :=
  .eqBool (.ltNat witness bound) (SC.b true)

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

inductive Deriv : {arity : Nat} -> List (SFormula arity) -> SFormula arity -> Type where
  | hyp {Γ : List (SFormula arity)} {A : SFormula arity} : A ∈ Γ -> Deriv Γ A
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
  | allNatLtIntro {Γ : List (SFormula arity)}
      (n : STerm arity .nat) (A : SFormula (arity + 1)) :
      Deriv (Γ.map (fun G => G.weaken)) A -> Deriv Γ (.allNatLt n A)
  | allNatLtElim {Γ : List (SFormula arity)}
      (n : STerm arity .nat) (A : SFormula (arity + 1))
      (witness : STerm arity .nat) :
      Deriv Γ (.allNatLt n A) ->
        Deriv Γ (SFormula.witnessLt witness n) ->
          Deriv Γ (.applyNat witness A)
  | existsNatLtIntro {Γ : List (SFormula arity)}
      (n : STerm arity .nat) (A : SFormula (arity + 1)) (witness : Nat) :
      Deriv (Γ.map (fun G => G.weaken)) A -> Deriv Γ (.existsNatLt n A)

namespace Deriv

def assumption {arity : Nat} {Γ : List (SFormula arity)} {A : SFormula arity} :
    Deriv (A :: Γ) A :=
  .hyp (by simp)

def weakenBy {arity : Nat} {Γ Δ : List (SFormula arity)} {A : SFormula arity}
    (hsub : forall C, C ∈ Γ -> C ∈ Δ) :
    Deriv Γ A -> Deriv Δ A
  | .hyp h => .hyp (hsub _ h)
  | .top => .top
  | .botElim child => .botElim (child.weakenBy hsub)
  | .andIntro left right => .andIntro (left.weakenBy hsub) (right.weakenBy hsub)
  | .andElimLeft child => .andElimLeft (child.weakenBy hsub)
  | .andElimRight child => .andElimRight (child.weakenBy hsub)
  | .orIntroLeft child => .orIntroLeft (child.weakenBy hsub)
  | .orIntroRight child => .orIntroRight (child.weakenBy hsub)
  | .orElim disj left right =>
      .orElim (disj.weakenBy hsub)
        (left.weakenBy fun C hmem => by
          cases hmem with
          | head => simp
          | tail _ htail => exact List.mem_cons_of_mem _ (hsub C htail))
        (right.weakenBy fun C hmem => by
          cases hmem with
          | head => simp
          | tail _ htail => exact List.mem_cons_of_mem _ (hsub C htail))
  | .notIntro child =>
      .notIntro <| child.weakenBy fun C hmem => by
        cases hmem with
        | head => simp
        | tail _ htail => exact List.mem_cons_of_mem _ (hsub C htail)
  | .notElim positive negative => .notElim (positive.weakenBy hsub) (negative.weakenBy hsub)
  | .impIntro child =>
      .impIntro <| child.weakenBy fun C hmem => by
        cases hmem with
        | head => simp
        | tail _ htail => exact List.mem_cons_of_mem _ (hsub C htail)
  | .mp implication antecedent => .mp (implication.weakenBy hsub) (antecedent.weakenBy hsub)
  | .allNatLtIntro n A child =>
      .allNatLtIntro n A <| child.weakenBy fun C hmem => by
        simp at hmem ⊢
        rcases hmem with ⟨G, hG, rfl⟩
        exact ⟨G, hsub G hG, rfl⟩
  | .allNatLtElim n A witness forallD ltD =>
      .allNatLtElim n A witness (forallD.weakenBy hsub) (ltD.weakenBy hsub)
  | .existsNatLtIntro n A witness child =>
      .existsNatLtIntro n A witness <| child.weakenBy fun C hmem => by
        simp at hmem ⊢
        rcases hmem with ⟨G, hG, rfl⟩
        exact ⟨G, hsub G hG, rfl⟩

def weakenContext {arity : Nat} {Γ : List (SFormula arity)} {A B : SFormula arity} :
    Deriv Γ A -> Deriv (B :: Γ) A :=
  weakenBy (fun _ h => List.mem_cons_of_mem _ h)

def check {arity : Nat} {Γ : List (SFormula arity)} {A : SFormula arity} :
    Deriv Γ A -> Bool
  | .hyp _ => true
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
  | .allNatLtIntro _ _ child => child.check
  | .allNatLtElim _ _ _ forallD ltD => forallD.check && ltD.check
  | .existsNatLtIntro _ _ _ child => child.check

def size {arity : Nat} {Γ : List (SFormula arity)} {A : SFormula arity} :
    Deriv Γ A -> Nat
  | .hyp _ => 1
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
  | .allNatLtIntro _ _ child => 1 + child.size
  | .allNatLtElim _ _ _ forallD ltD => 1 + forallD.size + ltD.size
  | .existsNatLtIntro _ _ _ child => 1 + child.size

def FormulaDefined {arity : Nat} (codeBody : Term 2 .stab) (fuel : Nat)
    (rho : Env arity) (E : PartialStabilizer) (A : SFormula arity) : Prop :=
  exists b, A.eval codeBody fuel rho E = some b

def DefinedObligations {arity : Nat} {Γ : List (SFormula arity)} {A : SFormula arity}
    (D : Deriv Γ A) (codeBody : Term 2 .stab) (fuel : Nat)
    (rho : Env arity) (E : PartialStabilizer) : Prop :=
  match D with
  | .hyp _ => True
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
  | .allNatLtIntro (Γ := Γ) n _ child =>
      exists bound, n.eval codeBody fuel rho E = some bound /\
        forall x, x < bound ->
          child.DefinedObligations codeBody fuel (Env.cons x rho) E /\
            ContextHolds codeBody fuel (Env.cons x rho) E
              (Γ.map (fun G => G.weaken))
  | .allNatLtElim _ _ _ forallD ltD =>
      forallD.DefinedObligations codeBody fuel rho E /\
        ltD.DefinedObligations codeBody fuel rho E
  | .existsNatLtIntro (Γ := Γ) n A witness child =>
      exists bound, n.eval codeBody fuel rho E = some bound /\
        witness < bound /\
          (forall x, x < bound ->
            FormulaDefined codeBody fuel (Env.cons x rho) E A) /\
            child.DefinedObligations codeBody fuel (Env.cons witness rho) E /\
              ContextHolds codeBody fuel (Env.cons witness rho) E
                (Γ.map (fun G => G.weaken))

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
  | allNatLtIntro n A child ih =>
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
  | existsNatLtIntro n A witness child ih =>
      intro hdef _
      rcases hdef with ⟨bound, hbound, hwitness, htotal, hChildDef, hChildCtx⟩
      simp [SFormula.eval, hbound]
      exact existsNatLt_complete htotal ⟨witness, hwitness, ih hChildDef hChildCtx⟩

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

def boundedTopWitnessLt : SFormula 0 :=
  SFormula.witnessLt (SC.n (arity := 0) 1) (SC.n (arity := 0) 2)

/-- Bounded universal elimination is a two-premise syntactic rule:
    the universal proof plus a proof of the object-language bound side
    condition.  This smoke proof deliberately supplies the side condition as
    an assumption, not as a semantic leaf. -/
def boundedTopElimDeriv :
    SFormula.Deriv [boundedTopWitnessLt]
      (.applyNat (SC.n (arity := 0) 1) (SFormula.top (arity := 1))) :=
  .allNatLtElim (SC.n (arity := 0) 2) (SFormula.top (arity := 1))
    (SC.n (arity := 0) 1)
    (boundedTopDeriv.weakenContext)
    .assumption

/-- Right disjunction introduction is a real checked rule, not a semantic leaf. -/
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

/-- info: 2 -/
#guard_msgs in
#eval boundedTopDeriv.size

#print axioms STerm.eval
#print axioms SFormula.eval
#print axioms SFormula.Deriv.sound
#print axioms ForallStabFormula.holds
#print axioms ForallStabFormula.checkClosedInstance
#print axioms ForallStabDeriv.sound

end StabBinder

end QHL.CodeLang
