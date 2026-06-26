import QStab.QHL.Assertion.Semantics
import QStab.Step

/-! # Syntactic state substitution for QHL formulas

`StateSubst` rewrites the dynamic state symbols currently present in the deep
language: remaining budget, error flow, and measurement coordinate. Each
substitution carries its semantic state transformer and proofs that the term
rewrites denote the corresponding updated fields.
-/

namespace QHL.AssertionLang

open QStab

/-- A certified rewrite of the dynamic state symbols in QHL terms. -/
structure StateSubst (P : QECParams) where
  remaining : {Γ : List (Ty P)} -> Term P Γ .nat
  error : {Γ : List (Ty P)} -> Term P Γ .vec
  current : {Γ : List (Ty P)} -> Term P Γ .coord
  apply : State P -> State P
  eval_remaining : forall {Γ} (ρ : Env Γ) (σ : State P),
    Term.eval remaining ρ σ = (apply σ).C
  eval_error : forall {Γ} (ρ : Env Γ) (σ : State P),
    Term.eval error ρ σ = (apply σ).E_tilde
  eval_current : forall {Γ} (ρ : Env Γ) (σ : State P),
    Term.eval current ρ σ = (apply σ).coord

/-- Rewrite every dynamic state occurrence in a term. -/
def Term.substState {P : QECParams} {Γ : List (Ty P)} {s : Ty P} (θ : StateSubst P) :
    Term P Γ s -> Term P Γ s
  | .var v => .var v
  | .boolLit b => .boolLit b
  | .natLit n => .natLit n
  | .pauliLit p => .pauliLit p
  | .qubitLit q => .qubitLit q
  | .stabLit i => .stabLit i
  | .roundLit r => .roundLit r
  | .coordLit c => .coordLit c
  | .vecLit E => .vecLit E
  | .budget => .budget
  | .remaining => θ.remaining
  | .error => θ.error
  | .current => θ.current
  | .detector k => .detector (k.substState θ)
  | .coordNext c => .coordNext (c.substState θ)
  | .coordStab c => .coordStab (c.substState θ)
  | .scheduledStab prog c => .scheduledStab prog (c.substState θ)
  | .coordRound c => .coordRound (c.substState θ)
  | .natAdd a b => .natAdd (a.substState θ) (b.substState θ)
  | .natSub a b => .natSub (a.substState θ) (b.substState θ)
  | .boolNot b => .boolNot (b.substState θ)
  | .boolXor a b => .boolXor (a.substState θ) (b.substState θ)
  | .ite c t e => .ite (c.substState θ) (t.substState θ) (e.substState θ)
  | .identity => .identity
  | .vecMul a b => .vecMul (a.substState θ) (b.substState θ)
  | .vecUpdate E q p => .vecUpdate (E.substState θ) (q.substState θ) (p.substState θ)
  | .vecAt E q => .vecAt (E.substState θ) (q.substState θ)
  | .weight E => .weight (E.substState θ)
  | .parity a b => .parity (a.substState θ) (b.substState θ)
  | .hasX p => .hasX (p.substState θ)
  | .stabMaskProduct mask => .stabMaskProduct (mask.substState θ)
  | .stabilizer i => .stabilizer (i.substState θ)
  | .familyStabilizer F i => .familyStabilizer F (i.substState θ)
  | .scheduleActive S i slot => .scheduleActive S (i.substState θ) (slot.substState θ)
  | .scheduleQubit S i slot => .scheduleQubit S (i.substState θ) (slot.substState θ)
  | .schedulePauli S i slot => .schedulePauli S (i.substState θ) (slot.substState θ)
  | .namedVec v => .namedVec v
  | .cut g i => .cut g (i.substState θ)
  | .barrier b E => .barrier b (E.substState θ)

/-- Rewrite every dynamic state occurrence in a formula. -/
def Formula.substState {P : QECParams} {Γ : List (Ty P)} (θ : StateSubst P) :
    Formula P Γ -> Formula P Γ
  | .top => .top
  | .bot => .bot
  | .eq a b => .eq (a.substState θ) (b.substState θ)
  | .le a b => .le (a.substState θ) (b.substState θ)
  | .lt a b => .lt (a.substState θ) (b.substState θ)
  | .and A B => .and (A.substState θ) (B.substState θ)
  | .or A B => .or (A.substState θ) (B.substState θ)
  | .imp A B => .imp (A.substState θ) (B.substState θ)
  | .not A => .not (A.substState θ)
  | .all s A => .all s (A.substState θ)
  | .exists s A => .exists s (A.substState θ)
  | .inStab E => .inStab (E.substState θ)
  | .logicalMember L E => .logicalMember L (E.substState θ)
  | .logicalSetMember L E => .logicalSetMember L (E.substState θ)
  | .backAction i E => .backAction (i.substState θ) (E.substState θ)
  | .inGroup g q i => .inGroup g (q.substState θ) (i.substState θ)
  | .nextCoord c n => .nextCoord (c.substState θ) (n.substState θ)

/-- The fundamental term-substitution theorem. -/
theorem Term.eval_substState {P : QECParams} {Γ : List (Ty P)} {s : Ty P}
    (θ : StateSubst P)
    (t : Term P Γ s) (ρ : Env Γ) (σ : State P) :
    (t.substState θ).eval ρ σ = t.eval ρ (θ.apply σ) := by
  induction t <;> simp only [Term.substState, Term.eval, *]
  · exact θ.eval_remaining ρ σ
  · exact θ.eval_error ρ σ
  · exact θ.eval_current ρ σ

/-- The fundamental formula-substitution theorem. -/
theorem Formula.eval_substState {P : QECParams} {Γ : List (Ty P)} (θ : StateSubst P)
    (A : Formula P Γ) (ρ : Env Γ) (σ : State P) :
    (A.substState θ).eval ρ σ <-> A.eval ρ (θ.apply σ) := by
  induction A <;>
    simp only [Formula.substState, Formula.eval, Term.eval_substState, *]

namespace StateSubst

/-- Program-independent syntactic update for a Type-0 data fault. -/
def err0 {P : QECParams} (i : Fin P.n) (p : Pauli) : StateSubst P where
  remaining := .natSub .remaining (.natLit 1)
  error := .vecUpdate .error (.qubitLit i) (.pauliLit p)
  current := .current
  apply := fun σ => { σ with
    C := σ.C - 1
    cnt0 := σ.cnt0 + 1
    lam_E := σ.lam_E + 1
    E_tilde := ErrorVec.update σ.E_tilde i p }
  eval_remaining := by intros; rfl
  eval_error := by intros; rfl
  eval_current := by intros; rfl

/-- Program-indexed syntactic update for a type-1 fault. -/
def errI {P : QECParams} (prog : QStabProgram P) (i : Fin P.n) (p : Pauli)
    (mf : Bool) : StateSubst P where
  remaining := .natSub .remaining (.natLit 1)
  error := .vecUpdate .error (.qubitLit i) (.pauliLit p)
  current := .current
  apply := fun σ => { σ with
    C := σ.C - 1
    cnt1 := σ.cnt1 + 1
    lam_E := σ.lam_E + 1
    E_tilde := ErrorVec.update σ.E_tilde i p
    G := fun x y =>
      if mf && x = currentStab prog σ && y = σ.coord.y then !σ.G x y else σ.G x y }
  eval_remaining := by intros; rfl
  eval_error := by intros; rfl
  eval_current := by intros; rfl

/-- Program-indexed syntactic update for a type-2 back-action fault. -/
def errII {P : QECParams} (prog : QStabProgram P) (e : ErrorVec P.n)
    (mf : Bool) : StateSubst P where
  remaining := .natSub .remaining (.natLit 1)
  error := .vecMul (.vecLit e) .error
  current := .current
  apply := fun σ => { σ with
    C := σ.C - 1
    cnt2 := σ.cnt2 + 1
    lam_E := σ.lam_E + ErrorVec.weight e
    E_tilde := ErrorVec.mul e σ.E_tilde
    G := fun x y =>
      if mf && x = currentStab prog σ && y = σ.coord.y then !σ.G x y else σ.G x y
    F := fun j => if j = currentStab prog σ then
      xor (xor (σ.F j) (ErrorVec.parity (P.stabilizers (currentStab prog σ)) e))
        (if mf then true else false)
      else σ.F j }
  eval_remaining := by intros; rfl
  eval_error := by intros; rfl
  eval_current := by intros; rfl

/-- Program-indexed syntactic update for a type-3 measurement-bit fault. -/
def errIII {P : QECParams} (prog : QStabProgram P) : StateSubst P where
  remaining := .natSub .remaining (.natLit 1)
  error := .error
  current := .current
  apply := fun σ => { σ with
    C := σ.C - 1
    cnt3 := σ.cnt3 + 1
    G := fun x y =>
      if x = currentStab prog σ ∧ y = σ.coord.y then !σ.G x y else σ.G x y }
  eval_remaining := by intros; rfl
  eval_error := by intros; rfl
  eval_current := by intros; rfl

/-- Program-indexed syntactic update for a measurement. -/
def measFor {P : QECParams} (prog : QStabProgram P) : StateSubst P where
  remaining := .remaining
  error := .error
  current := .coordNext .current
  apply := fun σ => measureStep prog σ (σ.coord.next.getD σ.coord)
  eval_remaining := by intros; rfl
  eval_error := by intros; rfl
  eval_current := by intros; rfl

end StateSubst

/-- Syntactic weakest precondition for Type-0 data faults. -/
def Formula.wpErr0 {P : QECParams} (i : Fin P.n) (p : Pauli) (Q : Formula P []) :
    Formula P [] :=
  .imp (.lt (.natLit 0) .remaining) (Q.substState (StateSubst.err0 i p))

/-- Syntactic weakest precondition for program-indexed Type-I faults. -/
def Formula.wpErrI {P : QECParams} (prog : QStabProgram P)
    (i : Fin P.n) (p : Pauli) (mf : Bool) (Q : Formula P []) : Formula P [] :=
  .imp (.lt (.natLit 0) .remaining) (Q.substState (StateSubst.errI prog i p mf))

/-- Syntactic weakest precondition for program-indexed Type-II faults. -/
def Formula.wpErrII {P : QECParams} (prog : QStabProgram P)
    (e : ErrorVec P.n) (mf : Bool) (Q : Formula P []) : Formula P [] :=
  .imp (.backAction (.scheduledStab prog .current) (.vecLit e))
    (.imp (.lt (.natLit 0) .remaining) (Q.substState (StateSubst.errII prog e mf)))

/-- Syntactic weakest precondition for program-indexed Type-III faults. -/
def Formula.wpErrIII {P : QECParams} (prog : QStabProgram P) (Q : Formula P []) :
    Formula P [] :=
  .imp (.lt (.natLit 0) .remaining) (Q.substState (StateSubst.errIII prog))

/-- Syntactic weakest precondition for program-indexed measurement. -/
def Formula.wpMeasFor {P : QECParams} (prog : QStabProgram P) (Q : Formula P []) :
    Formula P [] :=
  Q.substState (StateSubst.measFor prog)

end QHL.AssertionLang
