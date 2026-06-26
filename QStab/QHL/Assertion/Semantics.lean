import QStab.QHL.Assertion.Syntax

/-! # Semantics of deep QHL assertions -/

namespace QHL.AssertionLang

open QStab

/-- Environments for intrinsically sorted bound variables. -/
def Env {P : QECParams} (Γ : List (Ty P)) : Type :=
  {s : Ty P} -> Var Γ s -> s.denote

namespace Env

/-- The unique environment for a closed term or formula. -/
def empty {P : QECParams} : Env (P := P) [] := fun {_} v => nomatch v

/-- Extend an environment below one binder. -/
def extend {P : QECParams} {Γ : List (Ty P)} {s : Ty P} (ρ : Env Γ) (x : s.denote) :
    Env (s :: Γ)
  | _, .zero => x
  | _, .succ v => ρ v

end Env

/-- Backend interpreting the dynamic fields of the shared assertion language.

The syntax of stabilizer/logical/barrier assertions is shared.  A backend says
how dynamic state symbols such as the current residual error, spent fault
count, remaining budget, and detector log are read from a concrete semantic
state. -/
structure AssertionBackend (P : QECParams) (StateTy : Type) where
  error : StateTy -> ErrorVec P.n
  spent : StateTy -> Nat
  remaining : StateTy -> Nat
  budget : Nat
  current : StateTy -> QECParams.Coord P
  detector : Nat -> StateTy -> Bool

/-- The original QStab interpretation as an `AssertionBackend`. -/
def qstabBackend (P : QECParams) : AssertionBackend P (State P) where
  error := fun σ => σ.E_tilde
  spent := fun σ => State.totalErrors σ
  remaining := fun σ => σ.C
  budget := P.C_budget
  current := fun σ => σ.coord
  detector := fun _ _ => false

/-- Product of the stabilizer generators selected by a Boolean mask. -/
def stabilizerProduct (P : QECParams) (mask : Fin P.numStab -> Bool) : ErrorVec P.n :=
  (List.finRange P.numStab).foldl
    (fun acc i => if mask i then ErrorVec.mul (P.stabilizers i) acc else acc)
    (ErrorVec.identity P.n)

/-- Whether an error has a finite generator-mask witness. -/
def generatedByStabilizers (P : QECParams) (E : ErrorVec P.n) : Prop :=
  exists mask : Fin P.numStab -> Bool, E = stabilizerProduct P mask

/-- Whether a single-qubit Pauli has an X component. -/
def pauliHasX : Pauli -> Bool
  | .X | .Y => true
  | .I | .Z => false

/-- Semantics of intrinsically typed terms. -/
noncomputable def Term.eval {P : QECParams} {Γ : List (Ty P)} {s : Ty P} :
    Term P Γ s -> Env Γ -> State P -> s.denote
  | .var v, ρ, _ => ρ v
  | .boolLit b, _, _ => b
  | .natLit n, _, _ => n
  | .pauliLit p, _, _ => p
  | .qubitLit q, _, _ => q
  | .stabLit i, _, _ => i
  | .roundLit r, _, _ => r
  | .coordLit c, _, _ => c
  | .vecLit E, _, _ => E
  | .budget, _, _ => P.C_budget
  | .remaining, _, σ => σ.C
  | .error, _, σ => σ.E_tilde
  | .current, _, σ => σ.coord
  | .detector _, _, _ => false
  | .coordNext c, ρ, σ => (c.eval ρ σ).next.getD (c.eval ρ σ)
  | .coordStab c, ρ, σ => (c.eval ρ σ).x
  | .scheduledStab prog c, ρ, σ => prog.currentStab (c.eval ρ σ)
  | .coordRound c, ρ, σ => (c.eval ρ σ).y
  | .natAdd a b, ρ, σ => Nat.add (a.eval ρ σ) (b.eval ρ σ)
  | .natSub a b, ρ, σ => Nat.sub (a.eval ρ σ) (b.eval ρ σ)
  | .boolNot b, ρ, σ => !(b.eval ρ σ)
  | .boolXor a b, ρ, σ => xor (a.eval ρ σ) (b.eval ρ σ)
  | .ite c t e, ρ, σ => bif c.eval ρ σ then t.eval ρ σ else e.eval ρ σ
  | .identity, _, _ => ErrorVec.identity P.n
  | .vecMul a b, ρ, σ => ErrorVec.mul (a.eval ρ σ) (b.eval ρ σ)
  | .vecUpdate E q p, ρ, σ => ErrorVec.update (E.eval ρ σ) (q.eval ρ σ) (p.eval ρ σ)
  | .vecAt E q, ρ, σ => E.eval ρ σ (q.eval ρ σ)
  | .weight E, ρ, σ => ErrorVec.weight (E.eval ρ σ)
  | .parity a b, ρ, σ => ErrorVec.parity (a.eval ρ σ) (b.eval ρ σ)
  | .hasX p, ρ, σ => pauliHasX (p.eval ρ σ)
  | .stabMaskProduct mask, ρ, σ => maskStabilizerProduct P (mask.eval ρ σ)
  | .stabilizer i, ρ, σ => P.stabilizers (i.eval ρ σ)
  | .familyStabilizer F i, ρ, σ => F.eval (i.eval ρ σ)
  | .scheduleActive S i slot, ρ, σ => S.isActive (i.eval ρ σ) (slot.eval ρ σ)
  | .scheduleQubit S i slot, ρ, σ => S.scheduledQubit (i.eval ρ σ) (slot.eval ρ σ)
  | .schedulePauli S i slot, ρ, σ => S.scheduledPauli (i.eval ρ σ) (slot.eval ρ σ)
  | .namedVec v, _, _ => v.eval
  | .cut g i, ρ, σ => g.cut (i.eval ρ σ)
  | .barrier b E, ρ, σ => b.eval (E.eval ρ σ)

/-- Backend-parametric semantics of terms.  This is the shared interpretation
used by QStab and QClifford VC generation. -/
noncomputable def Term.evalWith {P : QECParams} {StateTy : Type} (B : AssertionBackend P StateTy)
    {Γ : List (Ty P)} {s : Ty P} :
    Term P Γ s -> Env Γ -> StateTy -> s.denote
  | .var v, ρ, _ => ρ v
  | .boolLit b, _, _ => b
  | .natLit n, _, _ => n
  | .pauliLit p, _, _ => p
  | .qubitLit q, _, _ => q
  | .stabLit i, _, _ => i
  | .roundLit r, _, _ => r
  | .coordLit c, _, _ => c
  | .vecLit E, _, _ => E
  | .budget, _, _ => B.budget
  | .remaining, _, σ => B.remaining σ
  | .error, _, σ => B.error σ
  | .current, _, σ => B.current σ
  | .detector k, ρ, σ => B.detector (k.evalWith B ρ σ) σ
  | .coordNext c, ρ, σ => (c.evalWith B ρ σ).next.getD (c.evalWith B ρ σ)
  | .coordStab c, ρ, σ => (c.evalWith B ρ σ).x
  | .scheduledStab prog c, ρ, σ => prog.currentStab (c.evalWith B ρ σ)
  | .coordRound c, ρ, σ => (c.evalWith B ρ σ).y
  | .natAdd a b, ρ, σ => Nat.add (a.evalWith B ρ σ) (b.evalWith B ρ σ)
  | .natSub a b, ρ, σ => Nat.sub (a.evalWith B ρ σ) (b.evalWith B ρ σ)
  | .boolNot b, ρ, σ => !(b.evalWith B ρ σ)
  | .boolXor a b, ρ, σ => xor (a.evalWith B ρ σ) (b.evalWith B ρ σ)
  | .ite c t e, ρ, σ => bif c.evalWith B ρ σ then t.evalWith B ρ σ else e.evalWith B ρ σ
  | .identity, _, _ => ErrorVec.identity P.n
  | .vecMul a b, ρ, σ => ErrorVec.mul (a.evalWith B ρ σ) (b.evalWith B ρ σ)
  | .vecUpdate E q p, ρ, σ => ErrorVec.update (E.evalWith B ρ σ) (q.evalWith B ρ σ)
      (p.evalWith B ρ σ)
  | .vecAt E q, ρ, σ => E.evalWith B ρ σ (q.evalWith B ρ σ)
  | .weight E, ρ, σ => ErrorVec.weight (E.evalWith B ρ σ)
  | .parity a b, ρ, σ => ErrorVec.parity (a.evalWith B ρ σ) (b.evalWith B ρ σ)
  | .hasX p, ρ, σ => pauliHasX (p.evalWith B ρ σ)
  | .stabMaskProduct mask, ρ, σ => maskStabilizerProduct P (mask.evalWith B ρ σ)
  | .stabilizer i, ρ, σ => P.stabilizers (i.evalWith B ρ σ)
  | .familyStabilizer F i, ρ, σ => F.eval (i.evalWith B ρ σ)
  | .scheduleActive S i slot, ρ, σ => S.isActive (i.evalWith B ρ σ) (slot.evalWith B ρ σ)
  | .scheduleQubit S i slot, ρ, σ => S.scheduledQubit (i.evalWith B ρ σ)
      (slot.evalWith B ρ σ)
  | .schedulePauli S i slot, ρ, σ => S.scheduledPauli (i.evalWith B ρ σ)
      (slot.evalWith B ρ σ)
  | .namedVec v, _, _ => v.eval
  | .cut g i, ρ, σ => g.cut (i.evalWith B ρ σ)
  | .barrier b E, ρ, σ => b.eval (E.evalWith B ρ σ)

/-- Satisfaction semantics of QHL formulas. -/
noncomputable def Formula.eval {P : QECParams} {Γ : List (Ty P)} :
    Formula P Γ -> Env Γ -> State P -> Prop
  | .top, _, _ => True
  | .bot, _, _ => False
  | .eq a b, ρ, σ => a.eval ρ σ = b.eval ρ σ
  | .le a b, ρ, σ => Nat.le (a.eval ρ σ) (b.eval ρ σ)
  | .lt a b, ρ, σ => Nat.lt (a.eval ρ σ) (b.eval ρ σ)
  | .and A B, ρ, σ => A.eval ρ σ /\ B.eval ρ σ
  | .or A B, ρ, σ => A.eval ρ σ \/ B.eval ρ σ
  | .imp A B, ρ, σ => A.eval ρ σ -> B.eval ρ σ
  | .not A, ρ, σ => Not (A.eval ρ σ)
  | .all s A, ρ, σ => forall x : s.denote, A.eval (ρ.extend x) σ
  | .exists s A, ρ, σ => exists x : s.denote, A.eval (ρ.extend x) σ
  | .inStab E, ρ, σ => generatedByStabilizers P (E.eval ρ σ)
  | .logicalMember L E, ρ, σ => L.contains (E.eval ρ σ)
  | .logicalSetMember L E, ρ, σ => L.contains (E.eval ρ σ)
  | .backAction i E, ρ, σ => E.eval ρ σ ∈ P.backActionSet (i.eval ρ σ)
  | .inGroup g q i, ρ, σ => g.groupOf (q.eval ρ σ) = some (i.eval ρ σ)
  | .nextCoord c n, ρ, σ => QECParams.Coord.next (c.eval ρ σ) = some (n.eval ρ σ)

/-- Backend-parametric satisfaction semantics. -/
noncomputable def Formula.evalWith {P : QECParams} {StateTy : Type}
    (B : AssertionBackend P StateTy) {Γ : List (Ty P)} :
    Formula P Γ -> Env Γ -> StateTy -> Prop
  | .top, _, _ => True
  | .bot, _, _ => False
  | .eq a b, ρ, σ => a.evalWith B ρ σ = b.evalWith B ρ σ
  | .le a b, ρ, σ => Nat.le (a.evalWith B ρ σ) (b.evalWith B ρ σ)
  | .lt a b, ρ, σ => Nat.lt (a.evalWith B ρ σ) (b.evalWith B ρ σ)
  | .and A C, ρ, σ => A.evalWith B ρ σ /\ C.evalWith B ρ σ
  | .or A C, ρ, σ => A.evalWith B ρ σ \/ C.evalWith B ρ σ
  | .imp A C, ρ, σ => A.evalWith B ρ σ -> C.evalWith B ρ σ
  | .not A, ρ, σ => Not (A.evalWith B ρ σ)
  | .all s A, ρ, σ => forall x : s.denote, A.evalWith B (ρ.extend x) σ
  | .exists s A, ρ, σ => exists x : s.denote, A.evalWith B (ρ.extend x) σ
  | .inStab E, ρ, σ => generatedByStabilizers P (E.evalWith B ρ σ)
  | .logicalMember L E, ρ, σ => L.contains (E.evalWith B ρ σ)
  | .logicalSetMember L E, ρ, σ => L.contains (E.evalWith B ρ σ)
  | .backAction i E, ρ, σ => E.evalWith B ρ σ ∈ P.backActionSet (i.evalWith B ρ σ)
  | .inGroup g q i, ρ, σ => g.groupOf (q.evalWith B ρ σ) = some (i.evalWith B ρ σ)
  | .nextCoord c n, ρ, σ => QECParams.Coord.next (c.evalWith B ρ σ) =
      some (n.evalWith B ρ σ)

/-- A closed formula denotes a semantic assertion on QStab states. -/
noncomputable def Formula.denote {P : QECParams} (A : Formula P []) : State P -> Prop :=
  fun σ => A.eval Env.empty σ

/-- A closed formula denotes an assertion over any backend state. -/
noncomputable def Formula.denoteWith {P : QECParams} {StateTy : Type}
    (B : AssertionBackend P StateTy) (A : Formula P []) : StateTy -> Prop :=
  fun σ => A.evalWith B Env.empty σ

theorem Term.evalWith_qstabBackend {P : QECParams} {Γ : List (Ty P)} {s : Ty P}
    (t : Term P Γ s) (ρ : Env Γ) (σ : State P) :
    t.evalWith (qstabBackend P) ρ σ = t.eval ρ σ := by
  induction t <;> simp [Term.evalWith, Term.eval, *]
  all_goals simp [qstabBackend]

theorem Formula.evalWith_qstabBackend {P : QECParams} {Γ : List (Ty P)}
    (A : Formula P Γ) (ρ : Env Γ) (σ : State P) :
    A.evalWith (qstabBackend P) ρ σ ↔ A.eval ρ σ := by
  induction A <;> simp [Formula.evalWith, Formula.eval, Term.evalWith_qstabBackend, *]

theorem Formula.denoteWith_qstabBackend {P : QECParams} (A : Formula P []) :
    A.denoteWith (qstabBackend P) = A.denote := by
  funext σ
  exact propext (A.evalWith_qstabBackend Env.empty σ)

/-- Semantic entailment between closed formulas. -/
def Formula.Entails {P : QECParams} (A B : Formula P []) : Prop :=
  forall σ, A.denote σ -> B.denote σ

/-- Validity of a closed formula in every QStab state. -/
def Formula.Valid {P : QECParams} (A : Formula P []) : Prop :=
  forall σ, A.denote σ

/-- Every well-formed stabilizer-family symbol validates its generic agreement
    formula. The proof obligation lives in the symbol, while the stabilizer
    generator itself is recursive syntax. -/
theorem stabilizerFamilyAgreementF_valid {P : QECParams}
    (F : StabilizerFamilySymbol P) :
    (stabilizerFamilyAgreementF F).Valid := by
  intro σ k
  exact F.agrees k

end QHL.AssertionLang
