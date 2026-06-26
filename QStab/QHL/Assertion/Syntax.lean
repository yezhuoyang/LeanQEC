import QStab.Program

/-! # Deep syntax for QHL assertions

This module defines the typed first-order core of the QHL assertion language.
The existing `QHL.Assertion` type remains the semantic compatibility layer
`State P -> Prop`; a closed `Formula P []` is interpreted as such an assertion
in `Semantics.lean`.

The syntax separates dynamic state terms (`C`, `error`) from static QEC theory
symbols (stabilizer families, logical classes, geometry, schedules, and barriers).
Code-specific mathematics therefore enters a certificate through named symbols,
not through an arbitrary Lean predicate hidden inside an assertion.
-/

namespace QHL.AssertionLang

open QStab

/-- Sorts available to QHL assertions. Natural-number quantification should be
    introduced through an explicitly bounded derived form; the core does not
    provide an unbounded `Nat` quantifier. -/
inductive Ty (P : QECParams) where
  | bool
  | nat
  | pauli
  | qubit
  | stab
  | round
  | coord
  | vec
  | stabMask
  | group (d : Nat)

/-- Lean interpretation of an assertion-language sort. -/
def Ty.denote {P : QECParams} : Ty P -> Type
  | .bool => Bool
  | .nat => Nat
  | .pauli => Pauli
  | .qubit => Fin P.n
  | .stab => Fin P.numStab
  | .round => Fin P.R
  | .coord => QECParams.Coord P
  | .vec => ErrorVec P.n
  | .stabMask => Fin P.numStab -> Bool
  | .group d => Fin d

/-- Intrinsically sorted de Bruijn variables. -/
inductive Var {P : QECParams} : List (Ty P) -> Ty P -> Type where
  | zero : Var (s :: Γ) s
  | succ : Var Γ s -> Var (t :: Γ) s

/-- Environments for closed, static code-family expressions. These expressions
    cannot inspect the dynamic QStab execution state. -/
def StaticEnv {P : QECParams} (Ctx : List (Ty P)) : Type :=
  {s : Ty P} -> Var Ctx s -> s.denote

namespace StaticEnv

/-- The unique environment for a closed static expression. -/
def empty {P : QECParams} : StaticEnv (P := P) [] := fun {_} v => nomatch v

/-- Extend a static environment below one binder. -/
def extend {P : QECParams} {Ctx : List (Ty P)} {s : Ty P}
    (rho : StaticEnv Ctx) (x : s.denote) : StaticEnv (s :: Ctx)
  | _, .zero => x
  | _, .succ v => rho v

end StaticEnv

/-! ## Tiny integer-indexed kernel

The following kernel is deliberately smaller than `FamilyTerm`: it only has
natural-number variables, Booleans, and Pauli literals. Code-family objects
such as logical operators and stabilizer rows are derived by interpreting a
kernel Pauli program at a qubit index, or at a stabilizer index plus qubit
index. This is the extraction-facing core: Surface/HGP/LDPC structure should
live in programs over this kernel, not in new assertion-language primitives.
-/

/-- Sorts in the tiny static kernel. -/
inductive KernelTy where
  | nat
  | bool
  | pauli

namespace KernelTy

/-- Interpret a tiny-kernel sort as a Lean type. -/
def denote : KernelTy -> Type
  | .nat => Nat
  | .bool => Bool
  | .pauli => Pauli

/-- Embed tiny-kernel sorts into QHL's static family-expression sorts. -/
def toTy (P : QECParams) : KernelTy -> Ty P
  | .nat => .nat
  | .bool => .bool
  | .pauli => .pauli

end KernelTy

/-- Environments for tiny-kernel programs: every variable is just an integer. -/
def KernelEnv (arity : Nat) : Type :=
  Fin arity -> Nat

namespace KernelEnv

/-- Empty tiny-kernel environment. -/
def empty : KernelEnv 0 := fun i => nomatch i

/-- Add one head integer variable to a tiny-kernel environment. -/
def cons {arity : Nat} (x : Nat) (rho : KernelEnv arity) : KernelEnv (arity + 1)
  | ⟨0, _⟩ => x
  | ⟨n + 1, h⟩ => rho ⟨n, Nat.lt_of_succ_lt_succ h⟩

end KernelEnv

/-- Tiny state-free programs over integer variables. -/
inductive KernelTerm (arity : Nat) : KernelTy -> Type where
  | var : Fin arity -> KernelTerm arity .nat
  | natLit : Nat -> KernelTerm arity .nat
  | boolLit : Bool -> KernelTerm arity .bool
  | pauliLit : Pauli -> KernelTerm arity .pauli
  | pauliLookup2 : Pauli -> List ((Nat × Nat) × Pauli) ->
      KernelTerm arity .nat -> KernelTerm arity .nat -> KernelTerm arity .pauli
  | natAdd : KernelTerm arity .nat -> KernelTerm arity .nat -> KernelTerm arity .nat
  | natSub : KernelTerm arity .nat -> KernelTerm arity .nat -> KernelTerm arity .nat
  | natMul : KernelTerm arity .nat -> KernelTerm arity .nat -> KernelTerm arity .nat
  | natDiv : KernelTerm arity .nat -> KernelTerm arity .nat -> KernelTerm arity .nat
  | natMod : KernelTerm arity .nat -> KernelTerm arity .nat -> KernelTerm arity .nat
  | natEq : KernelTerm arity .nat -> KernelTerm arity .nat -> KernelTerm arity .bool
  | natLe : KernelTerm arity .nat -> KernelTerm arity .nat -> KernelTerm arity .bool
  | natLt : KernelTerm arity .nat -> KernelTerm arity .nat -> KernelTerm arity .bool
  | boolNot : KernelTerm arity .bool -> KernelTerm arity .bool
  | boolAnd : KernelTerm arity .bool -> KernelTerm arity .bool -> KernelTerm arity .bool
  | boolOr : KernelTerm arity .bool -> KernelTerm arity .bool -> KernelTerm arity .bool
  | boolXor : KernelTerm arity .bool -> KernelTerm arity .bool -> KernelTerm arity .bool
  | ite : KernelTerm arity .bool -> KernelTerm arity s -> KernelTerm arity s ->
      KernelTerm arity s

/-- Static code-family expressions used to describe parametric stabilizers.

    This is intentionally state-free and recursive. It can express a stabilizer
    row by arithmetic on the stabilizer index, arithmetic on the qubit index,
    conditionals, vector updates/products, and finite folds over all data
    qubits. LDPC families should normally use a `StabilizerBody.byEntry`
    expression whose result is `I` off the row's sparse support. -/
inductive FamilyTerm (P : QECParams) : List (Ty P) -> Ty P -> Type where
  | var : Var Ctx s -> FamilyTerm P Ctx s
  | boolLit : Bool -> FamilyTerm P Ctx .bool
  | natLit : Nat -> FamilyTerm P Ctx .nat
  | pauliLit : Pauli -> FamilyTerm P Ctx .pauli
  | pauliLookup2 : Pauli -> List ((Nat × Nat) × Pauli) ->
      FamilyTerm P Ctx .nat -> FamilyTerm P Ctx .nat -> FamilyTerm P Ctx .pauli
  | qubitLit : Fin P.n -> FamilyTerm P Ctx .qubit
  | stabLit : Fin P.numStab -> FamilyTerm P Ctx .stab
  | vecLit : ErrorVec P.n -> FamilyTerm P Ctx .vec
  | qubitVal : FamilyTerm P Ctx .qubit -> FamilyTerm P Ctx .nat
  | stabVal : FamilyTerm P Ctx .stab -> FamilyTerm P Ctx .nat
  | stabilizerAt : FamilyTerm P Ctx .stab -> FamilyTerm P Ctx .vec
  | natAdd : FamilyTerm P Ctx .nat -> FamilyTerm P Ctx .nat -> FamilyTerm P Ctx .nat
  | natSub : FamilyTerm P Ctx .nat -> FamilyTerm P Ctx .nat -> FamilyTerm P Ctx .nat
  | natMul : FamilyTerm P Ctx .nat -> FamilyTerm P Ctx .nat -> FamilyTerm P Ctx .nat
  | natDiv : FamilyTerm P Ctx .nat -> FamilyTerm P Ctx .nat -> FamilyTerm P Ctx .nat
  | natMod : FamilyTerm P Ctx .nat -> FamilyTerm P Ctx .nat -> FamilyTerm P Ctx .nat
  | natEq : FamilyTerm P Ctx .nat -> FamilyTerm P Ctx .nat -> FamilyTerm P Ctx .bool
  | natLe : FamilyTerm P Ctx .nat -> FamilyTerm P Ctx .nat -> FamilyTerm P Ctx .bool
  | natLt : FamilyTerm P Ctx .nat -> FamilyTerm P Ctx .nat -> FamilyTerm P Ctx .bool
  | boolNot : FamilyTerm P Ctx .bool -> FamilyTerm P Ctx .bool
  | boolAnd : FamilyTerm P Ctx .bool -> FamilyTerm P Ctx .bool -> FamilyTerm P Ctx .bool
  | boolOr : FamilyTerm P Ctx .bool -> FamilyTerm P Ctx .bool -> FamilyTerm P Ctx .bool
  | boolXor : FamilyTerm P Ctx .bool -> FamilyTerm P Ctx .bool -> FamilyTerm P Ctx .bool
  | ite : FamilyTerm P Ctx .bool -> FamilyTerm P Ctx s -> FamilyTerm P Ctx s ->
      FamilyTerm P Ctx s
  | identity : FamilyTerm P Ctx .vec
  | vecMul : FamilyTerm P Ctx .vec -> FamilyTerm P Ctx .vec -> FamilyTerm P Ctx .vec
  | vecUpdate : FamilyTerm P Ctx .vec -> FamilyTerm P Ctx .qubit ->
      FamilyTerm P Ctx .pauli -> FamilyTerm P Ctx .vec
  | vecAt : FamilyTerm P Ctx .vec -> FamilyTerm P Ctx .qubit -> FamilyTerm P Ctx .pauli
  | weight : FamilyTerm P Ctx .vec -> FamilyTerm P Ctx .nat
  | parity : FamilyTerm P Ctx .vec -> FamilyTerm P Ctx .vec -> FamilyTerm P Ctx .bool
  | hasX : FamilyTerm P Ctx .pauli -> FamilyTerm P Ctx .bool
  | foldQubits : FamilyTerm P Ctx .vec -> FamilyTerm P (.vec :: .qubit :: Ctx) .vec ->
      FamilyTerm P Ctx .vec

/-- Whether a single-qubit Pauli has an X component. Duplicated here so the
    static language can be interpreted without importing dynamic semantics. -/
def pauliHasXStatic : Pauli -> Bool
  | .X | .Y => true
  | .I | .Z => false

/-- Whether a single-qubit Pauli has a Z component.  This is the dual of
    `pauliHasXStatic`, used by column/Z-spread barriers. -/
def pauliHasZStatic : Pauli -> Bool
  | .Z | .Y => true
  | .I | .X => false

/-- Boolean natural-number `<=` for the static expression interpreter. -/
def natLeBool : Nat -> Nat -> Bool
  | 0, _ => true
  | _ + 1, 0 => false
  | a + 1, b + 1 => natLeBool a b

/-- Boolean natural-number `<` for the static expression interpreter. -/
def natLtBool : Nat -> Nat -> Bool
  | 0, 0 => false
  | 0, _ + 1 => true
  | _ + 1, 0 => false
  | a + 1, b + 1 => natLtBool a b

@[simp] theorem natLeBool_eq_decide (a b : Nat) :
    natLeBool a b = decide (a <= b) := by
  induction a generalizing b with
  | zero =>
      simp [natLeBool]
  | succ a ih =>
      cases b with
      | zero =>
          simp [natLeBool]
      | succ b =>
          simp [natLeBool, ih b, Nat.succ_le_succ_iff]

@[simp] theorem natLtBool_eq_decide (a b : Nat) :
    natLtBool a b = decide (a < b) := by
  induction a generalizing b with
  | zero =>
      cases b <;> simp [natLtBool]
  | succ a ih =>
      cases b with
      | zero =>
          simp [natLtBool]
      | succ b =>
          simp [natLtBool, ih b, Nat.succ_lt_succ_iff]

@[simp] theorem natBeq_eq_decide (a b : Nat) :
    Nat.beq a b = decide (a = b) := by
  induction a generalizing b with
  | zero =>
      cases b <;> simp [Nat.beq]
  | succ a ih =>
      cases b with
      | zero =>
          simp [Nat.beq]
      | succ b =>
          simp [Nat.beq, ih b]

/-- Prop-backed Boolean conjunction for static expressions. -/
def boolAndStatic (a b : Bool) : Bool :=
  decide (a = true /\ b = true)

/-- Prop-backed Boolean disjunction for static expressions. -/
def boolOrStatic (a b : Bool) : Bool :=
  decide (a = true \/ b = true)

@[simp] theorem boolAndStatic_decide (p q : Prop) [Decidable p] [Decidable q] :
    boolAndStatic (decide p) (decide q) = decide (p /\ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [boolAndStatic, hp, hq]

@[simp] theorem boolOrStatic_decide (p q : Prop) [Decidable p] [Decidable q] :
    boolOrStatic (decide p) (decide q) = decide (p \/ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [boolOrStatic, hp, hq]

@[simp] theorem bif_decide_eq_if {α : Sort u} (p : Prop) [Decidable p] (t e : α) :
    (bif decide p then t else e) = (if p then t else e) := by
  by_cases hp : p <;> simp [hp]

theorem bool_and_decide_eq_decide_and (p q : Prop) [Decidable p] [Decidable q] :
    (decide p && decide q) = decide (p /\ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem bool_or_decide_eq_decide_or (p q : Prop) [Decidable p] [Decidable q] :
    (decide p || decide q) = decide (p \/ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

@[simp] theorem bif_decide_and_decide_eq_if {α : Sort u}
    (p q : Prop) [Decidable p] [Decidable q] (t e : α) :
    (bif decide p && decide q then t else e) = (if p /\ q then t else e) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

@[simp] theorem bif_decide_or_decide_eq_if {α : Sort u}
    (p q : Prop) [Decidable p] [Decidable q] (t e : α) :
    (bif decide p || decide q then t else e) = (if p \/ q then t else e) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

@[simp] theorem bif_decide_and_or_decide_eq_if {α : Sort u}
    (p q r : Prop) [Decidable p] [Decidable q] [Decidable r] (t e : α) :
    (bif decide p && (decide q || decide r) then t else e) =
      (if p /\ (q \/ r) then t else e) := by
  by_cases hp : p <;> by_cases hq : q <;> by_cases hr : r <;> simp [hp, hq, hr]

@[simp] theorem bif_or_decide_and_or_decide_eq_if {α : Sort u}
    (p q r s : Prop) [Decidable p] [Decidable q] [Decidable r] [Decidable s] (t e : α) :
    (bif (decide p || decide q) && (decide r || decide s) then t else e) =
      (if (p \/ q) /\ (r \/ s) then t else e) := by
  by_cases hp : p <;> by_cases hq : q <;> by_cases hr : r <;> by_cases hs : s <;>
    simp [hp, hq, hr, hs]

@[simp] theorem boolAndStatic_decide_or_decide
    (p q r : Prop) [Decidable p] [Decidable q] [Decidable r] :
    boolAndStatic (decide p) (decide q || decide r) = decide (p /\ (q \/ r)) := by
  by_cases hp : p <;> by_cases hq : q <;> by_cases hr : r <;>
    simp [boolAndStatic, hp, hq, hr]

@[simp] theorem boolAndStatic_or_decide_decide
    (p q r : Prop) [Decidable p] [Decidable q] [Decidable r] :
    boolAndStatic (decide p || decide q) (decide r) = decide ((p \/ q) /\ r) := by
  by_cases hp : p <;> by_cases hq : q <;> by_cases hr : r <;>
    simp [boolAndStatic, hp, hq, hr]

@[simp] theorem boolAndStatic_or_decide_or_decide
    (p q r s : Prop) [Decidable p] [Decidable q] [Decidable r] [Decidable s] :
    boolAndStatic (decide p || decide q) (decide r || decide s) =
      decide ((p \/ q) /\ (r \/ s)) := by
  by_cases hp : p <;> by_cases hq : q <;> by_cases hr : r <;> by_cases hs : s <;>
    simp [boolAndStatic, hp, hq, hr, hs]

/-- Lookup in a finite syntactic two-index Pauli table. This is the
    finite-code/LDPC escape hatch: the table is certificate data, not a
    semantic callback. -/
def lookupPauliTable2 (default : Pauli) (table : List ((Nat × Nat) × Pauli)) (key : Nat × Nat) :
    Pauli :=
  match table.find? (fun entry => decide (entry.1 = key)) with
  | some entry => entry.2
  | none => default

namespace KernelTerm

/-- Interpret a tiny-kernel program. -/
def eval {arity : Nat} {s : KernelTy} :
    KernelTerm arity s -> KernelEnv arity -> s.denote
  | .var i, rho => rho i
  | .natLit n, _ => n
  | .boolLit b, _ => b
  | .pauliLit p, _ => p
  | .pauliLookup2 default table a b, rho =>
      lookupPauliTable2 default table (a.eval rho, b.eval rho)
  | .natAdd a b, rho => Nat.add (a.eval rho) (b.eval rho)
  | .natSub a b, rho => Nat.sub (a.eval rho) (b.eval rho)
  | .natMul a b, rho => Nat.mul (a.eval rho) (b.eval rho)
  | .natDiv a b, rho => Nat.div (a.eval rho) (b.eval rho)
  | .natMod a b, rho => Nat.mod (a.eval rho) (b.eval rho)
  | .natEq a b, rho => Nat.beq (a.eval rho) (b.eval rho)
  | .natLe a b, rho => natLeBool (a.eval rho) (b.eval rho)
  | .natLt a b, rho => natLtBool (a.eval rho) (b.eval rho)
  | .boolNot b, rho => !(b.eval rho)
  | .boolAnd a b, rho => boolAndStatic (a.eval rho) (b.eval rho)
  | .boolOr a b, rho => boolOrStatic (a.eval rho) (b.eval rho)
  | .boolXor a b, rho => xor (a.eval rho) (b.eval rho)
  | .ite c t e, rho => bif c.eval rho then t.eval rho else e.eval rho

end KernelTerm

namespace KernelTerm

/-- Compile a tiny-kernel program into the richer existing `FamilyTerm` layer.
    The caller supplies the meaning of each integer variable as a static QHL
    natural-number expression. -/
def toFamilyTerm {P : QECParams} {Ctx : List (Ty P)} {arity : Nat}
    (varNat : Fin arity -> FamilyTerm P Ctx .nat) :
    {s : KernelTy} -> KernelTerm arity s -> FamilyTerm P Ctx (s.toTy P)
  | .nat, .var i => varNat i
  | .nat, .natLit n => .natLit n
  | .bool, .boolLit b => .boolLit b
  | .pauli, .pauliLit p => .pauliLit p
  | .pauli, .pauliLookup2 default table a b =>
      .pauliLookup2 default table (toFamilyTerm varNat a) (toFamilyTerm varNat b)
  | .nat, .natAdd a b => .natAdd (toFamilyTerm varNat a) (toFamilyTerm varNat b)
  | .nat, .natSub a b => .natSub (toFamilyTerm varNat a) (toFamilyTerm varNat b)
  | .nat, .natMul a b => .natMul (toFamilyTerm varNat a) (toFamilyTerm varNat b)
  | .nat, .natDiv a b => .natDiv (toFamilyTerm varNat a) (toFamilyTerm varNat b)
  | .nat, .natMod a b => .natMod (toFamilyTerm varNat a) (toFamilyTerm varNat b)
  | .bool, .natEq a b => .natEq (toFamilyTerm varNat a) (toFamilyTerm varNat b)
  | .bool, .natLe a b => .natLe (toFamilyTerm varNat a) (toFamilyTerm varNat b)
  | .bool, .natLt a b => .natLt (toFamilyTerm varNat a) (toFamilyTerm varNat b)
  | .bool, .boolNot b => .boolNot (toFamilyTerm varNat b)
  | .bool, .boolAnd a b => .boolAnd (toFamilyTerm varNat a) (toFamilyTerm varNat b)
  | .bool, .boolOr a b => .boolOr (toFamilyTerm varNat a) (toFamilyTerm varNat b)
  | .bool, .boolXor a b => .boolXor (toFamilyTerm varNat a) (toFamilyTerm varNat b)
  | _, .ite c t e => .ite (toFamilyTerm varNat c) (toFamilyTerm varNat t)
      (toFamilyTerm varNat e)

/-- Interpret a unary integer-kernel Pauli program as a per-qubit vector body.
    Variable 0 is the qubit index. -/
def toQubitFamily {P : QECParams} :
    KernelTerm 1 .pauli -> FamilyTerm P [.qubit] .pauli :=
  toFamilyTerm fun _ => FamilyTerm.qubitVal (FamilyTerm.var Var.zero)

/-- Interpret a binary integer-kernel Pauli program as a stabilizer-row entry.
    Variable 0 is the qubit index and variable 1 is the stabilizer index. -/
def toQubitStabFamily {P : QECParams} :
    KernelTerm 2 .pauli -> FamilyTerm P [.qubit, .stab] .pauli :=
  toFamilyTerm fun i =>
    if i.val = 0 then
      FamilyTerm.qubitVal (FamilyTerm.var Var.zero)
    else
      FamilyTerm.stabVal (FamilyTerm.var (Var.succ Var.zero))

end KernelTerm

/-- Interpretation of static code-family expressions. -/
def FamilyTerm.eval {P : QECParams} {Ctx : List (Ty P)} {s : Ty P} :
    FamilyTerm P Ctx s -> StaticEnv Ctx -> s.denote
  | .var v, rho => rho v
  | .boolLit b, _ => b
  | .natLit n, _ => n
  | .pauliLit p, _ => p
  | .pauliLookup2 default table a b, rho =>
      lookupPauliTable2 default table (a.eval rho, b.eval rho)
  | .qubitLit q, _ => q
  | .stabLit i, _ => i
  | .vecLit E, _ => E
  | .qubitVal q, rho => (q.eval rho).val
  | .stabVal i, rho => (i.eval rho).val
  | .stabilizerAt i, rho => P.stabilizers (i.eval rho)
  | .natAdd a b, rho => Nat.add (a.eval rho) (b.eval rho)
  | .natSub a b, rho => Nat.sub (a.eval rho) (b.eval rho)
  | .natMul a b, rho => Nat.mul (a.eval rho) (b.eval rho)
  | .natDiv a b, rho => Nat.div (a.eval rho) (b.eval rho)
  | .natMod a b, rho => Nat.mod (a.eval rho) (b.eval rho)
  | .natEq a b, rho => Nat.beq (a.eval rho) (b.eval rho)
  | .natLe a b, rho => natLeBool (a.eval rho) (b.eval rho)
  | .natLt a b, rho => natLtBool (a.eval rho) (b.eval rho)
  | .boolNot b, rho => !(b.eval rho)
  | .boolAnd a b, rho => boolAndStatic (a.eval rho) (b.eval rho)
  | .boolOr a b, rho => boolOrStatic (a.eval rho) (b.eval rho)
  | .boolXor a b, rho => xor (a.eval rho) (b.eval rho)
  | .ite c t e, rho => bif c.eval rho then t.eval rho else e.eval rho
  | .identity, _ => ErrorVec.identity P.n
  | .vecMul a b, rho => ErrorVec.mul (a.eval rho) (b.eval rho)
  | .vecUpdate E q p, rho => ErrorVec.update (E.eval rho) (q.eval rho) (p.eval rho)
  | .vecAt E q, rho => E.eval rho (q.eval rho)
  | .weight E, rho => ErrorVec.weight (E.eval rho)
  | .parity a b, rho => ErrorVec.parity (a.eval rho) (b.eval rho)
  | .hasX p, rho => pauliHasXStatic (p.eval rho)
  | .foldQubits init body, rho =>
      (List.finRange P.n).foldl
        (fun acc q =>
          body.eval
            (StaticEnv.extend (s := .vec)
              (StaticEnv.extend (s := .qubit) rho q) acc))
        (init.eval rho)

/-- A syntactic stabilizer-row generator. The common LDPC case is `byEntry e`:
    the `e` term computes the Pauli in row `s` and data qubit `q`, so the whole
    stabilizer is the function `q |-> e(s, q)` without expanding a dense vector
    in the certificate. -/
inductive StabilizerBody (P : QECParams) where
  | byEntry : FamilyTerm P [.qubit, .stab] .pauli -> StabilizerBody P
  | byVector : FamilyTerm P [.stab] .vec -> StabilizerBody P

/-- Interpret a syntactic stabilizer body at one stabilizer index. -/
def StabilizerBody.eval {P : QECParams} :
    StabilizerBody P -> Fin P.numStab -> ErrorVec P.n
  | .byEntry entry, i => fun q =>
      entry.eval
        (StaticEnv.extend (s := .qubit)
          (StaticEnv.extend (s := .stab) (StaticEnv.empty (P := P)) i) q)
  | .byVector body, i =>
      body.eval (StaticEnv.extend (s := .stab) (StaticEnv.empty (P := P)) i)

namespace StabilizerBody

/-- Build a stabilizer row from the tiny integer-indexed kernel.
    Variable 0 is the data-qubit index; variable 1 is the stabilizer index. -/
def ofKernelEntry {P : QECParams} (entry : KernelTerm 2 .pauli) : StabilizerBody P :=
  .byEntry entry.toQubitStabFamily

end StabilizerBody

/-- A named Pauli-vector constant, such as a logical operator.

    The vector is exposed through per-qubit syntax, plus a proof that this
    syntax agrees with the mathematical vector carried by the code spec. -/
structure VecSymbol (P : QECParams) where
  name : String
  body : FamilyTerm P [.qubit] .pauli
  value : ErrorVec P.n
  agrees : forall q, body.eval
    (StaticEnv.extend (s := .qubit) (StaticEnv.empty (P := P)) q) = value q

/-- Interpret a syntactic vector symbol as a Pauli vector. -/
def VecSymbol.eval {P : QECParams} (v : VecSymbol P) : ErrorVec P.n :=
  fun q => v.body.eval
    (StaticEnv.extend (s := .qubit) (StaticEnv.empty (P := P)) q)

@[simp] theorem VecSymbol.eval_eq_value {P : QECParams} (v : VecSymbol P) :
    v.eval = v.value := by
  funext q
  exact v.agrees q

namespace VecSymbol

/-- Build a named vector from the tiny integer-indexed kernel.
    Variable 0 is the data-qubit index. -/
def ofKernel {P : QECParams} (name : String) (body : KernelTerm 1 .pauli)
    (value : ErrorVec P.n)
    (agrees : forall q,
      body.toQubitFamily.eval
        (StaticEnv.extend (s := .qubit) (StaticEnv.empty (P := P)) q) = value q) :
    VecSymbol P where
  name := name
  body := body.toQubitFamily
  value := value
  agrees := agrees

end VecSymbol

/-- A named stabilizer-family accessor at a selected distance.

    The assertion language is indexed by a fixed `QECParams`, so the dependent
    family parameter `d` is selected before a formula is formed. The symbol
    records that distance and exposes a recursive syntactic body for
    `k |-> T_{d,k}`. The `agrees` proof connects that syntax to the canonical
    table in `P`; the data itself is not an arbitrary semantic callback. -/
structure StabilizerFamilySymbol (P : QECParams) where
  name : String
  distance : Nat
  body : StabilizerBody P
  /-- The syntactic accessor agrees with the canonical stabilizer table in `P`. -/
  agrees : forall k, body.eval k = P.stabilizers k

/-- Interpret a named stabilizer-family symbol at one stabilizer index. -/
def StabilizerFamilySymbol.eval {P : QECParams}
    (F : StabilizerFamilySymbol P) (k : Fin P.numStab) : ErrorVec P.n :=
  F.body.eval k

/-- A named intra-stabilizer scheduling symbol.

The QStab program schedules which stabilizer is measured at each coordinate.
This symbol describes the fixed gate/support order inside each stabilizer
measurement. Type-II back-action sets are generated from suffixes of this
order, so the schedule belongs in the static assertion language rather than in
the executable QStab program syntax. -/
structure ScheduleFamilySymbol (P : QECParams) where
  name : String
  distance : Nat
  /-- Whether local slot `slot` is part of stabilizer `k`'s measurement order. -/
  active : Fin P.numStab -> Nat -> Bool
  /-- Totalized scheduled data qubit. Invalid slots may return any default. -/
  qubit : Fin P.numStab -> Nat -> Fin P.n
  /-- Totalized scheduled Pauli. Invalid slots may return any default. -/
  pauli : Fin P.numStab -> Nat -> Pauli
  /-- Uniform finite bound on the number of active slots per stabilizer. -/
  maxSlots : Nat
  active_lt_max : forall k slot, active k slot = true -> slot < maxSlots

namespace ScheduleFamilySymbol

def isActive {P : QECParams} (S : ScheduleFamilySymbol P)
    (k : Fin P.numStab) (slot : Nat) : Bool :=
  S.active k slot

def scheduledQubit {P : QECParams} (S : ScheduleFamilySymbol P)
    (k : Fin P.numStab) (slot : Nat) : Fin P.n :=
  S.qubit k slot

def scheduledPauli {P : QECParams} (S : ScheduleFamilySymbol P)
    (k : Fin P.numStab) (slot : Nat) : Pauli :=
  S.pauli k slot

end ScheduleFamilySymbol

/-- A named logical class, characterised purely syntactically by two finite
    lists of `ErrorVec` generators:

    * `parityZero`: every element of this list must *commute* with the
      candidate error (`ErrorVec.parity S E = false`). Typically the
      stabilizer generators.
    * `parityOne`: every element of this list must *anticommute* with the
      candidate error (`ErrorVec.parity T E = true`). Typically the
      logical-operator representative(s).

    Membership in the class is the finite conjunction
    `(∀ S ∈ parityZero, parity S E = false) ∧ (∀ T ∈ parityOne, parity T E = true)`,
    which is decidable. No arbitrary `ErrorVec → Prop` atom escape: the
    interpretation is forced by the algebraic data.

    This denotes one parity coset.  For a one-encoded-qubit code, the full
    "any nontrivial logical" predicate is usually a disjunction of the
    logical-X and logical-Z cosets, not a single `LogicalClassSymbol` of this
    conjunctive form. -/
structure LogicalClassSymbol (P : QECParams) where
  name : String
  /-- Generators with which every member must commute (Bool `parity` evaluates to `false`). -/
  parityZero : List (ErrorVec P.n)
  /-- Generators with which every member must anticommute (Bool `parity` evaluates to `true`). -/
  parityOne  : List (ErrorVec P.n)
  distance : Nat

/-- Syntactic membership predicate: a finite conjunction of explicit `parity`
    constraints. Decidable, syntactic, no `Prop`-atom escape. -/
def LogicalClassSymbol.contains {P : QECParams} (L : LogicalClassSymbol P)
    (E : ErrorVec P.n) : Prop :=
  (∀ S, S ∈ L.parityZero → ErrorVec.parity S E = false) ∧
  (∀ T, T ∈ L.parityOne  → ErrorVec.parity T E = true)

/-- A named finite set of nontrivial logical cosets.

    This is the shared assertion-language form for "any logical residual" when
    a code has one encoded qubit.  It is still syntactic: membership is a
    finite centralizer check plus a finite disjunction over named logical
    representatives.

    * `parityZero`: every listed generator must commute with the error.
      Typically this is the stabilizer-generator list.
    * `parityAny`: at least one listed representative must anticommute with
      the error.  For surface d=3 this list is `[logicalZ, logicalX]`, covering
      logical-X, logical-Z, and logical-Y residual classes.

    Unlike `LogicalClassSymbol`, this denotes a union of parity cosets rather
    than one conjunctive parity coset. -/
structure LogicalSetSymbol (P : QECParams) where
  name : String
  /-- Generators with which every member must commute. -/
  parityZero : List (ErrorVec P.n)
  /-- At least one representative in this list must anticommute with the member. -/
  parityAny : List (ErrorVec P.n)
  distance : Nat

/-- Syntactic membership in a finite logical-coset union. -/
def LogicalSetSymbol.contains {P : QECParams} (L : LogicalSetSymbol P)
    (E : ErrorVec P.n) : Prop :=
  (∀ S, S ∈ L.parityZero → ErrorVec.parity S E = false) ∧
  (∃ T, T ∈ L.parityAny ∧ ErrorVec.parity T E = true)

/-- A named code geometry used by Surface/HGP structural assertions. -/
structure GeometrySymbol (P : QECParams) (d : Nat) where
  name : String
  groupOf : Fin P.n -> Option (Fin d)
  cut : Fin d -> ErrorVec P.n

/-- Drop the last Boolean-coordinate of a mask. -/
def boolFunTail {n : Nat} (mask : Fin (n + 1) -> Bool) : Fin n -> Bool :=
  fun i => mask ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self n)⟩

/-- Extend a mask on `Fin n` by one final Boolean coordinate. -/
def boolFunExtend {n : Nat} (tail : Fin n -> Bool) (last : Bool) : Fin (n + 1) -> Bool :=
  fun i => if h : i.val < n then tail ⟨i.val, h⟩ else last

/-- Extending a mask by its own tail and last coordinate is extensionally
    the original mask. -/
theorem boolFunExtend_tail_last {n : Nat} (mask : Fin (n + 1) -> Bool) :
    boolFunExtend (boolFunTail mask) (mask ⟨n, Nat.lt_succ_self n⟩) = mask := by
  funext i
  unfold boolFunExtend boolFunTail
  by_cases h : i.val < n
  · simp [h]
  · have hi : i.val = n := by omega
    have hfin : i = ⟨n, Nat.lt_succ_self n⟩ := by
      apply Fin.ext
      exact hi
    simp [hfin]

/-- All Boolean masks over `Fin n`, as a recursive syntax tree. -/
def allBoolFunctions : (n : Nat) -> List (Fin n -> Bool)
  | 0 => [fun i => Fin.elim0 i]
  | n + 1 =>
      (allBoolFunctions n).flatMap fun tail =>
        [boolFunExtend tail false, boolFunExtend tail true]

/-- The recursive mask syntax is complete: every Boolean function over `Fin n`
    appears in `allBoolFunctions n`. -/
theorem allBoolFunctions_complete (n : Nat) (mask : Fin n -> Bool) :
    mask ∈ allBoolFunctions n := by
  induction n with
  | zero =>
      simp [allBoolFunctions]
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      rw [allBoolFunctions]
      apply List.mem_flatMap.mpr
      let tail := boolFunTail mask
      refine ⟨tail, ih tail, ?_⟩
      have hEq := boolFunExtend_tail_last mask
      cases hlast : mask ⟨n, Nat.lt_succ_self n⟩
      · rw [hlast] at hEq
        rw [← hEq]
        left
      · rw [hlast] at hEq
        rw [← hEq]
        right
        exact List.mem_singleton.mpr rfl

/-- The four single-qubit Paulis in a concrete finite order. -/
def allPaulis : List Pauli := [.I, .X, .Y, .Z]

/-- The Pauli enumeration is complete. -/
theorem allPaulis_complete (p : Pauli) : p ∈ allPaulis := by
  cases p <;> simp [allPaulis]

/-- Drop the last Pauli coordinate of an error vector. -/
def errorVecTail {n : Nat} (E : ErrorVec (n + 1)) : ErrorVec n :=
  fun i => E ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self n)⟩

/-- Extend an error vector by one final Pauli coordinate. -/
def errorVecExtend {n : Nat} (tail : ErrorVec n) (last : Pauli) :
    ErrorVec (n + 1) :=
  fun i => if h : i.val < n then tail ⟨i.val, h⟩ else last

/-- Extending an error vector by its own tail and last coordinate is
extensionally the original vector. -/
theorem errorVecExtend_tail_last {n : Nat} (E : ErrorVec (n + 1)) :
    errorVecExtend (errorVecTail E) (E ⟨n, Nat.lt_succ_self n⟩) = E := by
  funext i
  unfold errorVecExtend errorVecTail
  by_cases h : i.val < n
  · simp [h]
  · have hi : i.val = n := by omega
    have hfin : i = ⟨n, Nat.lt_succ_self n⟩ := by
      apply Fin.ext
      exact hi
    simp [hfin]

/-- All Pauli error vectors over `Fin n`, as recursive concrete syntax. -/
def allErrorVecs : (n : Nat) -> List (ErrorVec n)
  | 0 => [fun i => Fin.elim0 i]
  | n + 1 =>
      (allErrorVecs n).flatMap fun tail =>
        allPaulis.map fun last => errorVecExtend tail last

/-- The recursive Pauli-vector syntax is complete. -/
theorem allErrorVecs_complete (n : Nat) (E : ErrorVec n) :
    E ∈ allErrorVecs n := by
  induction n with
  | zero =>
      simp [allErrorVecs]
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      rw [allErrorVecs]
      apply List.mem_flatMap.mpr
      let tail := errorVecTail E
      refine ⟨tail, ih tail, ?_⟩
      apply List.mem_map.mpr
      refine ⟨E ⟨n, Nat.lt_succ_self n⟩, allPaulis_complete _, ?_⟩
      simpa [tail] using errorVecExtend_tail_last E

/-- Fold a Boolean predicate over every Pauli error vector without
materialising the full `4^n` list.  This is the preferred shape for concrete
finite checkers: proof terms stay small, while the kernel still reduces the
closed checker. -/
def forallErrorVecs : (n : Nat) -> (ErrorVec n -> Bool) -> Bool
  | 0, pred => pred (fun i => Fin.elim0 i)
  | n + 1, pred =>
      forallErrorVecs n fun tail =>
        allPaulis.all fun last => pred (errorVecExtend tail last)

/-- Soundness of the recursive finite Pauli-vector checker. -/
theorem forallErrorVecs_sound (n : Nat) (pred : ErrorVec n -> Bool)
    (h : forallErrorVecs n pred = true) (E : ErrorVec n) :
    pred E = true := by
  induction n with
  | zero =>
      have hE : E = (fun i : Fin 0 => Fin.elim0 i) := by
        funext i
        exact Fin.elim0 i
      simpa [forallErrorVecs, hE] using h
  | succ n ih =>
      unfold forallErrorVecs at h
      let tail := errorVecTail E
      have hTail : (allPaulis.all fun last =>
          pred (errorVecExtend tail last)) = true :=
        ih (fun tail => allPaulis.all fun last => pred (errorVecExtend tail last)) h tail
      have hLast := (List.all_eq_true.mp hTail)
        (E ⟨n, Nat.lt_succ_self n⟩)
        (allPaulis_complete (E ⟨n, Nat.lt_succ_self n⟩))
      simpa [tail, errorVecExtend_tail_last E] using hLast

/-- Product of the stabilizer generators selected by a Boolean mask. -/
def maskStabilizerProduct (P : QECParams) (mask : Fin P.numStab -> Bool) :
    ErrorVec P.n :=
  (List.finRange P.numStab).foldr
    (fun i acc => if mask i then ErrorVec.mul (P.stabilizers i) acc else acc)
    (ErrorVec.identity P.n)

/-- Explicit finite enumeration of stabilizer-generator masks. -/
def allStabMasks (P : QECParams) : List (Fin P.numStab -> Bool) :=
  allBoolFunctions P.numStab

/-- Every Boolean stabilizer mask appears in the finite mask enumeration. -/
theorem allStabMasks_complete (P : QECParams) (mask : Fin P.numStab -> Bool) :
    mask ∈ allStabMasks P := by
  exact allBoolFunctions_complete P.numStab mask

/-- Number of geometry groups with an X component in `S * E`. -/
noncomputable def GeometrySymbol.groupsX {P : QECParams} {d : Nat}
    (G : GeometrySymbol P d) (S E : ErrorVec P.n) : Nat := by
  classical
  exact (Finset.univ.filter fun g : Fin d =>
    exists q : Fin P.n, G.groupOf q = some g /\
      pauliHasXStatic (ErrorVec.mul S E q) = true).card

/-- Number of geometry groups with a Z component in `S * E`.

This Z-side mirror is deliberately list-computable so concrete QClifford
assertion checkers can reduce `alignedSpreadZ` without hidden classical
decidability arguments. -/
def GeometrySymbol.groupsZ {P : QECParams} {d : Nat}
    (G : GeometrySymbol P d) (S E : ErrorVec P.n) : Nat :=
  ((List.finRange d).filter fun g : Fin d =>
    (List.finRange P.n).any fun q : Fin P.n =>
      decide (G.groupOf q = some g) && pauliHasZStatic (ErrorVec.mul S E q)).length

/-- Finite-mask version of the aligned spread minimisation. -/
noncomputable def GeometrySymbol.omegaMask {P : QECParams} {d : Nat}
    (G : GeometrySymbol P d) (E : ErrorVec P.n) : Nat := by
  classical
  exact (allStabMasks P).foldl
    (fun best mask => Nat.min best (G.groupsX (maskStabilizerProduct P mask) E))
    (G.groupsX (maskStabilizerProduct P (fun _ => false)) E)

/-- Finite-mask version of the dual Z-spread minimisation. -/
def GeometrySymbol.omegaMaskZ {P : QECParams} {d : Nat}
    (G : GeometrySymbol P d) (E : ErrorVec P.n) : Nat := by
  exact (allStabMasks P).foldl
    (fun best mask => Nat.min best (G.groupsZ (maskStabilizerProduct P mask) E))
    (G.groupsZ (maskStabilizerProduct P (fun _ => false)) E)

/-- Syntax for barrier functions.

    `alignedSpread` is generic: it is the finite, mask-minimised group-spread
    barrier used by Surface rows, HGP columns, and any LDPC family equipped with
    a suitable grouping. `external` quarantines legacy semantic callbacks. -/
inductive BarrierBody (P : QECParams) where
  | external : (ErrorVec P.n -> Nat) -> BarrierBody P
  | alignedSpread {d : Nat} : GeometrySymbol P d -> BarrierBody P
  | alignedSpreadZ {d : Nat} : GeometrySymbol P d -> BarrierBody P

namespace BarrierBody

/-- Interpret a barrier body on one Pauli error. -/
noncomputable def eval {P : QECParams} : BarrierBody P -> ErrorVec P.n -> Nat
  | .external f, E => f E
  | @BarrierBody.alignedSpread _ d G, E => d - G.omegaMask E
  | @BarrierBody.alignedSpreadZ _ d G, E => d - G.omegaMaskZ E

end BarrierBody

/-- A named barrier function. The symbol carries only syntax; semantics are
    supplied by `BarrierSymbol.eval`. Legacy semantic barriers are quarantined
    as `.external` bodies rather than as proof-carrying fields. -/
structure BarrierSymbol (P : QECParams) where
  name : String
  body : BarrierBody P

namespace BarrierSymbol

/-- Interpret a named barrier through its syntax. -/
noncomputable def eval {P : QECParams} (beta : BarrierSymbol P) :
    ErrorVec P.n -> Nat :=
  beta.body.eval

/-- Build a barrier symbol directly from generic aligned-spread syntax. -/
def ofAlignedSpread {P : QECParams} {d : Nat} (name : String)
    (G : GeometrySymbol P d) : BarrierSymbol P where
  name := name
  body := .alignedSpread G

/-- Build a barrier symbol from the dual Z-spread syntax. -/
def ofAlignedSpreadZ {P : QECParams} {d : Nat} (name : String)
    (G : GeometrySymbol P d) : BarrierSymbol P where
  name := name
  body := .alignedSpreadZ G

end BarrierSymbol

/-- Proof-free aligned-code descriptor. This is the assertion-language
    replacement for the data part of `AlignedCodeSpec`: the logical operator,
    group map, and cut operators are syntax/data, while the laws they must
    satisfy are expressed separately as formulas and certificates. -/
structure AlignedCodeData (P : QECParams) (d : Nat) where
  name : String
  logicalZ : ErrorVec P.n
  geometry : GeometrySymbol P d

namespace AlignedCodeData

/-- Bar-Z parity class generated from aligned-code data.  This is the class
    anticommutes with the chosen logical-Z representative, so in the usual
    one-qubit naming it detects the logical-X component, not pure logical-Z. -/
def logicalClass {P : QECParams} {d : Nat} (name : String)
    (A : AlignedCodeData P d) : LogicalClassSymbol P where
  name := name
  parityZero := (List.finRange P.numStab).map P.stabilizers
  parityOne := [A.logicalZ]
  distance := d

/-- Aligned-spread barrier generated from aligned-code data. -/
def barrier {P : QECParams} {d : Nat} (name : String)
    (A : AlignedCodeData P d) : BarrierSymbol P :=
  BarrierSymbol.ofAlignedSpread name A.geometry

end AlignedCodeData

/-- Intrinsically typed QHL terms. -/
inductive Term (P : QECParams) : List (Ty P) -> Ty P -> Type where
  | var : Var Γ s -> Term P Γ s
  | boolLit : Bool -> Term P Γ .bool
  | natLit : Nat -> Term P Γ .nat
  | pauliLit : Pauli -> Term P Γ .pauli
  | qubitLit : Fin P.n -> Term P Γ .qubit
  | stabLit : Fin P.numStab -> Term P Γ .stab
  | roundLit : Fin P.R -> Term P Γ .round
  | coordLit : QECParams.Coord P -> Term P Γ .coord
  | vecLit : ErrorVec P.n -> Term P Γ .vec
  | budget : Term P Γ .nat
  | remaining : Term P Γ .nat
  | error : Term P Γ .vec
  | current : Term P Γ .coord
  | detector : Term P Γ .nat -> Term P Γ .bool
  | coordNext : Term P Γ .coord -> Term P Γ .coord
  | coordStab : Term P Γ .coord -> Term P Γ .stab
  | scheduledStab : QStabProgram P -> Term P Γ .coord -> Term P Γ .stab
  | coordRound : Term P Γ .coord -> Term P Γ .round
  | natAdd : Term P Γ .nat -> Term P Γ .nat -> Term P Γ .nat
  | natSub : Term P Γ .nat -> Term P Γ .nat -> Term P Γ .nat
  | boolNot : Term P Γ .bool -> Term P Γ .bool
  | boolXor : Term P Γ .bool -> Term P Γ .bool -> Term P Γ .bool
  | ite : Term P Γ .bool -> Term P Γ s -> Term P Γ s -> Term P Γ s
  | identity : Term P Γ .vec
  | vecMul : Term P Γ .vec -> Term P Γ .vec -> Term P Γ .vec
  | vecUpdate : Term P Γ .vec -> Term P Γ .qubit -> Term P Γ .pauli -> Term P Γ .vec
  | vecAt : Term P Γ .vec -> Term P Γ .qubit -> Term P Γ .pauli
  | weight : Term P Γ .vec -> Term P Γ .nat
  | parity : Term P Γ .vec -> Term P Γ .vec -> Term P Γ .bool
  | hasX : Term P Γ .pauli -> Term P Γ .bool
  | stabMaskProduct : Term P Γ .stabMask -> Term P Γ .vec
  | stabilizer : Term P Γ .stab -> Term P Γ .vec
  | familyStabilizer : StabilizerFamilySymbol P -> Term P Γ .stab -> Term P Γ .vec
  | scheduleActive : ScheduleFamilySymbol P -> Term P Γ .stab -> Term P Γ .nat ->
      Term P Γ .bool
  | scheduleQubit : ScheduleFamilySymbol P -> Term P Γ .stab -> Term P Γ .nat ->
      Term P Γ .qubit
  | schedulePauli : ScheduleFamilySymbol P -> Term P Γ .stab -> Term P Γ .nat ->
      Term P Γ .pauli
  | namedVec : VecSymbol P -> Term P Γ .vec
  | cut : GeometrySymbol P d -> Term P Γ (.group d) -> Term P Γ .vec
  | barrier : BarrierSymbol P -> Term P Γ .vec -> Term P Γ .nat

/-- First-order QHL formulas. Domain-specific relations remain explicit syntax. -/
inductive Formula (P : QECParams) : List (Ty P) -> Type where
  | top {Γ : List (Ty P)} : Formula P Γ
  | bot {Γ : List (Ty P)} : Formula P Γ
  | eq : Term P Γ s -> Term P Γ s -> Formula P Γ
  | le : Term P Γ .nat -> Term P Γ .nat -> Formula P Γ
  | lt : Term P Γ .nat -> Term P Γ .nat -> Formula P Γ
  | and : Formula P Γ -> Formula P Γ -> Formula P Γ
  | or : Formula P Γ -> Formula P Γ -> Formula P Γ
  | imp : Formula P Γ -> Formula P Γ -> Formula P Γ
  | not : Formula P Γ -> Formula P Γ
  | all : (s : Ty P) -> Formula P (s :: Γ) -> Formula P Γ
  | exists : (s : Ty P) -> Formula P (s :: Γ) -> Formula P Γ
  | inStab : Term P Γ .vec -> Formula P Γ
  | logicalMember : LogicalClassSymbol P -> Term P Γ .vec -> Formula P Γ
  | logicalSetMember : LogicalSetSymbol P -> Term P Γ .vec -> Formula P Γ
  | backAction : Term P Γ .stab -> Term P Γ .vec -> Formula P Γ
  | inGroup : GeometrySymbol P d -> Term P Γ .qubit -> Term P Γ (.group d) -> Formula P Γ
  | nextCoord : Term P Γ .coord -> Term P Γ .coord -> Formula P Γ

namespace Term

/-- Syntactic support check for formulas interpreted over QClifford states.

The shared assertion language contains source/QStab-only state fields such as
the current measurement coordinate.  QClifford VC generation may still use the
same formulas for stabilizer arithmetic, barriers, logical residuals, detector
slots, and fault counts, but it must reject formulas that depend on the
source-only coordinate/program cursor. -/
def qcSupported {P : QECParams} {Γ : List (Ty P)} {s : Ty P} :
    Term P Γ s -> Bool
  | .var _ => true
  | .boolLit _ => true
  | .natLit _ => true
  | .pauliLit _ => true
  | .qubitLit _ => true
  | .stabLit _ => true
  | .roundLit _ => true
  | .coordLit _ => false
  | .vecLit _ => true
  | .budget => true
  | .remaining => true
  | .error => true
  | .current => false
  | .detector k => qcSupported k
  | .coordNext _ => false
  | .coordStab _ => false
  | .scheduledStab _ _ => false
  | .coordRound _ => false
  | .natAdd a b => qcSupported a && qcSupported b
  | .natSub a b => qcSupported a && qcSupported b
  | .boolNot b => qcSupported b
  | .boolXor a b => qcSupported a && qcSupported b
  | .ite c t e => qcSupported c && qcSupported t && qcSupported e
  | .identity => true
  | .vecMul a b => qcSupported a && qcSupported b
  | .vecUpdate E q p => qcSupported E && qcSupported q && qcSupported p
  | .vecAt E q => qcSupported E && qcSupported q
  | .weight E => qcSupported E
  | .parity a b => qcSupported a && qcSupported b
  | .hasX p => qcSupported p
  | .stabMaskProduct mask => qcSupported mask
  | .stabilizer i => qcSupported i
  | .familyStabilizer _ i => qcSupported i
  | .scheduleActive _ _ _ => false
  | .scheduleQubit _ _ _ => false
  | .schedulePauli _ _ _ => false
  | .namedVec _ => true
  | .cut _ i => qcSupported i
  | .barrier _ E => qcSupported E

end Term

namespace Formula

/-- Syntactic support check for QClifford interpretation of shared formulas. -/
def qcSupported {P : QECParams} {Γ : List (Ty P)} : Formula P Γ -> Bool
  | .top => true
  | .bot => true
  | .eq a b => a.qcSupported && b.qcSupported
  | .le a b => a.qcSupported && b.qcSupported
  | .lt a b => a.qcSupported && b.qcSupported
  | .and A B => A.qcSupported && B.qcSupported
  | .or A B => A.qcSupported && B.qcSupported
  | .imp A B => A.qcSupported && B.qcSupported
  | .not A => A.qcSupported
  | .all _ A => A.qcSupported
  | .exists _ A => A.qcSupported
  | .inStab E => E.qcSupported
  | .logicalMember _ E => E.qcSupported
  | .logicalSetMember _ E => E.qcSupported
  | .backAction i E => i.qcSupported && E.qcSupported
  | .inGroup _ q i => q.qcSupported && i.qcSupported
  | .nextCoord _ _ => false

end Formula

/-- Generic contract: a syntactic stabilizer-family symbol agrees with the
    canonical stabilizer table carried by the selected `QECParams`. -/
def stabilizerFamilyAgreementF {P : QECParams} (F : StabilizerFamilySymbol P) :
    Formula P [] :=
  .all .stab
    (.eq
      (.familyStabilizer F (.var .zero))
      (.stabilizer (.var .zero)))

/-- Generic LDPC-style row-weight contract for a syntactic stabilizer family.
    A family with constant row bound `w` is sparse independently of whether the
    code is Surface, HGP, bicycle, or another stabilizer-code family. -/
def stabilizerFamilyWeightBoundF {P : QECParams}
    (F : StabilizerFamilySymbol P) (w : Nat) : Formula P [] :=
  .all .stab
    (.le
      (.weight (.familyStabilizer F (.var .zero)))
      (.natLit w))

/-- The static intra-stabilizer schedule agrees with the generated stabilizer
    family: every active schedule slot points to a data qubit whose Pauli in
    the stabilizer row is exactly the scheduled Pauli. -/
def scheduleFamilyAgreementF {P : QECParams}
    (F : StabilizerFamilySymbol P) (S : ScheduleFamilySymbol P) : Formula P [] :=
  .all .stab
    (.all .nat
      (.imp
        (.eq
          (.scheduleActive S (.var (.succ .zero)) (.var .zero))
          (.boolLit true))
        (.eq
          (.vecAt
            (.familyStabilizer F (.var (.succ .zero)))
            (.scheduleQubit S (.var (.succ .zero)) (.var .zero)))
          (.schedulePauli S (.var (.succ .zero)) (.var .zero)))))

/-- A generic schedule/back-action sanity formula: every back-action branch has
    weight bounded by the schedule symbol's uniform local support bound.  The
    code-specific proof that the back-action set is generated from suffixes of
    the schedule is supplied by the family certificate, not by QStab's program
    syntax. -/
def scheduleBackActionWeightF {P : QECParams} (S : ScheduleFamilySymbol P) :
    Formula P [] :=
  .all .stab
    (.all .vec
      (.imp
        (.backAction (.var (.succ .zero)) (.var .zero))
        (.le (.weight (.var .zero)) (.natLit S.maxSlots))))

namespace AlignedCodeData

/-- Every cut operator is a stabilizer product times the logical-Z operator. -/
def cutStabEquivF {P : QECParams} {d : Nat} (A : AlignedCodeData P d) :
    Formula P [] :=
  .all (.group d)
    (.exists .stabMask
      (.eq
        (.cut A.geometry (.var (.succ .zero)))
        (.vecMul (.stabMaskProduct (.var .zero)) (.vecLit A.logicalZ))))

/-- Every cut has `Z` exactly on its group and `I` outside that group. -/
def cutShapeF {P : QECParams} {d : Nat} (A : AlignedCodeData P d) :
    Formula P [] :=
  .all (.group d)
    (.all .qubit
      (.and
        (.imp
          (.inGroup A.geometry (.var .zero) (.var (.succ .zero)))
          (.eq
            (.vecAt (.cut A.geometry (.var (.succ .zero))) (.var .zero))
            (.pauliLit Pauli.Z)))
        (.imp
          (.not (.inGroup A.geometry (.var .zero) (.var (.succ .zero))))
          (.eq
            (.vecAt (.cut A.geometry (.var (.succ .zero))) (.var .zero))
            (.pauliLit Pauli.I)))))

/-- The logical-Z operator commutes with every stabilizer generator. -/
def logicalZNormalizerF {P : QECParams} {d : Nat} (A : AlignedCodeData P d) :
    Formula P [] :=
  .all .stab
    (.eq
      (.parity (.stabilizer (.var .zero)) (.vecLit A.logicalZ))
      (.boolLit false))

/-- Stabilizer generators commute pairwise. -/
def stabilizersCommuteF {P : QECParams} {d : Nat} (_A : AlignedCodeData P d) :
    Formula P [] :=
  .all .stab
    (.all .stab
      (.eq
        (.parity (.stabilizer (.var .zero)) (.stabilizer (.var (.succ .zero))))
        (.boolLit false)))

/-- Schedule-alignment expressed directly as a barrier law over the aligned
    spread barrier generated from this code data. -/
def hookAlignedF {P : QECParams} {d : Nat} (betaName : String)
    (A : AlignedCodeData P d) : Formula P [] :=
  .all .stab (.all .vec
    (.imp
      (.backAction (.var (.succ .zero)) (.var .zero))
      (.all .vec
        (.le
          (.barrier (A.barrier betaName) (.var .zero))
          (.natAdd
            (.barrier (A.barrier betaName)
              (.vecMul (.var (.succ .zero)) (.var .zero)))
            (.natLit 1))))))

/-- The aligned-code contract as five closed assertion-language obligations. -/
def contractF {P : QECParams} {d : Nat} (betaName : String)
    (A : AlignedCodeData P d) : Formula P [] :=
  .and A.cutStabEquivF
    (.and A.cutShapeF
      (.and A.logicalZNormalizerF
        (.and A.stabilizersCommuteF (A.hookAlignedF betaName))))

end AlignedCodeData

end QHL.AssertionLang
