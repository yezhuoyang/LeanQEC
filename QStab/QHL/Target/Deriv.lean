import QStab.QHL.Target.Rules

/-! # Proof-theoretic Hoare logic for QClifford (Floyd-Hoare model-theoretic layerII)

The inductive type `DerivC P c Q` is inhabited iff `⦃P⦄ c ⦃Q⦄_c` has a
derivation tree built from the QClifford inference rules. It is the target-side
analogue of the current source branch calculus, with one structural difference:

- Source QStab proofs are over a fixed `QStabProgram` plus nondeterministic
  branch labels (`TransitionLabel`) and the demonic `H_HavocStep` rule.
- QClifford `Circuit` is just `List (Gate nq)` — list-shape is the
  control structure. `DerivC` has three "shape" constructors
  (`Nil`, `Cons`, `App`) plus consequence. The per-gate Hoare rule is
  baked into `Cons` via the WP substitution `gate_sub`.

Compile-friendly: a `DerivC` term is pure data; every leaf is one of
four constructor names plus a Lean witness for the consequence
implications.
-/

namespace QHL.Target

open QStab.QClifford

/-- Derivation trees for the QClifford Hoare logic. Indexed by
    precondition, circuit, postcondition. -/
inductive DerivC (nq : Nat) : AssertionC nq → Circuit nq → AssertionC nq → Type where

  /-- **C_Nil** : `⦃P⦄ [] ⦃P⦄` -/
  | C_Nil (P : AssertionC nq) : DerivC nq P [] P

  /-- **C_Gate** (WP form): `⦃ Q[g-update] ⦄ [g] ⦃Q⦄`.
      The QClifford analog of the standard `H_Asgn`. -/
  | C_Gate (g : Gate nq) (Q : AssertionC nq) :
      DerivC nq (gate_sub g Q) [g] Q

  /-- **C_App** : sequence two sub-derivations whose circuits concatenate. -/
  | C_App {Pre Mid Post : AssertionC nq} {c1 c2 : Circuit nq} :
      DerivC nq Pre c1 Mid → DerivC nq Mid c2 Post →
      DerivC nq Pre (c1 ++ c2) Post

  /-- **C_Consequence** : the standard combined consequence rule. -/
  | C_Consequence {Pre Pre' Post Post' : AssertionC nq} {c : Circuit nq} :
      DerivC nq Pre' c Post' →
      (∀ es : ErrorState nq, Pre es → Pre' es) →
      (∀ es : ErrorState nq, Post' es → Post es) →
      DerivC nq Pre c Post

end QHL.Target
