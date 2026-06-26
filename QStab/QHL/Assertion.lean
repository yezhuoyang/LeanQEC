import QStab.State
import QStab.QHL.Assertion.Semantics
import QStab.QHL.Assertion.Substitution
import QStab.QHL.Assertion.Distance

/-! # QHL Assertions

An assertion in QHL is a predicate on QStab states.
We use a shallow embedding: an `Assertion P` is literally `State P → Prop`.

This type is the semantic compatibility layer used by the existing Hoare and
compiler APIs. New certificates should be authored as a closed
`QHL.AssertionLang.Formula P []` and converted with `Formula.denote`.

The Hoare triples in `QHL.Syntax` are indexed by two assertions (pre and post),
so the reader sees both at every step.

This corresponds to §6.1 of the paper.
-/

namespace QHL

open QStab

/-- An assertion is a predicate on QStab states. -/
abbrev Assertion (P : QECParams) : Type := State P → Prop

namespace Assertion

/-- The always-true assertion. -/
def top {P : QECParams} : Assertion P := fun _ => True

/-- Conjunction of two assertions, pointwise. -/
def and {P : QECParams} (A B : Assertion P) : Assertion P :=
  fun s => A s ∧ B s

/-- Implication between assertions on every state. -/
def implies {P : QECParams} (A B : Assertion P) : Prop :=
  ∀ s, A s → B s

/-- Membership/satisfaction: a state satisfies an assertion. -/
def satisfies {P : QECParams} (s : State P) (A : Assertion P) : Prop := A s

end Assertion

end QHL
