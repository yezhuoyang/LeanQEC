import QStab.QHL.Assertion.Barrier
import QStab.MultiStep

/-! # Circuit-distance assertions and operational judgments

The state-local content is represented by deep `Formula` syntax. Reachability
remains outside the formula language because it is a judgment about a QStab
execution, not a field of one state.
-/

namespace QHL.AssertionLang

open QStab

/-- Exactly `faults` units of the QStab budget have been consumed. -/
def spentExactlyF {P : QECParams} (faults : Nat) : Formula P [] :=
  .eq spentF (.natLit faults)

/-- A logical error requires at least `distance` consumed faults. -/
def distanceLowerF {P : QECParams} (logicalError : Formula P [])
    (distance : Nat) : Formula P [] :=
  .imp logicalError (.le (.natLit distance) spentF)

/-- A final attack state: logical error after exactly `distance` faults. -/
def distanceUpperF {P : QECParams} (logicalError : Formula P [])
    (distance : Nat) : Formula P [] :=
  .and logicalError (spentExactlyF distance)

/-- Operational lower bound over every active state reachable under a fixed
    QStab measurement program. -/
def OperationalLowerBound {P : QECParams} (prog : QStabProgram P) (logicalError : Formula P [])
    (distance : Nat) : Prop :=
  ∀ s : State P,
    MultiStep prog (.active (State.init P)) (.active s) →
    (distanceLowerF logicalError distance).denote s

/-- Operational upper bound witnessed by a genuine execution of a fixed QStab
    measurement program. -/
def OperationalUpperBound {P : QECParams} (prog : QStabProgram P) (logicalError : Formula P [])
    (distance : Nat) : Prop :=
  ∃ s : State P,
    MultiStep prog (.active (State.init P)) (.active s) ∧
    (distanceUpperF logicalError distance).denote s

/-- Matching operational lower and upper bounds. -/
structure OperationalExactDistance {P : QECParams} (prog : QStabProgram P)
    (logicalError : Formula P []) (distance : Nat) : Prop where
  lower : OperationalLowerBound prog logicalError distance
  upper : OperationalUpperBound prog logicalError distance

end QHL.AssertionLang
