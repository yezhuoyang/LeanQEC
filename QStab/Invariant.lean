import QStab.MultiStep

/-! # Generic invariant framework

The canonical invariant is `ProgramInvariant prog`: it is attached to a fixed
measurement program and must be preserved by every active-to-active branch of
the nondeterministic transition relation for that program.

`Invariant P` is retained as a row-major compatibility abbreviation for older
theory files while the QHL/certificate layer migrates to explicit programs.
-/

namespace QStab

/-- A state invariant for a fixed QStab measurement program. -/
structure ProgramInvariant {P : QECParams} (prog : QStabProgram P) where
  /-- The predicate on active states. -/
  holds : State P -> Prop
  /-- The predicate holds for the initial state. -/
  holds_init : holds (State.init P)
  /-- The predicate is preserved by every active-to-active transition branch. -/
  preservation : ∀ s s' : State P,
    holds s -> Step prog (.active s) (.active s') -> holds s'

/-- Legacy row-major invariant abbreviation. New code should use
    `ProgramInvariant prog` when the schedule matters. -/
abbrev Invariant (P : QECParams) : Type :=
  ProgramInvariant (QStabProgram.rowMajor P)

namespace ProgramInvariant

/-- Helper: an invariant holds for the underlying state of any reachable
    execution state. -/
private theorem holds_of_reachable_aux {P : QECParams} {prog : QStabProgram P}
    (inv : ProgramInvariant prog) (e : ExecState P)
    (hrun : MultiStep prog (.active (State.init P)) e) :
    inv.holds e.state := by
  induction hrun with
  | refl => exact inv.holds_init
  | tail _ step ih =>
    cases step with
    | type0 s i p hp hC =>
        exact inv.preservation _ _ ih (Step.type0 (prog := prog) s i p hp hC)
    | type1 s i p hp mf hC =>
        exact inv.preservation _ _ ih (Step.type1 (prog := prog) s i p hp mf hC)
    | type2 s ev he mf hC =>
        exact inv.preservation _ _ ih (Step.type2 (prog := prog) s ev he mf hC)
    | type3 s hC =>
        exact inv.preservation _ _ ih (Step.type3 (prog := prog) s hC)
    | measure s nc hN =>
        exact inv.preservation _ _ ih (Step.measure (prog := prog) s nc hN)
    | halt _ _ => exact ih
    | budget_exhausted _ _ => exact ih

/-- An invariant holds for any active state reachable from init. -/
theorem holds_of_reachable {P : QECParams} {prog : QStabProgram P}
    (inv : ProgramInvariant prog) (s : State P)
    (hrun : MultiStep prog (.active (State.init P)) (.active s)) :
    inv.holds s :=
  holds_of_reachable_aux inv (.active s) hrun

/-- An invariant holds for the underlying state of any done state reachable from init. -/
theorem holds_at_done {P : QECParams} {prog : QStabProgram P}
    (inv : ProgramInvariant prog) (s : State P) (hrun : Run prog (.done s)) :
    inv.holds s :=
  holds_of_reachable_aux inv (.done s) hrun

/-- An invariant holds for the underlying state of any error state reachable from init. -/
theorem holds_at_error {P : QECParams} {prog : QStabProgram P}
    (inv : ProgramInvariant prog) (s : State P) (hrun : Run prog (.error s)) :
    inv.holds s :=
  holds_of_reachable_aux inv (.error s) hrun

/-- Conjunction of two invariants is an invariant. -/
def conj {P : QECParams} {prog : QStabProgram P}
    (inv₁ inv₂ : ProgramInvariant prog) : ProgramInvariant prog where
  holds := fun s => inv₁.holds s ∧ inv₂.holds s
  holds_init := ⟨inv₁.holds_init, inv₂.holds_init⟩
  preservation := fun s s' ⟨h1, h2⟩ step =>
    ⟨inv₁.preservation s s' h1 step, inv₂.preservation s s' h2 step⟩

/-- Implication: if an invariant implies a predicate on all states, then that
    predicate holds for all active reachable states. -/
theorem holds_of_implies {P : QECParams} {prog : QStabProgram P}
    (inv₁ : ProgramInvariant prog) (p : State P -> Prop)
    (h : ∀ s, inv₁.holds s -> p s) (s : State P)
    (hrun : MultiStep prog (.active (State.init P)) (.active s)) :
    p s :=
  h s (inv₁.holds_of_reachable s hrun)

end ProgramInvariant

namespace Invariant

abbrev holds_of_reachable {P : QECParams} (inv : Invariant P) (s : State P)
    (hrun : MultiStep (QStabProgram.rowMajor P) (.active (State.init P)) (.active s)) :
    inv.holds s :=
  ProgramInvariant.holds_of_reachable inv s hrun

abbrev holds_at_done {P : QECParams} (inv : Invariant P) (s : State P)
    (hrun : Run (QStabProgram.rowMajor P) (.done s)) : inv.holds s :=
  ProgramInvariant.holds_at_done inv s hrun

abbrev holds_at_error {P : QECParams} (inv : Invariant P) (s : State P)
    (hrun : Run (QStabProgram.rowMajor P) (.error s)) : inv.holds s :=
  ProgramInvariant.holds_at_error inv s hrun

abbrev conj {P : QECParams} (inv₁ inv₂ : Invariant P) : Invariant P :=
  ProgramInvariant.conj inv₁ inv₂

abbrev holds_of_implies {P : QECParams} (inv₁ : Invariant P) (p : State P -> Prop)
    (h : ∀ s, inv₁.holds s -> p s) (s : State P)
    (hrun : MultiStep (QStabProgram.rowMajor P) (.active (State.init P)) (.active s)) :
    p s :=
  ProgramInvariant.holds_of_implies inv₁ p h s hrun

end Invariant

end QStab
