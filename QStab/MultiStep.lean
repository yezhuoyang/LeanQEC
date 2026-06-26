import QStab.Step
import Mathlib.Logic.Relation

/-! # Multi-step transition and execution runs

Reachability is the reflexive-transitive closure of the nondeterministic
`Step prog` relation for a fixed measurement program `prog`.
-/

namespace QStab

/-- Multi-step transition for a fixed QStab measurement program. -/
def MultiStep {P : QECParams} (prog : QStabProgram P) :
    ExecState P -> ExecState P -> Prop :=
  Relation.ReflTransGen (Step prog)

/-- A valid execution run from the initial state for a fixed program. -/
def Run {P : QECParams} (prog : QStabProgram P) (final : ExecState P) : Prop :=
  MultiStep prog (.active (State.init P)) final

/-- Once in a done state, no further steps are possible. -/
theorem done_is_stuck {P : QECParams} (prog : QStabProgram P) (s : State P)
    (s' : ExecState P) :
    ¬ Step prog (.done s) s' := by
  intro h
  cases h

/-- Once in an error state, no further steps are possible. -/
theorem error_is_stuck {P : QECParams} (prog : QStabProgram P) (s : State P)
    (s' : ExecState P) :
    ¬ Step prog (.error s) s' := by
  intro h
  cases h

/-- Multi-step transitivity. -/
theorem multi_step_trans {P : QECParams} {prog : QStabProgram P}
    {a b c : ExecState P} :
    MultiStep prog a b -> MultiStep prog b c -> MultiStep prog a c :=
  Relation.ReflTransGen.trans

/-- Single step lifts to multi-step. -/
theorem step_to_multi {P : QECParams} {prog : QStabProgram P} {a b : ExecState P} :
    Step prog a b -> MultiStep prog a b :=
  Relation.ReflTransGen.single

end QStab
