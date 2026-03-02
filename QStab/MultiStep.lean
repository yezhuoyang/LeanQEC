import QStab.Step
import Mathlib.Logic.Relation

/-! # Multi-step transition and execution runs

Defines multi-step reachability via `Relation.ReflTransGen`
and the notion of a valid execution run from σ_init.
-/

namespace QStab

/-- Multi-step transition: the reflexive-transitive closure of Step.
    σ →* σ' in the paper. -/
def MultiStep (P : QECParams) : ExecState P → ExecState P → Prop :=
  Relation.ReflTransGen (Step P)

/-- A valid execution run from init to some final state.
    σ_0 →* σ in the paper. -/
def Run (P : QECParams) (final : ExecState P) : Prop :=
  MultiStep P (.active (State.init P)) final

/-- Once in a done state, no further steps are possible. -/
theorem done_is_stuck (P : QECParams) (s : State P) (s' : ExecState P) :
    ¬ Step P (.done s) s' := by
  intro h; cases h

/-- Once in an error state, no further steps are possible. -/
theorem error_is_stuck (P : QECParams) (s : State P) (s' : ExecState P) :
    ¬ Step P (.error s) s' := by
  intro h; cases h

/-- Multi-step transitivity. -/
theorem multi_step_trans {P : QECParams} {a b c : ExecState P} :
    MultiStep P a b → MultiStep P b c → MultiStep P a c :=
  Relation.ReflTransGen.trans

/-- Single step lifts to multi-step. -/
theorem step_to_multi {P : QECParams} {a b : ExecState P} :
    Step P a b → MultiStep P a b :=
  Relation.ReflTransGen.single

end QStab
