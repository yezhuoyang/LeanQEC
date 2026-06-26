import QStab.QHL.Source.Branch

/-! # A tiny fixed-program QStab example: measuring `XXYYI`

This file is intentionally small.  It demonstrates the refactored separation:

* `xxyyiProgram` is the fixed program, a schedule with one stabilizer
  measurement.
* `TransitionLabel.err0/errI/errII/errIII/meas` are not program statements;
  they are nondeterministic semantic branches around the current coordinate.
-/

namespace QHL.Source.Examples.XXYYIProgram

open QStab QHL.Source.Branch

def xxyyiStabilizer : ErrorVec 5
  | ⟨0, _⟩ => Pauli.X
  | ⟨1, _⟩ => Pauli.X
  | ⟨2, _⟩ => Pauli.Y
  | ⟨3, _⟩ => Pauli.Y
  | ⟨4, _⟩ => Pauli.I

def xxyyiParams : QECParams where
  n := 5
  k := 4
  d := 1
  R := 1
  numStab := 1
  stabilizers := fun _ => xxyyiStabilizer
  backActionSet := fun _ => ∅
  r := 0
  backAction_weight_bound := fun _ _ h => h.elim
  C_budget := 1
  hn := by omega
  hns := by omega
  hR := by omega

/-- The fixed one-measurement QStab program. -/
def xxyyiProgram : QStabProgram xxyyiParams :=
  QStabProgram.rowMajor xxyyiParams

example (c : QECParams.Coord xxyyiParams) :
    xxyyiProgram.currentStab c = c.x :=
  rfl

example : xxyyiStabilizer ⟨0, by decide⟩ = Pauli.X := rfl
example : xxyyiStabilizer ⟨1, by decide⟩ = Pauli.X := rfl
example : xxyyiStabilizer ⟨2, by decide⟩ = Pauli.Y := rfl
example : xxyyiStabilizer ⟨3, by decide⟩ = Pauli.Y := rfl
example : xxyyiStabilizer ⟨4, by decide⟩ = Pauli.I := rfl

/-- A Type-0 fault is an enabled nondeterministic branch when budget remains. -/
example (s : State xxyyiParams) (hC : 0 < s.C) :
    TransitionStep xxyyiProgram
      (.err0 ⟨0, by decide⟩ Pauli.X) s
      { s with
        C := s.C - 1
        cnt0 := s.cnt0 + 1
        lam_E := s.lam_E + 1
        E_tilde := ErrorVec.update s.E_tilde ⟨0, by decide⟩ Pauli.X } :=
  TransitionStep.err0 (prog := xxyyiProgram) s ⟨0, by decide⟩ Pauli.X
    (by decide) hC

/-- The fixed program action is only the measurement branch. -/
example (s : State xxyyiParams) (nc : QECParams.Coord xxyyiParams)
    (hN : s.coord.next = some nc) :
    TransitionStep xxyyiProgram .meas s (measureStep xxyyiProgram s nc) :=
  TransitionStep.meas (prog := xxyyiProgram) s nc hN

/-- Type-II has no branch in this example because the back-action set is empty. -/
theorem xxyyi_no_typeII_branch (s : State xxyyiParams) (e : ErrorVec xxyyiParams.n)
    (mf : Bool) (s' : State xxyyiParams) :
    ¬ TransitionStep xxyyiProgram (.errII e mf) s s' := by
  intro h
  cases h with
  | errII _ _ he _ _ => exact he.elim

end QHL.Source.Examples.XXYYIProgram
