import QStab.BackAction
import QStab.Program

/-! # Program-indexed small-step operational semantics

The canonical QStab program is a fixed stabilizer-measurement schedule.  The
program action is the measurement at the current coordinate; faults are
nondeterministic semantic transitions enabled around that coordinate.

Each constructor corresponds to one transition rule from the paper:
- `type0`: Type-0 data-qubit error
- `type1`: Type-I error during measurement
- `type2`: Type-II back-action error
- `type3`: Type-III measurement bit flip
- `measure`: the fixed scheduled stabilizer measurement
- `halt`: transition to `done`
- `budget_exhausted`: transition to `error` when the budget is exhausted
-/

namespace QStab

open QECParams

/-- The stabilizer scheduled at the state's current coordinate. -/
abbrev currentStab {P : QECParams} (prog : QStabProgram P) (s : State P) :
    Fin P.numStab :=
  prog.currentStab s.coord

/-- Compute the state after measuring the stabilizer scheduled at the current
    coordinate.  All updates use pre-transition values. -/
def measureStep {P : QECParams} (prog : QStabProgram P) (s : State P)
    (next_coord : Coord P) : State P :=
  let stab := currentStab prog s
  let measurement := xor (s.G stab s.coord.y) (ErrorVec.parity (P.stabilizers stab) s.E_tilde)
  let new_I_syn := fun j => if j = stab then measurement else s.I_syn j
  let new_G := fun x y => if x = stab ∧ y = s.coord.y then measurement else s.G x y
  let new_F := fun j => if j = stab then (s.I_syn stab != measurement) else s.F j
  let any_inconsistent : Bool := decide (∃ j : Fin P.numStab, new_F j = true)
  let new_RI := if decide s.coord.isRoundEnd && any_inconsistent then s.RI + 1 else s.RI
  { s with
    coord := next_coord
    RI := new_RI
    I_syn := new_I_syn
    G := new_G
    F := new_F }

/-- Small-step transition relation for a fixed QStab measurement program. -/
inductive Step {P : QECParams} (prog : QStabProgram P) :
    ExecState P -> ExecState P -> Prop where

  /-- Type-0 error: data-qubit error injection. -/
  | type0 (s : State P) (i : Fin P.n) (p : Pauli) (hp : p ≠ Pauli.I)
      (hC : 0 < s.C) :
      Step prog (.active s) (.active { s with
        C := s.C - 1
        cnt0 := s.cnt0 + 1
        lam_E := s.lam_E + 1
        E_tilde := ErrorVec.update s.E_tilde i p
      })

  /-- Type-I error: data error during the scheduled measurement, with an
      optional measurement-register flip. -/
  | type1 (s : State P) (i : Fin P.n) (p : Pauli) (hp : p ≠ Pauli.I)
      (mflip : Bool) (hC : 0 < s.C) :
      Step prog (.active s) (.active { s with
        C := s.C - 1
        cnt1 := s.cnt1 + 1
        lam_E := s.lam_E + 1
        E_tilde := ErrorVec.update s.E_tilde i p
        G := fun x y => if mflip && x = currentStab prog s && y = s.coord.y
                         then !s.G x y
                         else s.G x y
      })

  /-- Type-II error: scheduled-stabilizer back-action error, with an optional
      measurement-register flip. -/
  | type2 (s : State P) (e : ErrorVec P.n)
      (he : e ∈ backActionSet P (currentStab prog s))
      (mflip : Bool) (hC : 0 < s.C) :
      Step prog (.active s) (.active { s with
        C := s.C - 1
        cnt2 := s.cnt2 + 1
        lam_E := s.lam_E + ErrorVec.weight e
        E_tilde := ErrorVec.mul e s.E_tilde
        G := fun x y => if mflip && x = currentStab prog s && y = s.coord.y
                         then !s.G x y
                         else s.G x y
        F := fun j => if j = currentStab prog s
                       then xor (xor (s.F j)
                         (ErrorVec.parity (P.stabilizers (currentStab prog s)) e))
                         (if mflip then true else false)
                       else s.F j
      })

  /-- Type-III error: scheduled measurement bit flip. -/
  | type3 (s : State P) (hC : 0 < s.C) :
      Step prog (.active s) (.active { s with
        C := s.C - 1
        cnt3 := s.cnt3 + 1
        G := fun x y => if x = currentStab prog s ∧ y = s.coord.y
                         then !s.G x y
                         else s.G x y
      })

  /-- Fixed scheduled stabilizer measurement. -/
  | measure (s : State P) (next_coord : Coord P)
      (hNext : s.coord.next = some next_coord) :
      Step prog (.active s) (.active (measureStep prog s next_coord))

  /-- Halt rule: all scheduled measurements are complete. -/
  | halt (s : State P) (hDone : s.coord.next = none) :
      Step prog (.active s) (.done s)

  /-- Error rule: budget exhausted and the adversary attempts another fault. -/
  | budget_exhausted (s : State P) (hC : s.C = 0) :
      Step prog (.active s) (.error s)

-- measureStep preserves fields not in its `with` clause.
@[simp] theorem measureStep_C {P : QECParams} (prog : QStabProgram P)
    (s : State P) (nc : Coord P) :
    (measureStep prog s nc).C = s.C := by
  unfold measureStep
  rfl

@[simp] theorem measureStep_cnt0 {P : QECParams} (prog : QStabProgram P)
    (s : State P) (nc : Coord P) :
    (measureStep prog s nc).cnt0 = s.cnt0 := by
  unfold measureStep
  rfl

@[simp] theorem measureStep_cnt1 {P : QECParams} (prog : QStabProgram P)
    (s : State P) (nc : Coord P) :
    (measureStep prog s nc).cnt1 = s.cnt1 := by
  unfold measureStep
  rfl

@[simp] theorem measureStep_cnt2 {P : QECParams} (prog : QStabProgram P)
    (s : State P) (nc : Coord P) :
    (measureStep prog s nc).cnt2 = s.cnt2 := by
  unfold measureStep
  rfl

@[simp] theorem measureStep_cnt3 {P : QECParams} (prog : QStabProgram P)
    (s : State P) (nc : Coord P) :
    (measureStep prog s nc).cnt3 = s.cnt3 := by
  unfold measureStep
  rfl

@[simp] theorem measureStep_lam_E {P : QECParams} (prog : QStabProgram P)
    (s : State P) (nc : Coord P) :
    (measureStep prog s nc).lam_E = s.lam_E := by
  unfold measureStep
  rfl

@[simp] theorem measureStep_E_tilde {P : QECParams} (prog : QStabProgram P)
    (s : State P) (nc : Coord P) :
    (measureStep prog s nc).E_tilde = s.E_tilde := by
  unfold measureStep
  rfl

@[simp] theorem measureStep_coord {P : QECParams} (prog : QStabProgram P)
    (s : State P) (nc : Coord P) :
    (measureStep prog s nc).coord = nc := by
  unfold measureStep
  rfl

/-- measureStep preserves I_syn for stabilizers other than the scheduled one. -/
theorem measureStep_I_syn_ne {P : QECParams} (prog : QStabProgram P)
    (s : State P) (nc : Coord P) (j : Fin P.numStab)
    (hj : j ≠ currentStab prog s) :
    (measureStep prog s nc).I_syn j = s.I_syn j := by
  unfold measureStep
  simp [currentStab, hj]

/-- measureStep sets I_syn at the scheduled stabilizer to the measurement value. -/
theorem measureStep_I_syn_eq {P : QECParams} (prog : QStabProgram P)
    (s : State P) (nc : Coord P) :
    (measureStep prog s nc).I_syn (currentStab prog s) =
      xor (s.G (currentStab prog s) s.coord.y)
        (ErrorVec.parity (P.stabilizers (currentStab prog s)) s.E_tilde) := by
  unfold measureStep
  simp [currentStab]

/-- measureStep preserves F for stabilizers other than the scheduled one. -/
theorem measureStep_F_ne {P : QECParams} (prog : QStabProgram P)
    (s : State P) (nc : Coord P) (j : Fin P.numStab)
    (hj : j ≠ currentStab prog s) :
    (measureStep prog s nc).F j = s.F j := by
  unfold measureStep
  simp [currentStab, hj]

/-- measureStep sets F at the scheduled stabilizer. -/
theorem measureStep_F_eq {P : QECParams} (prog : QStabProgram P)
    (s : State P) (nc : Coord P) :
    (measureStep prog s nc).F (currentStab prog s) =
      (s.I_syn (currentStab prog s) != xor (s.G (currentStab prog s) s.coord.y)
        (ErrorVec.parity (P.stabilizers (currentStab prog s)) s.E_tilde)) := by
  unfold measureStep
  simp [currentStab]

/-- measureStep preserves G for entries other than the scheduled measurement slot. -/
theorem measureStep_G_ne {P : QECParams} (prog : QStabProgram P)
    (s : State P) (nc : Coord P) (a : Fin P.numStab) (b : Fin P.R)
    (h : ¬(a = currentStab prog s ∧ b = s.coord.y)) :
    (measureStep prog s nc).G a b = s.G a b := by
  unfold measureStep
  simp [currentStab, h]

/-- measureStep sets G at the scheduled measurement slot to the measurement value. -/
theorem measureStep_G_eq {P : QECParams} (prog : QStabProgram P)
    (s : State P) (nc : Coord P) :
    (measureStep prog s nc).G (currentStab prog s) s.coord.y =
      xor (s.G (currentStab prog s) s.coord.y)
        (ErrorVec.parity (P.stabilizers (currentStab prog s)) s.E_tilde) := by
  unfold measureStep
  simp [currentStab]

end QStab
