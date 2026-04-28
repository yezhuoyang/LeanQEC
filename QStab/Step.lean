import QStab.BackAction

/-! # Small-step operational semantics: transition relation

Each constructor corresponds to one transition rule from the paper (Theorem 1):
- `type0`: Type-0 data qubit error (Eq. 1)
- `type1`: Type-I error during measurement (Eq. 2)
- `type2`: Type-II back-action error (Eq. 5)
- `type3`: Type-III measurement bit flip (Eq. 3)
- `measure`: Stabilizer measurement (Eq. 4)
- `halt`: Transition to σ_done
- `budget_exhausted`: Transition to σ_error when C=0 (Eq. 6)
-/

namespace QStab

open QECParams

/-- Compute the state after a stabilizer measurement at the current coordinate.
    This implements Eq. 4 from the paper. All updates use pre-transition values. -/
def measureStep (P : QECParams) (s : State P) (next_coord : Coord P) : State P :=
  let measurement := xor (s.G s.coord.x s.coord.y)
                         (ErrorVec.parity (P.stabilizers s.coord.x) s.E_tilde)
  let new_I_syn := fun j => if j = s.coord.x then measurement else s.I_syn j
  let new_G := fun x y => if x = s.coord.x ∧ y = s.coord.y
                           then measurement
                           else s.G x y
  let new_F := fun j => if j = s.coord.x
                         then (s.I_syn s.coord.x != measurement)
                         else s.F j
  let any_inconsistent : Bool := decide (∃ j : Fin P.numStab, new_F j = true)
  let new_RI := if decide (s.coord.isRoundEnd) && any_inconsistent
                 then s.RI + 1
                 else s.RI
  { s with
    coord := next_coord
    RI := new_RI
    I_syn := new_I_syn
    G := new_G
    F := new_F }

/-- Small-step transition relation for the QStab operational semantics. -/
inductive Step (P : QECParams) : ExecState P → ExecState P → Prop where

  /-- Type-0 error: data qubit error injection (Eq. 1).
      Requires C > 0. Updates: C-1, cnt0+1, lam_E+1, Ẽ updated at qubit i. -/
  | type0 (s : State P) (i : Fin P.n) (p : Pauli) (hp : p ≠ Pauli.I)
      (hC : 0 < s.C) :
      Step P (.active s) (.active { s with
        C := s.C - 1
        cnt0 := s.cnt0 + 1
        lam_E := s.lam_E + 1
        E_tilde := ErrorVec.update s.E_tilde i p
      })

  /-- Type-I error: error during stabilizer measurement (Eq. 2).
      Requires C > 0. Same effect as Type-0 but counted separately.
      The `mflip` flag models Y/Z faults on data qubits during CNOT:
      the Z component propagates to the ancilla and flips the measurement.
      When mflip = false: pure data error (X fault on data).
      When mflip = true: data error + measurement flip (Y/Z fault on data). -/
  | type1 (s : State P) (i : Fin P.n) (p : Pauli) (hp : p ≠ Pauli.I)
      (mflip : Bool) (hC : 0 < s.C) :
      Step P (.active s) (.active { s with
        C := s.C - 1
        cnt1 := s.cnt1 + 1
        lam_E := s.lam_E + 1
        E_tilde := ErrorVec.update s.E_tilde i p
        G := fun x y => if mflip && x = s.coord.x && y = s.coord.y
                         then !s.G x y
                         else s.G x y
      })

  /-- Type-II error: back-action error after measurement (Eq. 5).
      Requires C > 0, e ∈ B¹(T_{current stabilizer}).
      Updates: C-1, cnt2+1, lam_E += |e|, Ẽ → e·Ẽ.
      F is updated: f_i ⊕ Parity(e, T_s).
      The `mflip` flag models Y faults on the ancilla: the X component
      propagates as the hook (e), the Z component flips the measurement.
      When mflip = false: pure hook error (X fault on ancilla).
      When mflip = true: hook + measurement flip (Y fault on ancilla). -/
  | type2 (s : State P) (e : ErrorVec P.n)
      (he : e ∈ backActionSet P s.coord.x)
      (mflip : Bool) (hC : 0 < s.C) :
      Step P (.active s) (.active { s with
        C := s.C - 1
        cnt2 := s.cnt2 + 1
        lam_E := s.lam_E + ErrorVec.weight e
        E_tilde := ErrorVec.mul e s.E_tilde
        G := fun x y => if mflip && x = s.coord.x && y = s.coord.y
                         then !s.G x y
                         else s.G x y
        F := fun j => if j = s.coord.x
                       then xor (xor (s.F j) (ErrorVec.parity (P.stabilizers s.coord.x) e))
                                (if mflip then true else false)
                       else s.F j
      })

  /-- Type-III error: measurement bit flip (Eq. 3).
      Requires C > 0. Updates: C-1, cnt3+1, G bit at current position flipped. -/
  | type3 (s : State P) (hC : 0 < s.C) :
      Step P (.active s) (.active { s with
        C := s.C - 1
        cnt3 := s.cnt3 + 1
        G := fun x y => if x = s.coord.x ∧ y = s.coord.y
                         then !s.G x y
                         else s.G x y
      })

  /-- Stabilizer measurement (Eq. 4).
      Deterministic step using measureStep helper. -/
  | measure (s : State P) (next_coord : Coord P)
      (hNext : s.coord.next = some next_coord) :
      Step P (.active s) (.active (measureStep P s next_coord))

  /-- Halt rule: all measurements complete, transition to σ_done. -/
  | halt (s : State P) (hDone : s.coord.next = none) :
      Step P (.active s) (.done s)

  /-- Error rule (Eq. 6): budget exhausted (C=0), any error injection → σ_error. -/
  | budget_exhausted (s : State P) (hC : s.C = 0) :
      Step P (.active s) (.error s)

-- measureStep preserves fields not in its `with` clause
@[simp] theorem measureStep_C (P : QECParams) (s : State P) (nc : Coord P) :
    (measureStep P s nc).C = s.C := by unfold measureStep; rfl
@[simp] theorem measureStep_cnt0 (P : QECParams) (s : State P) (nc : Coord P) :
    (measureStep P s nc).cnt0 = s.cnt0 := by unfold measureStep; rfl
@[simp] theorem measureStep_cnt1 (P : QECParams) (s : State P) (nc : Coord P) :
    (measureStep P s nc).cnt1 = s.cnt1 := by unfold measureStep; rfl
@[simp] theorem measureStep_cnt2 (P : QECParams) (s : State P) (nc : Coord P) :
    (measureStep P s nc).cnt2 = s.cnt2 := by unfold measureStep; rfl
@[simp] theorem measureStep_cnt3 (P : QECParams) (s : State P) (nc : Coord P) :
    (measureStep P s nc).cnt3 = s.cnt3 := by unfold measureStep; rfl
@[simp] theorem measureStep_lam_E (P : QECParams) (s : State P) (nc : Coord P) :
    (measureStep P s nc).lam_E = s.lam_E := by unfold measureStep; rfl
@[simp] theorem measureStep_E_tilde (P : QECParams) (s : State P) (nc : Coord P) :
    (measureStep P s nc).E_tilde = s.E_tilde := by unfold measureStep; rfl
@[simp] theorem measureStep_coord (P : QECParams) (s : State P) (nc : Coord P) :
    (measureStep P s nc).coord = nc := by unfold measureStep; rfl

/-- measureStep preserves I_syn for stabilizers other than the current one. -/
theorem measureStep_I_syn_ne {P : QECParams} (s : State P) (nc : Coord P)
    (j : Fin P.numStab) (hj : j ≠ s.coord.x) :
    (measureStep P s nc).I_syn j = s.I_syn j := by
  unfold measureStep; simp only [hj, ite_false]

/-- measureStep sets I_syn at the current stabilizer to the measurement value. -/
theorem measureStep_I_syn_eq {P : QECParams} (s : State P) (nc : Coord P) :
    (measureStep P s nc).I_syn s.coord.x =
      xor (s.G s.coord.x s.coord.y) (ErrorVec.parity (P.stabilizers s.coord.x) s.E_tilde) := by
  unfold measureStep; simp only [ite_true]

/-- measureStep preserves F for stabilizers other than the current one. -/
theorem measureStep_F_ne {P : QECParams} (s : State P) (nc : Coord P)
    (j : Fin P.numStab) (hj : j ≠ s.coord.x) :
    (measureStep P s nc).F j = s.F j := by
  unfold measureStep; simp only [hj, ite_false]

/-- measureStep sets F at the current stabilizer:
    F[x] = (old I_syn[x] != G[x,y] xor parity(T_x, Ẽ)). -/
theorem measureStep_F_eq {P : QECParams} (s : State P) (nc : Coord P) :
    (measureStep P s nc).F s.coord.x =
      (s.I_syn s.coord.x != xor (s.G s.coord.x s.coord.y)
        (ErrorVec.parity (P.stabilizers s.coord.x) s.E_tilde)) := by
  unfold measureStep; simp only [ite_true]

/-- measureStep preserves G for entries other than (coord.x, coord.y). -/
theorem measureStep_G_ne {P : QECParams} (s : State P) (nc : Coord P)
    (a : Fin P.numStab) (b : Fin P.R) (h : ¬(a = s.coord.x ∧ b = s.coord.y)) :
    (measureStep P s nc).G a b = s.G a b := by
  unfold measureStep; simp only [h, ite_false]

/-- measureStep sets G at (coord.x, coord.y) to the measurement value. -/
theorem measureStep_G_eq {P : QECParams} (s : State P) (nc : Coord P) :
    (measureStep P s nc).G s.coord.x s.coord.y =
      xor (s.G s.coord.x s.coord.y) (ErrorVec.parity (P.stabilizers s.coord.x) s.E_tilde) := by
  unfold measureStep; simp only [and_self, ite_true]

end QStab
