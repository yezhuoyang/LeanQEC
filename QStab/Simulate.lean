import QStab.Step

/-! # Computable simulation functions for QStab

Mirrors the `Step` inductive relation with computable functions
for running concrete QStab programs via `#eval`.
-/

namespace QStab

open QECParams

/-! ## Error injection functions -/

/-- Apply a Type-0 data qubit error: multiply Pauli `p` onto qubit `i`. -/
def applyType0 (s : State P) (i : Fin P.n) (p : Pauli) : State P :=
  { s with
    C := s.C - 1
    cnt0 := s.cnt0 + 1
    lam_E := s.lam_E + 1
    E_tilde := ErrorVec.update s.E_tilde i p }

/-- Apply a Type-I error during measurement. -/
def applyType1 (s : State P) (i : Fin P.n) (p : Pauli) : State P :=
  { s with
    C := s.C - 1
    cnt1 := s.cnt1 + 1
    lam_E := s.lam_E + 1
    E_tilde := ErrorVec.update s.E_tilde i p }

/-- Apply a Type-III measurement bit flip at the current coordinate. -/
def applyType3 (s : State P) : State P :=
  { s with
    C := s.C - 1
    cnt3 := s.cnt3 + 1
    G := fun x y => if x = s.coord.x ∧ y = s.coord.y
                     then !s.G x y
                     else s.G x y }

/-! ## Measurement step -/

/-- Run one measurement step. Returns `none` if at the last coordinate (done). -/
def stepMeasure (P : QECParams) (s : State P) : Option (State P) :=
  match s.coord.next with
  | some next_coord => some (measureStep P s next_coord)
  | none => none

/-- Perform the final measurement (at the last coordinate where next = none).
    Same logic as measureStep but coord stays at last. -/
def measureFinal (P : QECParams) (s : State P) : State P :=
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
    RI := new_RI
    I_syn := new_I_syn
    G := new_G
    F := new_F }

/-! ## Run all remaining measurements -/

/-- Run all remaining measurement steps (no error injection).
    Uses `fuel` to guarantee termination. Performs the final measurement
    at the last coordinate. -/
def runAllMeasurements (P : QECParams) (s : State P) (fuel : Nat) : State P :=
  match fuel with
  | 0 => measureFinal P s
  | fuel + 1 =>
    match stepMeasure P s with
    | some s' => runAllMeasurements P s' fuel
    | none => measureFinal P s

/-! ## String representations for #eval debugging -/

instance : ToString Pauli where
  toString
    | .I => "I"
    | .X => "X"
    | .Y => "Y"
    | .Z => "Z"

/-- Show an ErrorVec as a string like "[X, I, Z]". -/
def showErrorVec {n : Nat} (e : ErrorVec n) : String :=
  let entries := (List.finRange n).map fun i => toString (e i)
  "[" ++ ", ".intercalate entries ++ "]"

/-- Show a Bool function over Fin n as a list. -/
def showBoolVec {n : Nat} (f : Fin n → Bool) : String :=
  let entries := (List.finRange n).map fun i => toString (f i)
  "[" ++ ", ".intercalate entries ++ "]"

/-- Show a summary of the state for debugging. -/
def showState (P : QECParams) (s : State P) : String :=
  s!"C={s.C}, RI={s.RI}, coord=({s.coord.x.val},{s.coord.y.val}), " ++
  s!"lam_E={s.lam_E}, E_tilde={showErrorVec s.E_tilde}, " ++
  s!"I_syn={showBoolVec s.I_syn}, F={showBoolVec s.F}, " ++
  s!"cnt=({s.cnt0},{s.cnt1},{s.cnt2},{s.cnt3})"

end QStab
