import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Fintype.Fin

/-! # Single-qubit Pauli operators and phases -/

inductive Pauli where
  | I | X | Y | Z
  deriving Repr, DecidableEq

inductive Phase where
  | one | i | neg_one | neg_i
  deriving Repr, DecidableEq

structure PauliWithPhase where
  phase : Phase
  op : Pauli
  deriving Repr, DecidableEq

-- ============================================================
-- Phase: cyclic group Z/4Z
-- ============================================================

namespace Phase

def mul : Phase → Phase → Phase
  | .one,     p       => p
  | p,        .one    => p
  | .i,       .i      => .neg_one
  | .i,       .neg_one => .neg_i
  | .i,       .neg_i  => .one
  | .neg_one, .i      => .neg_i
  | .neg_one, .neg_one => .one
  | .neg_one, .neg_i  => .i
  | .neg_i,   .i      => .one
  | .neg_i,   .neg_one => .i
  | .neg_i,   .neg_i  => .neg_one

def inv : Phase → Phase
  | .one     => .one
  | .i       => .neg_i
  | .neg_one => .neg_one
  | .neg_i   => .i

instance : Mul Phase := ⟨Phase.mul⟩
instance : One Phase := ⟨Phase.one⟩
instance : Inv Phase := ⟨Phase.inv⟩

instance : CommGroup Phase where
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry
  inv_mul_cancel := sorry
  mul_comm := sorry

end Phase

-- ============================================================
-- Pauli multiplication (ignoring phase, just the operator part)
-- This is the Klein four-group: X² = Y² = Z² = I, XY = Z, etc.
-- ============================================================

namespace Pauli

def mul : Pauli → Pauli → Pauli
  | .I, p   => p
  | p,  .I  => p
  | .X, .X  => .I
  | .X, .Y  => .Z
  | .X, .Z  => .Y
  | .Y, .X  => .Z
  | .Y, .Y  => .I
  | .Y, .Z  => .X
  | .Z, .X  => .Y
  | .Z, .Y  => .X
  | .Z, .Z  => .I

-- The phase produced when multiplying two Paulis: e.g., X * Y = iZ gives phase i
def mulPhase : Pauli → Pauli → Phase
  | .I, _   => .one
  | _,  .I  => .one
  | .X, .X  => .one
  | .X, .Y  => .i
  | .X, .Z  => .neg_i
  | .Y, .X  => .neg_i
  | .Y, .Y  => .one
  | .Y, .Z  => .i
  | .Z, .X  => .i
  | .Z, .Y  => .neg_i
  | .Z, .Z  => .one

end Pauli

-- ============================================================
-- PauliWithPhase: the full 16-element single-qubit Pauli group
-- ============================================================

namespace PauliWithPhase

def mul (a b : PauliWithPhase) : PauliWithPhase where
  phase := a.phase * b.phase * Pauli.mulPhase a.op b.op
  op := Pauli.mul a.op b.op

def inv (a : PauliWithPhase) : PauliWithPhase where
  phase := a.phase⁻¹ * Pauli.mulPhase a.op a.op
  op := a.op  -- every Pauli operator is self-inverse (as an operator)

def one : PauliWithPhase where
  phase := .one
  op := .I

instance : Mul PauliWithPhase := ⟨PauliWithPhase.mul⟩
instance : One PauliWithPhase := ⟨PauliWithPhase.one⟩
instance : Inv PauliWithPhase := ⟨PauliWithPhase.inv⟩

instance : Group PauliWithPhase where
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry
  inv_mul_cancel := sorry

end PauliWithPhase

-- ============================================================
-- n-qubit Pauli group
-- ============================================================

structure PauliN (n : Nat) where
  phase : Phase
  ops : Fin n → Pauli

namespace PauliN

def mul (a b : PauliN n) : PauliN n where
  phase := a.phase * b.phase * (Finset.univ.prod fun j => Pauli.mulPhase (a.ops j) (b.ops j))
  ops := fun j => Pauli.mul (a.ops j) (b.ops j)

def inv (a : PauliN n) : PauliN n where
  phase := a.phase⁻¹ * (Finset.univ.prod fun j => Pauli.mulPhase (a.ops j) (a.ops j))
  ops := a.ops

def one : PauliN n where
  phase := .one
  ops := fun _ => .I

instance : Mul (PauliN n) := ⟨PauliN.mul⟩
instance : One (PauliN n) := ⟨PauliN.one⟩
instance : Inv (PauliN n) := ⟨PauliN.inv⟩

instance : Group (PauliN n) where
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry
  inv_mul_cancel := sorry

end PauliN
