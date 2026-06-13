import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  one_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl
  inv_mul_cancel a := by cases a <;> rfl
  mul_comm a b := by cases a <;> cases b <;> rfl

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

/-! ## Structural lemmas about Pauli multiplication

The Klein-four group structure of `Pauli` plus the 2-cocycle structure of
`Pauli.mulPhase` together describe the central extension
`Phase → PauliWithPhase → Pauli`. The lemmas below cover the algebraic
identities needed to close the `Group` instances for both `PauliWithPhase`
and `PauliN`. -/

theorem mul_assoc (a b c : Pauli) : Pauli.mul (Pauli.mul a b) c = Pauli.mul a (Pauli.mul b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem mul_self (a : Pauli) : Pauli.mul a a = .I := by cases a <;> rfl

theorem mulPhase_self (a : Pauli) : Pauli.mulPhase a a = Phase.one := by cases a <;> rfl

theorem mul_I (a : Pauli) : Pauli.mul a .I = a := by cases a <;> rfl

theorem I_mul (a : Pauli) : Pauli.mul .I a = a := rfl

theorem mulPhase_I (a : Pauli) : Pauli.mulPhase a .I = Phase.one := by cases a <;> rfl

theorem mulPhase_I_left (a : Pauli) : Pauli.mulPhase .I a = Phase.one := rfl

/-- The 2-cocycle equation for the central extension `Phase → PauliWithPhase → Pauli`.
    Equivalent to saying that `mulPhase` is the associator of the twisted product. -/
theorem mulPhase_cocycle (a b c : Pauli) :
    Phase.mul (Pauli.mulPhase a b) (Pauli.mulPhase (Pauli.mul a b) c) =
    Phase.mul (Pauli.mulPhase b c) (Pauli.mulPhase a (Pauli.mul b c)) := by
  cases a <;> cases b <;> cases c <;> rfl

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

/-- `PauliWithPhase` is a group. 16-element finite group; we discharge the laws
    by exhaustive case analysis on both fields. -/
instance : Group PauliWithPhase where
  mul_assoc := by
    rintro ⟨pa, oa⟩ ⟨pb, ob⟩ ⟨pc, oc⟩
    cases pa <;> cases oa <;> cases pb <;> cases ob <;> cases pc <;> cases oc <;> rfl
  one_mul := by
    rintro ⟨p, o⟩
    cases p <;> cases o <;> rfl
  mul_one := by
    rintro ⟨p, o⟩
    cases p <;> cases o <;> rfl
  inv_mul_cancel := by
    rintro ⟨p, o⟩
    cases p <;> cases o <;> rfl

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

/-! ## `PauliN n` is a group.

Parametric in `n`, so we cannot brute-force with `cases`. Instead the proofs use
the structural lemmas about `Pauli.mul`, `Pauli.mulPhase`, and `Phase` (CommGroup)
together with `Finset.prod` manipulation. -/

instance : Group (PauliN n) where
  mul_assoc a b c := by
    obtain ⟨pa, oa⟩ := a
    obtain ⟨pb, ob⟩ := b
    obtain ⟨pc, oc⟩ := c
    show PauliN.mul (PauliN.mul ⟨pa, oa⟩ ⟨pb, ob⟩) ⟨pc, oc⟩
       = PauliN.mul ⟨pa, oa⟩ (PauliN.mul ⟨pb, ob⟩ ⟨pc, oc⟩)
    simp only [PauliN.mul]
    refine PauliN.mk.injEq .. |>.mpr ⟨?_, ?_⟩
    · -- Phase equality: rearrange using Phase commutativity + Pauli cocycle.
      -- The per-position 2-cocycle equation:
      --   mulPhase(a,b) * mulPhase(ab,c) = mulPhase(b,c) * mulPhase(a,bc).
      -- Take Finset.prod of both sides, split via prod_mul_distrib.
      have hProd :
          (∏ j, Pauli.mulPhase (oa j) (ob j)) *
          (∏ j, Pauli.mulPhase (Pauli.mul (oa j) (ob j)) (oc j))
        = (∏ j, Pauli.mulPhase (ob j) (oc j)) *
          (∏ j, Pauli.mulPhase (oa j) (Pauli.mul (ob j) (oc j))) := by
        rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl
          (fun j _ => Pauli.mulPhase_cocycle (oa j) (ob j) (oc j))
      -- Set abbreviations: A=pa, B=pb, C=pc, P=∏mp(a,b), Q=∏mp(ab,c),
      -- R=∏mp(b,c), S=∏mp(a,bc). hProd : P * Q = R * S.
      -- Goal (after change): A * B * P * C * Q = A * (B * C * R) * S.
      set A := pa
      set B := pb
      set C := pc
      set P := ∏ j, Pauli.mulPhase (oa j) (ob j)
      set Q := ∏ j, Pauli.mulPhase (Pauli.mul (oa j) (ob j)) (oc j)
      set R := ∏ j, Pauli.mulPhase (ob j) (oc j)
      set S := ∏ j, Pauli.mulPhase (oa j) (Pauli.mul (ob j) (oc j))
      calc A * B * P * C * Q
          = A * B * C * (P * Q) := by
              rw [mul_right_comm (A * B) P C, mul_assoc (A * B * C) P Q]
        _ = A * B * C * (R * S) := by rw [hProd]
        _ = A * (B * C * R) * S := by
              rw [← mul_assoc (A * B * C) R S, mul_assoc A B C,
                  mul_assoc A (B * C) R]
    · -- Ops equality: per-position Pauli.mul_assoc.
      funext j
      exact Pauli.mul_assoc (oa j) (ob j) (oc j)
  one_mul a := by
    obtain ⟨p, o⟩ := a
    show PauliN.mul PauliN.one ⟨p, o⟩ = ⟨p, o⟩
    simp only [PauliN.mul, PauliN.one]
    refine PauliN.mk.injEq .. |>.mpr ⟨?_, ?_⟩
    · -- phase: 1 * p * ∏_j mulPhase(I, o_j) = p; each mulPhase(I, o_j) = 1.
      have h : ∀ j, Pauli.mulPhase Pauli.I (o j) = (1 : Phase) := fun _ => rfl
      rw [show (Phase.one : Phase) = 1 from rfl,
          Finset.prod_congr rfl (fun j _ => h j), Finset.prod_const_one,
          one_mul, mul_one]
    · funext j
      exact Pauli.I_mul (o j)
  mul_one a := by
    obtain ⟨p, o⟩ := a
    show PauliN.mul ⟨p, o⟩ PauliN.one = ⟨p, o⟩
    simp only [PauliN.mul, PauliN.one]
    refine PauliN.mk.injEq .. |>.mpr ⟨?_, ?_⟩
    · have h : ∀ j, Pauli.mulPhase (o j) Pauli.I = (1 : Phase) :=
        fun j => Pauli.mulPhase_I (o j)
      rw [show (Phase.one : Phase) = 1 from rfl,
          Finset.prod_congr rfl (fun j _ => h j), Finset.prod_const_one,
          mul_one, mul_one]
    · funext j
      exact Pauli.mul_I (o j)
  inv_mul_cancel a := by
    obtain ⟨p, o⟩ := a
    show PauliN.mul (PauliN.inv ⟨p, o⟩) ⟨p, o⟩ = PauliN.one
    simp only [PauliN.mul, PauliN.inv, PauliN.one]
    refine PauliN.mk.injEq .. |>.mpr ⟨?_, ?_⟩
    · -- phase: (p⁻¹ * ∏ mulPhase(o_j, o_j)) * p * ∏ mulPhase(o_j, o_j) = 1
      have h : ∀ j, Pauli.mulPhase (o j) (o j) = (1 : Phase) :=
        fun j => Pauli.mulPhase_self (o j)
      rw [show (Phase.one : Phase) = 1 from rfl,
          Finset.prod_congr rfl (fun j _ => h j), Finset.prod_const_one,
          mul_one, mul_one, inv_mul_cancel]
    · funext j
      exact Pauli.mul_self (o j)

end PauliN
