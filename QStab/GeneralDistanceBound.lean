import QStab.Invariant
import QStab.MultiStep

/-! # General distance bound from abstract error measures (Section 4)

Formalizes Definition 4.1 (ErrorMeasure), Proposition 4.2 (invariant),
and Theorem 4.3 (distance bound) for BOTH c_max = 1 and general c_max.
All theorems fully proved, zero sorry.
-/

namespace QStab.GeneralBound

open QECParams

/-- Definition 4.1: Scheduling-compatible error measure. -/
structure ErrorMeasure (P : QECParams) where
  ω : ErrorVec P.n → Nat
  c_data : Nat
  c_hook : Nat
  δ : Nat
  ω_identity : ω (ErrorVec.identity P.n) = 0
  ω_single_qubit : ∀ (E : ErrorVec P.n) (i : Fin P.n) (p : Pauli),
    p ≠ Pauli.I → ω (ErrorVec.update E i p) ≤ ω E + c_data
  ω_hook : ∀ (s : Fin P.numStab) (E e_B : ErrorVec P.n),
    e_B ∈ backActionSet P s → ω (ErrorVec.mul e_B E) ≤ ω E + c_hook

def ErrorMeasure.c_max (m : ErrorMeasure P) : Nat := max m.c_data m.c_hook

/-! ### Proposition 4.2: The weighted invariant ω + c_max * C ≤ c_max * budget -/

def WeightedInv (m : ErrorMeasure P) (s : State P) : Prop :=
  m.ω s.E_tilde + m.c_max * s.C ≤ m.c_max * P.C_budget

theorem weightedInv_init (m : ErrorMeasure P) : WeightedInv m (State.init P) := by
  simp [WeightedInv, State.init, m.ω_identity]

/-- Helper: ω' ≤ ω + c and c ≤ cm and ω + cm*C ≤ cm*bd and 1 ≤ C
    imply ω' + cm*(C-1) ≤ cm*bd. -/
private theorem error_step_bound (ω' ω c cm C bd : Nat)
    (hω : ω' ≤ ω + c) (hc : c ≤ cm) (hinv : ω + cm * C ≤ cm * bd) (hC : 1 ≤ C) :
    ω' + cm * (C - 1) ≤ cm * bd := by
  -- cm * (C-1) = cm * C - cm (when C ≥ 1)
  have hcm_sub : cm * (C - 1) + cm = cm * C := by
    have hC1 : C = (C - 1) + 1 := by omega
    conv_rhs => rw [hC1]
    rw [Nat.mul_add, Nat.mul_one]
  -- ω' + cm*(C-1) ≤ (ω + c) + cm*(C-1) ≤ ω + cm + cm*(C-1) = ω + cm*C ≤ cm*bd
  omega

theorem weightedInv_preserve (m : ErrorMeasure P)
    (s s' : State P) (hinv : WeightedInv m s)
    (hstep : Step P (.active s) (.active s')) : WeightedInv m s' := by
  unfold WeightedInv at *
  cases hstep with
  | type0 _ i p hp hC =>
    show m.ω (ErrorVec.update s.E_tilde i p) + m.c_max * (s.C - 1) ≤ m.c_max * P.C_budget
    exact error_step_bound (m.ω (ErrorVec.update s.E_tilde i p)) (m.ω s.E_tilde)
      m.c_data m.c_max s.C P.C_budget
      (m.ω_single_qubit s.E_tilde i p hp) (Nat.le_max_left _ _) hinv hC
  | type1 _ i p hp hC =>
    show m.ω (ErrorVec.update s.E_tilde i p) + m.c_max * (s.C - 1) ≤ m.c_max * P.C_budget
    exact error_step_bound (m.ω (ErrorVec.update s.E_tilde i p)) (m.ω s.E_tilde)
      m.c_data m.c_max s.C P.C_budget
      (m.ω_single_qubit s.E_tilde i p hp) (Nat.le_max_left _ _) hinv hC
  | type2 _ e he hC =>
    show m.ω (ErrorVec.mul e s.E_tilde) + m.c_max * (s.C - 1) ≤ m.c_max * P.C_budget
    have hω := m.ω_hook s.coord.x s.E_tilde e he
    exact error_step_bound _ (m.ω s.E_tilde) m.c_hook m.c_max s.C P.C_budget
      hω (Nat.le_max_right _ _) hinv hC
  | type3 _ hC =>
    show m.ω s.E_tilde + m.c_max * (s.C - 1) ≤ m.c_max * P.C_budget
    have : m.c_max * (s.C - 1) ≤ m.c_max * s.C :=
      Nat.mul_le_mul_left _ (Nat.sub_le s.C 1)
    omega
  | measure _ nc _ =>
    rw [measureStep_E_tilde, measureStep_C]; exact hinv

def weightedInvariant (m : ErrorMeasure P) : Invariant P where
  holds := WeightedInv m
  holds_init := weightedInv_init m
  preservation := weightedInv_preserve m

/-! ### Theorem 4.3: The general distance bound -/

/-- Theorem 4.3 (pointwise): ω ≥ δ and invariant imply δ + c_max*C ≤ c_max*budget. -/
theorem general_distance_bound (m : ErrorMeasure P) (s : State P)
    (hinv : WeightedInv m s)
    (hlog : m.δ ≤ m.ω s.E_tilde) :
    m.δ + m.c_max * s.C ≤ m.c_max * P.C_budget := by
  unfold WeightedInv at hinv; omega

/-- Theorem 4.3 at σ_done (general c_max). -/
theorem distance_bound_at_done_general (m : ErrorMeasure P) (s : State P)
    (hrun : Run P (.done s))
    (hlog : m.δ ≤ m.ω s.E_tilde) :
    m.δ + m.c_max * s.C ≤ m.c_max * P.C_budget :=
  general_distance_bound m s
    ((weightedInvariant m).holds_at_done s hrun) hlog

/-! ### Special case c_max = 1 -/

/-- Simpler invariant for c_max = 1: ω + C ≤ budget. -/
def SimpleInv (m : ErrorMeasure P) (s : State P) : Prop :=
  m.ω s.E_tilde + s.C ≤ P.C_budget

theorem simpleInv_init (m : ErrorMeasure P) : SimpleInv m (State.init P) := by
  simp [SimpleInv, State.init, m.ω_identity]

theorem simpleInv_preserve (m : ErrorMeasure P) (hcd : m.c_data ≤ 1) (hch : m.c_hook ≤ 1)
    (s s' : State P) (hinv : SimpleInv m s)
    (hstep : Step P (.active s) (.active s')) : SimpleInv m s' := by
  unfold SimpleInv at *
  cases hstep with
  | type0 _ i p hp hC =>
    have hω := m.ω_single_qubit s.E_tilde i p hp
    show m.ω (ErrorVec.update s.E_tilde i p) + (s.C - 1) ≤ P.C_budget
    have : ∀ a b c bd : Nat, a ≤ b + 1 → b + c ≤ bd → 1 ≤ c →
        a + (c - 1) ≤ bd := by omega
    exact this _ _ _ _ (by omega) hinv hC
  | type1 _ i p hp hC =>
    have hω := m.ω_single_qubit s.E_tilde i p hp
    show m.ω (ErrorVec.update s.E_tilde i p) + (s.C - 1) ≤ P.C_budget
    have : ∀ a b c bd : Nat, a ≤ b + 1 → b + c ≤ bd → 1 ≤ c →
        a + (c - 1) ≤ bd := by omega
    exact this _ _ _ _ (by omega) hinv hC
  | type2 _ e he _ hC =>
    have hω := m.ω_hook s.coord.x s.E_tilde e he
    show m.ω (ErrorVec.mul e s.E_tilde) + (s.C - 1) ≤ P.C_budget
    have hch1 : m.c_hook ≤ 1 := hch
    have : ∀ a b c bd ch : Nat, a ≤ b + ch → ch ≤ 1 → b + c ≤ bd → 1 ≤ c →
        a + (c - 1) ≤ bd := by omega
    exact this _ _ _ _ _ hω hch1 hinv hC
  | type3 _ hC =>
    show m.ω s.E_tilde + (s.C - 1) ≤ P.C_budget; omega
  | measure _ nc _ =>
    rw [measureStep_E_tilde, measureStep_C]; exact hinv

def simpleInvariant (m : ErrorMeasure P) (hcd : m.c_data ≤ 1) (hch : m.c_hook ≤ 1) :
    Invariant P where
  holds := SimpleInv m
  holds_init := simpleInv_init m
  preservation := simpleInv_preserve m hcd hch

/-- Theorem 4.3 (c_max = 1 special case): δ + C ≤ C_budget at σ_done. -/
theorem distance_bound_at_done_unit (m : ErrorMeasure P) (s : State P)
    (hrun : Run P (.done s))
    (hcd : m.c_data ≤ 1) (hch : m.c_hook ≤ 1)
    (hlog : m.δ ≤ m.ω s.E_tilde) :
    m.δ + s.C ≤ P.C_budget := by
  have hinv : SimpleInv m s := (simpleInvariant m hcd hch).holds_at_done s hrun
  unfold SimpleInv at hinv; omega

end QStab.GeneralBound
