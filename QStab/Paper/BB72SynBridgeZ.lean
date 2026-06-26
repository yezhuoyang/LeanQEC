import QStab.Paper.BB72SynVerifyZ
import QStab.Paper.BB72ReachableEBridgeZ
import QStab.Paper.BB72BVBridge
import QStab.PauliOps

/-!
# BB72 NZ Z-side syndrome-form ↔ ErrorVec bridge

Connects the precomputed Z-mech (X-stab-syndrome, L_X parity) arrays
to ErrorVec parity definitions. Mirror of `BB72SynBridge` for Z-side.
-/

set_option maxHeartbeats 4000000

namespace QStab.Paper.BB72BVZ

open QStab QStab.Paper.BB72Instance QStab.Paper.BB72JointInstance
  QStab.Paper.BB72ReachableEBridgeZ
open QStab.Paper.BB72BVBridge ErrorVec

/-- X-stab index embedding into Fin 72 (X-stabs occupy indices 0..35). -/
def xStabIdx (i : Fin 36) : Fin 72 := ⟨i.val, by omega⟩

/-! ## Pauli-level: anticommute over multiplication for X-only stab × Z-only operands -/

theorem anticommutes_mul_xor_xz (x a b : Pauli) :
    (x = .I ∨ x = .X) → (a = .I ∨ a = .Z) → (b = .I ∨ b = .Z) →
    Pauli.anticommutes x (Pauli.mul a b) =
      xor (Pauli.anticommutes x a) (Pauli.anticommutes x b) := by
  intro hx ha hb
  rcases hx with hx | hx <;> rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    subst hx <;> subst ha <;> subst hb <;> rfl

/-! ## ErrorVec parity is XOR-homomorphic for X-only stab × Z-only operands -/

theorem parity_mul_xor_xz (x a b : ErrorVec 72)
    (hx : QStab.Paper.BB72BVBridge.is_X_only x = true)
    (ha : is_Z_only_ev a = true) (hb : is_Z_only_ev b = true) :
    ErrorVec.parity x (ErrorVec.mul a b) =
      xor (ErrorVec.parity x a) (ErrorVec.parity x b) := by
  rw [QStab.Paper.BB72BVBridge.is_X_only_iff] at hx
  rw [is_Z_only_ev_iff] at ha
  rw [is_Z_only_ev_iff] at hb
  have hpw : ∀ i : Fin 72,
      Pauli.anticommutes (x i) ((ErrorVec.mul a b) i) =
      xor (Pauli.anticommutes (x i) (a i)) (Pauli.anticommutes (x i) (b i)) := by
    intro i
    show Pauli.anticommutes (x i) (Pauli.mul (a i) (b i)) =
         xor (Pauli.anticommutes (x i) (a i)) (Pauli.anticommutes (x i) (b i))
    exact anticommutes_mul_xor_xz (x i) (a i) (b i) (hx i) (ha i) (hb i)
  unfold ErrorVec.parity
  have hfilter_eq : (Finset.univ.filter fun i : Fin 72 =>
        Pauli.anticommutes (x i) ((ErrorVec.mul a b) i) = true) =
      Finset.univ.filter fun i : Fin 72 =>
        xor (Pauli.anticommutes (x i) (a i))
            (Pauli.anticommutes (x i) (b i)) = true := by
    apply Finset.filter_congr
    intro i _
    rw [hpw i]
  rw [hfilter_eq, QStab.Paper.BB72BVBridge.card_filter_xor_mod_two,
      QStab.Paper.BB72BVBridge.add_mod_two_eq_xor]

/-! ## Per-Z-mech-per-X-stab and L_X identities (data-level, native_decide) -/

theorem mech_xstab_syn_bit_eq :
    ∀ (i : Fin 252) (x : Fin 36),
      (mech_xstab_syn i).getLsbD x.val =
        ErrorVec.parity (bb_stabilizers (xStabIdx x)) (bb_zMech i) := by
  decide

theorem mech_lx_bit_eq :
    ∀ (i : Fin 252) (l : Fin 12),
      (mech_lx i).getLsbD l.val =
        ErrorVec.parity (bb_logicalX_basis l) (bb_zMech i) := by
  decide

/-! ## Chain-level lift -/

def chain_xor_syn_Z : List (Fin 252) → BitVec 36
  | []        => 0
  | i :: rest => mech_xstab_syn i ^^^ chain_xor_syn_Z rest

def chain_xor_lx : List (Fin 252) → BitVec 12
  | []        => 0
  | i :: rest => mech_lx i ^^^ chain_xor_lx rest

/-- The Z-side chain XOR is Z-only. -/
theorem chain_xor_Z_is_Z_only (c : List (Fin 252)) :
    is_Z_only_ev (chain_xor_Z c) = true := by
  induction c with
  | nil =>
    show is_Z_only_ev (ErrorVec.identity 72) = true
    rw [is_Z_only_ev_iff]
    intro _; left; rfl
  | cons head tail ih =>
    show is_Z_only_ev (ErrorVec.mul (bb_zMech head) (chain_xor_Z tail)) = true
    rw [is_Z_only_ev_iff]
    intro i
    have ha : ∀ j : Fin 72, bb_zMech head j = .I ∨ bb_zMech head j = .Z := by
      have := bb_zMech_is_Z_only head
      rw [is_Z_only_ev_iff] at this
      exact this
    have hb : ∀ j : Fin 72, chain_xor_Z tail j = .I ∨ chain_xor_Z tail j = .Z := by
      rw [is_Z_only_ev_iff] at ih
      exact ih
    show (ErrorVec.mul (bb_zMech head) (chain_xor_Z tail)) i = .I ∨
         (ErrorVec.mul (bb_zMech head) (chain_xor_Z tail)) i = .Z
    unfold ErrorVec.mul
    rcases ha i with hai | hai <;> rcases hb i with hbi | hbi <;>
      rw [hai, hbi] <;> simp [Pauli.mul]

/-- Chain-level X-stab-syndrome bit identity. -/
theorem chain_xor_syn_Z_bit_eq_parity (c : List (Fin 252)) (x : Fin 36) :
    (chain_xor_syn_Z c).getLsbD x.val =
    ErrorVec.parity (bb_stabilizers (xStabIdx x)) (chain_xor_Z c) := by
  induction c with
  | nil =>
    show ((0 : BitVec 36)).getLsbD x.val =
         ErrorVec.parity (bb_stabilizers (xStabIdx x)) (ErrorVec.identity 72)
    rw [ErrorVec.parity_identity]
    simp
  | cons head tail ih =>
    show (mech_xstab_syn head ^^^ chain_xor_syn_Z tail).getLsbD x.val =
         ErrorVec.parity (bb_stabilizers (xStabIdx x))
           (ErrorVec.mul (bb_zMech head) (chain_xor_Z tail))
    rw [BitVec.getLsbD_xor]
    have hx_xonly : QStab.Paper.BB72BVBridge.is_X_only (bb_stabilizers (xStabIdx x)) = true :=
      QStab.Paper.BB72BVBridge.is_X_only_bb_xstab (xStabIdx x) (by show x.val < 36; exact x.isLt)
    rw [parity_mul_xor_xz _ _ _ hx_xonly (bb_zMech_is_Z_only head)
        (chain_xor_Z_is_Z_only tail)]
    rw [mech_xstab_syn_bit_eq head x, ih]

/-- Chain-level L_X bit identity. -/
theorem chain_xor_lx_bit_eq_parity (c : List (Fin 252)) (l : Fin 12) :
    (chain_xor_lx c).getLsbD l.val =
    ErrorVec.parity (bb_logicalX_basis l) (chain_xor_Z c) := by
  induction c with
  | nil =>
    show ((0 : BitVec 12)).getLsbD l.val =
         ErrorVec.parity (bb_logicalX_basis l) (ErrorVec.identity 72)
    rw [ErrorVec.parity_identity]
    simp
  | cons head tail ih =>
    show (mech_lx head ^^^ chain_xor_lx tail).getLsbD l.val =
         ErrorVec.parity (bb_logicalX_basis l)
           (ErrorVec.mul (bb_zMech head) (chain_xor_Z tail))
    rw [BitVec.getLsbD_xor]
    rw [parity_mul_xor_xz _ _ _ (is_X_only_bb_lx l) (bb_zMech_is_Z_only head)
        (chain_xor_Z_is_Z_only tail)]
    rw [mech_lx_bit_eq head l, ih]

/-- For Z-only chains, `chain_xor_syn_Z c = 0` iff all X-stab parities are false. -/
theorem chain_xor_syn_Z_zero_iff (c : List (Fin 252)) :
    chain_xor_syn_Z c = 0 ↔
      ∀ x : Fin 36,
        ErrorVec.parity (bb_stabilizers (xStabIdx x)) (chain_xor_Z c) = false := by
  constructor
  · intro h x
    rw [← chain_xor_syn_Z_bit_eq_parity, h]
    simp
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i
    by_cases hi : i < 36
    · rw [chain_xor_syn_Z_bit_eq_parity c ⟨i, hi⟩]
      simp [h]
    · simp [BitVec.getLsbD]
      omega

/-- For Z-only chains, `chain_xor_lx c ≠ 0` iff some L_X parity is true. -/
theorem chain_xor_lx_nonzero_iff (c : List (Fin 252)) :
    chain_xor_lx c ≠ 0 ↔
      ∃ l : Fin 12,
        ErrorVec.parity (bb_logicalX_basis l) (chain_xor_Z c) = true := by
  constructor
  · intro h
    by_contra hno
    push_neg at hno
    apply h
    apply BitVec.eq_of_getLsbD_eq
    intro i
    by_cases hi : i < 12
    · rw [chain_xor_lx_bit_eq_parity c ⟨i, hi⟩]
      have := hno ⟨i, hi⟩
      simp at this
      simp [this]
    · simp [BitVec.getLsbD]
      omega
  · intro ⟨l, hl⟩ h
    rw [← chain_xor_lx_bit_eq_parity] at hl
    rw [h] at hl
    simp at hl

/-! ## Z-side chain attack predicate -/

/-- A Z-side chain is a successful Z-side attack iff its XOR has zero parity
    vs all stabs AND non-zero parity vs some L_X. -/
def bb_chain_attack_Z (chain : List (Fin 252)) : Bool :=
  bb_isSuccessZside (chain_xor_Z chain)

/-! ## Full bridge: bb_chain_attack_Z ↔ chain_xor_syn_Z = 0 ∧ chain_xor_lx ≠ 0 -/

theorem bb_chain_attack_Z_iff_syn (c : List (Fin 252)) :
    bb_chain_attack_Z c = true ↔
    chain_xor_syn_Z c = 0 ∧ chain_xor_lx c ≠ 0 := by
  unfold bb_chain_attack_Z bb_isSuccessZside
  rw [Bool.and_eq_true, List.all_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨h_all, l, _, hl_parity⟩
    refine ⟨?_, ?_⟩
    · rw [chain_xor_syn_Z_zero_iff]
      intro x
      have := h_all (xStabIdx x) (List.mem_finRange _)
      simpa using this
    · rw [chain_xor_lx_nonzero_iff]
      exact ⟨l, hl_parity⟩
  · rintro ⟨h_syn, h_lx⟩
    rw [chain_xor_syn_Z_zero_iff] at h_syn
    rw [chain_xor_lx_nonzero_iff] at h_lx
    refine ⟨?_, ?_⟩
    · intro s _
      simp only [decide_eq_true_eq]
      by_cases hs36 : s.val < 36
      · -- X-stab case: parity from h_syn
        have hsv : s = xStabIdx ⟨s.val, hs36⟩ := by
          unfold xStabIdx
          ext
          show s.val = s.val
          rfl
        rw [hsv]
        exact h_syn ⟨s.val, hs36⟩
      · -- Z-stab case: Z-only × Z-only = 0
        push_neg at hs36
        have hbound : s.val - 36 < 36 := by omega
        have hsv : s = QStab.Paper.BB72BVBridge.zStabIdx ⟨s.val - 36, hbound⟩ := by
          unfold QStab.Paper.BB72BVBridge.zStabIdx
          ext
          show s.val = (s.val - 36) + 36
          omega
        rw [hsv]
        have h_zonly_stab : is_Z_only_ev
            (bb_stabilizers (QStab.Paper.BB72BVBridge.zStabIdx ⟨s.val - 36, hbound⟩)) = true := by
          have := QStab.Paper.BB72BVBridge.is_Z_only_bb_zstab ⟨s.val - 36, hbound⟩
          -- Need: convert is_Z_only (BVBridge) to is_Z_only_ev
          rw [is_Z_only_ev_iff]
          rw [QStab.Paper.BB72BVBridge.is_Z_only_iff] at this
          exact this
        exact parity_Z_only_Z_only _ _ h_zonly_stab (chain_xor_Z_is_Z_only c)
    · obtain ⟨l, hl⟩ := h_lx
      exact ⟨l, List.mem_finRange _, hl⟩

end QStab.Paper.BB72BVZ
