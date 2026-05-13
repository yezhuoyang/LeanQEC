import QStab.Paper.BB72SESynVerify
import QStab.Paper.BB72SEReachableEBridge
import QStab.Paper.BB72BVBridge

/-!
# BB72 SE syndrome-form ↔ ErrorVec bridge

Mirror of `BB72SynBridge` for the SE scheduling.
-/

set_option maxHeartbeats 4000000

namespace QStab.Paper.BB72BVSE

open QStab QStab.Paper.BB72Instance QStab.Paper.BB72SEInstance
  QStab.Paper.BB72ReachableEBridgeSE
open QStab.Paper.BB72BVBridge ErrorVec

/-- Each bit of `mech_se_syn[i]` matches the ErrorVec parity vs Z-stab. -/
theorem mech_se_syn_bit_eq :
    ∀ (i : Fin 252) (z : Fin 36),
      (mech_se_syn i).getLsbD z.val =
        ErrorVec.parity (bb_stabilizers (zStabIdx z)) (bb_se_xMech i) := by
  native_decide

theorem mech_se_lz_bit_eq :
    ∀ (i : Fin 252) (l : Fin 12),
      (mech_se_lz i).getLsbD l.val =
        ErrorVec.parity (bb_logicalZ_basis l) (bb_se_xMech i) := by
  native_decide

def chain_xor_se_syn : List (Fin 252) → BitVec 36
  | []        => 0
  | i :: rest => mech_se_syn i ^^^ chain_xor_se_syn rest

def chain_xor_se_lz : List (Fin 252) → BitVec 12
  | []        => 0
  | i :: rest => mech_se_lz i ^^^ chain_xor_se_lz rest

/-- The SE chain XOR is X-only. -/
theorem chain_xor_SE_is_X_only (c : List (Fin 252)) :
    is_X_only (chain_xor_SE c) = true := by
  induction c with
  | nil =>
    show is_X_only (ErrorVec.identity 72) = true
    rw [is_X_only_iff]
    intro _; left; rfl
  | cons head tail ih =>
    show is_X_only (ErrorVec.mul (bb_se_xMech head) (chain_xor_SE tail)) = true
    exact mul_preserves_X_only _ _ (bb_se_xMech_is_X_only head) ih

theorem chain_xor_se_syn_bit_eq_parity (c : List (Fin 252)) (z : Fin 36) :
    (chain_xor_se_syn c).getLsbD z.val =
    ErrorVec.parity (bb_stabilizers (zStabIdx z)) (chain_xor_SE c) := by
  induction c with
  | nil =>
    show ((0 : BitVec 36)).getLsbD z.val =
         ErrorVec.parity (bb_stabilizers (zStabIdx z)) (ErrorVec.identity 72)
    rw [ErrorVec.parity_identity]
    simp
  | cons head tail ih =>
    show (mech_se_syn head ^^^ chain_xor_se_syn tail).getLsbD z.val =
         ErrorVec.parity (bb_stabilizers (zStabIdx z))
           (ErrorVec.mul (bb_se_xMech head) (chain_xor_SE tail))
    rw [BitVec.getLsbD_xor]
    rw [parity_mul_xor_zx _ _ _ (is_Z_only_bb_zstab z) (bb_se_xMech_is_X_only head)
        (chain_xor_SE_is_X_only tail)]
    rw [mech_se_syn_bit_eq head z, ih]

theorem chain_xor_se_lz_bit_eq_parity (c : List (Fin 252)) (l : Fin 12) :
    (chain_xor_se_lz c).getLsbD l.val =
    ErrorVec.parity (bb_logicalZ_basis l) (chain_xor_SE c) := by
  induction c with
  | nil =>
    show ((0 : BitVec 12)).getLsbD l.val =
         ErrorVec.parity (bb_logicalZ_basis l) (ErrorVec.identity 72)
    rw [ErrorVec.parity_identity]
    simp
  | cons head tail ih =>
    show (mech_se_lz head ^^^ chain_xor_se_lz tail).getLsbD l.val =
         ErrorVec.parity (bb_logicalZ_basis l)
           (ErrorVec.mul (bb_se_xMech head) (chain_xor_SE tail))
    rw [BitVec.getLsbD_xor]
    rw [parity_mul_xor_zx _ _ _ (is_Z_only_bb_lz l) (bb_se_xMech_is_X_only head)
        (chain_xor_SE_is_X_only tail)]
    rw [mech_se_lz_bit_eq head l, ih]

theorem chain_xor_se_syn_zero_iff (c : List (Fin 252)) :
    chain_xor_se_syn c = 0 ↔
      ∀ z : Fin 36,
        ErrorVec.parity (bb_stabilizers (zStabIdx z)) (chain_xor_SE c) = false := by
  constructor
  · intro h z
    rw [← chain_xor_se_syn_bit_eq_parity, h]
    simp
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i
    by_cases hi : i < 36
    · rw [chain_xor_se_syn_bit_eq_parity c ⟨i, hi⟩]
      simp [h]
    · simp [BitVec.getLsbD]
      omega

theorem chain_xor_se_lz_nonzero_iff (c : List (Fin 252)) :
    chain_xor_se_lz c ≠ 0 ↔
      ∃ l : Fin 12,
        ErrorVec.parity (bb_logicalZ_basis l) (chain_xor_SE c) = true := by
  constructor
  · intro h
    by_contra hno
    push_neg at hno
    apply h
    apply BitVec.eq_of_getLsbD_eq
    intro i
    by_cases hi : i < 12
    · rw [chain_xor_se_lz_bit_eq_parity c ⟨i, hi⟩]
      have := hno ⟨i, hi⟩
      simp at this
      simp [this]
    · simp [BitVec.getLsbD]
      omega
  · intro ⟨l, hl⟩ h
    rw [← chain_xor_se_lz_bit_eq_parity] at hl
    rw [h] at hl
    simp at hl

/-- SE chain attack predicate. -/
def bb_chain_attack_SE (chain : List (Fin 252)) : Bool :=
  bb_se_isSuccess (chain_xor_SE chain)

theorem bb_chain_attack_SE_iff_syn (c : List (Fin 252)) :
    bb_chain_attack_SE c = true ↔
    chain_xor_se_syn c = 0 ∧ chain_xor_se_lz c ≠ 0 := by
  unfold bb_chain_attack_SE bb_se_isSuccess
  rw [Bool.and_eq_true, List.all_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨h_all, l, _, hl_parity⟩
    refine ⟨?_, ?_⟩
    · rw [chain_xor_se_syn_zero_iff]
      intro z
      have := h_all (zStabIdx z) (List.mem_finRange _)
      simpa using this
    · rw [chain_xor_se_lz_nonzero_iff]
      exact ⟨l, hl_parity⟩
  · rintro ⟨h_syn, h_lz⟩
    rw [chain_xor_se_syn_zero_iff] at h_syn
    rw [chain_xor_se_lz_nonzero_iff] at h_lz
    refine ⟨?_, ?_⟩
    · intro s _
      simp only [decide_eq_true_eq]
      by_cases hs36 : s.val < 36
      · exact parity_xx_zero _ _ (is_X_only_bb_xstab s hs36) (chain_xor_SE_is_X_only c)
      · push_neg at hs36
        have hbound : s.val - 36 < 36 := by omega
        have hsv : s = zStabIdx ⟨s.val - 36, hbound⟩ := by
          unfold zStabIdx
          ext
          show s.val = (s.val - 36) + 36
          omega
        rw [hsv]
        exact h_syn ⟨s.val - 36, hbound⟩
    · obtain ⟨l, hl⟩ := h_lz
      exact ⟨l, List.mem_finRange _, hl⟩

end QStab.Paper.BB72BVSE
