import QStab.Paper.BB72SynVerify
import QStab.Paper.BB72BVBridge
import QStab.Paper.BB72ChainAttack

/-!
# BB72 syndrome-form ↔ ErrorVec bridge

Connects the precomputed mech-syndrome arrays (`BB72SynData`) to the
ErrorVec parity definitions (`BB72Instance`).

This iteration: prove the per-mech identities
  * `(mech_syn i).getLsbD z = parity (bb_zs z) (bb_xMech i)` for all (i, z)
  * `(mech_lz i).getLsbD l = parity (bb_logicalZ_basis l) (bb_xMech i)` for all (i, l)

via `native_decide`. These give the data-level connection from the fast
syndrome arrays to the slow ErrorVec parity computations.
-/

set_option maxHeartbeats 4000000

namespace QStab.Paper.BB72BV

open QStab QStab.Paper.BB72Instance QStab.Paper.BB72ChainCheck
open QStab.Paper.BB72BVBridge

/-- Each bit of `mech_syn[i]` matches the ErrorVec parity vs the corresponding
    Z-stab. Discharged by `native_decide` over 252 × 36 = 9k cases. -/
theorem mech_syn_bit_eq :
    ∀ (i : Fin 252) (z : Fin 36),
      (mech_syn i).getLsbD z.val =
        ErrorVec.parity (bb_stabilizers (zStabIdx z)) (bb_xMech i) := by
  native_decide

/-- Each bit of `mech_lz[i]` matches the ErrorVec parity vs the corresponding
    L_Z basis vector. Discharged by `native_decide` over 252 × 12 = 3k cases. -/
theorem mech_lz_bit_eq :
    ∀ (i : Fin 252) (l : Fin 12),
      (mech_lz i).getLsbD l.val =
        ErrorVec.parity (bb_logicalZ_basis l) (bb_xMech i) := by
  native_decide

/-! ## Chain-level lift: chain syndrome XOR = parity of chain XOR vs Z-stab -/

/-- Chain syndrome XOR via foldr (matches `chain_xor`'s right-fold). -/
def chain_xor_syn : List (Fin 252) → BitVec 36
  | []        => 0
  | i :: rest => mech_syn i ^^^ chain_xor_syn rest

/-- Chain L_Z parity XOR via foldr. -/
def chain_xor_lz : List (Fin 252) → BitVec 12
  | []        => 0
  | i :: rest => mech_lz i ^^^ chain_xor_lz rest

/-- The chain XOR is X-only. -/
theorem chain_xor_is_X_only (c : List (Fin 252)) :
    is_X_only (QStab.Paper.BB72ChainAttack.chain_xor c) = true := by
  induction c with
  | nil =>
    show is_X_only (ErrorVec.identity 72) = true
    rw [is_X_only_iff]
    intro _; left; rfl
  | cons head tail ih =>
    show is_X_only (ErrorVec.mul (bb_xMech head) (QStab.Paper.BB72ChainAttack.chain_xor tail)) = true
    exact mul_preserves_X_only _ _ (bb_xMech_is_X_only head) ih

/-- **Chain-level Z-syndrome bit identity**: for any chain `c` and Z-stab index `z`,
    bit `z` of the chain syndrome XOR equals the ErrorVec parity of the
    corresponding Z-stabilizer with the chain XOR. -/
theorem chain_xor_syn_bit_eq_parity (c : List (Fin 252)) (z : Fin 36) :
    (chain_xor_syn c).getLsbD z.val =
    ErrorVec.parity (bb_stabilizers (zStabIdx z)) (QStab.Paper.BB72ChainAttack.chain_xor c) := by
  induction c with
  | nil =>
    show ((0 : BitVec 36)).getLsbD z.val =
         ErrorVec.parity (bb_stabilizers (zStabIdx z)) (ErrorVec.identity 72)
    rw [ErrorVec.parity_identity]
    simp
  | cons head tail ih =>
    show (mech_syn head ^^^ chain_xor_syn tail).getLsbD z.val =
         ErrorVec.parity (bb_stabilizers (zStabIdx z))
           (ErrorVec.mul (bb_xMech head) (QStab.Paper.BB72ChainAttack.chain_xor tail))
    rw [BitVec.getLsbD_xor]
    rw [parity_mul_xor_zx _ _ _ (is_Z_only_bb_zstab z) (bb_xMech_is_X_only head)
        (chain_xor_is_X_only tail)]
    rw [mech_syn_bit_eq head z, ih]

/-- **Chain-level L_Z bit identity**: for any chain `c` and L_Z basis index `l`,
    bit `l` of the chain L_Z parity XOR equals the ErrorVec parity of the
    corresponding L_Z basis vector with the chain XOR. -/
theorem chain_xor_lz_bit_eq_parity (c : List (Fin 252)) (l : Fin 12) :
    (chain_xor_lz c).getLsbD l.val =
    ErrorVec.parity (bb_logicalZ_basis l) (QStab.Paper.BB72ChainAttack.chain_xor c) := by
  induction c with
  | nil =>
    show ((0 : BitVec 12)).getLsbD l.val =
         ErrorVec.parity (bb_logicalZ_basis l) (ErrorVec.identity 72)
    rw [ErrorVec.parity_identity]
    simp
  | cons head tail ih =>
    show (mech_lz head ^^^ chain_xor_lz tail).getLsbD l.val =
         ErrorVec.parity (bb_logicalZ_basis l)
           (ErrorVec.mul (bb_xMech head) (QStab.Paper.BB72ChainAttack.chain_xor tail))
    rw [BitVec.getLsbD_xor]
    rw [parity_mul_xor_zx _ _ _ (is_Z_only_bb_lz l) (bb_xMech_is_X_only head)
        (chain_xor_is_X_only tail)]
    rw [mech_lz_bit_eq head l, ih]

/-! ## Characterization of bb_isSuccess via chain syndromes -/

/-- For X-only chains, `chain_xor_syn c = 0` iff all Z-stab parities are false. -/
theorem chain_xor_syn_zero_iff (c : List (Fin 252)) :
    chain_xor_syn c = 0 ↔
      ∀ z : Fin 36,
        ErrorVec.parity (bb_stabilizers (zStabIdx z))
          (QStab.Paper.BB72ChainAttack.chain_xor c) = false := by
  constructor
  · intro h z
    rw [← chain_xor_syn_bit_eq_parity, h]
    simp
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i
    by_cases hi : i < 36
    · rw [chain_xor_syn_bit_eq_parity c ⟨i, hi⟩]
      simp [h]
    · simp [BitVec.getLsbD]
      omega

/-- For X-only chains, `chain_xor_lz c ≠ 0` iff some L_Z parity is true. -/
theorem chain_xor_lz_nonzero_iff (c : List (Fin 252)) :
    chain_xor_lz c ≠ 0 ↔
      ∃ l : Fin 12,
        ErrorVec.parity (bb_logicalZ_basis l)
          (QStab.Paper.BB72ChainAttack.chain_xor c) = true := by
  constructor
  · intro h
    by_contra hno
    push_neg at hno
    apply h
    apply BitVec.eq_of_getLsbD_eq
    intro i
    by_cases hi : i < 12
    · rw [chain_xor_lz_bit_eq_parity c ⟨i, hi⟩]
      have := hno ⟨i, hi⟩
      simp at this
      simp [this]
    · simp [BitVec.getLsbD]
      omega
  · intro ⟨l, hl⟩ h
    rw [← chain_xor_lz_bit_eq_parity] at hl
    rw [h] at hl
    simp at hl

/-! ## Full bridge: bb_chain_attack ↔ chain_xor_syn = 0 ∧ chain_xor_lz ≠ 0 -/

/-- Characterizes `bb_chain_attack` (which uses `bb_isSuccess`) entirely
    in terms of the precomputed chain syndromes. -/
theorem bb_chain_attack_iff_syn (c : List (Fin 252)) :
    QStab.Paper.BB72ChainAttack.bb_chain_attack c = true ↔
    chain_xor_syn c = 0 ∧ chain_xor_lz c ≠ 0 := by
  unfold QStab.Paper.BB72ChainAttack.bb_chain_attack
  unfold bb_isSuccess
  rw [Bool.and_eq_true, List.all_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨h_all, l, _, hl_parity⟩
    refine ⟨?_, ?_⟩
    · rw [chain_xor_syn_zero_iff]
      intro z
      have := h_all (zStabIdx z) (List.mem_finRange _)
      simpa using this
    · rw [chain_xor_lz_nonzero_iff]
      exact ⟨l, hl_parity⟩
  · rintro ⟨h_syn, h_lz⟩
    rw [chain_xor_syn_zero_iff] at h_syn
    rw [chain_xor_lz_nonzero_iff] at h_lz
    refine ⟨?_, ?_⟩
    · intro s _
      simp only [decide_eq_true_eq]
      by_cases hs36 : s.val < 36
      · exact parity_xx_zero _ _ (is_X_only_bb_xstab s hs36) (chain_xor_is_X_only c)
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

end QStab.Paper.BB72BV
